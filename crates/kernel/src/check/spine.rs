//! Applications with holes: an argument written `_`, or a level-polymorphic
//! head whose levels are left out (`Nat.elim` without `@ctx {.m = ...}`).
//!
//! The algorithm is local argument synthesis (Pierce and Turner, "Local
//! type inference", TOPLAS 2000) by first-order matching on read-back types,
//! which suffices for the endpoints of equality reasoning and the motive
//! level of a recursor (issue #470). Every argument position gets a
//! placeholder variable, bound past the context, and every left-out level a
//! placeholder parameter, past the global's own. Then:
//!
//! 1. In check mode, the head's result type, with every argument a
//!    placeholder, is matched against the expected type. What this solves
//!    is a guess.
//! 2. The arguments are elaborated left to right. One whose type is known
//!    (no placeholder left in it) is checked; otherwise it is inferred, a
//!    lambda under the known domains of its type, and its type matched
//!    against the one it should have. A `_` stays a placeholder until solved.
//!    An argument whose type conflicts with the guesses waits; if something
//!    is still unsolved after the last argument, the waiting ones are matched
//!    again, the guesses dropped if they still conflict. Then the result
//!    with the arguments in is matched against the expected type, and a
//!    dropped guess fills what is still unsolved.
//! 3. The application is checked again with the solutions, by the ordinary
//!    rules: each solution against its type by the re-checker, each other
//!    argument's type by conversion, and the result against the expected
//!    type.
//!
//! Matching only guesses; step 3 decides. A guess can be wrong where an
//! equality computes (`nsucc a ~ nsucc b` is `a ~ b`), and then step 3
//! rejects it and the argument has to be written out.
//!
//! Entry point: `Checker::spine`, for a raw term that `is_open_spine`.

use std::rc::Rc;

use utilities::{Code, Result, Span};

use super::{Checker, Context};
use crate::level::Level;
use crate::nbe::{global_type, quote, BindingVal, Closure, Lvl, Val};
use crate::recheck::check_in;
use crate::signature::GlobalId;
use crate::syntax::{Raw, RawKind};
use crate::term::{children, mentions, rename, Index, Name, Term};

/// The head of a spine: a global at its levels, `None` where left out, or
/// any term with its type.
enum Head {
    Global(GlobalId, Vec<Option<Level>>),
    Term(Term, Val),
}

/// How an argument was elaborated, its term in the context with the
/// placeholders bound.
enum Arg {
    Hole,
    /// Checked against the type it should have then, kept to compare with
    /// the one it has once every placeholder is solved.
    Checked(Term, Val),
    Inferred(Term, Val),
}

/// The placeholders of one spine and what matching has solved them to.
#[derive(Clone)]
struct Holes {
    /// The depth with every placeholder bound; argument `j`'s placeholder is
    /// the variable at level `depth - count + j`.
    depth: Lvl,
    count: u32,
    /// Left-out level `s` is level parameter `first_level + s`.
    first_level: u32,
    /// Each argument's solution, at `depth`.
    terms: Vec<Option<Term>>,
    levels: Vec<Option<Level>>,
    /// Whether a solution is only a guess from the expected type.
    guessed: (Vec<bool>, Vec<bool>),
}

impl Holes {
    /// The argument whose placeholder index `i` is, under `under` binders.
    fn argument(&self, i: Index, under: Index) -> Option<usize> {
        let i = i.checked_sub(under)?;
        (i < self.count).then(|| (self.count - 1 - i) as usize)
    }

    fn level_slot(&self, p: u32) -> Option<usize> {
        p.checked_sub(self.first_level).map(|s| s as usize)
    }

    /// Whether `t`, under `under` binders, still mentions a placeholder.
    fn open(&self, t: &Term, under: Index) -> bool {
        let level_open = |l: &Level| self.level_open(l);
        let here = match t {
            Term::Var(i) => self.argument(*i, under).is_some(),
            Term::Global(_, levels) => levels.iter().any(level_open),
            Term::Sort(l) | Term::Eq(l, ..) | Term::Quot(_, _, l, _) | Term::QElim(_, _, _, l, _) => level_open(l),
            Term::Pi(b) | Term::Sigma(b) => level_open(&b.dom_level) || level_open(&b.cod_level),
            _ => false,
        };
        here || children(t).into_iter().any(|(c, k)| self.open(c, under + k))
    }

    fn level_open(&self, l: &Level) -> bool {
        match l {
            Level::Zero => false,
            Level::Succ(l) => self.level_open(l),
            Level::Max(a, b) | Level::IMax(a, b) => self.level_open(a) || self.level_open(b),
            Level::Param(p) => self.level_slot(*p).is_some(),
        }
    }

    /// Match `pattern` against `target`, both at `depth`, solving
    /// placeholders; on failure nothing is solved.
    fn unify(&mut self, pattern: &Term, target: &Term) -> bool {
        let saved = self.clone();
        let ok = self.matches(0, pattern, target);
        if !ok {
            *self = saved;
        }
        ok
    }

    /// Mark every solution so far a guess.
    fn guess(&mut self) {
        self.guessed = (
            self.terms.iter().map(Option::is_some).collect(),
            self.levels.iter().map(Option::is_some).collect(),
        );
    }

    /// Forget the guesses, returning whether there were any.
    fn drop_guesses(&mut self) -> bool {
        let any = self.guessed.0.iter().chain(&self.guessed.1).any(|g| *g);
        for (solution, guessed) in self.terms.iter_mut().zip(&mut self.guessed.0) {
            if std::mem::take(guessed) {
                *solution = None;
            }
        }
        for (solution, guessed) in self.levels.iter_mut().zip(&mut self.guessed.1) {
            if std::mem::take(guessed) {
                *solution = None;
            }
        }
        any
    }

    fn matches(&mut self, under: Index, p: &Term, t: &Term) -> bool {
        if let Term::Var(i) = p {
            if let Some(j) = self.argument(*i, under) {
                return self.solve(j, under, t);
            }
        }
        if std::mem::discriminant(p) != std::mem::discriminant(t) {
            return false;
        }
        let levels_match = match (p, t) {
            (Term::Var(i), Term::Var(k)) => i == k,
            (Term::Global(a, la), Term::Global(b, lb)) => {
                a == b && la.len() == lb.len() && la.iter().zip(lb.iter()).all(|(x, y)| self.level(x, y))
            }
            (Term::Sort(a), Term::Sort(b))
            | (Term::Eq(a, ..), Term::Eq(b, ..))
            | (Term::Quot(_, _, a, _), Term::Quot(_, _, b, _))
            | (Term::QElim(_, _, _, a, _), Term::QElim(_, _, _, b, _)) => self.level(a, b),
            (Term::Pi(a), Term::Pi(b)) | (Term::Sigma(a), Term::Sigma(b)) => {
                self.level(&a.dom_level, &b.dom_level) && self.level(&a.cod_level, &b.cod_level)
            }
            // A lambda's domain is there only where the source wrote one.
            (Term::Lam(_, _, a), Term::Lam(_, _, b)) => return self.matches(under + 1, a, b),
            _ => true,
        };
        let (ps, ts) = (children(p), children(t));
        levels_match && ps.len() == ts.len() && ps.into_iter().zip(ts).all(|((p, k), (t, _))| self.matches(under + k, p, t))
    }

    /// Solve argument `j` to `t`, found under `under` binders.
    fn solve(&mut self, j: usize, under: Index, t: &Term) -> bool {
        // A solution lives outside the binders it was found under, and
        // cannot mention a placeholder.
        if (0..under).any(|ix| mentions(t, ix)) || self.open(t, under) {
            return false;
        }
        let t = rename(t, 0, &|i| i - under);
        match &self.terms[j] {
            Some(solved) => *solved == t,
            None => {
                self.terms[j] = Some(t);
                true
            }
        }
    }

    fn level(&mut self, p: &Level, t: &Level) -> bool {
        match (p, t) {
            (Level::Param(q), _) if self.level_slot(*q).is_some() && !self.level_open(t) => {
                let s = self.level_slot(*q).unwrap();
                match &self.levels[s] {
                    Some(solved) => solved.equal(t),
                    None => {
                        self.levels[s] = Some(t.clone());
                        true
                    }
                }
            }
            (Level::Succ(p), Level::Succ(t)) => self.level(p, t),
            (Level::Max(p1, p2), Level::Max(t1, t2)) | (Level::IMax(p1, p2), Level::IMax(t1, t2)) => {
                self.level(p1, t1) && self.level(p2, t2)
            }
            _ => p.equal(t),
        }
    }
}

/// The head and arguments of an application.
fn flatten(raw: &Raw) -> (&Raw, Vec<&Raw>) {
    let mut args = Vec::new();
    let mut head = raw;
    while let RawKind::App(f, a) = &head.kind {
        args.push(&**a);
        head = f;
    }
    args.reverse();
    (head, args)
}

impl Checker<'_> {
    /// Whether `raw` is an application with a `_` argument, or a global
    /// (applied or not) with a level left out.
    pub(super) fn is_open_spine(&self, ctx: &Context, raw: &Raw) -> bool {
        let (head, args) = flatten(raw);
        args.iter().any(|a| matches!(a.kind, RawKind::Hole)) || self.global_head(ctx, head).is_some_and(|(id, given)| given < self.sig.global(id).level_params.len())
    }

    /// The global a spine's head names, with how many levels it is given.
    fn global_head(&self, ctx: &Context, head: &Raw) -> Option<(GlobalId, usize)> {
        let RawKind::Var(name, level_args) = &head.kind else { return None };
        if ctx.names.contains(name) {
            return None;
        }
        Some((self.sig.lookup(name)?, level_args.len()))
    }

    // Algorithm [Local argument synthesis]
    /// Elaborate an open spine, against `expected` in check mode.
    pub(super) fn spine(&self, ctx: &mut Context, raw: &Raw, expected: Option<&Val>) -> Result<(Term, Val)> {
        let (head_raw, args) = flatten(raw);
        let head = match (&head_raw.kind, self.global_head(ctx, head_raw)) {
            (RawKind::Var(name, level_args), Some((id, _))) => Head::Global(id, self.level_args(ctx, name, id, level_args)?),
            _ => {
                let (t, ty) = self.infer(ctx, head_raw)?;
                Head::Term(t, ty)
            }
        };
        let left_out = match &head {
            Head::Global(_, given) => given.iter().filter(|l| l.is_none()).count(),
            Head::Term(..) => 0,
        };
        let outer = ctx.depth();
        let count = args.len() as u32;
        let mut holes = Holes {
            depth: outer + count,
            count,
            first_level: ctx.level_names.len() as u32,
            terms: vec![None; args.len()],
            levels: vec![None; left_out],
            guessed: (vec![false; args.len()], vec![false; left_out]),
        };

        let env = ctx.env.clone();
        for _ in 0..count {
            ctx.bind("?".into(), Val::Top);
        }
        let elaborated = self.solve_spine(ctx, &head, &args, expected, &mut holes);
        ctx.names.truncate(outer as usize);
        ctx.types.truncate(outer as usize);
        ctx.env = env;
        let elaborated = elaborated?;

        // Step 3: the application again, by the ordinary rules.
        let down = |t: &Term| {
            assert!((0..count).all(|ix| !mentions(t, ix)), "an elaborated argument mentions a placeholder");
            rename(t, 0, &|i| i - count)
        };
        let (mut term, mut ty) = match head {
            Head::Term(t, ty) => (t, ty),
            Head::Global(id, given) => {
                let mut solved = holes.levels.iter();
                let mut levels = Vec::with_capacity(given.len());
                for (i, l) in given.into_iter().enumerate() {
                    match l.or_else(|| solved.next().cloned().flatten()) {
                        Some(l) => levels.push(l),
                        None => {
                            let global = self.sig.global(id);
                            let (name, param) = (&global.name, &global.level_params[i]);
                            return Err(self
                                .error(Code::TypeAnnotationRequired, head_raw.span, format!("cannot infer level `{param}` of `{name}`"))
                                .with_help(format!("write `{name} @ctx {{.{param} = ...}}`")));
                        }
                    }
                }
                let levels: Rc<[Level]> = levels.into();
                let ty = global_type(&self.sig, id, levels.clone());
                (Term::Global(id, levels), ty)
            }
        };
        for (j, (arg, raw_arg)) in elaborated.into_iter().zip(&args).enumerate() {
            let Val::Pi(pi) = ty.force(&self.sig).clone() else {
                let end = if j == 0 { head_raw.span.end } else { args[j - 1].span.end };
                let applied = Span::new(head_raw.span.start, end);
                return Err(self.error(
                    Code::TypeMismatch,
                    applied,
                    format!("applied a value of type `{}`, which is not a function", self.show(ctx, &ty)),
                ));
            };
            let arg_term = match arg {
                Arg::Checked(t, dom) => {
                    if !self.conversion(ctx).conv_type(&dom, &pi.dom) {
                        return Err(self.mismatch(ctx, raw_arg.span, &pi.dom, &dom));
                    }
                    down(&t)
                }
                Arg::Inferred(t, found) => {
                    if !self.conversion(ctx).conv_type(&found, &pi.dom) {
                        return Err(self.mismatch(ctx, raw_arg.span, &pi.dom, &found));
                    }
                    self.as_proof(ctx, down(&t), &pi.dom)
                }
                Arg::Hole => {
                    let Some(solution) = &holes.terms[j] else {
                        return Err(self
                            .error(Code::TypeAnnotationRequired, raw_arg.span, "cannot infer this argument")
                            .with_note(format!("it has type `{}`", self.show(ctx, &pi.dom)))
                            .with_help("write it out"));
                    };
                    let solution = down(solution);
                    let scope = (&ctx.names[..], &ctx.types[..], &ctx.env);
                    if let Err(why) = check_in(&self.sig, scope, &ctx.level_names, &solution, &pi.dom) {
                        return Err(self
                            .error(Code::TypeMismatch, raw_arg.span, "this argument was inferred, but does not fit")
                            .with_note(why)
                            .with_help("write it out"));
                    }
                    self.as_proof(ctx, solution, &pi.dom)
                }
            };
            ty = pi.cod.apply(&self.sig, self.eval(ctx, &arg_term));
            term = Term::app(term, arg_term);
        }
        if let Some(expected) = expected {
            if !self.conversion(ctx).conv_type(&ty, expected) {
                return Err(self.mismatch(ctx, raw.span, expected, &ty));
            }
        }
        Ok((term, ty))
    }

    /// `t` as checked against `ty`: wrapped when `ty` is a proposition.
    /// See Rule [Proof-Witness].
    fn as_proof(&self, ctx: &mut Context, t: Term, ty: &Val) -> Term {
        if self.conversion(ctx).is_proposition(ty) && !matches!(t, Term::Proof(_)) {
            Term::Proof(Rc::new(t))
        } else {
            t
        }
    }

    /// Steps 1 and 2: solve the placeholders and elaborate the arguments, in
    /// the context with the placeholders bound.
    fn solve_spine(&self, ctx: &mut Context, head: &Head, args: &[&Raw], expected: Option<&Val>, holes: &mut Holes) -> Result<Vec<Arg>> {
        let first = holes.depth - holes.count;
        let placeholder = |j: usize| Val::var(first + j as Lvl);
        // Step 1, guessing from the result alone: what it says about the
        // positions written out is dropped.
        if let Some(expected) = expected {
            let all: Vec<Val> = (0..args.len()).map(placeholder).collect();
            if let Some(result) = self.applied_type(head, holes, &all) {
                self.unify(holes, holes.depth, &result, expected);
                for (j, a) in args.iter().enumerate() {
                    if !matches!(a.kind, RawKind::Hole) {
                        holes.terms[j] = None;
                    }
                }
                holes.guess();
            }
        }
        let guesses = (holes.terms.clone(), holes.levels.clone());

        // Step 2. An argument whose type conflicts with the guesses waits.
        let mut elaborated: Vec<Arg> = Vec::with_capacity(args.len());
        let mut postponed: Vec<(usize, Val)> = Vec::new();
        for (j, raw) in args.iter().enumerate() {
            // Not a function: step 3 says so.
            let Some(dom) = self.domain(ctx, head, holes, &elaborated) else {
                elaborated.extend(args[j..].iter().map(|_| Arg::Hole));
                break;
            };
            let arg = if matches!(raw.kind, RawKind::Hole) {
                Arg::Hole
            } else if !holes.open(&quote(&self.sig, ctx.depth(), &dom), 0) {
                Arg::Checked(self.check(ctx, raw, &dom)?, dom)
            } else {
                let (t, found) = self.infer_under(ctx, raw, &dom, holes)?;
                if !self.unify(holes, ctx.depth(), &dom, &found) {
                    postponed.push((j, found.clone()));
                }
                Arg::Inferred(t, found)
            };
            elaborated.push(arg);
        }
        // What the waiting arguments say wins over the guesses, if something
        // is still unsolved.
        for (j, found) in postponed {
            let unsolved = holes.terms.iter().zip(args).any(|(t, a)| t.is_none() && matches!(a.kind, RawKind::Hole));
            if !unsolved && holes.levels.iter().all(Option::is_some) {
                break;
            }
            let dom = |holes: &Holes| self.domain(ctx, head, holes, &elaborated[..j]).expect("a function before");
            if self.unify(holes, ctx.depth(), &dom(holes), &found) {
                continue;
            }
            let saved = holes.clone();
            if !(holes.drop_guesses() && self.unify(holes, ctx.depth(), &dom(holes), &found)) {
                *holes = saved;
            }
        }
        // What is left to solve, from the result with the arguments in.
        if let (Some(expected), true) = (expected, elaborated.len() == args.len()) {
            if let Some(result) = self.applied_type(head, holes, &self.argument_values(ctx, &elaborated, holes)) {
                self.unify(holes, holes.depth, &result, expected);
            }
        }
        // A guess dropped for a conflict elsewhere may still be right; step
        // 3 decides.
        for (solution, guess) in holes.terms.iter_mut().zip(guesses.0) {
            if solution.is_none() {
                *solution = guess;
            }
        }
        for (solution, guess) in holes.levels.iter_mut().zip(guesses.1) {
            if solution.is_none() {
                *solution = guess;
            }
        }
        Ok(elaborated)
    }

    /// The values of the arguments elaborated so far, a placeholder for
    /// each unsolved `_`.
    fn argument_values(&self, ctx: &Context, elaborated: &[Arg], holes: &Holes) -> Vec<Val> {
        let first = holes.depth - holes.count;
        elaborated
            .iter()
            .enumerate()
            .map(|(k, a)| match a {
                Arg::Checked(t, _) | Arg::Inferred(t, _) => self.eval(ctx, t),
                Arg::Hole => match &holes.terms[k] {
                    Some(t) => self.eval(ctx, t),
                    None => Val::var(first + k as Lvl),
                },
            })
            .collect()
    }

    /// Match `pattern` against `target` at `depth`, as read back and, failing
    /// that, with a definition at either head unfolded (`same x y` is an
    /// equality).
    fn unify(&self, holes: &mut Holes, depth: Lvl, pattern: &Val, target: &Val) -> bool {
        let read = |v: &Val| quote(&self.sig, depth, v);
        holes.unify(&read(pattern), &read(target)) || holes.unify(&read(pattern.force(&self.sig)), &read(target.force(&self.sig)))
    }

    /// The type of the argument after `elaborated`, if the head takes one.
    fn domain(&self, ctx: &Context, head: &Head, holes: &Holes, elaborated: &[Arg]) -> Option<Val> {
        let values = self.argument_values(ctx, elaborated, holes);
        match self.applied_type(head, holes, &values)?.force(&self.sig) {
            Val::Pi(pi) => Some(pi.dom.clone()),
            _ => None,
        }
    }

    /// The head's type applied to `values`, its left-out levels the solved
    /// ones or placeholders; `None` past the end of its Pi types.
    fn applied_type(&self, head: &Head, holes: &Holes, values: &[Val]) -> Option<Val> {
        let mut ty = match head {
            Head::Term(_, ty) => ty.clone(),
            Head::Global(id, given) => {
                let mut slot = 0;
                let levels: Rc<[Level]> = given
                    .iter()
                    .map(|l| match l {
                        Some(l) => l.clone(),
                        None => {
                            slot += 1;
                            holes.levels[slot - 1].clone().unwrap_or(Level::Param(holes.first_level + slot as u32 - 1))
                        }
                    })
                    .collect();
                global_type(&self.sig, *id, levels)
            }
        };
        for v in values {
            let Val::Pi(pi) = ty.force(&self.sig) else { return None };
            ty = pi.cod.apply(&self.sig, v.clone());
        }
        Some(ty)
    }

    /// Infer `raw`, whose type should be `ty`: a lambda is elaborated under
    /// the domains of `ty` that are known, so its body's type is found.
    fn infer_under(&self, ctx: &mut Context, raw: &Raw, ty: &Val, holes: &Holes) -> Result<(Term, Val)> {
        let under = ctx.depth() - holes.depth;
        if let (RawKind::Lam(name, None, body), Val::Pi(pi)) = (&raw.kind, ty.force(&self.sig)) {
            if !holes.open(&quote(&self.sig, ctx.depth(), &pi.dom), under) {
                let pi = pi.clone();
                let (body, cod, cod_level) = self.under(ctx, name, pi.dom.clone(), |c, ctx| {
                    let cod = pi.cod.apply(&c.sig, Val::var(ctx.depth() - 1));
                    let (body, found) = c.infer_under(ctx, body, &cod, holes)?;
                    let level = c.conversion(ctx).sort_of(&found);
                    Ok::<_, utilities::Diagnostic>((body, quote(&c.sig, ctx.depth(), &found), level))
                })?;
                let Some(cod_level) = cod_level else {
                    return Err(self.error(Code::TypeAnnotationRequired, raw.span, "cannot infer the sort of this lambda's result"));
                };
                let dom_level = self.conversion(ctx).sort_of(&pi.dom).unwrap_or_else(|| pi.dom_level.clone());
                let found = Val::Pi(Rc::new(BindingVal {
                    name: name.clone(),
                    dom: pi.dom.clone(),
                    cod: Closure::Term(ctx.env.clone(), Rc::new(cod)),
                    dom_level,
                    cod_level,
                }));
                let name: Name = name.clone();
                return Ok((Term::Lam(name, None, Rc::new(body)), found));
            }
        }
        self.infer(ctx, raw)
    }
}

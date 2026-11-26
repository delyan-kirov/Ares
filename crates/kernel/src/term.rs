//! Core terms of the kernel, with de Bruijn indices.
//!
//! The checker elaborates the script syntax into these terms, normalisation
//! by evaluation reads them back from values, and nothing else builds them.
//! A bound variable is its de Bruijn index (0 is the innermost binder); a
//! global is its position in the [`Signature`] with the levels it is
//! instantiated at. Binders keep their source name for printing only.
//!
//! Children are `Rc`-shared: a value's closure captures the body it will
//! evaluate, so a term outlives the pass that built it.
//!
//! Entry point: [`Term`], printed by [`TermDisplay`].

use std::collections::BTreeSet;
use std::fmt;
use std::rc::Rc;

use crate::level::{Level, LevelDisplay};
use crate::signature::{GlobalId, Signature};

/// A de Bruijn index: the number of binders between a variable and its own.
pub type Index = u32;

/// A binder's source name.
pub type Name = Rc<str>;

/// A dependent binding form, `(name: dom) -> cod`, with the sorts of both
/// sides (the sort of the whole is computed from them).
#[derive(Clone, Debug, PartialEq)]
pub struct Binding {
    pub name: Name,
    pub dom: Rc<Term>,
    pub cod: Rc<Term>,
    pub dom_level: Level,
    pub cod_level: Level,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(Index),
    Global(GlobalId, Rc<[Level]>),
    /// `@Type l`; `@Type 0` is the universe of propositions.
    Sort(Level),
    Pi(Rc<Binding>),
    /// `\name => body`, with the domain when the source wrote one: a lambda
    /// in a position that infers its type needs it to be re-checked.
    Lam(Name, Option<Rc<Term>>, Rc<Term>),
    App(Rc<Term>, Rc<Term>),
    /// `let name: ty = val in body`, kept so `name` stays transparent.
    Let(Name, Rc<Term>, Rc<Term>, Rc<Term>),
    /// `(name: dom) * cod`, the dependent pair type.
    Sigma(Rc<Binding>),
    Pair(Rc<Term>, Rc<Term>),
    Fst(Rc<Term>),
    Snd(Rc<Term>),
    /// The true proposition and its proof.
    Top,
    Tt,
    /// The false proposition, and its elimination into any type.
    Bottom,
    Absurd(Rc<Term>, Rc<Term>),
    /// `a ~ b` at type `ty`, where `ty : @Type level`.
    Eq(Level, Rc<Term>, Rc<Term>, Rc<Term>),
    /// `@cast from to proof value`.
    Cast(Rc<Term>, Rc<Term>, Rc<Term>, Rc<Term>),
    /// `@refl a`.
    Refl(Rc<Term>),
    /// `@transp t motive proof t2 e`.
    Transp(Rc<[Rc<Term>; 5]>),
    /// `@Quot carrier relation refl sym trans`, at the carrier's sort, with
    /// the proofs that the relation is an equivalence.
    Quot(Rc<Term>, Rc<Term>, Level, Rc<[Rc<Term>; 3]>),
    /// `@qin a`, the class of `a`.
    QIn(Rc<Term>),
    /// `@qelim motive method respect q`, with the motive's sort and the
    /// proof that the method respects the relation.
    QElim(Rc<Term>, Rc<Term>, Rc<Term>, Level, Rc<Term>),
    /// `(e : ty)`, kept so a term that infers its type is re-checked as one.
    Ann(Rc<Term>, Rc<Term>),
    /// A term checked against a proposition. It is kept, so the term can be
    /// re-checked, and never evaluated: its value is the irrelevant witness.
    /// See Note [Proofs evaluate to an irrelevant witness].
    Proof(Rc<Term>),
    /// The irrelevant witness itself, where a value is read back to a term or
    /// a computation rule needs some proof. It cannot be re-checked.
    Irrelevant,
    /// A numeral: the prelude's `@Nat`, the global, and the number, which
    /// stands for its unary constructor chain. See Rule [Nat-Literal].
    Nat(GlobalId, u64),
}

impl Term {
    pub fn app(f: Term, a: Term) -> Term {
        Term::App(Rc::new(f), Rc::new(a))
    }
}

// ## Printing

/// Prints a term, naming bound variables from `names` (outermost first).
pub struct TermDisplay<'a> {
    pub sig: &'a Signature,
    pub names: &'a [Name],
    pub level_names: &'a [Name],
    pub term: &'a Term,
}

/// How tightly a printed position binds, loosest first.
#[derive(Clone, Copy, PartialEq, PartialOrd)]
enum Precedence {
    Top,
    Arrow,
    Product,
    App,
    Atom,
}

struct Printer<'a> {
    sig: &'a Signature,
    names: Vec<Name>,
    level_names: &'a [Name],
}

impl Printer<'_> {
    fn name_at(&self, ix: Index) -> String {
        let depth = self.names.len();
        match depth.checked_sub(ix as usize + 1) {
            Some(level) => self.names[level].to_string(),
            None => format!("#{ix}"),
        }
    }

    fn level(&self, l: &Level) -> String {
        LevelDisplay { level: l, names: self.level_names }.to_string()
    }

    fn bind<R>(&mut self, name: &Name, k: impl FnOnce(&mut Self) -> R) -> R {
        self.names.push(name.clone());
        let r = k(self);
        self.names.pop();
        r
    }

    fn print(&mut self, out: &mut String, prec: Precedence, t: &Term) {
        let open = |out: &mut String, needs: Precedence| {
            if prec > needs {
                out.push('(');
            }
        };
        let close = |out: &mut String, needs: Precedence| {
            if prec > needs {
                out.push(')');
            }
        };
        match t {
            Term::App(..) | Term::Global(..) if self.numeral(out, prec, t) => {}
            Term::Var(ix) => out.push_str(&self.name_at(*ix)),
            Term::Nat(_, n) => out.push_str(&n.to_string()),
            Term::Global(id, levels) => {
                let global = self.sig.global(*id);
                out.push_str(&global.name);
                if !levels.is_empty() {
                    out.push_str(" @ctx {");
                    for (i, (param, l)) in global.level_params.iter().zip(levels.iter()).enumerate() {
                        if i > 0 {
                            out.push_str(", ");
                        }
                        out.push_str(&format!(".{param} = {}", self.level(l)));
                    }
                    out.push('}');
                }
            }
            Term::Sort(l) => {
                open(out, Precedence::App);
                out.push_str("@Type ");
                let shown = self.level(l);
                if shown.contains(' ') {
                    out.push_str(&format!("({shown})"));
                } else {
                    out.push_str(&shown);
                }
                close(out, Precedence::App);
            }
            Term::Pi(b) => self.binding(out, prec, b, " -> ", Precedence::Arrow),
            Term::Sigma(_) => self.sigma(out, t),
            Term::Lam(name, dom, body) => {
                open(out, Precedence::Arrow);
                match dom {
                    Some(dom) => {
                        out.push_str(&format!("\\({name}: "));
                        self.print(out, Precedence::Top, dom);
                        out.push_str(") => ");
                    }
                    None => out.push_str(&format!("\\{name} => ")),
                }
                self.bind(name, |p| p.print(out, Precedence::Top, body));
                close(out, Precedence::Arrow);
            }
            Term::App(..) if self.infix(out, prec, t) => {}
            Term::App(..) if self.constructor(out, prec, t) => {}
            Term::App(f, a) => {
                open(out, Precedence::App);
                self.print(out, Precedence::App, f);
                out.push(' ');
                self.print(out, Precedence::Atom, a);
                close(out, Precedence::App);
            }
            Term::Let(name, ty, val, body) => {
                open(out, Precedence::Arrow);
                out.push_str(&format!("let {name}: "));
                self.print(out, Precedence::Top, ty);
                out.push_str(" = ");
                self.print(out, Precedence::Top, val);
                out.push_str(" in ");
                self.bind(name, |p| p.print(out, Precedence::Top, body));
                close(out, Precedence::Arrow);
            }
            Term::Pair(a, b) => {
                out.push('{');
                self.print(out, Precedence::Top, a);
                let mut rest = &**b;
                while let Term::Pair(x, y) = rest {
                    out.push_str(", ");
                    self.print(out, Precedence::Top, x);
                    rest = y;
                }
                out.push_str(", ");
                self.print(out, Precedence::Top, rest);
                out.push('}');
            }
            Term::Fst(e) | Term::Snd(e) => {
                self.print(out, Precedence::Atom, e);
                out.push_str(if matches!(t, Term::Fst(_)) { ".0" } else { ".1" });
            }
            // A boolean in a type, `b ~ true`, prints as `b`.
            // See Note [Booleans as propositions].
            Term::Eq(_, ty, b, t) if self.is_true(ty, t) => self.print(out, prec, b),
            Term::Eq(_, _, a, b) => {
                open(out, Precedence::Product);
                self.print(out, Precedence::App, a);
                out.push_str(" ~ ");
                self.print(out, Precedence::App, b);
                close(out, Precedence::Product);
            }
            Term::Cast(from, to, proof, value) => {
                open(out, Precedence::App);
                out.push_str("@cast");
                for t in [from, to, proof, value] {
                    out.push(' ');
                    self.print(out, Precedence::Atom, t);
                }
                close(out, Precedence::App);
            }
            Term::Refl(a) => {
                open(out, Precedence::App);
                out.push_str("@refl ");
                self.print(out, Precedence::Atom, a);
                close(out, Precedence::App);
            }
            Term::Transp(args) => {
                open(out, Precedence::App);
                out.push_str("@transp");
                for t in args.iter() {
                    out.push(' ');
                    self.print(out, Precedence::Atom, t);
                }
                close(out, Precedence::App);
            }
            Term::Ann(e, ty) => {
                out.push('(');
                self.print(out, Precedence::Top, e);
                out.push_str(" : ");
                self.print(out, Precedence::Top, ty);
                out.push(')');
            }
            Term::Proof(e) => self.print(out, prec, e),
            Term::Irrelevant => out.push_str("@irrelevant"),
            Term::Quot(a, r, _, _) => {
                open(out, Precedence::App);
                out.push_str("@Quot ");
                self.print(out, Precedence::Atom, a);
                out.push(' ');
                self.print(out, Precedence::Atom, r);
                close(out, Precedence::App);
            }
            Term::QIn(a) => {
                open(out, Precedence::App);
                out.push_str("@qin ");
                self.print(out, Precedence::Atom, a);
                close(out, Precedence::App);
            }
            Term::QElim(p, f, _, _, q) => {
                open(out, Precedence::App);
                out.push_str("@qelim");
                for t in [p, f, q] {
                    out.push(' ');
                    self.print(out, Precedence::Atom, t);
                }
                close(out, Precedence::App);
            }
            Term::Top => out.push_str("@Top"),
            Term::Tt => out.push_str("@tt"),
            Term::Bottom => out.push_str("@Bottom"),
            Term::Absurd(ty, e) => {
                out.push('(');
                self.print(out, Precedence::App, e);
                out.push_str(" |> @absurd : ");
                self.print(out, Precedence::Top, ty);
                out.push(')');
            }
        }
    }

    /// A Sigma type: `{A, B}`, or `{x: A, snd: B}` when `B` mentions `x`.
    /// Right-nested pairs of types flatten, `{A, B, C}`.
    fn sigma(&mut self, out: &mut String, t: &Term) {
        let Term::Sigma(b) = t else { unreachable!("a Sigma type") };
        if mentions(&b.cod, 0) {
            out.push_str(&format!("{{{}: ", b.name));
            self.print(out, Precedence::Top, &b.dom);
            out.push_str(", snd: ");
            self.bind(&b.name, |p| p.print(out, Precedence::Top, &b.cod));
            out.push('}');
            return;
        }
        out.push('{');
        self.print(out, Precedence::Top, &b.dom);
        let mut pushed = 1;
        self.names.push(b.name.clone());
        let mut rest = &*b.cod;
        while let Term::Sigma(c) = rest {
            if mentions(&c.cod, 0) {
                break;
            }
            out.push_str(", ");
            self.print(out, Precedence::Top, &c.dom);
            self.names.push(c.name.clone());
            pushed += 1;
            rest = &c.cod;
        }
        out.push_str(", ");
        self.print(out, Precedence::Top, rest);
        self.names.truncate(self.names.len() - pushed);
        out.push('}');
    }

    /// Whether `ty` is the prelude's `Bool` and `t` its `true`.
    fn is_true(&self, ty: &Term, t: &Term) -> bool {
        let Some(b) = self.sig.builtins() else { return false };
        matches!(ty, Term::Global(id, _) if *id == b.bool)
            && matches!(t, Term::Global(id, _) if *id == b.true_value || *id == b.true_ctor)
    }

    /// A chain of the prelude's `@Nat.Succ` over `@Nat.Zero` or a numeral,
    /// written as its numeral, or over another term `t`, written `t + k`; or
    /// an `@Int` constructor of a numeral, written as the integer. Reports
    /// whether `t` is one.
    fn numeral(&mut self, out: &mut String, prec: Precedence, t: &Term) -> bool {
        let Some(b) = self.sig.builtins() else { return false };
        // An integer: `@Int.Pos.{ n }` is `n`, `@Int.NegSucc.{ n }` is `-(n + 1)`.
        if let Term::App(f, a) = t {
            if let (Term::Global(id, _), Term::Nat(_, n)) = (&**f, &**a) {
                if *id == b.int_pos {
                    out.push_str(&n.to_string());
                    return true;
                }
                if *id == b.int_neg_succ {
                    let shown = format!("-{}", u128::from(*n) + 1);
                    out.push_str(&if prec == Precedence::Atom { format!("({shown})") } else { shown });
                    return true;
                }
            }
        }
        let mut count = 0u64;
        let mut rest = t;
        while let Term::App(f, a) = rest {
            if !matches!(&**f, Term::Global(id, _) if *id == b.succ) {
                break;
            }
            count += 1;
            rest = a;
        }
        match rest {
            Term::Global(id, _) if *id == b.zero => out.push_str(&count.to_string()),
            _ if count == 0 => return false,
            Term::Nat(_, n) if n.checked_add(count).is_some() => out.push_str(&(n + count).to_string()),
            _ => {
                if prec > Precedence::Product {
                    out.push('(');
                }
                self.print(out, Precedence::App, rest);
                out.push_str(&format!(" + {count}"));
                if prec > Precedence::Product {
                    out.push(')');
                }
            }
        }
        true
    }

    /// A global named by an operator, such as the prelude's `<`, applied to
    /// two arguments: its name and the two sides.
    fn infix_parts<'t>(&self, t: &'t Term) -> Option<(Name, &'t Term, &'t Term)> {
        let Term::App(f, rhs) = t else { return None };
        let Term::App(op, lhs) = &**f else { return None };
        let Term::Global(id, levels) = &**op else { return None };
        // A builtin type's operator, `@Int.+`, prints as its operator.
        let name = &self.sig.global(*id).name;
        let name = match name.strip_prefix('@').and_then(|n| n.rsplit_once('.')) {
            Some((_, op)) => op,
            None => name,
        };
        let symbolic = !name.is_empty() && name.chars().all(|c| "+-*/%<>=!&|^".contains(c));
        (levels.is_empty() && symbolic).then(|| (Name::from(name), &**lhs, &**rhs))
    }

    /// Writes an operator application `a < b`, a side in parentheses unless
    /// its own operator binds tighter. `&&` and `||` bind alike, so a mix of
    /// them is parenthesised. Reports whether `t` is one.
    fn infix(&mut self, out: &mut String, prec: Precedence, t: &Term) -> bool {
        let Some((name, lhs, rhs)) = self.infix_parts(t) else { return false };
        let binds = |op: &str| match op {
            "&&" | "||" => 1,
            "+" | "-" => 3,
            "*" | "/" | "%" => 4,
            _ => 2,
        };
        if prec > Precedence::Product {
            out.push('(');
        }
        for (i, side) in [lhs, rhs].into_iter().enumerate() {
            if i == 1 {
                out.push_str(&format!(" {name} "));
            }
            match self.infix_parts(side) {
                Some((inner, ..)) if binds(&inner) > binds(&name) => {
                    self.infix(out, Precedence::Product, side);
                }
                _ => self.print(out, Precedence::App, side),
            }
        }
        if prec > Precedence::Product {
            out.push(')');
        }
        true
    }

    /// A constructor applied to its parameters and every field, written
    /// `D.Tag.{ fields }` (`D.Tag` with none). Reports whether `t` is one.
    fn constructor(&mut self, out: &mut String, prec: Precedence, t: &Term) -> bool {
        let mut args = Vec::new();
        let mut head = t;
        while let Term::App(f, a) = head {
            args.push(&**a);
            head = f;
        }
        let Term::Global(id, levels) = head else { return false };
        let crate::signature::GlobalKind::Constructor(data, index) = self.sig.global(*id).kind else { return false };
        let decl = self.sig.data(data);
        let fields = decl.constructors[index].surface.len();
        if args.len() != decl.uniform + fields {
            return false;
        }
        args.reverse();
        let _ = (prec, levels);
        out.push_str(&self.sig.global(*id).name);
        if fields > 0 {
            out.push_str(".{ ");
            for (i, a) in args[decl.uniform..].iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                self.print(out, Precedence::Top, a);
            }
            out.push_str(" }");
        }
        true
    }

    /// A Pi or Sigma type, written `(x: A) op B`, or `A op B` when `B` does
    /// not mention `x`.
    fn binding(&mut self, out: &mut String, prec: Precedence, b: &Binding, op: &str, own: Precedence) {
        if prec > own {
            out.push('(');
        }
        if mentions(&b.cod, 0) {
            out.push_str(&format!("({}: ", b.name));
            self.print(out, Precedence::Top, &b.dom);
            out.push(')');
        } else {
            let next = if own == Precedence::Arrow { Precedence::Product } else { Precedence::App };
            self.print(out, next, &b.dom);
        }
        out.push_str(op);
        self.bind(&b.name, |p| p.print(out, own, &b.cod));
        if prec > own {
            out.push(')');
        }
    }
}

/// `t` with every variable at index `cutoff` or above moved out by `by`:
/// the de Bruijn shift that makes room for `by` new binders below `cutoff`
/// bound variables.
pub fn shift(t: &Term, cutoff: Index, by: Index) -> Term {
    rename(t, cutoff, &|i| i + by)
}

/// `t` with every variable at index `cutoff` or above, `cutoff + i`, moved to
/// `cutoff + f(i)`: a shift, or a move to a context with other binders.
pub fn rename(t: &Term, cutoff: Index, f: &dyn Fn(Index) -> Index) -> Term {
    let go = |t: &Rc<Term>, cutoff| Rc::new(rename(t, cutoff, f));
    let binding = |b: &Binding| {
        Rc::new(Binding {
            name: b.name.clone(),
            dom: go(&b.dom, cutoff),
            cod: go(&b.cod, cutoff + 1),
            dom_level: b.dom_level.clone(),
            cod_level: b.cod_level.clone(),
        })
    };
    match t {
        Term::Var(i) if *i >= cutoff => Term::Var(cutoff + f(i - cutoff)),
        Term::Var(_) | Term::Global(..) | Term::Sort(_) | Term::Top | Term::Tt | Term::Bottom | Term::Irrelevant | Term::Nat(..) => {
            t.clone()
        }
        Term::Eq(l, ty, a, b) => Term::Eq(l.clone(), go(ty, cutoff), go(a, cutoff), go(b, cutoff)),
        Term::Cast(x, y, e, v) => Term::Cast(go(x, cutoff), go(y, cutoff), go(e, cutoff), go(v, cutoff)),
        Term::Refl(a) => Term::Refl(go(a, cutoff)),
        Term::Transp(args) => Term::Transp(Rc::new(args.each_ref().map(|t| go(t, cutoff)))),
        Term::Quot(a, r, l, proofs) => Term::Quot(go(a, cutoff), go(r, cutoff), l.clone(), Rc::new(proofs.each_ref().map(|t| go(t, cutoff)))),
        Term::QIn(a) => Term::QIn(go(a, cutoff)),
        Term::QElim(p, f, e, l, q) => Term::QElim(go(p, cutoff), go(f, cutoff), go(e, cutoff), l.clone(), go(q, cutoff)),
        Term::Ann(e, ty) => Term::Ann(go(e, cutoff), go(ty, cutoff)),
        Term::Proof(e) => Term::Proof(go(e, cutoff)),
        Term::Pi(b) => Term::Pi(binding(b)),
        Term::Sigma(b) => Term::Sigma(binding(b)),
        Term::Lam(name, dom, body) => Term::Lam(name.clone(), dom.as_ref().map(|d| go(d, cutoff)), go(body, cutoff + 1)),
        Term::App(f, a) => Term::App(go(f, cutoff), go(a, cutoff)),
        Term::Let(name, ty, val, body) => Term::Let(name.clone(), go(ty, cutoff), go(val, cutoff), go(body, cutoff + 1)),
        Term::Pair(a, b) => Term::Pair(go(a, cutoff), go(b, cutoff)),
        Term::Fst(e) => Term::Fst(go(e, cutoff)),
        Term::Snd(e) => Term::Snd(go(e, cutoff)),
        Term::Absurd(ty, e) => Term::Absurd(go(ty, cutoff), go(e, cutoff)),
    }
}

/// The immediate subterms of `t`, each with the number of binders it is
/// under relative to `t`.
pub fn children(t: &Term) -> Vec<(&Term, Index)> {
    fn here<'a>(ts: &[&'a Rc<Term>]) -> Vec<(&'a Term, Index)> {
        ts.iter().map(|t| (&***t, 0)).collect()
    }
    match t {
        Term::Var(_) | Term::Global(..) | Term::Sort(_) | Term::Top | Term::Tt | Term::Bottom | Term::Irrelevant | Term::Nat(..) => {
            Vec::new()
        }
        Term::Pi(b) | Term::Sigma(b) => vec![(&*b.dom, 0), (&*b.cod, 1)],
        Term::Lam(_, dom, body) => dom.iter().map(|d| (&**d, 0)).chain([(&**body, 1)]).collect(),
        Term::Let(_, ty, val, body) => vec![(&**ty, 0), (&**val, 0), (&**body, 1)],
        Term::App(a, b) | Term::Pair(a, b) | Term::Absurd(a, b) | Term::Ann(a, b) => here(&[a, b]),
        Term::Fst(e) | Term::Snd(e) | Term::Refl(e) | Term::QIn(e) | Term::Proof(e) => here(&[e]),
        Term::Eq(_, ty, a, b) => here(&[ty, a, b]),
        Term::Cast(x, y, e, v) => here(&[x, y, e, v]),
        Term::Transp(args) => args.iter().map(|t| (&**t, 0)).collect(),
        Term::Quot(a, r, _, proofs) => [a, r].into_iter().chain(proofs.iter()).map(|t| (&**t, 0)).collect(),
        Term::QElim(p, f, e, _, q) => here(&[p, f, e, q]),
    }
}

/// Whether global `id` occurs in `t`.
pub fn mentions_global(t: &Term, id: GlobalId) -> bool {
    match t {
        Term::Global(g, _) | Term::Nat(g, _) => *g == id,
        _ => children(t).into_iter().any(|(c, _)| mentions_global(c, id)),
    }
}

/// Add every global that occurs in `t` to `out`.
pub fn globals(t: &Term, out: &mut BTreeSet<GlobalId>) {
    if let Term::Global(g, _) | Term::Nat(g, _) = t {
        out.insert(*g);
    }
    for (c, _) in children(t) {
        globals(c, out);
    }
}

/// Whether variable `ix` occurs free in `t`.
pub fn mentions(t: &Term, ix: Index) -> bool {
    match t {
        Term::Var(i) => *i == ix,
        _ => children(t).into_iter().any(|(c, under)| mentions(c, ix + under)),
    }
}

impl fmt::Display for TermDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut printer = Printer {
            sig: self.sig,
            names: self.names.to_vec(),
            level_names: self.level_names,
        };
        let mut out = String::new();
        printer.print(&mut out, Precedence::Top, self.term);
        f.write_str(&out)
    }
}

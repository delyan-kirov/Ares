//! Field groups: adjacent named fields of one type merge into one group,
//! `a: T, b: T` into `a b: T` (#575).
//!
//! The merge drops tokens, so it runs on an item's tokens before layout, and
//! the re-lex check compares the output with the merged tokens.
//!
//! The lists it merges are the entries of every `{ }` (a `@ctx`, a record
//! type, a variant payload; a tuple or a literal has no `name:` entries) and
//! an item's body after `@struct` or after the `=` that starts an effect's
//! operations. Entries are split at the commas outside brackets and effect
//! rows. Two adjacent entries merge when both are `names: T` with the same
//! `T`, token for token, and no comment sits between them.

use super::Tok;
use crate::lexer::data::Kind;

/// `toks` with every run of same-typed adjacent fields merged into a group.
pub(super) fn merge_groups<'s>(toks: &[Tok<'s>]) -> Vec<Tok<'s>> {
    let close = matching(toks);
    let mut drop = vec![false; toks.len()];
    let mut joined = vec![false; toks.len()];
    for (i, t) in toks.iter().enumerate() {
        if matches!(t.kind, Kind::LBrace) {
            if let Some(end) = close[i] {
                merge_list(toks, &close, i + 1, end, &mut drop, &mut joined);
            }
        }
    }
    if let Some(start) = body_start(toks, &close) {
        merge_list(toks, &close, start, toks.len(), &mut drop, &mut joined);
    }
    toks.iter()
        .enumerate()
        .filter(|&(i, _)| !drop[i])
        .map(|(i, t)| if joined[i] { Tok { gap: true, newline: false, blank: false, ..*t } } else { *t })
        .collect()
}

/// Per opening bracket or effect row, the index of its closer.
fn matching(toks: &[Tok]) -> Vec<Option<usize>> {
    let mut close = vec![None; toks.len()];
    let mut open: Vec<usize> = Vec::new();
    for (i, t) in toks.iter().enumerate() {
        if opens(toks, i) {
            open.push(i);
        } else if closes(t) && open.last().is_some_and(|&o| pairs(&toks[o], t)) {
            close[open.pop().unwrap()] = Some(i);
        }
    }
    close
}

/// A bracket, or the `<` of an effect row right after `->`.
fn opens(toks: &[Tok], i: usize) -> bool {
    match toks[i].kind {
        Kind::LBrace | Kind::LParen | Kind::LBrack => true,
        Kind::Op => toks[i].text == "<" && i > 0 && matches!(toks[i - 1].kind, Kind::Arrow),
        _ => false,
    }
}

fn closes(t: &Tok) -> bool {
    matches!(t.kind, Kind::RBrace | Kind::RParen | Kind::RBrack) || (matches!(t.kind, Kind::Op) && t.text == ">")
}

fn pairs(open: &Tok, close: &Tok) -> bool {
    matches!(
        (open.kind, close.kind),
        (Kind::LBrace, Kind::RBrace) | (Kind::LParen, Kind::RParen) | (Kind::LBrack, Kind::RBrack) | (Kind::Op, Kind::Op)
    )
}

/// Where an item's own field list starts: after `@struct` (and its
/// `@extern "abi"`), or after the item's `=` when operations follow.
fn body_start(toks: &[Tok], close: &[Option<usize>]) -> Option<usize> {
    let mut i = 0;
    while i < toks.len() {
        let t = &toks[i];
        if matches!(t.kind, Kind::At) && t.text == "@struct" {
            let mut s = i + 1;
            if toks.get(s).is_some_and(|t| t.text == "@extern") {
                s += 2;
            }
            return Some(s);
        }
        if matches!(t.kind, Kind::Eq) && toks.get(i + 1).is_none_or(|n| n.text != "@struct") {
            return (group_len(toks, i + 1) > 0).then_some(i + 1);
        }
        i = close[i].map_or(i + 1, |c| c + 1);
    }
    None
}

/// How many names open a group `a b: T` at `at`, or 0.
fn group_len(toks: &[Tok], at: usize) -> usize {
    let n = toks[at.min(toks.len())..].iter().take_while(|t| matches!(t.kind, Kind::Word)).count();
    if n > 0 && toks.get(at + n).is_some_and(|t| matches!(t.kind, Kind::Colon)) { n } else { 0 }
}

/// One entry of a list: `toks[start..end]`, and the comma after it, if any.
struct Entry {
    start: usize,
    end: usize,
    comma: Option<usize>,
}

/// Merge the same-typed adjacent fields among `toks[start..end]`.
fn merge_list(toks: &[Tok], close: &[Option<usize>], start: usize, end: usize, drop: &mut [bool], joined: &mut [bool]) {
    let mut entries = Vec::new();
    // An entry starts at its first name, past the comments before it.
    let first = |from: usize| (from..end).find(|&j| !matches!(toks[j].kind, Kind::Comment)).unwrap_or(end);
    let (mut from, mut i) = (first(start), start);
    while i < end {
        if matches!(toks[i].kind, Kind::Comma) {
            entries.push(Entry { start: from, end: i, comma: Some(i) });
            from = first(i + 1);
        }
        i = close[i].map_or(i + 1, |c| c + 1);
    }
    if from < end {
        entries.push(Entry { start: from, end, comma: None });
    }
    for pair in entries.windows(2) {
        let (a, b) = (&pair[0], &pair[1]);
        let (na, nb) = (group_len(toks, a.start), group_len(toks, b.start));
        let Some(comma) = a.comma else { continue };
        if na == 0 || nb == 0 || toks[a.start..b.end].iter().any(|t| matches!(t.kind, Kind::Comment)) {
            continue;
        }
        let ty = |e: &Entry, n: usize| &toks[e.start + n + 1..e.end];
        let (ta, tb) = (ty(a, na), ty(b, nb));
        let same = ta.len() == tb.len() && ta.iter().zip(tb).all(|(x, y)| x.kind == y.kind && x.text == y.text);
        if !same || ta.is_empty() {
            continue;
        }
        // `a: T, b: T` keeps `a`, then `b: T`: drop the first `: T,`.
        for d in &mut drop[a.start + na..=comma] {
            *d = true;
        }
        joined[b.start] = true;
    }
}

use super::*;

fn fmt(src: &str) -> String {
    format_source(src, &Style::default()).unwrap_or_else(|e| panic!("{e}\n{src}"))
}

fn narrow(src: &str, width: usize) -> String {
    format_source(src, &Style { width, indent: 4 }).unwrap_or_else(|e| panic!("{e}\n{src}"))
}

#[test]
fn spacing_is_normalized_within_a_line() {
    assert_eq!(fmt("$ @mod M\n$ x=1+2\n"), "$ @mod M\n$ x = 1 + 2\n");
    assert_eq!(
        fmt("$ @mod M\n$ h = \\l => l |> \\ | List.Cons.{h, t} => h | _ => 0\n"),
        "$ @mod M\n$ h = \\l => l |> \\ | List.Cons.{ h, t } => h | _ => 0\n"
    );
}

#[test]
fn a_long_match_breaks_its_arms_under_the_head() {
    let src = "$ @mod M\n$ go : Light -> @Int = \\l =>\n\tl |> \\ | Light.Red => 0\n\t       | Light.Yellow => 1\n";
    let three = "$ @mod M\n$ go = \\l => l |> \\\n| A => 0 | B => 1 | C => 2\n";
    assert_eq!(fmt(three), "$ @mod M\n$ go = \\l =>\n    l |> \\\n        | A => 0\n        | B => 1\n        | C => 2\n");
    assert_eq!(
        narrow(src, 40),
        "$ @mod M\n$ go : Light -> @Int = \\l =>\n    l |> \\\n        | Light.Red    => 0\n        | Light.Yellow => 1\n"
    );
    assert_eq!(fmt(src), "$ @mod M\n$ go : Light -> @Int = \\l => l |> \\ | Light.Red => 0 | Light.Yellow => 1\n");
}

#[test]
fn a_trailing_comma_keeps_a_declaration_exploded() {
    let src = "$ @mod M\n$ P : @Type = @struct\n  x: @Int, y: @Nat,\n$ Q : @Type = @struct x: @Int, y: @Nat,\n";
    assert_eq!(
        fmt(src),
        "$ @mod M\n$ P : @Type = @struct\n    x: @Int,\n    y: @Nat,\n$ Q : @Type = @struct x: @Int, y: @Nat,\n"
    );
}

#[test]
fn comments_survive_and_line_comments_end_their_line() {
    let src = "$ @mod M\n\n# lead\n$ f = \\x => # why\n  x + 1  # tail\n";
    assert_eq!(fmt(src), "$ @mod M\n\n# lead\n$ f = \\x => # why\n    x + 1 # tail\n");
}

#[test]
fn blank_lines_between_items_collapse_to_one() {
    assert_eq!(fmt("$ @mod M\n\n\n\n$ a = 1\n$ b = 2\n"), "$ @mod M\n\n$ a = 1\n$ b = 2\n");
}

#[test]
fn dots_and_unary_minus_keep_their_adjacency() {
    assert_eq!(fmt("$ @mod M\n$ x = f (-1) p.x t.0\n"), "$ @mod M\n$ x = f (-1) p.x t.0\n");
}

#[test]
fn a_let_chain_reads_as_a_sequence() {
    let src = "$ @mod M\n$ f = \\x => let a = x + 1 in let bb = a * 2 in a + bb\n";
    assert_eq!(fmt(src), "$ @mod M\n$ f = \\x => let a = x + 1 in let bb = a * 2 in a + bb\n");
    assert_eq!(narrow(src, 30), "$ @mod M\n$ f = \\x =>\n    let a = x + 1 in\n    let bb = a * 2 in\n    a + bb\n");
    let finale = "$ @mod M\n$ f = \\x => @finale g <| \\_ => @finale h <| \\_ => x\n";
    assert_eq!(narrow(finale, 24), "$ @mod M\n$ f = \\x =>\n    @finale g <| \\_ =>\n    @finale h <| \\_ =>\n    x\n");
}

#[test]
fn a_broken_let_chain_ends_every_line_with_in() {
    let src = "$ @mod M\n$ f = \\x => let a = x in let b = a in let c = b in a + b + c\n";
    assert_eq!(
        narrow(src, 40),
        "$ @mod M\n$ f = \\x =>\n    let a = x in\n    let b = a in\n    let c = b in\n    a + b + c\n"
    );
}

#[test]
fn sequences_break_after_semicolons() {
    let src = "$ @mod M\n$ f = \\x => println \"a\"; println \"b\"; x\n";
    assert_eq!(narrow(src, 20), "$ @mod M\n$ f = \\x =>\n    println \"a\";\n    println \"b\";\n    x\n");
}

#[test]
fn formatting_is_idempotent() {
    let src = "$ @mod M\n$ go : Light -> @Int = \\l =>\n\tl |> \\ | Light.Red => 0\n\t       | Light.Yellow => if l == l => 1 else 2\n$ P : @Type = @struct\n\tx: @Int,\n";
    let once = narrow(src, 30);
    assert_eq!(narrow(&once, 30), once);
}

#[test]
fn range_formatting_touches_only_the_window() {
    let src = "$ @mod M\n$ a=1\n$ b=2\n";
    let at = src.find("b=2").unwrap();
    let edits = format_edits(src, &Style::default(), Some((at, at))).unwrap();
    assert_eq!(edits.len(), 1);
    assert_eq!(edits[0].text, "$ b = 2");
}

#[test]
fn unlexable_input_is_refused() {
    assert!(format_source("$ @mod M\n$ s = \"open\n", &Style::default()).is_err());
}

#[test]
fn let_chains_end_each_line_with_in() {
    let src = "$ @mod M\n$ f = \\p =>\n\tlet q = g p in\n\tlet i = h q in\n\tq + i\n";
    assert_eq!(narrow(src, 20), "$ @mod M\n$ f = \\p =>\n    let q = g p in\n    let i = h q in\n    q + i\n");
}

#[test]
fn a_broken_if_puts_every_body_under_its_arrow_or_else() {
    let src = "$ @mod M\n$ f = \\i => if i < 0 => 1 else if i == 0 => 2 # zero\n else 3\n";
    assert_eq!(
        narrow(src, 30),
        "$ @mod M\n$ f = \\i =>\n    if i < 0 =>\n        1\n    else if i == 0 =>\n        2 # zero\n    else\n        3\n"
    );
    assert_eq!(fmt("$ @mod M\n$ f = \\i => if i < 0 => 1 else 2\n"), "$ @mod M\n$ f = \\i => if i < 0 => 1 else 2\n");
}

#[test]
fn a_comment_block_keeps_its_blank_line_before_the_item() {
    let src = "$ @mod M\n# about\n\n$ @import OPT\n";
    assert_eq!(fmt(src), src);
}

#[test]
fn a_broken_handler_puts_is_on_its_own_line() {
    let src = "$ @mod M\n$ s = \\g => do g {}\nis k | Y.y v => v + k {} | _ => 0\n";
    assert_eq!(fmt(src), "$ @mod M\n$ s = \\g =>\n    do g {}\n    is k | Y.y v => v + k {} | _ => 0\n");
}

#[test]
fn a_long_concatenation_breaks_before_each_plus_plus() {
    let src = "$ @mod M\n$ s : @Str = \"aaaaaaaaaa\" ++ \"bbbbbbbbbb\" ++ \"cccccccccc\"\n";
    assert_eq!(
        narrow(src, 30),
        "$ @mod M\n$ s : @Str =\n    \"aaaaaaaaaa\"\n        ++ \"bbbbbbbbbb\"\n        ++ \"cccccccccc\"\n"
    );
}

#[test]
fn a_long_signature_wraps_before_its_arrows() {
    let src = "$ @mod M\n$ f : @Int -> {@Vec @Int, @Int} = \\x => x\n";
    assert_eq!(narrow(src, 36), "$ @mod M\n$ f : @Int\n    -> { @Vec @Int, @Int } = \\x =>\n    x\n");
}

#[test]
fn a_long_sum_packs_its_operands() {
    let src = "$ @mod M\n$ t : @Int = aaaa + bbbb + cccc + dddd + eeee\n";
    assert_eq!(narrow(src, 30), "$ @mod M\n$ t : @Int =\n    aaaa + bbbb + cccc + dddd\n        + eeee\n");
}

#[test]
fn long_alternatives_wrap_one_level_in() {
    let src = "$ @mod M\n$ k = \\s => s |> \\ | \"aaaa\" | \"bbbb\" | \"cccc\" | \"dddd\" => 1 | _ => 0\n";
    assert_eq!(
        narrow(src, 30),
        "$ @mod M\n$ k = \\s =>\n    s |> \\\n        | \"aaaa\" | \"bbbb\"\n            | \"cccc\"\n            | \"dddd\" =>\n            1\n        | _ => 0\n"
    );
}

#[test]
fn a_broken_paren_nests_its_contents() {
    let src = "$ @mod M\n$ f = \\x => x |> \\ | 0 => (let a = x in let b = a in { a, b, a, b }) | _ => (x)\n";
    assert_eq!(
        narrow(src, 30),
        "$ @mod M\n$ f = \\x =>\n    x |> \\\n        | 0 => (\n            let a = x in\n            let b = a in\n            { a, b, a, b }\n        )\n        | _ => (x)\n"
    );
}

#[test]
fn a_braced_body_opens_on_its_heads_line() {
    let src = "$ @mod M\n$ t = { aaaaaaaaaa, bbbbbbbbbb, cccccccccc }\n";
    assert_eq!(narrow(src, 30), "$ @mod M\n$ t = {\n    aaaaaaaaaa,\n    bbbbbbbbbb,\n    cccccccccc\n}\n");
}

#[test]
fn an_is_inside_a_handler_clause_ends_at_the_next_clause() {
    let src = "$ @mod M\n$ h = \\g => do g {} is k\n| Y.y v => (v |> \\ | 0 => 1 | _ => 2) | X.x u => u |> \\ | 0 => 1 | _ => 2 | Z.z w => 3\n";
    assert_eq!(
        fmt(src),
        "$ @mod M\n$ h = \\g =>\n    do g {} is k\n        | Y.y v => (v |> \\ | 0 => 1 | _ => 2)\n        | X.x u => u |> \\ | 0 => 1 | _ => 2\n        | Z.z w => 3\n"
    );
}

#[test]
fn trailing_comments_of_neighbouring_lines_line_up() {
    let src = "$ @mod M\n$ a = 1 # one\n$ bbb = 22 # two\n\n$ c = 3 # alone\n";
    assert_eq!(fmt(src), "$ @mod M\n$ a = 1    # one\n$ bbb = 22 # two\n\n$ c = 3 # alone\n");
}

#[test]
fn a_value_that_cannot_share_the_line_goes_under_its_equals() {
    let src = "$ @mod M\n$ f = \\g => let h = do g {} is k\n| Y.y v => v | X.x u => 1 | _ => 0 in h\n";
    assert_eq!(
        fmt(src),
        "$ @mod M\n$ f = \\g =>\n    let h =\n        do g {} is k\n            | Y.y v => v\n            | X.x u => 1\n            | _     => 0\n    in\n    h\n"
    );
}

#[test]
fn a_form_after_a_broken_else_goes_one_level_in() {
    let els = "$ @mod M\n$ f = \\x => if x == 0 => 1 else let y = x * 2 in y + 1\n";
    assert_eq!(narrow(els, 30), "$ @mod M\n$ f = \\x =>\n    if x == 0 =>\n        1\n    else\n        let y = x * 2 in y + 1\n");
}

#[test]
fn an_else_if_chain_starts_each_arm_at_the_first_if() {
    let src = "$ @mod M\n$ f = \\i => if i < 0 => 1 else if i == 0 => g iiiiiiiiii jjjjjjjjjj else 3\n";
    assert_eq!(
        narrow(src, 40),
        "$ @mod M\n$ f = \\i =>\n    if i < 0 =>\n        1\n    else if i == 0 =>\n        g iiiiiiiiii jjjjjjjjjj\n    else\n        3\n"
    );
    assert_eq!(narrow(&narrow(src, 40), 40), narrow(src, 40));
}

#[test]
fn a_trailing_lambda_opens_on_the_calls_line() {
    let src = "$ @mod M\n$ f = \\s => let r = with_a (\\u => with_b s (\\v => with_c (\\w => go s u v w))) in r\n";
    assert_eq!(
        narrow(src, 40),
        "$ @mod M\n$ f = \\s =>\n    let r = with_a (\\u =>\n        with_b s (\\v =>\n            with_c (\\w =>\n                go s u v w))) in\n    r\n"
    );
}

#[test]
fn an_import_stays_on_one_line() {
    assert_eq!(fmt("$ @mod M\n$ @import V=VEC\n"), "$ @mod M\n$ @import V = VEC\n");
    assert_eq!(fmt("$ @mod M\n$ @import   A.B\n"), "$ @mod M\n$ @import A.B\n");
    let commented = "$ @mod M\n# the vectors\n$ @import V = VEC # qualified\n$ @import LIST\n";
    assert_eq!(fmt(commented), commented);
}

#[test]
fn a_multi_arm_lambda_keeps_its_backslash_on_the_head_line() {
    assert_eq!(fmt("$ @mod M\n$ f = \\ | 0 => 1 | _ => 2\n"), "$ @mod M\n$ f = \\ | 0 => 1 | _ => 2\n");
    assert_eq!(
        fmt("$ @mod M\n$ f : @Int -> @Str = \\\n|0=>\"zero\"|1=>\"one\"|_=>\"many\"\n"),
        "$ @mod M\n$ f : @Int -> @Str = \\\n    | 0 => \"zero\"\n    | 1 => \"one\"\n    | _ => \"many\"\n"
    );
    assert_eq!(
        fmt("$ @mod M\n$ f = \\s => s |> \\\n | \"yes\" => 1 | \"no\" => 0 | _ => 99\n"),
        "$ @mod M\n$ f = \\s =>\n    s |> \\\n        | \"yes\" => 1\n        | \"no\"  => 0\n        | _     => 99\n"
    );
}

#[test]
fn a_comma_in_an_arm_separates_its_arguments() {
    let src = "$ @mod M\n$ f : @Int -> @Int -> @Int = \\\n | 0,_ => 0 | n , x :: xs => n | _, _ => 1\n";
    assert_eq!(
        fmt(src),
        "$ @mod M\n$ f : @Int -> @Int -> @Int = \\\n    | 0, _       => 0\n    | n, x :: xs => n\n    | _, _       => 1\n"
    );
    // Inside a list, the comma after an arm's body still ends the element.
    let rec = "$ @mod M\n$ r = { .f = \\ | 0, _ => 0 | _, _ => 1, .g = 2 }\n";
    assert_eq!(fmt(rec), rec);
}

#[test]
fn a_break_at_a_forms_chosen_point_keeps_it_a_block() {
    // Arms: a break before the first `|`; none keeps a fitting match on one line.
    let flat = "$ @mod M\n$ f = \\ | A => 0 | B => 1 | C => 2\n";
    assert_eq!(fmt(flat), flat);
    let arms = "$ @mod M\n$ f = \\\n| A => 0 | B => 1\n";
    assert_eq!(fmt(arms), "$ @mod M\n$ f = \\\n    | A => 0\n    | B => 1\n");
    // A break before a later arm does not count.
    let later = "$ @mod M\n$ f = \\ | A => 0\n| B => 1\n";
    assert_eq!(fmt(later), "$ @mod M\n$ f = \\ | A => 0 | B => 1\n");
    // Sequences: a break after the first `;`.
    let seq = "$ @mod M\n$ f = \\x => print a; print b\n";
    assert_eq!(fmt(seq), seq);
    let block = "$ @mod M\n$ f = \\x => print a;\nprint b; print c\n";
    assert_eq!(fmt(block), "$ @mod M\n$ f = \\x =>\n    print a;\n    print b;\n    print c\n");
    // `let`: a break after `in`.
    let let_flat = "$ @mod M\n$ f = \\x => let a = x in a\n";
    assert_eq!(fmt(let_flat), let_flat);
    let let_block = "$ @mod M\n$ f = \\x => let a = x in\na\n";
    assert_eq!(fmt(let_block), "$ @mod M\n$ f = \\x =>\n    let a = x in\n    a\n");
    // `if`: a break before the first `else`.
    let if_flat = "$ @mod M\n$ f = \\x => if x => 1 else 2\n";
    assert_eq!(fmt(if_flat), if_flat);
    let if_block = "$ @mod M\n$ f = \\x => if x => 1\nelse 2\n";
    assert_eq!(fmt(if_block), "$ @mod M\n$ f = \\x =>\n    if x =>\n        1\n    else\n        2\n");
    // A handler: a break before `is`, and before the first `|` after `is k`.
    let handler = "$ @mod M\n$ h = \\g => do g {} is k | X.x u => 1 | Y.y v => 2 | _ => 0\n";
    assert_eq!(fmt(handler), handler);
    let is = "$ @mod M\n$ h = \\g => do g {}\nis k | X.x u => 1 | _ => 0\n";
    assert_eq!(fmt(is), "$ @mod M\n$ h = \\g =>\n    do g {}\n    is k | X.x u => 1 | _ => 0\n");
    let clauses = "$ @mod M\n$ h = \\g => do g {} is k\n| X.x u => 1 | _ => 0\n";
    assert_eq!(fmt(clauses), "$ @mod M\n$ h = \\g =>\n    do g {} is k\n        | X.x u => 1\n        | _     => 0\n");
    let both = "$ @mod M\n$ h = \\g => do g {}\nis k\n| X.x u => 1 | _ => 0\n";
    assert_eq!(fmt(both), "$ @mod M\n$ h = \\g =>\n    do g {}\n    is k\n    | X.x u => 1\n    | _     => 0\n");
    // A `do .. is k` too long for its line breaks before `is`, the clauses then at its level.
    let long = "$ @mod M\n$ h = \\g => do ffffffffff aaaaaaaaaa bbbbbbbbbb cccccccccc is k\n| X.x u => 1 | _ => 0\n";
    assert_eq!(
        narrow(long, 40),
        "$ @mod M\n$ h = \\g =>\n    do\n        ffffffffff aaaaaaaaaa bbbbbbbbbb\n            cccccccccc\n    is k\n    | X.x u => 1\n    | _     => 0\n"
    );
    assert_eq!(narrow(&narrow(long, 40), 40), narrow(long, 40));
    // Every result is a fixed point.
    for src in [arms, block, let_block, if_block, is, clauses, both] {
        assert_eq!(fmt(&fmt(src)), fmt(src));
    }
}

#[test]
fn adjacent_fields_of_one_type_merge_into_a_group() {
    let m = |src: &str| fmt(&format!("$ @mod M\n{src}\n"));
    assert_eq!(m("$ f : @ctx { a: @Type, b: @Type } -> a = 1"), "$ @mod M\n$ f : @ctx { a b: @Type } -> a = 1\n");
    assert_eq!(m("$ V : @Type = @struct x: @Int, y: @Int, z: @Int"), "$ @mod M\n$ V : @Type = @struct x y z: @Int\n");
    assert_eq!(m("$ S : @Type = @union R: { w: @Int, h: @Int }, D"), "$ @mod M\n$ S : @Type = @union R: { w h: @Int }, D\n");
    assert_eq!(m("$ E : @Effect = get : {} -> @Int, ask : {} -> @Int"), "$ @mod M\n$ E : @Effect = get ask : {} -> @Int\n");
    assert_eq!(m("$ P : @Type = { x: @Int, y: @Int | r }"), "$ @mod M\n$ P : @Type = { x: @Int, y: @Int | r }\n");
    // Only adjacent fields of one type merge, and never across a comment.
    assert_eq!(m("$ f : @ctx { n: @Nat, a: @Type, m: @Nat } -> a = 1"), "$ @mod M\n$ f : @ctx { n: @Nat, a: @Type, m: @Nat } -> a = 1\n");
    let commented = "$ @mod M\n$ V : @Type = @struct\n    # across\n    x: @Int,\n    # down\n    y: @Int,\n";
    assert_eq!(fmt(commented), commented);
    // A row's commas are not the list's.
    assert_eq!(
        m("$ f : @ctx { e: @Row } -> { p: {} -> <A, B> @Int, q: {} -> <A, B> @Int } -> @Int = 0"),
        "$ @mod M\n$ f : @ctx { e: @Row } -> { p q: {} -> <A, B> @Int } -> @Int = 0\n"
    );
}

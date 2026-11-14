//! The documentation's code blocks, checked: every ```` ```ares ```` block in the
//! documents listed in [`DOCS`] must pass `ares check` on its own, and every
//! ```` ```ares-fragment ```` block must fail it: one that does not check on its
//! own, because it shows a diagnostic, quotes CORE, or sketches with `...`. So a
//! fragment that starts checking is noticed and becomes a checked block.
//!
//! A block without a `$ @mod` header is checked as a module of its own, named
//! after the block's line. A block is self-contained: it cannot see the
//! definitions of the blocks before it.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The documents whose code blocks are checked, relative to the repository root.
const DOCS: &[&str] = &["documentation/language/language-reference.md", "documentation/tooling/lsp.md"];

struct Block {
    doc: &'static str,
    /// The line of the opening fence.
    line: usize,
    /// Whether the block is a fragment (```` ```ares-fragment ````).
    fails: bool,
    code: String,
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The `ares` and `ares-fragment` blocks of `src`.
fn blocks(doc: &'static str, src: &str) -> Vec<Block> {
    let mut out = Vec::new();
    let mut open: Option<Block> = None;
    for (i, line) in src.lines().enumerate() {
        match open.as_mut() {
            Some(_) if line.trim_end() == "```" => out.push(open.take().unwrap()),
            Some(b) => {
                b.code.push_str(line);
                b.code.push('\n');
            }
            None => {
                let fails = match line.trim_end() {
                    "```ares" => false,
                    "```ares-fragment" => true,
                    _ => continue,
                };
                open = Some(Block { doc, line: i + 1, fails, code: String::new() });
            }
        }
    }
    assert!(open.is_none(), "{doc}: a code block is never closed");
    out
}

/// The module a block declares, or `None` when it has no header.
fn module_of(code: &str) -> Option<&str> {
    code.lines().find_map(|l| l.strip_prefix("$ @mod ")).map(str::trim)
}

/// Check one block in a directory of its own. `Err` carries the report.
fn check(ares: &Path, dir: &Path, b: &Block) -> Result<(), String> {
    let (module, code) = match module_of(&b.code) {
        Some(m) => (m.to_string(), b.code.clone()),
        None => {
            let m = format!("DOC_{}", b.line);
            (m.clone(), format!("$ @mod {m}\n{}", b.code))
        }
    };
    let dir = dir.join(format!("line-{}", b.line));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let file = format!("{module}.ares");
    std::fs::write(dir.join(&file), &code).map_err(|e| e.to_string())?;
    let out = Command::new(ares)
        .arg("check")
        .arg(&file)
        .current_dir(&dir)
        .output()
        .map_err(|e| format!("cannot run ares: {e}"))?;
    let stderr = String::from_utf8_lossy(&out.stderr);
    let crashed = out.status.code().is_none() || stderr.contains("panicked");
    let at = format!("{}:{}", b.doc, b.line);
    match (b.fails, out.status.success()) {
        _ if crashed => Err(format!("{at}: `ares check` crashed\n{stderr}")),
        (false, true) | (true, false) => Ok(()),
        (false, false) => Err(format!("{at}: the block does not check\n{stderr}")),
        (true, true) => Err(format!("{at}: an `ares-fragment` block checks: make it an `ares` block")),
    }
}

#[test]
fn documentation_code_blocks_check() {
    let ares = PathBuf::from(env!("CARGO_BIN_EXE_ares"));
    let root = repo_root();
    let all: Vec<Block> = DOCS
        .iter()
        .flat_map(|doc| {
            let src = std::fs::read_to_string(root.join(doc)).unwrap_or_else(|e| panic!("{doc}: {e}"));
            blocks(doc, &src)
        })
        .collect();
    assert!(!all.is_empty(), "no code blocks found");
    let dir = std::env::temp_dir().join(format!("ares-doc-blocks-{}", std::process::id()));
    let failures: Vec<String> = std::thread::scope(|s| {
        let handles: Vec<_> = all
            .iter()
            .map(|b| {
                let (ares, dir) = (&ares, &dir);
                s.spawn(move || check(ares, dir, b))
            })
            .collect();
        handles.into_iter().filter_map(|h| h.join().unwrap().err()).collect()
    });
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        failures.is_empty(),
        "{} of {} documentation block(s) failed:\n\n{}",
        failures.len(),
        all.len(),
        failures.join("\n\n")
    );
}

#[test]
fn block_extraction() {
    let src = "text\n```ares\n$ x : @Int = 1\n```\n```sh\nls\n```\n```ares-fragment\n$ y = ???\n```\n";
    let got = blocks("D.md", src);
    let shown: Vec<(usize, bool, &str)> = got.iter().map(|b| (b.line, b.fails, b.code.as_str())).collect();
    assert_eq!(shown, [(2, false, "$ x : @Int = 1\n"), (8, true, "$ y = ???\n")]);
    assert_eq!(module_of("# c\n$ @mod M\n$ x : @Int = 1\n"), Some("M"));
}

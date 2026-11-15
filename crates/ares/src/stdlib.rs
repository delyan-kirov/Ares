//! The standard library this binary carries: every `library/*.ares`, embedded at
//! build time, plus where a distribution puts the same files on disk.
//!
//! A `ares` binary therefore runs anywhere. It prefers the files on disk, so a
//! checkout's own `library/` and an installed distribution's are both live and
//! editable, and falls back to the embedded copy when there are none, which is
//! what a bare `cargo build` or `cargo install` binary gets.

use std::path::{Path, PathBuf};

/// File name to source text, one entry per `library/*.ares`: `CORE`, `C`, and
/// the parts of the `ARES` module (`ARESxMAP`, ...). A new file must be added
/// here too; the tests below enforce it.
pub const MODULES: &[(&str, &str)] = &[
    ("ARESxALGO", include_str!("../../../library/ARESxALGO.ares")),
    ("ARESxASYNC", include_str!("../../../library/ARESxASYNC.ares")),
    ("ARESxBITS", include_str!("../../../library/ARESxBITS.ares")),
    ("ARESxCPX", include_str!("../../../library/ARESxCPX.ares")),
    ("ARESxDERIVE", include_str!("../../../library/ARESxDERIVE.ares")),
    ("ARESxIO", include_str!("../../../library/ARESxIO.ares")),
    ("ARESxLA", include_str!("../../../library/ARESxLA.ares")),
    ("ARESxLIST", include_str!("../../../library/ARESxLIST.ares")),
    ("ARESxMAP", include_str!("../../../library/ARESxMAP.ares")),
    ("ARESxMATH", include_str!("../../../library/ARESxMATH.ares")),
    ("ARESxOPT", include_str!("../../../library/ARESxOPT.ares")),
    ("ARESxPAR", include_str!("../../../library/ARESxPAR.ares")),
    ("ARESxPATH", include_str!("../../../library/ARESxPATH.ares")),
    ("ARESxRANDOM", include_str!("../../../library/ARESxRANDOM.ares")),
    ("ARESxRESULT", include_str!("../../../library/ARESxRESULT.ares")),
    ("ARESxSET", include_str!("../../../library/ARESxSET.ares")),
    ("ARESxSHELL", include_str!("../../../library/ARESxSHELL.ares")),
    ("ARESxSTM", include_str!("../../../library/ARESxSTM.ares")),
    ("ARESxSTR", include_str!("../../../library/ARESxSTR.ares")),
    ("ARESxVEC", include_str!("../../../library/ARESxVEC.ares")),
    ("C", include_str!("../../../library/C.ares")),
    ("CORE", include_str!("../../../library/CORE.ares")),
];

/// The embedded source of a standard-library module.
pub fn source(name: &str) -> Option<&'static str> {
    MODULES.iter().find(|(n, _)| *n == name).map(|(_, src)| *src)
}

/// The path diagnostics render for an embedded module: the file it was taken
/// from, so a span still names a location a reader can look up.
pub fn path(name: &str) -> String {
    format!("library/{name}.ares")
}

/// The standard-library directories a distribution ships, in search order and
/// relative to this executable: `<prefix>/library` beside `<prefix>/bin/ares`,
/// which is the layout the Nix package installs, then the workspace's own
/// `library/` beside a `target/<profile>/ares`. Empty when the executable's
/// path is unknown. The caller decides which of these really holds a standard
/// library.
pub(crate) fn distribution_dirs() -> Vec<PathBuf> {
    let Ok(exe) = std::env::current_exe() else {
        return Vec::new();
    };
    let Some(prefix) = exe.parent().and_then(Path::parent) else {
        return Vec::new();
    };
    let mut dirs = vec![prefix.join("library")];
    if let Some(above) = prefix.parent() {
        dirs.push(above.join("library"));
    }
    dirs
}

#[cfg(test)]
mod tests {
    use super::MODULES;

    #[test]
    fn embedded_modules_match_the_library_directory() {
        let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../library");
        let mut on_disk: Vec<String> = std::fs::read_dir(dir)
            .expect("read library/")
            .flatten()
            .map(|entry| entry.path())
            .filter(|p| p.extension().and_then(|x| x.to_str()) == Some("ares"))
            .filter_map(|p| p.file_stem().and_then(|s| s.to_str()).map(String::from))
            .collect();
        on_disk.sort();
        let mut embedded: Vec<String> = MODULES.iter().map(|(n, _)| n.to_string()).collect();
        embedded.sort();
        assert_eq!(
            embedded, on_disk,
            "a new library/*.ares must be added to MODULES"
        );
    }

    // Catches a mis-paired `include_str!` among the near-identical lines, which
    // comparing the name set alone cannot see: a part names its own file.
    #[test]
    fn embedded_sources_declare_their_own_module_name() {
        for (name, src) in MODULES {
            let module = name.split_once('x').map_or(*name, |(m, _)| m);
            assert_eq!(src.lines().next(), Some(format!("$ @mod {module}").as_str()));
            if module != *name {
                assert!(src.contains(&format!("# \\file {name}.ares")), "{name}");
            }
        }
    }
}

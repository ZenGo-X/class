use std::collections::HashSet;
use std::env;
use std::ffi::{OsStr, OsString};
use std::fs;
use std::io::Write;
use std::iter::FromIterator;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{anyhow, bail, Context};

fn main() -> anyhow::Result<()> {
    let out_dir = env::var("OUT_DIR").context("OUT_DIR env variable is not set")?;
    let out_dir = Path::new(&out_dir);
    let out_dir = fs::canonicalize(out_dir).context("canonicalize OUT_DIR")?;
    println!("Out dir: {}", out_dir.to_string_lossy());

    let pari_dir = PathBuf::from_iter([".", "depend", "pari"]);
    let pari_mirror = out_dir.join("pari-mirror");
    let pari_install = out_dir.join("pari-install");

    println!(
        "cargo:rerun-if-changed={}/CHANGES",
        pari_dir.to_string_lossy()
    );

    // Create a copy of pari directory inside of OUT_DIR
    {
        if pari_mirror.exists() {
            fs::remove_dir_all(&pari_mirror).context("remove mirror copy of pari")?;
        }

        let opts = fs_extra::dir::CopyOptions {
            copy_inside: true,
            ..Default::default()
        };
        fs_extra::dir::copy(&pari_dir, &pari_mirror, &opts)
            .context("create a copy of pari directory to OUT_DIR")?;
        // Ensure that the rest of build script doesn't refer to original pari directory by mistake
        drop(pari_dir);
    }

    {
        let output = Command::new(pari_mirror.join("Configure"))
            .arg(OsString::from_iter([
                OsStr::new("--prefix="),
                pari_install.as_os_str(),
            ]))
            .current_dir(&pari_mirror)
            .output()
            .context("run ./Configure")?;

        if !output.status.success() {
            std::io::stderr()
                .write_all(&output.stderr)
                .context("write error to stderr")?;
            bail!("./Configure returned non-zero code")
        }
    }

    {
        let output = Command::new("make")
            .arg("install-nodata")
            .current_dir(&pari_mirror)
            .output()
            .context("run `make install-nodata`")?;

        if !output.status.success() {
            std::io::stderr()
                .write_all(&output.stderr)
                .context("write error to stderr")?;
            bail!("`make install-nodata` returned non-zero code");
        }
    }

    {
        let output = Command::new("make")
            .arg("install-lib-sta")
            .current_dir(&pari_mirror)
            .output()
            .context("run `make install-lib-sta`")?;

        if !output.status.success() {
            std::io::stderr()
                .write_all(&output.stderr)
                .context("write error to stderr")?;
            bail!("`make install-lib-sta` returned non-zero code")
        }
    }

    let ignored_macros = IgnoreMacros(
        vec![
            "FP_INFINITE".into(),
            "FP_NAN".into(),
            "FP_NORMAL".into(),
            "FP_SUBNORMAL".into(),
            "FP_ZERO".into(),
            "IPPORT_RESERVED".into(),
        ]
        .into_iter()
        .collect(),
    );

    let bindings = bindgen::Builder::default()
        // The input header we would like to generate
        // bindings for.
        .header("wrapper.h")
        .clang_arg(format!(
            "-I{}",
            pari_install.join("include").to_string_lossy()
        ))
        .whitelist_type("GEN")
        .whitelist_function("mkintn")
        .whitelist_function("GENtostr")
        .whitelist_function("compo")
        .whitelist_function("qfi")
        .whitelist_function("nupow")
        .whitelist_function("qfbcompraw")
        .whitelist_function("primeform")
        .whitelist_function("pari_init")
        .whitelist_function("gneg")
        .whitelist_function("gadd")
        .whitelist_function("shifti")
        .whitelist_function("isprime")
        .parse_callbacks(Box::new(ignored_macros))
        // Finish the builder and generate the bindings.
        .generate()
        .map_err(|_| anyhow!("couldn't generate bindings"))?;

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .context("couldn't write bindings")?;

    println!(
        "cargo:rustc-link-search=native={}/lib",
        pari_install.to_string_lossy()
    );
    println!("cargo:rustc-link-lib=static=pari");

    Ok(())
}

#[derive(Debug)]
struct IgnoreMacros(HashSet<String>);

impl bindgen::callbacks::ParseCallbacks for IgnoreMacros {
    fn will_parse_macro(&self, name: &str) -> bindgen::callbacks::MacroParsingBehavior {
        if self.0.contains(name) {
            bindgen::callbacks::MacroParsingBehavior::Ignore
        } else {
            bindgen::callbacks::MacroParsingBehavior::Default
        }
    }
}

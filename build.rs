use std::collections::HashSet;
extern crate bindgen;

use std::env;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
fn main() {
    let path = fs::canonicalize("./depend/pari-2.11.2/Configure").unwrap();
    Command::new(path.to_str().unwrap())
        .output()
        .expect("failed to execute process");

    Command::new("make")
        .arg("install-nodata")
        .current_dir("depend/pari-2.11.2")
        .output()
        .expect("failed to make");

    Command::new("make")
        .arg("install-lib-sta")
        .current_dir("depend/pari-2.11.2")
        .output()
        .expect("failed to make");

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
        .parse_callbacks(Box::new(ignored_macros))
        // Finish the builder and generate the bindings.
        .generate()
        // Unwrap the Result and panic on failure.
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");

    println!("cargo:rustc-link-lib=dylib=pari");
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

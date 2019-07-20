extern crate bindgen;

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;
fn main() {
    // if Path::new("/test").exists()==false{
    let output = Command::new("./Configure")
        .current_dir("depend/pari-2.11.2")
        .output()
        .expect("failed to execute process");

    Command::new("make")
        .arg("all")
        .current_dir("depend/pari-2.11.2")
        .output()
        .expect("failed to make");

    Command::new("make")
        .arg("install-lib-sta")
        .current_dir("depend/pari-2.11.2")
        .output()
        .expect("failed to make");

    // }

    let bindings = bindgen::Builder::default()
        // The input header we would like to generate
        // bindings for.
        .header("wrapper.h")
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

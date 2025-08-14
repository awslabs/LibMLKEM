fn main() {
    // Tell cargo to look for shared libraries in the specified directory
    println!("cargo:rustc-link-search=/home/ubuntu/lib");
    println!("cargo:rustc-link-lib=refc");
}

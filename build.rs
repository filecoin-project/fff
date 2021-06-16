fn main() {
    #[cfg(target_arch = "x86_64")]
    cc::Build::new()
        .flag("-c")
        .file("./asm/mul_4.S")
        .compile("libff-derive-crypto.a");
}

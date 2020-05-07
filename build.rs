

fn main() {
    if let Ok(target_arch) = std::env::var("CARGO_CFG_TARGET_ARCH") {
        match target_arch.as_ref() {
            "x86_64" => {
                println!("cargo:rerun-if-changed=./asm/mul_4.S");
                cc::Build::new()
                    .flag("-c")
                    .file("./asm/mul_4.S")
                    .compile("libff-derive-crypto.a");
            },
            _ => {

            },
        }
    }
}

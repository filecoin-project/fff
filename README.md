# fff

> Fork of the great [`ff`](https://github.com/zkcrypto/ff) library.

`fff` is a finite field library written in Rust.

## Disclaimers

* This library does not provide constant-time guarantees.

## Usage

Add the `fff` crate to your `Cargo.toml`:

```toml
[dependencies]
fff = "0.3.0"
```

The `fff` crate contains the `Field` and `PrimeField` traits.
See the **[documentation](https://docs.rs/fff)** for more.

### `#[derive(PrimeField)]`

If you need an implementation of a prime field, this library also provides a procedural
macro that will expand into an efficient implementation of a prime field when supplied
with the modulus. `PrimeFieldGenerator` must be an element of Fp of p-1 order, that is
also quadratic nonresidue.

First, enable the `derive` crate feature:

```toml
[dependencies]
fff = { version = "0.3.0", features = ["derive"] }
```

And then use the macro like so:

```rust
#[macro_use]
extern crate fff;

#[derive(PrimeField)]
#[PrimeFieldModulus = "52435875175126190479447740508185965837690552500527637822603658699938581184513"]
#[PrimeFieldGenerator = "7"]
#[PrimeFieldReprEndianness = "little"]
struct Fp([u64; 4]);
```

And that's it! `Fp` now implements `Field` and `PrimeField`.

## Minimum Supported Rust Version

Requires Rust **1.51** or higher.

Minimum supported Rust version can be changed in the future, but it will be done with a
minor version bump.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.

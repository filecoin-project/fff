#![recursion_limit = "1024"]

#[macro_use]
extern crate quote;

use std::str::FromStr;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::One;

mod constants;
mod prime_field;
mod prime_field_repr;
mod sqrt;
mod util;

use crate::prime_field::*;
use crate::prime_field_repr::*;
use crate::util::*;

#[proc_macro_derive(PrimeField, attributes(PrimeFieldModulus, PrimeFieldGenerator))]
pub fn prime_field(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    // Parse the type definition
    let ast: syn::DeriveInput = syn::parse(input).unwrap();

    // The struct we're deriving for is a wrapper around a "Repr" type we must construct.
    let repr_ident = fetch_wrapped_ident(&ast.data)
        .expect("PrimeField derive only operates over tuple structs of a single item");

    // We're given the modulus p of the prime field
    let modulus_raw = fetch_attr("PrimeFieldModulus", &ast.attrs)
        .expect("Please supply a PrimeFieldModulus attribute");
    let modulus: BigUint = modulus_raw
        .parse()
        .expect("PrimeFieldModulus should be a number");

    // We may be provided with a generator of p - 1 order. It is required that this generator be quadratic
    // nonresidue.
    let generator: BigUint = fetch_attr("PrimeFieldGenerator", &ast.attrs)
        .expect("Please supply a PrimeFieldGenerator attribute")
        .parse()
        .expect("PrimeFieldGenerator should be a number");

    // The arithmetic in this library only works if the modulus*2 is smaller than the backing
    // representation. Compute the number of limbs we need.
    let mut limbs = 1;
    {
        let mod2 = (&modulus) << 1; // modulus * 2
        let mut cur = BigUint::one() << 64; // always 64-bit limbs for now
        while cur < mod2 {
            limbs += 1;
            cur = cur << 64;
        }
    }

    let mut gen = proc_macro2::TokenStream::new();

    // Compute R = 2**(64 * limbs) mod m
    let r = (BigUint::one() << (limbs * 64)) % &modulus;

    // modulus - 1 = 2^s * t
    let mut s: u32 = 0;
    let mut t = &modulus - BigUint::from_str("1").unwrap();
    while t.is_even() {
        t = t >> 1;
        s += 1;
    }

    let sqrt_impl = crate::sqrt::sqrt_impl(&ast.ident, &repr_ident, &modulus, limbs, &r, &t);
    let constants_impl =
        crate::constants::constants_impl(&repr_ident, limbs, &modulus, &r, s, &t, generator);

    gen.extend(constants_impl);
    gen.extend(prime_field_repr_impl(&repr_ident, limbs));
    gen.extend(prime_field_impl(
        &ast.ident,
        &repr_ident,
        limbs,
        &modulus_raw,
    ));
    gen.extend(sqrt_impl);

    // Return the generated impl
    gen.into()
}
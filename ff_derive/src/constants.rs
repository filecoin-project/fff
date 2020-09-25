use num_bigint::{BigUint, BigInt, ToBigInt};

use crate::util::*;

use std::ops::Neg;
use num_traits::{Zero, One, Signed};
use num_integer::Integer;

// https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
// r > q, modifies rinv and qinv such that rinv.r - qinv.q = 1
pub fn extended_euclidean_algo(r: &BigUint, q: &BigUint, r_inv: &mut BigInt, q_inv: &mut BigInt) {
    let mut s1: BigInt = BigInt::zero();
    let mut s2: BigInt;
    let mut t1: BigInt = BigInt::one();
    let mut t2: BigInt;
    let mut qi: BigInt;
    let mut tmp_muls: BigInt;
    let mut ri_plus_one: BigInt;
    let mut tmp_mult: BigInt;
    let mut a: BigInt = r.to_bigint().unwrap();
    let mut b: BigInt = q.to_bigint().unwrap();

    *r_inv = BigInt::one();
    *q_inv = BigInt::zero();

// r_i+1 = r_i-1 - q_i.r_i
// s_i+1 = s_i-1 - q_i.s_i
// t_i+1 = t_i-1 - q_i.s_i
    while b.cmp(&0.into()) == std::cmp::Ordering::Greater
    {
        qi = BigInt::from(&a / &b);
        ri_plus_one = &a % &b;

        tmp_muls = &s1 * &qi;
        tmp_mult = &t1 * &qi;

        s2 = s1;
        t2 = t1;

        s1 = r_inv.clone() - &tmp_muls;
        t1 = q_inv.clone() - &tmp_mult;
        *r_inv = s2;
        *q_inv = t2;

        a = b;
        b = ri_plus_one;
    }
    *q_inv = q_inv.clone().neg();
}

pub fn constants_impl(
    repr: &syn::Ident,
    limbs: usize,
    modulus: &BigUint,
    r: &BigUint,
    s: u32,
    t: &BigUint,
    generator: BigUint,
    modvec: &Vec<u64>
) -> proc_macro2::TokenStream {
    let mut gen = proc_macro2::TokenStream::new();

    let modulus_num_bits = biguint_num_bits(modulus.clone());

    // The number of bits we should "shave" from a randomly sampled reputation, i.e.,
    // if our modulus is 381 bits and our representation is 384 bits, we should shave
    // 3 bits from the beginning of a randomly sampled 384 bit representation to
    // reduce the cost of rejection sampling.
    let repr_shave_bits = (64 * limbs as u32) - biguint_num_bits(modulus.clone());

    // Compute 2^s root of unity given the generator
    let root_of_unity =
        biguint_to_u64_vec((exp(generator.clone(), t, &modulus) * r) % modulus, limbs);
    let generator = biguint_to_u64_vec((generator.clone() * r) % modulus, limbs);

    // Compute R^2 mod m
    let r2 = biguint_to_u64_vec((r * r) % modulus, limbs);

    let mut _r_inv: BigInt = BigInt::one();
    let mut _q_inv: BigInt = BigInt::zero();
    extended_euclidean_algo(&r, &modulus, &mut _r_inv, &mut _q_inv);
    _q_inv.mod_floor(&r.to_bigint().unwrap());

    let r = biguint_to_u64_vec(r.clone(), limbs);

    let q_inverse = biguint_to_u64_vec(_q_inv.abs().to_biguint().unwrap(), limbs);

    // Compute -m^-1 mod 2**64 by exponentiating by totient(2**64) - 1
    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(modvec[0]);
    }
    inv = inv.wrapping_neg();

    gen.extend(quote! {
        /// This is the modulus m of the prime field
        const MODULUS: #repr = #repr([#(#modvec,)*]);

        /// The number of bits needed to represent the modulus.
        const MODULUS_BITS: u32 = #modulus_num_bits;

        /// The number of bits that must be shaved from the beginning of
        /// the representation when randomly sampling.
        const REPR_SHAVE_BITS: u32 = #repr_shave_bits;

        /// 2^{limbs*64} mod m
        const R: #repr = #repr(#r);

        /// 2^{limbs*64*2} mod m
        const R2: #repr = #repr(#r2);

        /// -(m^{-1} mod m) mod m
        const INV: u64 = #inv;

        const Q_INV: #repr = #repr(#q_inverse);

        /// Multiplicative generator of `MODULUS` - 1 order, also quadratic
        /// nonresidue.
        const GENERATOR: #repr = #repr(#generator);

        /// 2^s * t = MODULUS - 1 with t odd
        const S: u32 = #s;

        /// 2^s root of unity computed by GENERATOR^t
        const ROOT_OF_UNITY: #repr = #repr(#root_of_unity);
    });

    gen
}

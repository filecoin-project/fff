use num_bigint::BigUint;

use crate::util::*;

pub fn constants_impl(
    repr: &syn::Ident,
    limbs: usize,
    modulus: &BigUint,
    r: &BigUint,
    s: u32,
    t: &BigUint,
    generator: BigUint,
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

    let r = biguint_to_u64_vec(r.clone(), limbs);
    let modulus = biguint_to_real_u64_vec(modulus.clone(), limbs);

    // Compute -m^-1 mod 2**64 by exponentiating by totient(2**64) - 1
    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(modulus[0]);
    }
    inv = inv.wrapping_neg();

    gen.extend(quote! {
        /// This is the modulus m of the prime field
        const MODULUS: #repr = #repr([#(#modulus,)*]);

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

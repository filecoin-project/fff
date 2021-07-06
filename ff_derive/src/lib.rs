#![recursion_limit = "1024"]

extern crate proc_macro;
extern crate proc_macro2;
extern crate syn;
#[macro_use]
extern crate quote;

extern crate num_bigint;
extern crate num_integer;
extern crate num_traits;

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, ToPrimitive, Zero};
use quote::TokenStreamExt;
use std::str::FromStr;

const BLS_381_FR_MODULUS: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

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

    // Compute the number lf 64-bit limbs.
    //
    // The arithmetic in this library works only if `2 * modulus` is smaller than the backing
    // representation `limbs * 64` bits. This is because we want to allow a carry bit to be stored
    // in the representation, see `add_nocarry()`, without having to perform reduction
    // `mod modulus`.
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

    let (constants_impl, sqrt_impl) =
        prime_field_constants_and_sqrt(&ast.ident, &repr_ident, modulus, limbs, generator);

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

/// Fetches the ident being wrapped by the type we're deriving.
fn fetch_wrapped_ident(body: &syn::Data) -> Option<syn::Ident> {
    match body {
        &syn::Data::Struct(ref variant_data) => match variant_data.fields {
            syn::Fields::Unnamed(ref fields) => {
                if fields.unnamed.len() == 1 {
                    match fields.unnamed[0].ty {
                        syn::Type::Path(ref path) => {
                            if path.path.segments.len() == 1 {
                                return Some(path.path.segments[0].ident.clone());
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        },
        _ => {}
    };

    None
}

/// Fetch an attribute string from the derived struct.
fn fetch_attr(name: &str, attrs: &[syn::Attribute]) -> Option<String> {
    for attr in attrs {
        if let Ok(meta) = attr.parse_meta() {
            match meta {
                syn::Meta::NameValue(nv) => {
                    if nv.path.get_ident().map(|i| i.to_string()) == Some(name.to_string()) {
                        match nv.lit {
                            syn::Lit::Str(ref s) => return Some(s.value()),
                            _ => {
                                panic!("attribute {} should be a string", name);
                            }
                        }
                    }
                }
                _ => {
                    panic!("attribute {} should be a string", name);
                }
            }
        }
    }

    None
}

// Implement PrimeFieldRepr for the wrapped ident `repr` with `limbs` limbs.
fn prime_field_repr_impl(repr: &syn::Ident, limbs: usize) -> proc_macro2::TokenStream {
    quote! {
        // Stores a prime field element, an integer `mod p`, using a little-endian array of `u64`s
        // (i.e. limbs). The first limb contains the integer's least-significant 64 bits and the
        // last limb contains the most-significant 64 bits. Storing a uint as an array of 64-bit
        // limbs is equivalent to storing the integer in radix-2^64 representation, i.e. if `a` is
        // an integer `mod p`, then `a = limbs[0] * 2^(64 * 0) + ... + limbs[n] * 2^(64 * n)`.
        //
        // Field elements are stored in Montgomery form, i.e. a field element `a ∈ Zp` is stored
        // as `a * R mod p` where `R` is the Montgomery factor. `R` is chosen to be a power of 2
        // greater than the modulus, i.e. `R = 2^x` where `R > p`. Choosing a Montgomery factor
        // which is a power of two converts division by `p` (which occurs at the end of modular
        // multiplication when reducing the product `mod p`) with division by `R` (which is much
        // more efficient because `R` is a power of two). Storing field elements in Montgomery form
        // makes performing a series of moduluar multiplications more efficient. Because `R` is
        // relatively prime to `p`, multiplying every field element `a ∈ Zp` covers `Zp`:
        // `{a * R (mod p) | ∀a ∈ Zp } = Zp`, i.e. multiplication by `R` is injective and
        // `a * R (mod p)` is unique for each `a ∈ Zp`.
        #[derive(Copy, Clone, PartialEq, Eq, Default, ::serde::Serialize, ::serde::Deserialize)]
        pub struct #repr(pub [u64; #limbs]);

        // Writes `self` as a hex string where the leftmost byte in the hex string, i.e. the two
        // characters to the right of "0x" represent the most significant byte of `self` and the hex
        // string's rightmost two characters represent `self`'s least-significant byte.
        impl ::std::fmt::Debug for #repr
        {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                write!(f, "0x")?;
                for i in self.0.iter().rev() {
                    write!(f, "{:016x}", *i)?;
                }

                Ok(())
            }
        }

        impl ::std::fmt::Display for #repr {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                write!(f, "0x")?;
                for i in self.0.iter().rev() {
                    write!(f, "{:016x}", *i)?;
                }

                Ok(())
            }
        }

        impl AsRef<[u64]> for #repr {
            #[inline(always)]
            fn as_ref(&self) -> &[u64] {
                &self.0
            }
        }

        impl AsMut<[u64]> for #repr {
            #[inline(always)]
            fn as_mut(&mut self) -> &mut [u64] {
                &mut self.0
            }
        }

        impl From<u64> for #repr {
            #[inline(always)]
            fn from(val: u64) -> #repr {
                use std::default::Default;

                let mut repr = Self::default();
                repr.0[0] = val;
                repr
            }
        }

        impl Ord for #repr {
            #[inline(always)]
            fn cmp(&self, other: &#repr) -> ::std::cmp::Ordering {
                for (a, b) in self.0.iter().rev().zip(other.0.iter().rev()) {
                    if a < b {
                        return ::std::cmp::Ordering::Less
                    } else if a > b {
                        return ::std::cmp::Ordering::Greater
                    }
                }

                ::std::cmp::Ordering::Equal
            }
        }

        impl PartialOrd for #repr {
            #[inline(always)]
            fn partial_cmp(&self, other: &#repr) -> Option<::std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl ::fff::PrimeFieldRepr for #repr {
            #[inline(always)]
            fn is_odd(&self) -> bool {
                self.0[0] & 1 == 1
            }

            #[inline(always)]
            fn is_even(&self) -> bool {
                !self.is_odd()
            }

            #[inline(always)]
            fn is_zero(&self) -> bool {
                self.0.iter().all(|&e| e == 0)
            }

            // Right-shift `self` by `n` bits, i.e. `self = self / 2^n`. Shifts all limbs rightwards
            // by `n` bits and does not perform reduction `mod p`.
            #[inline(always)]
            fn shr(&mut self, mut n: u32) {
                if n as usize >= 64 * #limbs {
                    *self = Self::from(0);
                    return;
                }

                // Shift out any full limbs (64-bits). Every iteration of the `while`-loop replaces
                // the most-significant non-zero limb with 0.
                while n >= 64 {
                    let mut prev_limb = 0;
                    // Move all limbs in the array one position towards the least-significant end.
                    for limb in self.0.iter_mut().rev() {
                        ::std::mem::swap(&mut prev_limb, limb);
                    }
                    n -= 64;
                }

                // Shift all limbs rightwords by `n` bits. The `n` least-significant bits of a limb
                // are shifted into the `n` most-significant bits of the next (less-significant)
                // limb.
                if n > 0 {
                    let mut bits_to_insert = 0;
                    for limb in self.0.iter_mut().rev() {
                        let bits_removed = *limb << (64 - n);
                        *limb >>= n;
                        *limb |= bits_to_insert;
                        bits_to_insert = bits_removed;
                    }
                }
            }

            // Equivalent to `self.shr(1)`. Does not perform reduction.
            #[inline(always)]
            fn div2(&mut self) {
                let mut bit_from_prev_limb = 0;
                for limb in self.0.iter_mut().rev() {
                    let bit_shifted_out = *limb << 63;
                    *limb >>= 1;
                    *limb |= bit_from_prev_limb;
                    bit_from_prev_limb = bit_shifted_out;
                }
            }

            // Equivalent to `self.shl(1)`. Does not perform reduction.
            #[inline(always)]
            fn mul2(&mut self) {
                let mut msb_prev_limb = 0;
                for limb in &mut self.0 {
                    let msb = *limb >> 63;
                    *limb <<= 1;
                    *limb |= msb_prev_limb;
                    msb_prev_limb = msb;
                }
            }

            // Left-shift `self` by `n` bits, i.e. `self = self * 2^n`. Shifts all limbs leftwards
            // by `n` bits and does not perform reduction `mod p`.
            #[inline(always)]
            fn shl(&mut self, mut n: u32) {
                if n as usize >= 64 * #limbs {
                    *self = Self::from(0);
                    return;
                }

                // Shift full limbs (64-bits) towards the most significant-end. Each iteration of
                // the `while`-loop replaces the least-significant non-zero limb with 0.
                while n >= 64 {
                    let mut prev_limb = 0;
                    // Move all limbs one position towards the most-significant end.
                    for limb in &mut self.0 {
                        ::std::mem::swap(&mut prev_limb, limb);
                    }
                    n -= 64;
                }

                // Shift all limbs leftwords by `n` bits. The `n` most-significant bits of a limb
                // are shifted into the `n` least-significant bits of the next more-significant
                // limb.
                if n > 0 {
                    let mut bits_to_insert = 0;
                    for limb in &mut self.0 {
                        let bits_removed = *limb >> (64 - n);
                        *limb <<= n;
                        *limb |= bits_to_insert;
                        bits_to_insert = bits_removed;
                    }
                }
            }

            // Returns the number of bits that are utilized in `self`.
            #[inline(always)]
            fn num_bits(&self) -> u32 {
                let mut n_bits = (#limbs as u32) * 64;
                for limb in self.0.iter().rev() {
                    let leading = limb.leading_zeros();
                    n_bits -= leading;
                    if leading != 64 {
                        break;
                    }
                }

                n_bits
            }

            // Addition without wrapping `mod p`. After calling `.add_nocarry()`, `self` may exceed
            // the modulus and will need to be reduced `mod p`. Any carry bits that exceed the
            // most-significant bit of the representation are thrown away. Note that the number of
            // limbs were chosen such that the addition of two field elements will not overflow the
            // representation, i.e. for any `a, b ∈ Zp`: `a + b < 2^(64 * limbs)`.
            #[inline(always)]
            fn add_nocarry(&mut self, other: &#repr) {
                let mut carry = 0;

                for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
                    *a = ::fff::adc(*a, *b, &mut carry);
                }
            }

            #[inline(always)]
            fn sub_noborrow(&mut self, other: &#repr) {
                let mut borrow = 0;

                for (a, b) in self.0.iter_mut().zip(other.0.iter()) {
                    *a = ::fff::sbb(*a, *b, &mut borrow);
                }
            }
        }
    }
}

/// Convert BigUint into a vector of 64-bit limbs.
fn biguint_to_real_u64_vec(mut v: BigUint, limbs: usize) -> Vec<u64> {
    let m = BigUint::one() << 64;
    let mut ret = vec![];

    while v > BigUint::zero() {
        ret.push((&v % &m).to_u64().unwrap());
        v = v >> 64;
    }

    while ret.len() < limbs {
        ret.push(0);
    }

    assert!(ret.len() == limbs);

    ret
}

/// Convert BigUint into a tokenized vector of 64-bit limbs.
fn biguint_to_u64_vec(v: BigUint, limbs: usize) -> proc_macro2::TokenStream {
    let ret = biguint_to_real_u64_vec(v, limbs);
    quote!([#(#ret,)*])
}

fn biguint_num_bits(mut v: BigUint) -> u32 {
    let mut bits = 0;

    while v != BigUint::zero() {
        v = v >> 1;
        bits += 1;
    }

    bits
}

/// BigUint modular exponentiation by square-and-multiply.
fn exp(base: BigUint, exp: &BigUint, modulus: &BigUint) -> BigUint {
    let mut ret = BigUint::one();

    for i in exp
        .to_bytes_be()
        .into_iter()
        .flat_map(|x| (0..8).rev().map(move |i| (x >> i).is_odd()))
    {
        ret = (&ret * &ret) % modulus;
        if i {
            ret = (ret * &base) % modulus;
        }
    }

    ret
}

#[test]
fn test_exp() {
    assert_eq!(
        exp(
            BigUint::from_str("4398572349857239485729348572983472345").unwrap(),
            &BigUint::from_str("5489673498567349856734895").unwrap(),
            &BigUint::from_str(
                "52435875175126190479447740508185965837690552500527637822603658699938581184513"
            )
            .unwrap()
        ),
        BigUint::from_str(
            "4371221214068404307866768905142520595925044802278091865033317963560480051536"
        )
        .unwrap()
    );
}

fn prime_field_constants_and_sqrt(
    name: &syn::Ident,
    repr: &syn::Ident,
    modulus: BigUint,
    limbs: usize,
    generator: BigUint,
) -> (proc_macro2::TokenStream, proc_macro2::TokenStream) {
    let modulus_num_bits = biguint_num_bits(modulus.clone());

    // The number of bits we should "shave" from a randomly sampled reputation, i.e.,
    // if our modulus is 381 bits and our representation is 384 bits, we should shave
    // 3 bits from the beginning of a randomly sampled 384 bit representation to
    // reduce the cost of rejection sampling.
    let repr_shave_bits = (64 * limbs as u32) - biguint_num_bits(modulus.clone());

    // Compute the Montgomery factor `R = 2^(64 * limbs) (mod p)`.
    let r = (BigUint::one() << (limbs * 64)) % &modulus;

    // Factor out the powers of two from `p - 1` by finding `s` and `t` (where `t` is odd) that
    // satisfy the equation: `p - 1 = 2^s * t`. Rearranging the equation into `t = (p-1)/2^s` and
    // initializing `s = 0` yields `t = p - 1`. Find the largest `s` s.t. `2^s` divides `p - 1`.
    let mut s: u32 = 0;
    let mut t = &modulus - BigUint::from_str("1").unwrap();
    while t.is_even() {
        t = t >> 1;
        s += 1;
    }

    // Compute a `2^s` root of unity given the generator for use in the Tonelli-Shanks algorithm. A
    // field element `x ∈ Zp*` is a `2^s` root of unity if `x^(2^s) = 1`. We use the generator as
    // the primitive root. Primitive roots `mod p` (where `p > 2`) are quadratic non-residues, i.e.
    // `∄x ∈ Zp` such that `x^2` equals the primitive root. It is a fact that a quadratic
    // non-residue raised to the `t`-th power has order `2^s`, i.e. is a `2^s` root or unity. See
    // https://ocw.mit.edu/courses/mathematics/18-781-theory-of-numbers-spring-2012/lecture-notes/MIT18_781S12_lec11.pdf
    // (page 2, "Tonelli's Algorithm")
    // Multiplying by `r` puts `generator^t into Montgomery form.
    let root_of_unity = biguint_to_u64_vec(
        (exp(generator.clone(), &t, &modulus) * &r) % &modulus,
        limbs,
    );

    // Convert the generator to Montgomery form.
    let generator = biguint_to_u64_vec((generator.clone() * &r) % &modulus, limbs);

    // The Legendre symbol for a prime field element `a` and modulus `p` is defined:
    // `a^(phi(p) / 2) mod p`, where `phi(p)` is the number of positive integers less than `p`
    // which are relatively prime to `p`. When `p` is prime, all positive integers less than `p` are
    // relatively prime to `p`, i.e. `phi(p) = p - 1`. If `a`'s Legendre symbol is `1` then `a` is
    // a quadratic residue, i.e. has a square root `∃x ∈ Zp*` such that `a = x^2 (mod p)`,
    // otherwise `a` is not a quadratic residue.
    let mod_minus_1_over_2 =
        biguint_to_u64_vec((&modulus - BigUint::from_str("1").unwrap()) >> 1, limbs);
    let legendre_impl = quote! {
        fn legendre(&self) -> ::fff::LegendreSymbol {
            // s = self^((modulus - 1) // 2)
            let s = self.pow(#mod_minus_1_over_2);
            if s == Self::zero() {
                ::fff::LegendreSymbol::Zero
            } else if s == Self::one() {
                ::fff::LegendreSymbol::QuadraticResidue
            } else {
                ::fff::LegendreSymbol::QuadraticNonResidue
            }
        }
    };

    // If `p = 3 (mod 4)` we use Shanks algorithm to compute square roots `mod p`. Otherwise, if
    // `p = 1 (mod 16)` we use the less efficient Tonelli-Shanks algorithm.
    // https://eprint.iacr.org/2012/685.pdf
    //   - Shanks Algorithm (page 8, section 4A)
    //   - Tonelli-Shanks Algorithm (page 12, algorithm 5)
    let sqrt_impl =
        if (&modulus % BigUint::from_str("4").unwrap()) == BigUint::from_str("3").unwrap() {
            let mod_minus_3_over_4 =
                biguint_to_u64_vec((&modulus - BigUint::from_str("3").unwrap()) >> 2, limbs);

            // Compute `-R` where negation is computed `p - R`.
            let rneg = biguint_to_u64_vec(&modulus - &r, limbs);

            quote! {
                impl ::fff::SqrtField for #name {
                    #legendre_impl

                    fn sqrt(&self) -> Option<Self> {
                        // Shank's algorithm for q mod 4 = 3
                        // https://eprint.iacr.org/2012/685.pdf (page 9, algorithm 2)

                        // `a1 = a^((p - 3) / 4)`
                        let mut a1 = self.pow(#mod_minus_3_over_4);

                        // `a0 = (a1^2) * a`
                        let mut a0 = a1;
                        a0.square();
                        a0.mul_assign(self);

                        // Note that `a0` is in Montgomery form, so `a0 = -r` in Montgomery form
                        // implies `a0` is -1 in non-Montgomery form.
                        if a0.0 == #repr(#rneg) {
                            None
                        } else {
                            a1.mul_assign(self);
                            Some(a1)
                        }
                    }
                }
            }
        } else if (&modulus % BigUint::from_str("16").unwrap()) == BigUint::from_str("1").unwrap() {
            // In the case where `p = 1 (mod 16)` no specialized square-root algorithm is known, see
            // https://eprint.iacr.org/2012/685.pdf (page 2)
            // in this case we use the Tonelli-Shanks algorithm.
            // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)

            let t_plus_1_over_2 = biguint_to_u64_vec((&t + BigUint::one()) >> 1, limbs);
            let t = biguint_to_u64_vec(t.clone(), limbs);

            quote! {
                impl ::fff::SqrtField for #name {
                    #legendre_impl

                    fn sqrt(&self) -> Option<Self> {
                        match self.legendre() {
                            ::fff::LegendreSymbol::Zero => Some(*self),
                            ::fff::LegendreSymbol::QuadraticNonResidue => None,
                            ::fff::LegendreSymbol::QuadraticResidue => {
                                let mut c = #name(ROOT_OF_UNITY);
                                let mut r = self.pow(#t_plus_1_over_2);
                                let mut t = self.pow(#t);
                                let mut m = S;

                                while t != Self::one() {
                                    let mut i = 1;
                                    {
                                        // `t^(2 * i)`
                                        let mut t2i = t;
                                        t2i.square();
                                        loop {
                                            if t2i == Self::one() {
                                                break;
                                            }
                                            t2i.square();
                                            i += 1;
                                        }
                                    }

                                    for _ in 0..(m - i - 1) {
                                        c.square();
                                    }
                                    r.mul_assign(&c);
                                    c.square();
                                    t.mul_assign(&c);
                                    m = i;
                                }

                                Some(r)
                            }
                        }
                    }
                }
            }
        } else {
            quote! {}
        };

    // Compute R^2 mod p
    let r2 = biguint_to_u64_vec((&r * &r) % &modulus, limbs);

    let r = biguint_to_u64_vec(r, limbs);
    let modulus = biguint_to_real_u64_vec(modulus, limbs);

    // Compute `-(p^-1) mod 2^64` using square-and-multiply exponentiation.
    //
    // From Euler's theorem we know that if `gcd(a, n) = 1` that `a^-1 = a^(phi(n) - 1) (mod n)`
    // where `phi` is the totient function. We know that `gcd(p, 2^64) = 1` because `p` is prime,
    // thus we can use Euler's theorem to compute `p^-1 mod 2^64`. It is a fact that
    // `phi(2^x) = 2^(x - 1)`; we substitute this into the Euler's theorem for modulus 2^64 yielding
    // `p^-1 = p^(2^63 - 1) (mod 2^64)`. The exponent `2^63 - 1` written as a bitstring 0b111...111
    // is 63 ones, thus we can compute `p^(2^63 - 1)` via 63 rounds of square-and-multiply on
    // `p`.
    //
    // Notice that when we represent a non-negative integer `x` using 64-bit limbs that
    // `x mod 2^64 = limbs[0]`. For example, if `p` has four `u64` limbs then:
    //
    // p mod 2^64
    //     = limbs[0]*2^(64*0) + limbs[1]*2^(64*1) + limbs[2]*2^(64*2) + limbs[3]*2^(64*3) (mod 2^64)
    //     = limbs[0]*2^(64*0) + 0                 + 0                 + 0                 (mod 2^64)
    //     = limbs[0]
    //
    // thus, we can substitute `p mod 2^64 = limbs[0]` into the inversion equation
    // `p^-1 = limbs[0]^(2^63 - 1) (mod 2^64)`.
    //
    // We compute the negation of the inverse `-(p^-1) mod 2^64` using `wrapping_neg()`. When
    // applied to `u64`s, the `wrapping_mul` and `wrapping_neg` methods are equivalent to performing
    // multiplication and negation `mod 2^64`.
    let mut inv = 1u64;
    for _ in 0..63 {
        inv = inv.wrapping_mul(inv);
        inv = inv.wrapping_mul(modulus[0]);
    }
    inv = inv.wrapping_neg();

    (
        quote! {
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

            /// `-(p^-1) mod 2^64` (usually denoted m' or p') used in Montgomery reduction.
            const INV: u64 = #inv;

            /// Multiplicative generator of `MODULUS` - 1 order, also quadratic
            /// nonresidue.
            const GENERATOR: #repr = #repr(#generator);

            /// 2^s * t = MODULUS - 1 with t odd
            const S: u32 = #s;

            /// 2^s root of unity computed by GENERATOR^t
            const ROOT_OF_UNITY: #repr = #repr(#root_of_unity);
        },
        sqrt_impl,
    )
}

/// Implement PrimeField for the derived type.
fn prime_field_impl(
    name: &syn::Ident,
    repr: &syn::Ident,
    limbs: usize,
    modulus_raw: &str,
) -> proc_macro2::TokenStream {
    // Returns r{n} as an ident.
    fn get_temp(n: usize) -> syn::Ident {
        syn::Ident::new(&format!("r{}", n), proc_macro2::Span::call_site())
    }

    // The parameter list for the mont_reduce() internal method.
    // r0: u64, mut r1: u64, mut r2: u64, ...
    let mut mont_paramlist = proc_macro2::TokenStream::new();
    mont_paramlist.append_separated(
        (0..(limbs * 2)).map(|i| (i, get_temp(i))).map(|(i, x)| {
            if i != 0 {
                quote! {mut #x: u64}
            } else {
                quote! {#x: u64}
            }
        }),
        proc_macro2::Punct::new(',', proc_macro2::Spacing::Alone),
    );

    // Implements Montgomery reduction for some number of limbs. See the paper
    // "Efficient Software-Implementation of Finite Fields with Applications to Cryptography"
    // (Algorithm 14. Montgomery Reduction)
    fn mont_impl(limbs: usize) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();

        for i in 0..limbs {
            {
                let temp = get_temp(i);
                gen.extend(quote! {
                    let k = #temp.wrapping_mul(INV);
                    let mut carry = 0;
                    ::fff::mac_with_carry(#temp, k, MODULUS.0[0], &mut carry);
                });
            }

            for j in 1..limbs {
                let temp = get_temp(i + j);
                gen.extend(quote! {
                    #temp = ::fff::mac_with_carry(#temp, k, MODULUS.0[#j], &mut carry);
                });
            }

            let temp = get_temp(i + limbs);

            if i == 0 {
                gen.extend(quote! {
                    #temp = ::fff::adc(#temp, 0, &mut carry);
                });
            } else {
                gen.extend(quote! {
                    #temp = ::fff::adc(#temp, carry2, &mut carry);
                });
            }

            if i != (limbs - 1) {
                gen.extend(quote! {
                    let carry2 = carry;
                });
            }
        }

        for i in 0..limbs {
            let temp = get_temp(limbs + i);

            gen.extend(quote! {
                (self.0).0[#i] = #temp;
            });
        }

        gen
    }

    fn sqr_impl(a: proc_macro2::TokenStream, limbs: usize) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();

        for i in 0..(limbs - 1) {
            gen.extend(quote! {
                let mut carry = 0;
            });

            for j in (i + 1)..limbs {
                let temp = get_temp(i + j);
                if i == 0 {
                    gen.extend(quote! {
                        let #temp = ::fff::mac_with_carry(0, (#a.0).0[#i], (#a.0).0[#j], &mut carry);
                    });
                } else {
                    gen.extend(quote!{
                        let #temp = ::fff::mac_with_carry(#temp, (#a.0).0[#i], (#a.0).0[#j], &mut carry);
                    });
                }
            }

            let temp = get_temp(i + limbs);

            gen.extend(quote! {
                let #temp = carry;
            });
        }

        for i in 1..(limbs * 2) {
            let temp0 = get_temp(limbs * 2 - i);
            let temp1 = get_temp(limbs * 2 - i - 1);

            if i == 1 {
                gen.extend(quote! {
                    let #temp0 = #temp1 >> 63;
                });
            } else if i == (limbs * 2 - 1) {
                gen.extend(quote! {
                    let #temp0 = #temp0 << 1;
                });
            } else {
                gen.extend(quote! {
                    let #temp0 = (#temp0 << 1) | (#temp1 >> 63);
                });
            }
        }

        gen.extend(quote! {
            let mut carry = 0;
        });

        for i in 0..limbs {
            let temp0 = get_temp(i * 2);
            let temp1 = get_temp(i * 2 + 1);
            if i == 0 {
                gen.extend(quote! {
                    let #temp0 = ::fff::mac_with_carry(0, (#a.0).0[#i], (#a.0).0[#i], &mut carry);
                });
            } else {
                gen.extend(quote!{
                    let #temp0 = ::fff::mac_with_carry(#temp0, (#a.0).0[#i], (#a.0).0[#i], &mut carry);
                });
            }

            gen.extend(quote! {
                let #temp1 = ::fff::adc(#temp1, 0, &mut carry);
            });
        }

        let mut mont_calling = proc_macro2::TokenStream::new();
        mont_calling.append_separated(
            (0..(limbs * 2)).map(|i| get_temp(i)),
            proc_macro2::Punct::new(',', proc_macro2::Spacing::Alone),
        );

        // Multiply the intermediary Montgomery product `(a * b) * R^2` by `R^1` to yield
        // `(a * b) * R`, the product `a * b` in Montgomery form.
        gen.extend(quote! {
            self.mont_reduce(#mont_calling);
        });

        gen
    }

    fn mul_impl(
        a: proc_macro2::TokenStream,
        b: proc_macro2::TokenStream,
        limbs: usize,
        modulus_raw: &str,
    ) -> proc_macro2::TokenStream {
        if limbs == 4 && modulus_raw == BLS_381_FR_MODULUS {
            mul_impl_asm4(a, b)
        } else {
            mul_impl_default(a, b, limbs)
        }
    }

    fn mul_impl_asm4(
        a: proc_macro2::TokenStream,
        b: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        // x86_64 asm for four limbs
        let default_impl = mul_impl_default(a.clone(), b.clone(), 4);

        let mut gen = proc_macro2::TokenStream::new();
        gen.extend(quote! {
            #[cfg(target_arch = "x86_64")]
            {
                if *::fff::CPU_SUPPORTS_ADX_INSTRUCTION {
                    ::fff::mod_mul_4w_assign(&mut (#a.0).0, &(#b.0).0);
                } else {
                    #default_impl
                }
            }
            #[cfg(not(target_arch = "x86_64"))]
            {
                #default_impl
            }
        });

        gen
    }

    fn mul_impl_default(
        a: proc_macro2::TokenStream,
        b: proc_macro2::TokenStream,
        limbs: usize,
    ) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();

        for i in 0..limbs {
            gen.extend(quote! {
                let mut carry = 0;
            });

            for j in 0..limbs {
                let temp = get_temp(i + j);

                if i == 0 {
                    gen.extend(quote! {
                        let #temp = ::fff::mac_with_carry(0, (#a.0).0[#i], (#b.0).0[#j], &mut carry);
                    });
                } else {
                    gen.extend(quote!{
                        let #temp = ::fff::mac_with_carry(#temp, (#a.0).0[#i], (#b.0).0[#j], &mut carry);
                    });
                }
            }

            let temp = get_temp(i + limbs);

            gen.extend(quote! {
                let #temp = carry;
            });
        }

        let mut mont_calling = proc_macro2::TokenStream::new();
        mont_calling.append_separated(
            (0..(limbs * 2)).map(|i| get_temp(i)),
            proc_macro2::Punct::new(',', proc_macro2::Spacing::Alone),
        );

        gen.extend(quote! {
            self.mont_reduce(#mont_calling);
        });

        gen
    }

    fn add_assign_impl(
        a: proc_macro2::TokenStream,
        b: proc_macro2::TokenStream,
        limbs: usize,
    ) -> proc_macro2::TokenStream {
        if limbs == 4 {
            add_assign_asm_impl(a, b, limbs)
        } else {
            add_assign_default_impl(a, b, limbs)
        }
    }

    fn add_assign_asm_impl(
        a: proc_macro2::TokenStream,
        b: proc_macro2::TokenStream,
        limbs: usize,
    ) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();
        let default_impl = add_assign_default_impl(a.clone(), b.clone(), limbs);

        gen.extend(quote! {
            #[cfg(target_arch = "x86_64")]
            {
                // This cannot exceed the backing capacity.
                use std::arch::x86_64::*;
                use std::mem;

                unsafe {
                    let mut carry = _addcarry_u64(
                        0,
                        (#a.0).0[0],
                        (#b.0).0[0],
                        &mut (#a.0).0[0]
                    );
                    carry = _addcarry_u64(
                        carry, (#a.0).0[1],
                        (#b.0).0[1],
                        &mut (#a.0).0[1]
                    );
                    carry = _addcarry_u64(
                        carry, (#a.0).0[2],
                        (#b.0).0[2],
                        &mut (#a.0).0[2]
                    );
                    _addcarry_u64(
                        carry,
                        (#a.0).0[3],
                        (#b.0).0[3],
                        &mut (#a.0).0[3]
                    );

                    let mut s_sub: [u64; 4] = mem::uninitialized();

                    carry = _subborrow_u64(
                        0,
                        (#a.0).0[0],
                        MODULUS.0[0],
                        &mut s_sub[0]
                    );
                    carry = _subborrow_u64(
                        carry,
                        (#a.0).0[1],
                        MODULUS.0[1],
                        &mut s_sub[1]
                    );
                    carry = _subborrow_u64(
                        carry,
                        (#a.0).0[2],
                        MODULUS.0[2],
                        &mut s_sub[2]
                    );
                    carry = _subborrow_u64(
                        carry,
                        (#a.0).0[3],
                        MODULUS.0[3],
                        &mut s_sub[3]
                    );

                    if carry == 0 {
                        // Direct assign fails since size can be 4 or 6
                        // Obviously code doesn't work at all for size 6
                        // (#a).0 = s_sub;
                        (#a.0).0[0] = s_sub[0];
                        (#a.0).0[1] = s_sub[1];
                        (#a.0).0[2] = s_sub[2];
                        (#a.0).0[3] = s_sub[3];
                    }
                }
            }
            #[cfg(not(target_arch = "x86_64"))]
            {
                #default_impl
            }
        });

        gen
    }

    fn add_assign_default_impl(
        a: proc_macro2::TokenStream,
        b: proc_macro2::TokenStream,
        _limbs: usize,
    ) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();

        gen.extend(quote! {
            // This cannot exceed the backing capacity.
            #a.0.add_nocarry(&#b.0);

            // However, it may need to be reduced.
            #a.reduce();
        });
        gen
    }

    let squaring_impl = sqr_impl(quote! {self}, limbs);
    let multiply_impl = mul_impl(quote! {self}, quote! {other}, limbs, modulus_raw);
    let add_assign = add_assign_impl(quote! {self}, quote! {other}, limbs);
    let montgomery_impl = mont_impl(limbs);

    // (self.0).0[0], (self.0).0[1], ..., 0, 0, 0, 0, ...
    let mut into_repr_params = proc_macro2::TokenStream::new();
    into_repr_params.append_separated(
        (0..limbs)
            .map(|i| quote! { (self.0).0[#i] })
            .chain((0..limbs).map(|_| quote! {0})),
        proc_macro2::Punct::new(',', proc_macro2::Spacing::Alone),
    );

    let top_limb_index = limbs - 1;

    quote! {
        impl ::std::marker::Copy for #name { }

        impl ::std::clone::Clone for #name {
            fn clone(&self) -> #name {
                *self
            }
        }

        impl ::std::cmp::PartialEq for #name {
            fn eq(&self, other: &#name) -> bool {
                self.0 == other.0
            }
        }

        impl ::std::cmp::Eq for #name { }

        impl ::std::fmt::Debug for #name
        {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                write!(f, "{}({:?})", stringify!(#name), self.into_repr())
            }
        }

        /// Elements are ordered lexicographically.
        impl Ord for #name {
            #[inline(always)]
            fn cmp(&self, other: &#name) -> ::std::cmp::Ordering {
                self.into_repr().cmp(&other.into_repr())
            }
        }

        impl PartialOrd for #name {
            #[inline(always)]
            fn partial_cmp(&self, other: &#name) -> Option<::std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl ::std::fmt::Display for #name {
            fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
                write!(f, "{}({})", stringify!(#name), self.into_repr())
            }
        }

        impl From<#name> for #repr {
            fn from(e: #name) -> #repr {
                e.into_repr()
            }
        }

        impl ::serde::Serialize for #name {
            fn serialize<S: ::serde::Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
                self.into_repr().serialize(s)
            }
        }

        impl<'de> ::serde::Deserialize<'de> for #name {
            fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
                use serde::de::Error;
                #name::from_repr(#repr::deserialize(d)?)
                    .map_err(|_| D::Error::custom(stringify!(format!("deserialized bytes don't encode a valid {}", #name))))
            }
        }

        impl ::fff::PrimeField for #name {
            type Repr = #repr;

            // Attempt to convert the bigint representation of a field element (not in Montgomery
            // form) into Montgomery form, failing if `r` represents an integer greater than the
            // modulus.
            fn from_repr(r: #repr) -> Result<#name, PrimeFieldDecodingError> {
                let mut r = #name(r);
                if r.is_valid() {
                    // We can put `r` into Montgomery form by taking the Montgomery product of `r`
                    // with `R^2 mod p`, i.e. `MontReduce(MontProd(a, R^2)) = aR (mod p)`.
                    // See "Montgomery’s Multiplication Technique: How to Make It Smaller and Faster"
                    // https://colinandmargaret.co.uk/Research/CDW_CHES_99.pdf (page 8)
                    // and the Wikipedia article:
                    // https://en.wikipedia.org/wiki/Montgomery_modular_multiplication#Arithmetic_in_Montgomery_form
                    // for more information regarding converting to and from Montgomery form.
                    r.mul_assign(&#name(R2));

                    Ok(r)
                } else {
                    Err(PrimeFieldDecodingError::NotInField(format!("{}", r.0)))
                }
            }

            // Convert `self` out of Montgomery form, returning the bigint representation. If
            // is in Montgomery form `self = a * R (mod p)` then Montgomery reduction removes the
            // factor of `R`, i.e. `MontReduce(a * R mod p) = a mod p`.
            fn into_repr(&self) -> #repr {
                let mut r = *self;
                r.mont_reduce(
                    #into_repr_params
                );

                r.0
            }

            fn char() -> #repr {
                MODULUS
            }

            const NUM_BITS: u32 = MODULUS_BITS;

            const CAPACITY: u32 = Self::NUM_BITS - 1;

            fn multiplicative_generator() -> Self {
                #name(GENERATOR)
            }

            const S: u32 = S;

            fn root_of_unity() -> Self {
                #name(ROOT_OF_UNITY)
            }


            fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
                use std::convert::TryInto;

                let mut repr = #repr::default();
                for (limb, chunk) in repr.0.iter_mut().zip(bytes.chunks_exact(8)) {
                    *limb = u64::from_le_bytes(chunk.try_into().unwrap());
                }

                // Mask away the unused most-significant bits.
                repr.0.as_mut()[#top_limb_index] &= 0xffffffffffffffff >> REPR_SHAVE_BITS;

                #name::from_repr(repr).ok()
            }
        }

        impl ::fff::Field for #name {
            /// Computes a uniformly random element using rejection sampling.
            fn random<R: ::rand_core::RngCore>(rng: &mut R) -> Self {
                loop {
                    let mut tmp = {
                        let mut repr = [0u64; #limbs];
                        for i in 0..#limbs {
                            repr[i] = rng.next_u64();
                        }
                        #name(#repr(repr))
                    };

                    // Mask away the unused most-significant bits.
                    tmp.0.as_mut()[#top_limb_index] &= 0xffffffffffffffff >> REPR_SHAVE_BITS;

                    if tmp.is_valid() {
                        return tmp
                    }
                }
            }

            #[inline]
            fn zero() -> Self {
                #name(#repr::from(0))
            }

            #[inline]
            fn one() -> Self {
                #name(R)
            }

            #[inline]
            fn is_zero(&self) -> bool {
                self.0.is_zero()
            }

            #[inline]
            fn add_assign(&mut self, other: &#name) {
                #add_assign
            }

            #[inline]
            fn double(&mut self) {
                // This cannot exceed the backing capacity.
                self.0.mul2();

                // However, it may need to be reduced.
                self.reduce();
            }

            #[inline]
            fn sub_assign(&mut self, other: &#name) {
                // If `other` is larger than `self`, we'll need to add the modulus to self first.
                if other.0 > self.0 {
                    self.0.add_nocarry(&MODULUS);
                }

                self.0.sub_noborrow(&other.0);
            }

            #[inline]
            fn negate(&mut self) {
                if !self.is_zero() {
                    let mut tmp = MODULUS;
                    tmp.sub_noborrow(&self.0);
                    self.0 = tmp;
                }
            }

            fn inverse(&self) -> Option<Self> {
                if self.is_zero() {
                    None
                } else {
                    // Guajardo Kumar Paar Pelzl
                    // Efficient Software-Implementation of Finite Fields with Applications to Cryptography
                    // Algorithm 16 (BEA for Inversion in Fp)

                    let one = #repr::from(1);

                    let mut u = self.0;
                    let mut v = MODULUS;
                    let mut b = #name(R2); // Avoids unnecessary reduction step.
                    let mut c = Self::zero();

                    while u != one && v != one {
                        while u.is_even() {
                            u.div2();

                            if b.0.is_even() {
                                b.0.div2();
                            } else {
                                b.0.add_nocarry(&MODULUS);
                                b.0.div2();
                            }
                        }

                        while v.is_even() {
                            v.div2();

                            if c.0.is_even() {
                                c.0.div2();
                            } else {
                                c.0.add_nocarry(&MODULUS);
                                c.0.div2();
                            }
                        }

                        if v < u {
                            u.sub_noborrow(&v);
                            b.sub_assign(&c);
                        } else {
                            v.sub_noborrow(&u);
                            c.sub_assign(&b);
                        }
                    }

                    if u == one {
                        Some(b)
                    } else {
                        Some(c)
                    }
                }
            }

            #[inline(always)]
            fn frobenius_map(&mut self, _: usize) {
                // This has no effect in a prime field.
            }

            #[inline]
            fn mul_assign(&mut self, other: &#name)
            {
                #multiply_impl
            }

            #[inline]
            fn square(&mut self)
            {
                #squaring_impl
            }
        }

        impl #name {
            /// Determines if the element is really in the field. This is only used
            /// internally.
            #[inline(always)]
            fn is_valid(&self) -> bool {
                self.0 < MODULUS
            }

            /// Subtracts the modulus from this element if this element is not in the
            /// field. Only used interally.
            #[inline(always)]
            fn reduce(&mut self) {
                if !self.is_valid() {
                    self.0.sub_noborrow(&MODULUS);
                }
            }

            // Perform Montgomery reduction on the integer `self` (which may be larger than the
            // modulus).
            #[inline(always)]
            fn mont_reduce(
                &mut self,
                #mont_paramlist
            )
            {
                // The Montgomery reduction here is based on Algorithm 14.32 in
                // Handbook of Applied Cryptography
                // <http://cacr.uwaterloo.ca/hac/about/chap14.pdf>.

                #montgomery_impl

                self.reduce();
            }
        }
    }
}

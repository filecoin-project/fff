use std::str::FromStr;

use num_bigint::BigUint;
use num_traits::One;

use crate::util::*;

fn legendre_impl(limbs: usize, modulus: &BigUint) -> proc_macro2::TokenStream {
    let mod_minus_1_over_2 =
        biguint_to_u64_vec((modulus - BigUint::from_str("1").unwrap()) >> 1, limbs);

    quote! {
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
    }
}

pub fn sqrt_impl(
    name: &syn::Ident,
    repr: &syn::Ident,
    modulus: &BigUint,
    limbs: usize,
    r: &BigUint,
    t: &BigUint,
) -> proc_macro2::TokenStream {
    let mut gen = proc_macro2::TokenStream::new();

    if (modulus % BigUint::from_str("4").unwrap()) == BigUint::from_str("3").unwrap() {
        let mod_minus_3_over_4 =
            biguint_to_u64_vec((modulus - BigUint::from_str("3").unwrap()) >> 2, limbs);

        // Compute -R as (m - r)
        let rneg = biguint_to_u64_vec(modulus - r, limbs);

        let legendre_impl = legendre_impl(limbs, modulus);

        gen.extend(quote! {
            impl ::fff::SqrtField for #name {
                #legendre_impl

                fn sqrt(&self) -> Option<Self> {
                    // Shank's algorithm for q mod 4 = 3
                    // https://eprint.iacr.org/2012/685.pdf (page 9, algorithm 2)

                    let mut a1 = self.pow(#mod_minus_3_over_4);

                    let mut a0 = a1;
                    a0.square();
                    a0.mul_assign(self);

                    if a0.0 == #repr(#rneg) {
                        None
                    } else {
                        a1.mul_assign(self);
                        Some(a1)
                    }
                }
            }
        });
    } else if (modulus % BigUint::from_str("8").unwrap()) == BigUint::from_str("5").unwrap() {
        let q_minus_5_div_8 = biguint_to_u64_vec((modulus) >> 3, limbs);

        gen.extend(quote! {
            impl ::fff::SqrtField for #name {
                fn sqrt(&self) -> Option<Self> {
                    // Atkin's algorithm for q mod 8 = 5
                    // https://github.com/ConsenSys/goff/blob/master/internal/templates/element/sqrt.go#L54
                    let mut tx = self.double();
                    let mut alpha = tx.pow(#q_minus_5_div_8);

                    let mut beta = alpha.square();
                    beta.mul_assign(tx);
                    beta.sub_assign(1);
                    beta.mul_assign(x);
                    beta.mul_assign(alpha);

                    let mut square = beta.square();
                    if square == self {
                        Some(beta)
                    } else {
                        None
                    }
                }
            }
        });
    } else if (modulus % BigUint::from_str("16").unwrap()) == BigUint::from_str("1").unwrap() {
        let t_plus_1_over_2 = biguint_to_u64_vec((t + BigUint::one()) >> 1, limbs);
        let t = biguint_to_u64_vec(t.clone(), limbs);
        let legendre_impl = legendre_impl(limbs, modulus);

        gen.extend(quote! {
            impl ::fff::SqrtField for #name {
                #legendre_impl

                fn sqrt(&self) -> Option<Self> {
                    // Tonelli-Shank's algorithm for q mod 16 = 1
                    // https://eprint.iacr.org/2012/685.pdf (page 12, algorithm 5)

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
        });
    }
    gen
}

use std::ops::{Neg, Sub};

use num_bigint::BigInt;
use num_bigint::BigUint;
use num_bigint::ToBigInt;
use num_bigint::ToBigUint;
use quote::TokenStreamExt;

use crate::util::*;

const BLS_381_FR_MODULUS: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";

// https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
// r > q, modifies rinv and qinv such that rinv.r - qinv.q = 1
pub fn extended_euclidean_algo(r: &BigInt, q: &BigInt, r_inv: &mut BigInt, q_inv: &mut BigInt) {
    let mut s1: BigInt = 0.into();
    let mut s2: BigInt = 0.into();
    let mut t1: BigInt = 1.into();
    let mut t2: BigInt = 0.into();
    let mut qi: BigInt = 0.into();
    let mut tmp_muls: BigInt = 0.into();
    let mut ri_plus_one: BigInt = 0.into();
    let mut tmp_mult: BigInt = 0.into();
    let mut a: BigInt = r.to_bigint().unwrap();
    let mut b: BigInt = q.to_bigint().unwrap();

    *r_inv = 1.into();
    *q_inv = 0.into();

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

        s1 = r_inv.to_bigint().unwrap() - &tmp_muls;
        t1 = q_inv.to_bigint().unwrap() - &tmp_mult;
        *r_inv = s2;
        *q_inv = t2;

        a = b;
        b = ri_plus_one;
    }
    *q_inv = q_inv.to_bigint().unwrap().neg();
}

/// Implement PrimeField for the derived type.
pub fn prime_field_impl(
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

    // Implement montgomery reduction for some number of limbs
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

    fn valid_impl(limbs: usize) -> proc_macro2::TokenStream {
        // (
        //   self[2] < modulus[2] || (self[2] == modulus[2] && (
        //     self[1] < modulus[1] || (self[1] == modulus[1] && (
        //       self[0] < modulus[0]
        //     ))
        //   ))
        // )

        let mut current = quote! {
            ((self.0).0[0] < MODULUS.0[0])
        };

        for i in 1..limbs {
            current = quote! {
                ((self.0).0[#i] < MODULUS.0[#i] || ((self.0).0[#i] == MODULUS.0[#i] && #current))
            };
        }

        current
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
                    gen.extend(quote! {
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
                gen.extend(quote! {
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
        if limbs == 4 && modulus_raw == BLS_381_FR_MODULUS && cfg!(target_arch = "x86_64") {
            mul_impl_asm4(a, b)
        } else {
            mul_impl_default(a, b, limbs)
        }
    }

    fn mul_impl_nocarry(
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
                    gen.extend(quote! {
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

    fn mul_impl_cios(
        a: proc_macro2::TokenStream,
        b: proc_macro2::TokenStream,
        modulus: &BigUint,
        limbs: usize,
    ) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();
        let temp = get_temp(limbs + 1);

        for i in 0..limbs {
            gen.extend(quote! {
                let mut carry = 0;
            });

            if i == 0 {
                gen.extend(quote! {
                    let (#temp.0).0[0] = ::fff::mac_with_carry(0, (#a.0).0[#i], (#b.0).0[0], &mut carry);
                });
                for j in 1..limbs {
                    gen.extend(quote! {
                        let (#temp.0).0[#i] = ::fff::mac_with_carry(0, (#a.0).0[#i], (#b.0).0[#j], &mut carry);
                    });
                }
            } else {
                gen.extend(quote! {
                carry = (#temp.0).0[0];
                    let (#temp.0).0[0] = ::fff::mac_with_carry(0, (#a.0).0[#i], (#b.0).0[0], &mut carry);
                });
                for j in 1..limbs {
                    gen.extend(quote! {
                        let (#temp.0).0[#j] = ::fff::mac_with_carry((#temp.0).0[#j], (#a.0).0[#i], (#b.0).0[#j], &mut carry);
                    });
                }
            }

            let _r: BigInt = BigInt::from(1 << (limbs * 64));
            let mut _r_inv: BigInt = BigInt::from(1);
            let mut _q_inv: BigInt = BigInt::from(0);
            extended_euclidean_algo(&_r, &modulus.to_bigint().unwrap(), &mut _r_inv, &mut _q_inv);
            _q_inv = _q_inv % _r;
            let q_inverse = biguint_to_u64_vec(_q_inv.to_biguint().unwrap(), limbs);
            let q = biguint_to_u64_vec(modulus.to_biguint().unwrap(), limbs);

            gen.extend(quote! {
                let mut d = carry;
                let mut m = ::fff::mac_with_carry(0, (#temp.0).0[0], (#q_inverse.0).0[0], &mut carry);
                carry = ::fff::mac_with_carry((#temp.0).0[0], m, (#q.0).0[0], carry);
            });
            for j in 1..limbs {
                if j == limbs - 1 {
                    gen.extend(quote! {
                        carry = ::fff::adc(carry, (#temp.0).0[#limbs])
                        let (#temp.0).0[#j - 1] = ::fff::mac_with_carry((#temp.0).0[#j], m, (#q.0).0[#j], &mut carry);
                    });
                } else {
                    gen.extend(quote! {
                        let (#temp.0).0[#j - 1] = ::fff::mac_with_carry((#temp.0).0[#j], m, (#q.0).0[#j], &mut carry);
                    });
                }
                gen.extend(quote! {
                    let (#temp.0).0[#limbs - 1] = ::fff::adc_no_carry(d, carry, &mut carry);
                    let (#temp.0).0[#limbs] = ::fff::adc_no_carry(d, carry, &mut carry);
                });
            }
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

    fn mul_impl_asm4(
        a: proc_macro2::TokenStream,
        b: proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream {
        // x86_64 asm for four limbs

        let default_impl = mul_impl_default(a.clone(), b.clone(), 4);

        let mut gen = proc_macro2::TokenStream::new();
        gen.extend(quote! {
            if *::fff::CPU_SUPPORTS_ADX_INSTRUCTION {
                ::fff::mod_mul_4w_assign(&mut (#a.0).0, &(#b.0).0);
            } else {
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
                    gen.extend(quote! {
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

    let squaring_impl = sqr_impl(quote! {self}, limbs);
    let multiply_impl = mul_impl(quote! {self}, quote! {other}, limbs, modulus_raw);
    let montgomery_impl = mont_impl(limbs);
    let is_valid_impl = valid_impl(limbs);

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

        impl ::fff::PrimeField for #name {
            type Repr = #repr;

            fn from_repr(r: #repr) -> Result<#name, PrimeFieldDecodingError> {
                let mut r = #name(r);
                if r.is_valid() {
                    r.mul_assign(&#name(R2));

                    Ok(r)
                } else {
                    Err(PrimeFieldDecodingError::NotInField(format!("{}", r.0)))
                }
            }

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
                if #limbs == 4 && cfg!(target_arch = "x86_64") {
                    // This cannot exceed the backing capacity.
                    use std::arch::x86_64::*;
                    use std::mem;

                    unsafe {
                        let mut carry = _addcarry_u64(
                            0,
                            (self.0).0[0],
                            (other.0).0[0],
                            &mut (self.0).0[0]
                        );
                        carry = _addcarry_u64(
                            carry, (self.0).0[1],
                            (other.0).0[1],
                            &mut (self.0).0[1]
                        );
                        carry = _addcarry_u64(
                            carry, (self.0).0[2],
                            (other.0).0[2],
                            &mut (self.0).0[2]
                        );
                        _addcarry_u64(
                            carry,
                            (self.0).0[3],
                            (other.0).0[3],
                            &mut (self.0).0[3]
                        );

                        let mut s_sub: [u64; 4] = mem::uninitialized();

                        carry = _subborrow_u64(
                            0,
                            (self.0).0[0],
                            MODULUS.0[0],
                            &mut s_sub[0]
                        );
                        carry = _subborrow_u64(
                            carry,
                            (self.0).0[1],
                            MODULUS.0[1],
                            &mut s_sub[1]
                        );
                        carry = _subborrow_u64(
                            carry,
                            (self.0).0[2],
                            MODULUS.0[2],
                            &mut s_sub[2]
                        );
                        carry = _subborrow_u64(
                            carry,
                            (self.0).0[3],
                            MODULUS.0[3],
                            &mut s_sub[3]
                        );

                        if carry == 0 {
                            // Direct assign fails since size can be 4 or 6
                            // Obviously code doesn't work at all for size 6
                            // (self.0).0 = s_sub;
                            (self.0).0[0] = s_sub[0];
                            (self.0).0[1] = s_sub[1];
                            (self.0).0[2] = s_sub[2];
                            (self.0).0[3] = s_sub[3];
                        }
                    }
                } else {
                    // This cannot exceed the backing capacity.
                    self.0.add_nocarry(&other.0);

                    // However, it may need to be reduced.
                    self.reduce();
                }
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

                    let mut u = self.0;
                    let mut v = MODULUS;
                    let mut b = #name(R2); // Avoids unnecessary reduction step.
                    let mut c = Self::zero();

                    while !u.is_one() && !v.is_one() {
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

                    if u.is_one() {
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
                #is_valid_impl
            }

            /// Subtracts the modulus from this element if this element is not in the
            /// field. Only used interally.
            #[inline(always)]
            fn reduce(&mut self) {
                if !self.is_valid() {
                    self.0.sub_noborrow(&MODULUS);
                }
            }

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

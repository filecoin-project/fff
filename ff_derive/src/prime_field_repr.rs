// Implement PrimeFieldRepr for the wrapped ident `repr` with `limbs` limbs.
pub fn prime_field_repr_impl(repr: &syn::Ident, limbs: usize) -> proc_macro2::TokenStream {
    let add_nocarry_impl = make_add_nocarry_impl(limbs);
    let is_zero_impl = make_is_zero_impl(limbs);
    let is_eq_impl = make_is_eq_impl(limbs);
    let is_one_impl = make_is_one_impl(limbs);
    let div2_impl = make_div2_impl(limbs);

    fn make_is_zero_impl(limbs: usize) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();
        let mut inner = proc_macro2::TokenStream::new();

        for i in (0..limbs).rev() {
            inner.extend(quote! {
                (self.0)[#i]
            });
            if i > 0 {
                inner.extend(quote! { | });
            }
        }

        gen.extend(quote! {
            (#inner) == 0
        });

        gen
    }

    fn make_is_one_impl(limbs: usize) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();
        let mut inner = proc_macro2::TokenStream::new();

        for i in (1..limbs).rev() {
            inner.extend(quote! {
                (self.0)[#i]
            });
            if i > 1 {
                inner.extend(quote! { | });
            }
        }

        gen.extend(quote! {
            ((self.0)[0] == 1) && ((#inner) == 0)
        });

        gen
    }

    fn make_is_eq_impl(limbs: usize) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();

        for i in (0..limbs).rev() {
            gen.extend(quote! {
                ((self.0)[#i] == (other.0)[#i])
            });
            if i > 0 {
                gen.extend(quote! { && });
            }
        }

        gen
    }

    fn make_add_nocarry_impl(limbs: usize) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();
        let len = limbs - 1;

        gen.extend(quote! {
            let mut carry = 0;
        });

        for i in 0..len {
            gen.extend(quote! {
                (self.0)[#i] = ::fff::adc(self.0[#i], other.0[#i], &mut carry);
            });
        }

        gen.extend(quote! {
            (self.0)[#len] = ::fff::adc_no_carry(self.0[#len], other.0[#len], &mut carry);
        });

        gen
    }

    fn make_div2_impl(limbs: usize) -> proc_macro2::TokenStream {
        let mut gen = proc_macro2::TokenStream::new();

        gen.extend(quote! {
            let mut t = 0;
        });

        for i in (0..limbs).rev() {
            gen.extend(quote! {
                let t2 = (self.0)[#i] << 63;
                (self.0)[#i] = ((self.0)[#i] >> 1) | t;
                t = t2;
            });
        }

        gen
    }

    quote! {
        #[derive(Copy, Clone, Default)]
        pub struct #repr(pub [u64; #limbs]);

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

        impl ::std::cmp::PartialEq for #repr {
            #[inline]
            fn eq(&self, other: &#repr) -> bool {
                #is_eq_impl
            }
        }

        impl ::std::cmp::Eq for #repr { }

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

        impl #repr {
            #[inline(always)]
            fn is_one(&self) -> bool {
                #is_one_impl
            }
        }

        impl ::fff::PrimeFieldRepr for #repr {
            #[inline(always)]
            fn is_odd(&self) -> bool {
                self.0[0] & 1 == 1
            }

            #[inline(always)]
            fn is_even(&self) -> bool {
                self.0[0] & 1 == 0
            }

            #[inline(always)]
            fn is_zero(&self) -> bool {
                #is_zero_impl
            }

            #[inline(always)]
            fn shr(&mut self, mut n: u32) {
                if n as usize >= 64 * #limbs {
                    *self = Self::from(0);
                    return;
                }

                while n >= 64 {
                    let mut t = 0;
                    for i in self.0.iter_mut().rev() {
                        ::std::mem::swap(&mut t, i);
                    }
                    n -= 64;
                }

                if n > 0 {
                    let mut t = 0;
                    for i in self.0.iter_mut().rev() {
                        let t2 = *i << (64 - n);
                        *i >>= n;
                        *i |= t;
                        t = t2;
                    }
                }
            }

            #[inline(always)]
            fn div2(&mut self) {
                #div2_impl
            }

            #[inline(always)]
            fn mul2(&mut self) {
                let mut last = 0;
                for i in &mut self.0 {
                    let tmp = *i >> 63;
                    *i <<= 1;
                    *i |= last;
                    last = tmp;
                }
            }

            #[inline(always)]
            fn shl(&mut self, mut n: u32) {
                if n as usize >= 64 * #limbs {
                    *self = Self::from(0);
                    return;
                }

                while n >= 64 {
                    let mut t = 0;
                    for i in &mut self.0 {
                        ::std::mem::swap(&mut t, i);
                    }
                    n -= 64;
                }

                if n > 0 {
                    let mut t = 0;
                    for i in &mut self.0 {
                        let t2 = *i >> (64 - n);
                        *i <<= n;
                        *i |= t;
                        t = t2;
                    }
                }
            }

            #[inline(always)]
            fn num_bits(&self) -> u32 {
                let mut ret = (#limbs as u32) * 64;
                for i in self.0.iter().rev() {
                    let leading = i.leading_zeros();
                    ret -= leading;
                    if leading != 64 {
                        break;
                    }
                }

                ret
            }

            #[inline(always)]
            fn add_nocarry(&mut self, other: &#repr) {
                #add_nocarry_impl
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

use crate::{AsBytes, NoPrefixesBytes, OrderedBytes};
use alloc::{boxed::Box, vec::Vec};
use core::{
    fmt::Debug,
    hash::Hash,
    marker::PhantomData,
    net::{Ipv4Addr, Ipv6Addr},
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
    },
};

/// Trait representing a reversible conversion from a type to some sort of byte
/// string.
///
/// # `Hash` and `Eq`
///
/// The transformation from the original type to the byte string should preserve
/// equality for the [`PartialEq`] and [`Eq`] implementations, along with
/// hashing for the [`Hash`] implementation.
///
/// The following property should hold true:
///
/// ```plaintext
/// value_a == value_b -> Mapping::to_bytes(value_a) == Mapping::to_bytes(value_b)
/// ```
///
/// And this implies that the `hash` implementations should also match, in line
/// with the [`Hash`] and [`Eq`] documentation.
///
/// [`Hash` and `Eq` documentation](https://doc.rust-lang.org/1.68.2/std/hash/trait.Hash.html#hash-and-eq)
///
/// # Ordering
///
/// The mapping may optionally preserve ordering of the original type, as
/// implemented by [`Ord`] on the original type. In that case, [`PartialOrd`]
/// and [`Ord`] should be implemented for [`Mapped<B, D>`] where `B` is the type
/// implementing `BytesMapping<D>` and `D` is the type being converted. Then the
/// trait [`OrderedBytes`] should be implemented for [`Mapped<B, D>`] as well.
pub trait BytesMapping<D> {
    /// The bytestring type that the `D` is converted to.
    type Bytes: AsBytes;

    /// Convert the domain type into the bytestring type
    fn to_bytes(value: D) -> Self::Bytes;

    /// Convert the bytestring type back into the domain type
    fn from_bytes(bytes: Self::Bytes) -> D;
}

/// This type implements a [`BytesMapping`] that preserves the original type
/// without converting it to bytes.
///
/// It only works for types which directly implement [`AsBytes`]. This type is
/// mostly meant for use with the [`ConcatTuple`] mapping, as one of the type
/// parameters.
#[derive(Debug)]
pub struct Identity;

impl<D> BytesMapping<D> for Identity
where
    D: AsBytes,
{
    type Bytes = D;

    fn to_bytes(value: D) -> Self::Bytes {
        value
    }

    fn from_bytes(bytes: Self::Bytes) -> D {
        bytes
    }
}

/// A container for the bytestring that is produced from [`BytesMapping`]
/// conversion
#[repr(transparent)]
pub struct Mapped<B, D>
where
    B: BytesMapping<D>,
{
    _mapping: PhantomData<(B, D)>,
    repr: B::Bytes,
}

impl<B, D> Mapped<B, D>
where
    B: BytesMapping<D>,
{
    /// Transform a value into its bytes representation
    pub fn new(value: D) -> Self {
        Mapped {
            _mapping: PhantomData,
            repr: B::to_bytes(value),
        }
    }

    /// Created a new instance of [`Mapped`] starting from the byte
    /// representation
    fn with_repr(repr: B::Bytes) -> Self {
        Mapped {
            _mapping: PhantomData,
            repr,
        }
    }

    /// Take the byte representation and convert it back to the original
    /// value
    pub fn get(self) -> D {
        B::from_bytes(self.repr)
    }
}

impl<B, D> Debug for Mapped<B, D>
where
    B: BytesMapping<D>,
    D: Debug,
    B::Bytes: Clone,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Mapped")
            .field("repr", &self.repr.as_bytes())
            .field("original_value", &B::from_bytes(self.repr.clone()))
            .finish()
    }
}

impl<B, D> Clone for Mapped<B, D>
where
    B: BytesMapping<D>,
    B::Bytes: Clone,
{
    fn clone(&self) -> Self {
        Self {
            _mapping: PhantomData,
            repr: self.repr.clone(),
        }
    }
}

impl<B, D> Copy for Mapped<B, D>
where
    B: BytesMapping<D>,
    B::Bytes: Copy,
{
}

impl<B, D> PartialEq for Mapped<B, D>
where
    B: BytesMapping<D>,
{
    fn eq(&self, other: &Self) -> bool {
        self.repr.as_bytes() == other.repr.as_bytes()
    }
}

impl<B, D> Eq for Mapped<B, D> where B: BytesMapping<D> {}

impl<B, D> Hash for Mapped<B, D>
where
    B: BytesMapping<D>,
{
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.repr.as_bytes().hash(state);
    }
}

impl<B, D> AsBytes for Mapped<B, D>
where
    B: BytesMapping<D>,
{
    fn as_bytes(&self) -> &[u8] {
        self.repr.as_bytes()
    }
}

macro_rules! impl_ord_for_mapped {
    ($(const $const_ident:ident: $const_ty:ty => )? $mapping:ty, $data:ty) => {
        impl<$(const $const_ident: $const_ty)?> PartialOrd for Mapped<$mapping, $data> {
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl<$(const $const_ident: $const_ty)?> Ord for Mapped<$mapping, $data> {
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                self.repr.cmp(&other.repr)
            }
        }
    };
}

/// This struct represents a conversion of **unsigned integers** to the [big
/// endian format], so that the natural ordering of the numbers matches the
/// lexicographic ordering of the bytes.
///
/// [big endian format]: https://en.wikipedia.org/wiki/Endianness
pub struct ToUBE;

/// This struct represents a conversion of **signed integers** to a format that
/// allows the natural ordering of the numbers to match the lexicographic
/// ordering of the bytes.
///
/// This is done by converting the numbers to their unsigned equivalent using `x
/// XOR (2 ^ (b - 1))` where `b` is the number of bits, then converting the
/// unsigned value to a big endian format if needed.
pub struct ToIBE;

macro_rules! impl_ordered_bytes_ints {
    ($([$unsigned:ty, $signed:ty]),*) => {
        $(
            impl BytesMapping<$unsigned> for ToUBE {
                type Bytes = [u8; core::mem::size_of::<$unsigned>()];

                fn to_bytes(value: $unsigned) -> Self::Bytes {
                    value.to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> $unsigned {
                    <$unsigned>::from_be_bytes(bytes)
                }
            }

            // SAFETY: Unsigned integers will have no byte prefixes when converted to their big endian
            // representation, also the byte number of bytes used is constant for all values of the type
            unsafe impl NoPrefixesBytes for Mapped<ToUBE, $unsigned> {}

            impl_ord_for_mapped!(ToUBE, $unsigned);

            // SAFETY: The big endian representation of unsigned integers is lexicographically ordered
            // and matches the natural ordering of the integer type
            unsafe impl OrderedBytes for Mapped<ToUBE, $unsigned> {}

            impl BytesMapping<$signed> for ToIBE {
                type Bytes = [u8; core::mem::size_of::<$unsigned>()];

                fn to_bytes(value: $signed) -> Self::Bytes {
                    (bytemuck::cast::<_, $unsigned>(value) ^ (1 << (<$unsigned>::BITS - 1))).to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> $signed {
                    bytemuck::cast::<_, $signed>(<$unsigned>::from_be_bytes(bytes) ^ (1 << (<$unsigned>::BITS - 1)))
                }
            }

            // SAFETY: ToIBE converts the transforms the signed integers, then converts them to the
            // big endian byte representation, which is the same number of bytes for all values of the
            // type, thus there can be no prefixes
            unsafe impl NoPrefixesBytes for Mapped<ToIBE, $signed> {}

            impl_ord_for_mapped!(ToIBE, $signed);

            // SAFETY: The transformation that ToIBE does to the signed values converts them to unsigned
            // equivalents in a way that preserves the overall ordering of the type. The conversion from
            // uint to big endian bytes also preserves order, so that the lexicographic ordering of the bytes
            // matches the original ordering of the signed values.
            unsafe impl OrderedBytes for Mapped<ToIBE, $signed> {}
        )*
    };
}

impl_ordered_bytes_ints!(
    [u8, i8],
    [u16, i16],
    [u32, i32],
    [u64, i64],
    [u128, i128],
    [usize, isize]
);

/// # Safety
///
/// 1. This macro must only be used with types `$elem` where `size_of::<$elem>
///    == <$elem as AsBytes>::as_bytes(&instance).len()`. The types must also be
///    fixed size, so all instance of `$elem` must have the same size.
/// 2. This macro must only be used with types that implement
/// ```ignore
/// impl BytesMapping<$elem> for $mapping {
///     // ...
/// }
/// ```
///
/// 3. `$elem` must also implement
///
/// ```ignore
/// unsafe impl OrderedBytes for Mapped<$mapping, $elem> {}
/// ```
macro_rules! impl_ordered_bytes_ints_arrays {
    ($([$mapping:ty => $($elem:ty),+]),*) => {
        $(
            $(
                impl_ordered_bytes_ints_arrays!($mapping; $elem; array);
                impl_ordered_bytes_ints_arrays!($mapping; $elem; vec_like; Vec<$elem>);
                impl_ordered_bytes_ints_arrays!($mapping; $elem; vec_like; Box<[$elem]>);
            )+
        )*
    };
    ($mapping:ty;$elem:ty;array) => {
        impl<const N: usize> BytesMapping<[$elem; N]> for $mapping {
            // TODO: When we can multiply in const generics, we could make this
            // type Bytes = [u8; const { N * core::mem::size_of::<$elem>() }];
            type Bytes = Box<[u8]>;

            fn to_bytes(values: [$elem; N]) -> Self::Bytes {
                let mut bytes = Vec::with_capacity(N * core::mem::size_of::<$elem>());

                for value in values {
                    bytes.extend(<Self as BytesMapping<$elem>>::to_bytes(value));
                }

                bytes.into_boxed_slice()
            }

            fn from_bytes(bytes: Self::Bytes) -> [$elem; N] {
                core::array::from_fn(|index| {
                    let value_bytes_slice = &bytes[(index * core::mem::size_of::<$elem>())
                        ..((index + 1) * core::mem::size_of::<$elem>())];
                    let value_bytes_array: [u8; core::mem::size_of::<$elem>()] = value_bytes_slice.try_into().unwrap();

                    <Self as BytesMapping<$elem>>::from_bytes(
                        value_bytes_array
                    )
                })
            }
        }

        // SAFETY: Covered by safety condition on macro, the array is a concatenation of
        // fixed size inputs
        unsafe impl<const N: usize> NoPrefixesBytes for Mapped<$mapping, [$elem; N]> {}

        // SAFETY: Covered by safety conditions on macro, the array is ordered because the
        // concatenation of ordered bytes is ordered
        unsafe impl<const N: usize> OrderedBytes for Mapped<$mapping, [$elem; N]> {}

        impl_ord_for_mapped!(const N: usize => $mapping, [$elem; N]);
    };
    ($mapping:ty;$elem:ty;vec_like;$domain:ty) => {
        impl BytesMapping<$domain> for $mapping {
            type Bytes = Box<[u8]>;

            fn to_bytes(values: $domain) -> Self::Bytes {
                let mut bytes = Vec::with_capacity(values.len() * core::mem::size_of::<$elem>());

                for value in Vec::from(values) {
                    bytes.extend(<Self as BytesMapping<$elem>>::to_bytes(value));
                }

                bytes.into_boxed_slice()
            }

            fn from_bytes(bytes: Self::Bytes) -> $domain {
                let num_elements = bytes.len() / core::mem::size_of::<$elem>();
                (0..num_elements).map(|index| {
                    let value_bytes_slice = &bytes[(index * core::mem::size_of::<$elem>())
                        ..((index + 1) * core::mem::size_of::<$elem>())];
                    let value_bytes_array: [u8; core::mem::size_of::<$elem>()] = value_bytes_slice.try_into().unwrap();

                    <Self as BytesMapping<$elem>>::from_bytes(
                        value_bytes_array
                    )
                }).collect()
            }
        }

        // SAFETY: Covered by safety conditions on macro, the array is ordered because the
        // concatenation of ordered bytes is ordered
        unsafe impl OrderedBytes for Mapped<$mapping, $domain> {}

        impl_ord_for_mapped!($mapping, $domain);
    };
}

// SAFETY: All integer type fulfill requirements
impl_ordered_bytes_ints_arrays!(
    [ToUBE => u8, u16, u32, u64, u128, usize],
    [ToIBE => i8, i16, i32, i64, i128, isize]
);

macro_rules! impl_ordered_bytes_nonzero_ints {
    ($([$nonzero_unsigned:ty; $unsigned:ty, $nonzero_signed:ty; $signed:ty]),*) => {
        $(
            impl BytesMapping<$nonzero_unsigned> for ToUBE {
                type Bytes = [u8; core::mem::size_of::<$unsigned>()];

                fn to_bytes(value: $nonzero_unsigned) -> Self::Bytes {
                    value.get().to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> $nonzero_unsigned {
                    <$nonzero_unsigned>::new(<$unsigned>::from_be_bytes(bytes))
                        .expect("input bytes should not produce a zero value")
                }
            }

            // SAFETY: The safety of the NonZero* version of the unsigned integer is the same as it
            // is for non-NonZero* variant
            unsafe impl NoPrefixesBytes for Mapped<ToUBE, $nonzero_unsigned> {}

            impl_ord_for_mapped!(ToUBE, $nonzero_unsigned);

            // SAFETY: The safety of the NonZero* version of the unsigned integer is the same as it
            // is for non-NonZero* variant
            unsafe impl OrderedBytes for Mapped<ToUBE, $nonzero_unsigned> {}

            impl BytesMapping<$nonzero_signed> for ToIBE {
                type Bytes = [u8; core::mem::size_of::<$unsigned>()];

                fn to_bytes(value: $nonzero_signed) -> Self::Bytes {
                    (bytemuck::cast::<_, $unsigned>(value.get()) ^ (1 << (<$unsigned>::BITS - 1))).to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> $nonzero_signed {
                    let signed = bytemuck::cast::<_, $signed>(
                        <$unsigned>::from_be_bytes(bytes) ^ (1 << (<$unsigned>::BITS - 1)));

                    <$nonzero_signed>::new(signed).expect("input bytes should not produce a zero value")
                }
            }

            // SAFETY: This impl is safe for the same reasons as the non-NonZero* impl is
            unsafe impl NoPrefixesBytes for Mapped<ToIBE, $nonzero_signed> {}

            impl_ord_for_mapped!(ToIBE, $nonzero_signed);

            // SAFETY: This impl is safe for the same reasons as the non-NonZero* impl is
            unsafe impl OrderedBytes for Mapped<ToIBE, $nonzero_signed> {}
        )*
    };
}

impl_ordered_bytes_nonzero_ints!(
    [NonZeroU8; u8, NonZeroI8; i8],
    [NonZeroU16; u16, NonZeroI16; i16],
    [NonZeroU32; u32, NonZeroI32; i32],
    [NonZeroU64; u64, NonZeroI64; i64],
    [NonZeroU128; u128, NonZeroI128; i128],
    [NonZeroUsize; usize, NonZeroIsize; isize]
);

// SAFETY: All non-zero integer type fulfill requirements
impl_ordered_bytes_ints_arrays!(
    [ToUBE => NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU128, NonZeroUsize],
    [ToIBE => NonZeroI8, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI128, NonZeroIsize]
);

/// This struct represents a conversion of **IP addresses** (V4 and V6) into
/// their component bytes.
///
/// The ordering of IP addresses is already the lexicographic ordering of the
/// component bytes, so it will be preserved.
pub struct ToOctets;

impl BytesMapping<Ipv4Addr> for ToOctets {
    type Bytes = [u8; 4];

    fn to_bytes(value: Ipv4Addr) -> Self::Bytes {
        value.octets()
    }

    fn from_bytes(bytes: Self::Bytes) -> Ipv4Addr {
        bytes.into()
    }
}

// SAFETY: The ToOctets mapping will always produce byte arrays of length 4 for
// all Ipv4Addr values. Thus there can be no prefixes
unsafe impl NoPrefixesBytes for Mapped<ToOctets, Ipv4Addr> {}

impl_ord_for_mapped!(ToOctets, Ipv4Addr);

// SAFETY: The ordering of the Ipv4Addr is already defined using the octet bytes
// see https://doc.rust-lang.org/1.69.0/src/core/net/ip_addr.rs.html#1066
unsafe impl OrderedBytes for Mapped<ToOctets, Ipv4Addr> {}

impl BytesMapping<Ipv6Addr> for ToOctets {
    type Bytes = [u8; 16];

    fn to_bytes(value: Ipv6Addr) -> Self::Bytes {
        value.octets()
    }

    fn from_bytes(bytes: Self::Bytes) -> Ipv6Addr {
        bytes.into()
    }
}

// SAFETY: The ToOctets mapping will always produce byte arrays of length 16 for
// all Ipv6Addr values. THus there can be no prefixes
unsafe impl NoPrefixesBytes for Mapped<ToOctets, Ipv6Addr> {}

impl_ord_for_mapped!(ToOctets, Ipv6Addr);

// SAFETY: The ordering of the Ipv6Addr is already defined using the octet bytes
// see https://doc.rust-lang.org/1.69.0/src/core/net/ip_addr.rs.html#1908
unsafe impl OrderedBytes for Mapped<ToOctets, Ipv6Addr> {}

/// This type implements a [`BytesMapping`] for tuples of types, concatenating
/// their byte representations together.
///
/// The `M` type parameter also takes a tuple, the same size as the input, which
/// contains types also implementing `BytesMapping`. Each type in this tuple is
/// used to transform the corresponding value in the input tuple.
///
/// # Examples
///
/// Here is a basic example using the [`Identity`] transform for both tuple
/// elements:
///
/// ```rust
/// use blart::{ConcatTuple, AsBytes, Mapped, Identity};
///
/// let c1 = b"aaa";
/// let c2 = b"bb";
///
/// let t = Mapped::<ConcatTuple<(Identity, Identity)>, _>::new((*c1, *c2));
///
/// assert_eq!(t.as_bytes(), b"aaabb");
/// ```
///
/// Here is a more complex example:
///
/// ```rust
/// use std::net::Ipv4Addr;
/// use std::num::NonZeroI16;
/// use blart::{ConcatTuple, AsBytes, Mapped, ToOctets, ToIBE};
///
/// let c1 = NonZeroI16::new(256).unwrap();
/// let c2 = Ipv4Addr::LOCALHOST;
///
/// assert_eq!(Mapped::<ToIBE, _>::new(c1).as_bytes(), &[129, 0][..]);
/// assert_eq!(Mapped::<ToOctets, _>::new(c2).as_bytes(), &[127, 0, 0, 1][..]);
///
/// let t = Mapped::<ConcatTuple<(ToIBE, ToOctets)>, _>::new((c1, c2));
///
/// assert_eq!(t.as_bytes(), &[129, 0, 127, 0, 0, 1][..]);
/// ```
#[derive(Debug)]
pub struct ConcatTuple<M>(PhantomData<M>);

macro_rules! sum {
    ($h:expr, ) => ($h);
    ($h:expr, $($t:expr,)*) =>
        ($h + sum!($($t,)*));
}

macro_rules! as_bytes_for_tuples {
    ($(($($ty:ident)+))+) => {
        $(
            paste::paste! {
                impl<
                    $(
                        // The input type
                        $ty,
                        // The mapping type which transforms the input type
                        [< M $ty >],
                    )+
                    $(
                        // The const generic type containing the fixed length of the mapped bytes for the given input
                        // type
                        const [< LEN_ $ty >]: usize,
                    )+
                > BytesMapping<($($ty,)+)> for ConcatTuple<($([< M $ty >], )+)>
                where
                $(
                    // Each mapping type must implement a mapping from the input type to a byte array of fixed length
                    [< M $ty >]: BytesMapping<$ty, Bytes = [u8; [< LEN_ $ty >]]>,
                )+
                {
                    // TODO: Convert this to use an array of `[u8; sum!($([< LEN_ $ty >],)+)]` once const generics
                    // supports that
                    type Bytes = Box<[u8]>;

                    #[expect(non_snake_case)]
                    fn to_bytes(value: ($($ty,)+)) -> Self::Bytes {
                        let mut bytes = Vec::with_capacity(sum!(
                            $([< LEN_ $ty >],)+
                        ));

                        let ($([<elem_ $ty>],)+) = value;
                        $(
                            let [<mapped_ $ty>] = Mapped::<[< M $ty >], $ty>::new([<elem_ $ty>]);
                            bytes.extend([<mapped_ $ty>].repr);
                        )+

                        bytes.into_boxed_slice()
                    }

                    fn from_bytes(bytes: Self::Bytes) -> ($($ty,)+) {
                        let remaining = &*bytes;

                        $(
                            #[expect(non_snake_case)]
                            let ([<bytes_ $ty>], remaining) = remaining.split_first_chunk::<[< LEN_ $ty >]>().unwrap();
                        )+

                        assert_eq!(remaining.len(), 0, "should have used all the bytes");

                        (
                            $(
                                Mapped::<[< M $ty >], $ty>::with_repr([<bytes_ $ty>].clone()).get(),
                            )+
                        )
                    }
                }

                // SAFETY: This is safe because all the component bytes are fixed length,
                // meaning all the full bytes mapping have the same length
                unsafe impl<
                    $(
                        // The input type
                        $ty,
                        // The mapping type which transforms the input type
                        [< M $ty >],
                    )+
                > NoPrefixesBytes for Mapped<ConcatTuple<($([< M $ty >], )+)>, ($($ty,)+)>
                where
                    // Concat mapping type containing each element mapping type must implement a mapping for the tuple
                    // containing all input types
                    ConcatTuple<($([< M $ty >], )+)>: BytesMapping<($($ty,)+)>
                {}

                impl<
                    $(
                        // The input type
                        $ty,
                        // The mapping type which transforms the input type
                        [< M $ty >],
                    )+
                > PartialOrd for Mapped<ConcatTuple<($([< M $ty >], )+)>, ($($ty,)+)>
                where
                    // For each tuple input element type:
                    $(
                        // The input type must be ordered
                        $ty: Ord,
                        // The mapping type must implementing a mapping for the input type
                        [< M $ty >]: BytesMapping<$ty>,
                        // The mapped struct (using the mapping type and the input type) must also be ordered by bytes
                        Mapped<[< M $ty >], $ty>: OrderedBytes,
                    )+
                    // Concat mapping type containing each element mapping type must implement a mapping for the tuple
                    // containing all input types
                    ConcatTuple<($([< M $ty >], )+)>: BytesMapping<($($ty,)+)>,
                    // The mapped bytes type of the Concat mapping type must have an order
                    <ConcatTuple<($([< M $ty >], )+)> as BytesMapping<($($ty,)+)>>::Bytes: Ord,
                {
                    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                        Some(self.cmp(other))
                    }
                }

                impl<
                    $(
                        // The input type
                        $ty,
                        // The mapping type which transforms the input type
                        [< M $ty >],
                    )+
                > Ord for Mapped<ConcatTuple<($([< M $ty >], )+)>, ($($ty,)+)>
                where
                    // For each tuple input element type:
                    $(
                        // The input type must be ordered
                        $ty: Ord,
                        // The mapping type must implementing a mapping for the input type
                        [< M $ty >]: BytesMapping<$ty>,
                        // The mapped struct (using the mapping type and the input type) must also be ordered by bytes
                        Mapped<[< M $ty >], $ty>: OrderedBytes,
                    )+
                    // Concat mapping type containing each element mapping type must implement a mapping for the tuple
                    // containing all input types
                    ConcatTuple<($([< M $ty >], )+)>: BytesMapping<($($ty,)+)>,
                    // The mapped bytes type of the Concat mapping type must have an order
                    <ConcatTuple<($([< M $ty >], )+)> as BytesMapping<($($ty,)+)>>::Bytes: Ord,
                {
                    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                        self.repr.cmp(&other.repr)
                    }
                }

                // SAFETY: When all components bytes are the same length, comparing the entire
                // bytestrings is the same as comparing the elements in order
                unsafe impl<
                    $(
                        // The input type
                        $ty,
                        // The mapping type which transforms the input type
                        [< M $ty >],
                    )+
                > OrderedBytes for Mapped<ConcatTuple<($([< M $ty >], )+)>, ($($ty,)+)>
                where
                    // For each tuple input element type:
                    $(
                        // The input type must be ordered
                        $ty: Ord,
                        // The mapping type must implementing a mapping for the input type
                        [< M $ty >]: BytesMapping<$ty>,
                        // The mapped struct (using the mapping type and the input type) must also be ordered by bytes
                        Mapped<[< M $ty >], $ty>: OrderedBytes,
                    )+
                    // Concat mapping type containing each element mapping type must implement a mapping for the tuple
                    // containing all input types
                    ConcatTuple<($([< M $ty >], )+)>: BytesMapping<($($ty,)+)>,
                    // The mapped bytes type of the Concat mapping type must have an order
                    <ConcatTuple<($([< M $ty >], )+)> as BytesMapping<($($ty,)+)>>::Bytes: Ord,
                {}
            }
        )*
    };
}

as_bytes_for_tuples!(
    (T0 T1)
    (T0 T1 T2)
    (T0 T1 T2 T3)
    (T0 T1 T2 T3 T4)
    (T0 T1 T2 T3 T4 T5)
    (T0 T1 T2 T3 T4 T5 T6)
    (T0 T1 T2 T3 T4 T5 T6 T7)
    (T0 T1 T2 T3 T4 T5 T6 T7 T8)
    (T0 T1 T2 T3 T4 T5 T6 T7 T8 T9)
    (T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10)
    (T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11)
);

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use core::{cmp::Ordering, fmt::Debug};

    fn check_is_ordered_bytes<T: OrderedBytes>() {}

    pub(in crate::bytes) fn assert_ordered_bytes_mapping_contract<B, D>(a: D, b: D)
    where
        B: BytesMapping<D>,
        D: Ord + Debug + Clone,
    {
        let a_mapped = Mapped::<B, D>::new(a.clone());
        let b_mapped = Mapped::<B, D>::new(b.clone());
        let a_bytes = a_mapped.as_bytes();
        let b_bytes = b_mapped.as_bytes();
        assert_eq!(
            a.cmp(&b),
            a_bytes.cmp(b_bytes),
            "{a:?} and {b:?} compare differently than their byte representation \
             (a_bytes={a_bytes:?},b_bytes={b_bytes:?})"
        );

        assert_eq!(B::from_bytes(B::to_bytes(a.clone())), a);
        assert_eq!(B::from_bytes(B::to_bytes(b.clone())), b);
    }

    macro_rules! impl_ordered_bytes_ints_tests {
        ($([$unsigned:ty, $signed:ty; $test_fn:ident]),*) => {
            $(
                #[test]
                fn $test_fn() {
                    let mid = (<$unsigned>::MAX + <$unsigned>::MIN) / 2;
                    assert_ordered_bytes_mapping_contract::<ToUBE, $unsigned>(
                        <$unsigned>::MAX, <$unsigned>::MIN);
                    assert_ordered_bytes_mapping_contract::<ToUBE, $unsigned>(
                        mid, <$unsigned>::MAX);
                    assert_ordered_bytes_mapping_contract::<ToUBE, $unsigned>(
                        mid, <$unsigned>::MIN);

                    check_is_ordered_bytes::<Mapped<ToUBE, $unsigned>>();

                    assert_ordered_bytes_mapping_contract::<ToIBE, $signed>(
                        0, <$signed>::MAX);
                    assert_ordered_bytes_mapping_contract::<ToIBE, $signed>(
                        0, <$signed>::MIN);
                    assert_ordered_bytes_mapping_contract::<ToIBE, $signed>(
                        <$signed>::MAX, <$signed>::MIN);

                    check_is_ordered_bytes::<Mapped<ToIBE, $signed>>();
                }
            )*
        }
    }

    impl_ordered_bytes_ints_tests!(
        [u8, i8; test_ordered_ui8],
        [u16, i16; test_ordered_ui16],
        [u32, i32; test_ordered_ui32],
        [u64, i64; test_ordered_ui64],
        [u128, i128; test_ordered_ui128],
        [usize, isize; test_ordered_uisize]
    );

    macro_rules! impl_ordered_bytes_int_arrays_tests {
        ($([$unsigned:ty, $signed:ty; $test_fn:ident]),*) => {
            $(
                #[test]
                fn $test_fn() {
                    let mid = (<$unsigned>::MAX + <$unsigned>::MIN) / 2;
                    let array_min = [<$unsigned>::MIN, <$unsigned>::MIN, <$unsigned>::MIN];
                    let array_mid = [<$unsigned>::MIN, mid, <$unsigned>::MIN];
                    let array_max = [<$unsigned>::MIN, mid, <$unsigned>::MAX];

                    assert_ordered_bytes_mapping_contract::<ToUBE, [$unsigned; 3]>(
                        array_min, array_max);
                    assert_ordered_bytes_mapping_contract::<ToUBE, [$unsigned; 3]>(
                        array_mid, array_max);
                    assert_ordered_bytes_mapping_contract::<ToUBE, [$unsigned; 3]>(
                        array_mid, array_min);

                    check_is_ordered_bytes::<Mapped<ToUBE, [$unsigned; 3]>>();

                    assert_ordered_bytes_mapping_contract::<ToUBE, Vec<$unsigned>>(
                        array_min.into(), array_max.into());
                    assert_ordered_bytes_mapping_contract::<ToUBE, Vec<$unsigned>>(
                        array_mid.into(), array_max.into());
                    assert_ordered_bytes_mapping_contract::<ToUBE, Vec<$unsigned>>(
                        array_mid.into(), array_min.into());

                    check_is_ordered_bytes::<Mapped<ToUBE, Vec<$unsigned>>>();

                    let array_min = [<$signed>::MIN, <$signed>::MIN, <$signed>::MIN];
                    let array_mid = [<$signed>::MIN, 0, <$signed>::MIN];
                    let array_max = [<$signed>::MIN, 0, <$signed>::MAX];

                    assert_ordered_bytes_mapping_contract::<ToIBE, [$signed; 3]>(
                        array_min, array_max);
                    assert_ordered_bytes_mapping_contract::<ToIBE, [$signed; 3]>(
                        array_mid, array_max);
                    assert_ordered_bytes_mapping_contract::<ToIBE, [$signed; 3]>(
                        array_mid, array_min);

                    check_is_ordered_bytes::<Mapped<ToIBE, [$signed; 3]>>();

                    assert_ordered_bytes_mapping_contract::<ToIBE, Vec<$signed>>(
                        array_min.into(), array_max.into());
                    assert_ordered_bytes_mapping_contract::<ToIBE, Vec<$signed>>(
                        array_mid.into(), array_max.into());
                    assert_ordered_bytes_mapping_contract::<ToIBE, Vec<$signed>>(
                        array_mid.into(), array_min.into());

                    check_is_ordered_bytes::<Mapped<ToIBE, Vec<$signed>>>();
                }
            )*
        }
    }

    impl_ordered_bytes_int_arrays_tests!(
        [u8, i8; test_ordered_ui8_array],
        [u16, i16; test_ordered_ui16_array],
        [u32, i32; test_ordered_ui32_array],
        [u64, i64; test_ordered_ui64_array],
        [u128, i128; test_ordered_ui128_array],
        [usize, isize; test_ordered_uisize_array]
    );

    macro_rules! impl_ordered_bytes_nonzero_ints_tests {
        ($([$nonzero_unsigned:ty, $unsigned:ty, $nonzero_signed:ty, $signed:ty; $test_fn:ident]),*) => {
            $(
                #[test]
                fn $test_fn() {
                    let mid = <$nonzero_unsigned>::new((<$unsigned>::MAX + <$unsigned>::MIN) / 2).unwrap();
                    assert_ordered_bytes_mapping_contract::<ToUBE, $nonzero_unsigned>(
                        <$nonzero_unsigned>::new(1).unwrap(),
                        <$nonzero_unsigned>::new(<$unsigned>::MAX).unwrap());
                    assert_ordered_bytes_mapping_contract::<ToUBE, $nonzero_unsigned>(
                        mid, <$nonzero_unsigned>::new(<$unsigned>::MAX).unwrap());
                    assert_ordered_bytes_mapping_contract::<ToUBE, $nonzero_unsigned>(
                        mid, <$nonzero_unsigned>::new(<$unsigned>::MIN + 1).unwrap());

                    check_is_ordered_bytes::<Mapped<ToUBE, $nonzero_unsigned>>();

                    let array_min = [<$nonzero_unsigned>::new(1).unwrap(), <$nonzero_unsigned>::new(1).unwrap(), <$nonzero_unsigned>::new(1).unwrap()];
                    let array_mid = [<$nonzero_unsigned>::new(1).unwrap(), mid, <$nonzero_unsigned>::new(1).unwrap()];
                    let array_max = [<$nonzero_unsigned>::new(1).unwrap(), mid, <$nonzero_unsigned>::new(<$unsigned>::MAX).unwrap()];

                    assert_ordered_bytes_mapping_contract::<ToUBE, [$nonzero_unsigned; 3]>(
                        array_min, array_max);
                    assert_ordered_bytes_mapping_contract::<ToUBE, [$nonzero_unsigned; 3]>(
                        array_mid, array_max);
                    assert_ordered_bytes_mapping_contract::<ToUBE, [$nonzero_unsigned; 3]>(
                        array_mid, array_min);

                    check_is_ordered_bytes::<Mapped<ToUBE, [$unsigned; 3]>>();

                    assert_ordered_bytes_mapping_contract::<ToIBE, $nonzero_signed>(
                        <$nonzero_signed>::new(<$signed>::MIN).unwrap(),
                        <$nonzero_signed>::new(<$signed>::MAX).unwrap());
                    assert_ordered_bytes_mapping_contract::<ToIBE, $nonzero_signed>(
                        <$nonzero_signed>::new(1).unwrap(),
                        <$nonzero_signed>::new(<$signed>::MAX).unwrap());
                    assert_ordered_bytes_mapping_contract::<ToIBE, $nonzero_signed>(
                        <$nonzero_signed>::new(<$signed>::MIN).unwrap(),
                        <$nonzero_signed>::new(1).unwrap());

                    check_is_ordered_bytes::<Mapped<ToIBE, $nonzero_signed>>();

                    let array_min = [<$nonzero_signed>::new(<$signed>::MIN).unwrap(), <$nonzero_signed>::new(<$signed>::MIN).unwrap(), <$nonzero_signed>::new(<$signed>::MIN).unwrap()];
                    let array_mid = [<$nonzero_signed>::new(<$signed>::MIN).unwrap(), <$nonzero_signed>::new(1).unwrap(), <$nonzero_signed>::new(<$signed>::MIN).unwrap()];
                    let array_max = [<$nonzero_signed>::new(<$signed>::MIN).unwrap(), <$nonzero_signed>::new(1).unwrap(), <$nonzero_signed>::new(<$signed>::MAX).unwrap()];

                    assert_ordered_bytes_mapping_contract::<ToIBE, [$nonzero_signed; 3]>(
                        array_min, array_max);
                    assert_ordered_bytes_mapping_contract::<ToIBE, [$nonzero_signed; 3]>(
                        array_mid, array_max);
                    assert_ordered_bytes_mapping_contract::<ToIBE, [$nonzero_signed; 3]>(
                        array_mid, array_min);

                    check_is_ordered_bytes::<Mapped<ToIBE, [$nonzero_signed; 3]>>();
                }
            )*
        }
    }

    impl_ordered_bytes_nonzero_ints_tests!(
        [NonZeroU8, u8, NonZeroI8, i8; test_ordered_nonzero_ui8],
        [NonZeroU16, u16, NonZeroI16, i16; test_ordered_nonzero_ui16],
        [NonZeroU32, u32, NonZeroI32, i32; test_ordered_nonzero_ui32],
        [NonZeroU64, u64, NonZeroI64, i64; test_ordered_nonzero_ui64],
        [NonZeroU128, u128, NonZeroI128, i128; test_ordered_nonzero_ui128],
        [NonZeroUsize, usize, NonZeroIsize, isize; test_ordered_nonzero_uisize]
    );

    #[test]
    fn test_ordered_ip_types() {
        assert_ordered_bytes_mapping_contract::<ToOctets, Ipv4Addr>(
            Ipv4Addr::LOCALHOST,
            Ipv4Addr::BROADCAST,
        );
        assert_ordered_bytes_mapping_contract::<ToOctets, Ipv4Addr>(
            Ipv4Addr::LOCALHOST,
            Ipv4Addr::UNSPECIFIED,
        );
        assert_ordered_bytes_mapping_contract::<ToOctets, Ipv4Addr>(
            Ipv4Addr::BROADCAST,
            Ipv4Addr::UNSPECIFIED,
        );

        check_is_ordered_bytes::<Mapped<ToOctets, Ipv4Addr>>();

        const IPV6_MAX: Ipv6Addr = Ipv6Addr::new(
            u16::MAX,
            u16::MAX,
            u16::MAX,
            u16::MAX,
            u16::MAX,
            u16::MAX,
            u16::MAX,
            u16::MAX,
        );

        assert_ordered_bytes_mapping_contract::<ToOctets, Ipv6Addr>(Ipv6Addr::LOCALHOST, IPV6_MAX);
        assert_ordered_bytes_mapping_contract::<ToOctets, Ipv6Addr>(
            Ipv6Addr::LOCALHOST,
            Ipv6Addr::UNSPECIFIED,
        );
        assert_ordered_bytes_mapping_contract::<ToOctets, Ipv6Addr>(
            IPV6_MAX,
            Ipv6Addr::UNSPECIFIED,
        );

        check_is_ordered_bytes::<Mapped<ToOctets, Ipv6Addr>>();
    }

    #[test]
    fn copy_tuple_as_bytes() {
        let tup1 = Mapped::<ConcatTuple<(Identity, Identity)>, ([u8; 5], [u8; 5])>::new((
            [0u8; 5], [10u8; 5],
        ));
        assert_eq!(tup1.as_bytes(), &[0, 0, 0, 0, 0, 10, 10, 10, 10, 10]);
    }

    #[test]
    fn concat_tuple_ord_matches_tuple_ord() {
        let t1 = (Ipv4Addr::UNSPECIFIED, -212, Ipv6Addr::UNSPECIFIED);
        let t2 = (Ipv4Addr::UNSPECIFIED, -212, Ipv6Addr::LOCALHOST);
        let t3 = (Ipv4Addr::UNSPECIFIED, 212, Ipv6Addr::LOCALHOST);
        let t4 = (Ipv4Addr::LOCALHOST, 212, Ipv6Addr::LOCALHOST);
        assert!(t1 < t2 && t2 < t3 && t3 < t4);

        assert_ordered_bytes_mapping_contract::<
            ConcatTuple<(ToOctets, ToIBE, ToOctets)>,
            (Ipv4Addr, i32, Ipv6Addr),
        >(t1, t2);
        assert_ordered_bytes_mapping_contract::<
            ConcatTuple<(ToOctets, ToIBE, ToOctets)>,
            (Ipv4Addr, i32, Ipv6Addr),
        >(t2, t3);
        assert_ordered_bytes_mapping_contract::<
            ConcatTuple<(ToOctets, ToIBE, ToOctets)>,
            (Ipv4Addr, i32, Ipv6Addr),
        >(t3, t4);
    }

    #[test]
    fn concat_array_of_signed_integers_ord() {
        let arr1 = [i32::MIN, i32::MAX, 0];
        let arr2 = [i32::MIN, i32::MAX, -1];

        assert_eq!(arr1.cmp(&arr2), Ordering::Greater);

        let mut bytes1 = [0; 12];
        bytes1[0..4].clone_from_slice(&Mapped::<ToIBE, _>::new(-121i32).repr);
        bytes1[4..8].clone_from_slice(&Mapped::<ToIBE, _>::new(100i32).repr);
        bytes1[8..12].clone_from_slice(&Mapped::<ToIBE, _>::new(0i32).repr);

        let mut bytes2 = [0; 12];
        bytes2[0..4].clone_from_slice(&Mapped::<ToIBE, _>::new(-121i32).repr);
        bytes2[4..8].clone_from_slice(&Mapped::<ToIBE, _>::new(100i32).repr);
        bytes2[8..12].clone_from_slice(&Mapped::<ToIBE, _>::new(-1i32).repr);

        assert_eq!(bytes1.cmp(&bytes2), Ordering::Greater);
    }
}

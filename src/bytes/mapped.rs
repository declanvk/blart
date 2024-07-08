use crate::{AsBytes, NoPrefixesBytes, OrderedBytes};
use std::{
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
/// string, while preserving the ordering of the original type.
///
/// The ordering of the original type is determined by the [`Ord`]
/// implementation, and the ordering of the byte string type is the
/// lexicographic ordering.
///
/// The mapping should also maintain equality for the [`PartialEq`] and [`Eq`]
/// implementations, along with hashing for the [`Hash`] implementation.
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
/// [`Hash`] and [`Eq`] [documentation](https://doc.rust-lang.org/1.68.2/std/hash/trait.Hash.html#hash-and-eq)
///
/// # Safety
///  - This trait is unsafe because implementing it implies that the
///    [`Mapped<Self>`] type will implement [`OrderedBytes`], so the safety
///    requirements must be upheld. Namely, that the ordering of values of the
///    [`BytesMapping::Domain`] type must be equal to the ordering of those same
///    values translated to the the [`BytesMapping::Bytes`] type.
pub unsafe trait BytesMapping {
    /// The unconverted type that has a specific ordering
    type Domain;
    /// The bytestring type that the [`Self::Domain`] is converted to.
    type Bytes: AsRef<[u8]>;

    /// Convert the domain type into the bytestring type
    fn to_bytes(value: Self::Domain) -> Self::Bytes;
    /// Convert the bytestring type back into the domain type
    fn from_bytes(bytes: Self::Bytes) -> Self::Domain;
}

/// A container for the bytestring that is produced from [`BytesMapping`]
/// conversion
pub struct Mapped<B>
where
    B: BytesMapping,
{
    _mapping: PhantomData<B>,
    repr: B::Bytes,
}

impl<B> Mapped<B>
where
    B: BytesMapping,
{
    /// Transform a value into its ordered representation
    pub fn new(value: B::Domain) -> Self {
        Mapped {
            _mapping: PhantomData,
            repr: B::to_bytes(value),
        }
    }

    /// Take the ordered representation and convert it back to the original
    /// value
    pub fn get(self) -> B::Domain {
        B::from_bytes(self.repr)
    }
}

impl<B> Debug for Mapped<B>
where
    B: BytesMapping,
    B::Domain: Debug,
    B::Bytes: Clone,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Mapped")
            .field("repr", &self.repr.as_ref())
            .field("original_value", &B::from_bytes(self.repr.clone()))
            .finish()
    }
}

impl<B> Clone for Mapped<B>
where
    B: BytesMapping,
    B::Bytes: Clone,
{
    fn clone(&self) -> Self {
        Self {
            _mapping: PhantomData,
            repr: self.repr.clone(),
        }
    }
}

impl<B> Copy for Mapped<B>
where
    B: BytesMapping,
    B::Bytes: Copy,
{
}

impl<B> PartialEq for Mapped<B>
where
    B: BytesMapping,
{
    fn eq(&self, other: &Self) -> bool {
        self.repr.as_ref() == other.repr.as_ref()
    }
}

impl<B> Eq for Mapped<B> where B: BytesMapping {}

impl<B> PartialOrd for Mapped<B>
where
    B: BytesMapping,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.repr.as_ref().cmp(other.repr.as_ref()))
    }
}

impl<B> Ord for Mapped<B>
where
    B: BytesMapping,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.repr.as_ref().cmp(other.repr.as_ref())
    }
}

impl<B> Hash for Mapped<B>
where
    B: BytesMapping,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.repr.as_ref().hash(state);
    }
}

impl<B> AsBytes for Mapped<B>
where
    B: BytesMapping,
{
    fn as_bytes(&self) -> &[u8] {
        self.repr.as_ref()
    }
}

/// This struct represents a conversion of **unsigned integers** to the [big
/// endian format], so that the natural ordering of the numbers matches the
/// lexicographic ordering of the bytes.
///
/// [big endian format]: https://en.wikipedia.org/wiki/Endianness
pub struct ToUBE<N>(PhantomData<N>);

/// This struct represents a conversion of **signed integers** to a format that
/// allows the natural ordering of the numbers to match the lexicographic
/// ordering of the bytes.
///
/// This is done by converting the numbers to their unsigned equivalent using `x
/// XOR (2 ^ (b - 1))` where `b` is the number of bits, then converting the
/// unsigned value to a big endian format if needed.
pub struct ToIBE<N>(PhantomData<N>);

macro_rules! impl_ordered_bytes_ints {
    ($([$unsigned:ty, $signed:ty]),*) => {
        $(
            // SAFETY: This is safe to implement because the big endian conversion is reversible and
            // will guarantee that the byte string ordering is the same as the natural number ordering.
            unsafe impl BytesMapping for ToUBE<$unsigned> {
                type Domain = $unsigned;
                type Bytes = [u8; std::mem::size_of::<$unsigned>()];

                fn to_bytes(value: Self::Domain) -> Self::Bytes {
                    value.to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
                    <$unsigned>::from_be_bytes(bytes)
                }
            }

            // SAFETY: Unsigned integers will have no byte prefixes when converted to their big endian
            // representation, also the byte number of bytes used is constant for all values of the type
            unsafe impl NoPrefixesBytes for Mapped<ToUBE<$unsigned>> {}

            // SAFETY: The big endian representation of unsigned integers is lexicographically ordered
            // and matches the natural ordering of the integer type
            unsafe impl OrderedBytes for Mapped<ToUBE<$unsigned>> {}

            // SAFETY: This is safe to implement because the big endian conversion and XOR operation is
            // reversible and  will guarantee that the byte string ordering is the same as the integer
            // number ordering.
            unsafe impl BytesMapping for ToIBE<$signed> {
                type Domain = $signed;
                type Bytes = [u8; std::mem::size_of::<$unsigned>()];

                fn to_bytes(value: Self::Domain) -> Self::Bytes {
                    (bytemuck::cast::<_, $unsigned>(value) ^ (1 << (<$unsigned>::BITS - 1))).to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
                    bytemuck::cast::<_, $signed>(<$unsigned>::from_be_bytes(bytes) ^ (1 << (<$unsigned>::BITS - 1)))
                }
            }

            // SAFETY: ToIBE converts the transforms the signed integers, then converts them to the
            // big endian byte representation, which is the same number of bytes for all values of the
            // type, thus there can be no prefixes
            unsafe impl NoPrefixesBytes for Mapped<ToIBE<$signed>> {}

            // SAFETY: The transformation that ToIBE does to the signed values converts them to unsigned
            // equivalents in a way that preserves the overall ordering of the type. The conversion from
            // uint to big endian bytes also preserves order, so that the lexicographic ordering of the bytes
            // matches the original ordering of the signed values.
            unsafe impl OrderedBytes for Mapped<ToIBE<$signed>> {}
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

macro_rules! impl_ordered_bytes_nonzero_ints {
    ($([$nonzero_unsigned:ty; $unsigned:ty, $nonzero_signed:ty; $signed:ty]),*) => {
        $(
            // SAFETY: This is safe to implement because the big endian conversion is reversible and
            // will guarantee that the byte string ordering is the same as the natural number ordering.
            unsafe impl BytesMapping for ToUBE<$nonzero_unsigned> {
                type Domain = $nonzero_unsigned;
                type Bytes = [u8; std::mem::size_of::<$unsigned>()];

                fn to_bytes(value: Self::Domain) -> Self::Bytes {
                    value.get().to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
                    <$nonzero_unsigned>::new(<$unsigned>::from_be_bytes(bytes))
                        .expect("input bytes should not produce a zero value")
                }
            }

            // SAFETY: The safety of the NonZero* version of the unsigned integer is the same as it
            // is for non-NonZero* variant
            unsafe impl NoPrefixesBytes for Mapped<ToUBE<$nonzero_unsigned>> {}

            // SAFETY: The safety of the NonZero* version of the unsigned integer is the same as it
            // is for non-NonZero* variant
            unsafe impl OrderedBytes for Mapped<ToUBE<$nonzero_unsigned>> {}

            // SAFETY: This is safe to implement because the big endian conversion and XOR operation is
            // reversible and  will guarantee that the byte string ordering is the same as the integer
            // number ordering.
            unsafe impl BytesMapping for ToIBE<$nonzero_signed> {
                type Domain = $nonzero_signed;
                type Bytes = [u8; std::mem::size_of::<$unsigned>()];

                fn to_bytes(value: Self::Domain) -> Self::Bytes {
                    (bytemuck::cast::<_, $unsigned>(value.get()) ^ (1 << (<$unsigned>::BITS - 1))).to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
                    let signed = bytemuck::cast::<_, $signed>(
                        <$unsigned>::from_be_bytes(bytes) ^ (1 << (<$unsigned>::BITS - 1)));

                    <$nonzero_signed>::new(signed).expect("input bytes should not produce a zero value")
                }
            }

            // SAFETY: This impl is safe for the same reasons as the non-NonZero* impl is
            unsafe impl NoPrefixesBytes for Mapped<ToIBE<$nonzero_signed>> {}

            // SAFETY: This impl is safe for the same reasons as the non-NonZero* impl is
            unsafe impl OrderedBytes for Mapped<ToIBE<$nonzero_signed>> {}
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

/// This struct represents a conversion of **IP addresses** (V4 and V6) into
/// their component bytes. The ordering of IP addresses is already the
/// lexicographic ordering of the component bytes, so it will be preserved.
pub struct ToOctets<IP>(PhantomData<IP>);

// SAFETY: This is safe to implement because the conversion to octets is
// reversible and the ordering of the `Ipv4Addr` is already based on these
// bytes.
unsafe impl BytesMapping for ToOctets<Ipv4Addr> {
    type Bytes = [u8; 4];
    type Domain = Ipv4Addr;

    fn to_bytes(value: Self::Domain) -> Self::Bytes {
        value.octets()
    }

    fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
        bytes.into()
    }
}

// SAFETY: The ToOctets mapping will always produce byte arrays of length 4 for
// all Ipv4Addr values. Thus there can be no prefixes
unsafe impl NoPrefixesBytes for Mapped<ToOctets<Ipv4Addr>> {}

// SAFETY: The ordering of the Ipv4Addr is already defined using the octet bytes
// see https://doc.rust-lang.org/1.69.0/src/core/net/ip_addr.rs.html#1066
unsafe impl OrderedBytes for Mapped<ToOctets<Ipv4Addr>> {}

// SAFETY: This is safe to implement because the conversion to octets is
// reversible and the ordering of the `Ipv6Addr` is already based on these
// bytes.
unsafe impl BytesMapping for ToOctets<Ipv6Addr> {
    type Bytes = [u8; 16];
    type Domain = Ipv6Addr;

    fn to_bytes(value: Self::Domain) -> Self::Bytes {
        value.octets()
    }

    fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
        bytes.into()
    }
}

// SAFETY: The ToOctets mapping will always produce byte arrays of length 16 for
// all Ipv6Addr values. THus there can be no prefixes
unsafe impl NoPrefixesBytes for Mapped<ToOctets<Ipv6Addr>> {}

// SAFETY: The ordering of the Ipv6Addr is already defined using the octet bytes
// see https://doc.rust-lang.org/1.69.0/src/core/net/ip_addr.rs.html#1908
unsafe impl OrderedBytes for Mapped<ToOctets<Ipv6Addr>> {}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use std::fmt::Debug;

    fn check_is_ordered_bytes<T: OrderedBytes>() {}

    pub(in crate::bytes) fn assert_ordered_bytes_mapping_contract<B>(a: B::Domain, b: B::Domain)
    where
        B: BytesMapping,
        B::Domain: Ord + Debug + Copy,
    {
        let a_mapped = Mapped::<B>::new(a);
        let b_mapped = Mapped::<B>::new(b);
        let a_bytes = a_mapped.as_bytes();
        let b_bytes = b_mapped.as_bytes();
        assert_eq!(
            a.cmp(&b),
            a_bytes.cmp(b_bytes),
            "{:?} and {:?} compare differently than their byte representation \
             (a_bytes={:?},b_bytes={:?})",
            a,
            b,
            a_bytes,
            b_bytes
        );

        assert_eq!(B::from_bytes(B::to_bytes(a)), a);
        assert_eq!(B::from_bytes(B::to_bytes(b)), b);
    }

    macro_rules! impl_ordered_bytes_ints_tests {
        ($([$unsigned:ty, $signed:ty; $test_fn:ident]),*) => {
            $(
                #[test]
                fn $test_fn() {
                    let mid = (<$unsigned>::MAX + <$unsigned>::MIN) / 2;
                    assert_ordered_bytes_mapping_contract::<ToUBE<$unsigned>>(
                        <$unsigned>::MAX, <$unsigned>::MIN);
                    assert_ordered_bytes_mapping_contract::<ToUBE<$unsigned>>(
                        mid, <$unsigned>::MAX);
                    assert_ordered_bytes_mapping_contract::<ToUBE<$unsigned>>(
                        mid, <$unsigned>::MIN);

                    check_is_ordered_bytes::<Mapped<ToUBE<$unsigned>>>();

                    assert_ordered_bytes_mapping_contract::<ToIBE<$signed>>(
                        0, <$signed>::MAX);
                    assert_ordered_bytes_mapping_contract::<ToIBE<$signed>>(
                        0, <$signed>::MIN);
                    assert_ordered_bytes_mapping_contract::<ToIBE<$signed>>(
                        <$signed>::MAX, <$signed>::MIN);

                    check_is_ordered_bytes::<Mapped<ToIBE<$signed>>>();
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

    macro_rules! impl_ordered_bytes_nonzero_ints_tests {
        ($([$nonzero_unsigned:ty, $unsigned:ty, $nonzero_signed:ty, $signed:ty; $test_fn:ident]),*) => {
            $(
                #[test]
                fn $test_fn() {
                    let mid = <$nonzero_unsigned>::new((<$unsigned>::MAX + <$unsigned>::MIN) / 2).unwrap();
                    assert_ordered_bytes_mapping_contract::<ToUBE<$nonzero_unsigned>>(
                        <$nonzero_unsigned>::new(1).unwrap(),
                        <$nonzero_unsigned>::new(<$unsigned>::MAX).unwrap());
                    assert_ordered_bytes_mapping_contract::<ToUBE<$nonzero_unsigned>>(
                        mid, <$nonzero_unsigned>::new(<$unsigned>::MAX).unwrap());
                    assert_ordered_bytes_mapping_contract::<ToUBE<$nonzero_unsigned>>(
                        mid, <$nonzero_unsigned>::new(<$unsigned>::MIN + 1).unwrap());

                    check_is_ordered_bytes::<Mapped<ToUBE<$nonzero_unsigned>>>();

                    assert_ordered_bytes_mapping_contract::<ToIBE<$nonzero_signed>>(
                        <$nonzero_signed>::new(<$signed>::MIN).unwrap(),
                        <$nonzero_signed>::new(<$signed>::MAX).unwrap());
                    assert_ordered_bytes_mapping_contract::<ToIBE<$nonzero_signed>>(
                        <$nonzero_signed>::new(1).unwrap(),
                        <$nonzero_signed>::new(<$signed>::MAX).unwrap());
                    assert_ordered_bytes_mapping_contract::<ToIBE<$nonzero_signed>>(
                        <$nonzero_signed>::new(<$signed>::MIN).unwrap(),
                        <$nonzero_signed>::new(1).unwrap());

                    check_is_ordered_bytes::<Mapped<ToIBE<$nonzero_signed>>>();
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
        assert_ordered_bytes_mapping_contract::<ToOctets<Ipv4Addr>>(
            Ipv4Addr::LOCALHOST,
            Ipv4Addr::BROADCAST,
        );
        assert_ordered_bytes_mapping_contract::<ToOctets<Ipv4Addr>>(
            Ipv4Addr::LOCALHOST,
            Ipv4Addr::UNSPECIFIED,
        );
        assert_ordered_bytes_mapping_contract::<ToOctets<Ipv4Addr>>(
            Ipv4Addr::BROADCAST,
            Ipv4Addr::UNSPECIFIED,
        );

        check_is_ordered_bytes::<Mapped<ToOctets<Ipv4Addr>>>();

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

        assert_ordered_bytes_mapping_contract::<ToOctets<Ipv6Addr>>(Ipv6Addr::LOCALHOST, IPV6_MAX);
        assert_ordered_bytes_mapping_contract::<ToOctets<Ipv6Addr>>(
            Ipv6Addr::LOCALHOST,
            Ipv6Addr::UNSPECIFIED,
        );
        assert_ordered_bytes_mapping_contract::<ToOctets<Ipv6Addr>>(
            IPV6_MAX,
            Ipv6Addr::UNSPECIFIED,
        );

        check_is_ordered_bytes::<Mapped<ToOctets<Ipv6Addr>>>();
    }
}

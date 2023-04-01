use crate::{AsBytes, NoPrefixesBytes, OrderedBytes};
use std::{fmt::Debug, hash::Hash, marker::PhantomData};

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
/// with the [`Hash` and `Eq` documentation].
///
/// [`Hash` and `Eq` documentation]: https://doc.rust-lang.org/1.68.2/std/hash/trait.Hash.html#hash-and-eq
///
/// # Safety
///
/// This trait is unsafe because implementing it implies that the
/// [`Mapped<Self>`] type will implement [`OrderedBytes`], so the safety
/// requirements must be upheld. Namely, that the ordering of values of the
/// [`Self::Domain`] type must be equal to the ordering of those same values
/// translated to the the [`Self::Bytes`] type.
pub unsafe trait BytesMapping {
    /// The unconverted type that has a specific ordering
    type Domain: Ord;
    /// The bytestring type that the [`Self::Domain`] is converted to.
    type Bytes: AsRef<[u8]> + Copy;

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
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Mapped")
            .field("repr", &self.repr.as_ref())
            .field("original_value", &B::from_bytes(self.repr))
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
            repr: self.repr,
        }
    }
}

impl<B> Copy for Mapped<B> where B: BytesMapping {}

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
        self.repr.as_ref().partial_cmp(other.repr.as_ref())
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

// SAFETY: `NoPrefixesBytes` is safe to implement because we know that the
// underlying [`BytesMapping::Bytes`] type (which is used in the [`AsBytes`]
// implementation) is guaranteed not to have any prefixes.
unsafe impl<B> NoPrefixesBytes for Mapped<B>
where
    B: BytesMapping,
    B::Bytes: NoPrefixesBytes,
{
}

// SAFETY: `OrderedBytes` is safe to implement because of the contract of the
// [`BytesMapping`] trait
unsafe impl<B> OrderedBytes for Mapped<B> where B: BytesMapping {}

/// This struct represents a conversion of unsigned integers to the [big endian
/// format], so that the natural ordering of the numbers matches the
/// lexicographic ordering of the bytes.
///
/// [big endian format]: https://en.wikipedia.org/wiki/Endianness
pub struct ToBE<N>(PhantomData<N>);

/// This struct represents a conversion of signed integers to a format that
/// allows the natural ordering of the numbers to match the lexicographic
/// ordering of the bytes.
///
/// This is done by converting the numbers to their unsigned equivalent using `x
/// XOR (2 ^ (b - 1))` where `b` is the number of bits, then converting the
/// unsigned value to a big endian format if needed.
pub struct ToUIntBE<N>(PhantomData<N>);

macro_rules! impl_ordered_bytes_ints {
    ($([$unsigned:ty, $signed:ty; $test_fn:ident]),*) => {

        $(
            // SAFETY: This is safe to implement because the big endian conversion is reversible and
            // will guarantee that the byte string ordering is the same as the natural number ordering.
            unsafe impl BytesMapping for ToBE<$unsigned> {
                type Domain = $unsigned;
                type Bytes = [u8; std::mem::size_of::<$unsigned>()];

                fn to_bytes(value: Self::Domain) -> Self::Bytes {
                    value.to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
                    <$unsigned>::from_be_bytes(bytes)
                }
            }

            // SAFETY: This is safe to implement because the big endian conversion and XOR operation is
            // reversible and  will guarantee that the byte string ordering is the same as the integer
            // number ordering.
            unsafe impl BytesMapping for ToUIntBE<$signed> {
                type Domain = $signed;
                type Bytes = [u8; std::mem::size_of::<$unsigned>()];

                fn to_bytes(value: Self::Domain) -> Self::Bytes {
                    (bytemuck::cast::<_, $unsigned>(value) ^ (1 << (<$unsigned>::BITS - 1))).to_be_bytes()
                }

                fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
                    bytemuck::cast::<_, $signed>(<$unsigned>::from_be_bytes(bytes) ^ (1 << (<$unsigned>::BITS - 1)))
                }
            }
        )*


        #[cfg(test)]
        mod tests {
            use std::fmt::Debug;

            use super::*;

            /// Check that for the given type
            fn assert_bytes_isomorphism_contract<B>(a: B::Domain, b: B::Domain)
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
                    "{:?} and {:?} compare differently than their byte representation (a_bytes={:?},b_bytes={:?})",
                    a,
                    b,
                    a_bytes,
                    b_bytes
                );

                fn check_is_ordered_bytes<T: OrderedBytes>() {}

                check_is_ordered_bytes::<Mapped<B>>();

                assert_eq!(B::from_bytes(B::to_bytes(a)), a);
                assert_eq!(B::from_bytes(B::to_bytes(b)), b);
            }



            $(
                #[test]
                fn $test_fn() {
                    assert_bytes_isomorphism_contract::<ToBE<$unsigned>>(
                        0, <$unsigned>::MAX);
                    assert_bytes_isomorphism_contract::<ToBE<$unsigned>>(
                        0, <$unsigned>::MIN);
                    assert_bytes_isomorphism_contract::<ToBE<$unsigned>>(
                        <$unsigned>::MAX, <$unsigned>::MIN);

                    assert_bytes_isomorphism_contract::<ToUIntBE<$signed>>(
                        0, <$signed>::MAX);
                    assert_bytes_isomorphism_contract::<ToUIntBE<$signed>>(
                        0, <$signed>::MIN);
                    assert_bytes_isomorphism_contract::<ToUIntBE<$signed>>(
                        <$signed>::MAX, <$signed>::MIN);
                }
            )*
        }
    };
}

impl_ordered_bytes_ints!(
    [u8, i8; test_orded_ui8],
    [u16, i16; test_orded_ui16],
    [u32, i32; test_orded_ui32],
    [u64, i64; test_orded_ui64],
    [u128, i128; test_orded_ui128],
    [usize, isize; test_orded_uisize]
);

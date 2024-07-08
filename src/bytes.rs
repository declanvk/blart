use crate::rust_nightly_apis::{box_assume_init, box_new_uninit_slice};
use paste::paste;
use std::{
    borrow::{Borrow, Cow},
    ffi::{CStr, CString, OsStr, OsString},
    io::{IoSlice, IoSliceMut},
    marker::PhantomData,
    mem::ManuallyDrop,
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
    },
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
};

mod mapped;
pub use mapped::*;

/// Any type implementing `AsBytes` can be decomposed into bytes.
///
/// The primary purpose of this trait is to allow different types to be used as
/// keys on the [`crate::TreeMap`] and `TreeSet` types.
pub trait AsBytes {
    /// View the current value as a byte array.
    fn as_bytes(&self) -> &[u8];
}

/// This trait is used to mark types which have a byte representation which is
/// guaranteed to not be a prefix of any other value of the same type.
///
/// # Safety
///  - This trait can only be implemented if the above condition holds.
pub unsafe trait NoPrefixesBytes: AsBytes {}

/// This trait is used to mark types where the lexicographic ordering of their
/// byte representation (as output by [`AsBytes::as_bytes`]) matches their
/// normal ordering (as determined by [`Ord`]).
///
/// # Safety
///  - This trait can only be implemented if the above condition holds.
pub unsafe trait OrderedBytes: AsBytes + Ord {}

macro_rules! as_bytes_for_integer_like_types {
    ($($type:ty),*) => {
        $(
            impl AsBytes for $type {
                fn as_bytes(&self) -> &[u8] {
                    bytemuck::bytes_of(self)
                }
            }

            // SAFETY: This trait is safe to implement because all the byte
            // representations for this type have the same length, ensuring there
            // can't be any prefixes
            unsafe impl NoPrefixesBytes for $type {}

            impl AsBytes for [$type] {
                fn as_bytes(&self) -> &[u8] {
                    bytemuck::cast_slice(self)
                }
            }

            impl AsBytes for Vec<$type> {
                fn as_bytes(&self) -> &[u8] {
                    bytemuck::cast_slice(self)
                }
            }
        )*
    };
}

as_bytes_for_integer_like_types!(
    u8,
    i8,
    u16,
    i16,
    u32,
    i32,
    u64,
    i64,
    u128,
    i128,
    usize,
    isize,
    char,
    bool,
    NonZeroU8,
    NonZeroI8,
    NonZeroU16,
    NonZeroI16,
    NonZeroU32,
    NonZeroI32,
    NonZeroU64,
    NonZeroI64,
    NonZeroU128,
    NonZeroI128,
    NonZeroUsize,
    NonZeroIsize
);

/// SAFETY: Since `u8` is a single byte, there are no concerns about endian
/// ordering
unsafe impl OrderedBytes for u8 {}

macro_rules! as_bytes_for_integer_arrays {
    ($($type:ty),*) => {
        $(
            impl<const N: usize> AsBytes for [$type; N] {
                fn as_bytes(&self) -> &[u8] {
                    bytemuck::bytes_of(self)
                }
            }

            // SAFETY: This trait is safe to implement because all the byte
            // representations for this type have the same length, ensuring there
            // can't be any prefixes
            unsafe impl<const N: usize> NoPrefixesBytes for [$type; N] {}
        )*
    };
}

as_bytes_for_integer_arrays!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128);

/// SAFETY: The lexicographic ordering of `[u8; N]` converted to bytes is the
/// same as its normal representation.
unsafe impl<const N: usize> OrderedBytes for [u8; N] {}

/// SAFETY: The lexicographic ordering of `[u8; N]` converted to bytes is the
/// same as its normal representation.
unsafe impl OrderedBytes for [u8] {}

/// SAFETY: Same reasoning as the `OrderedBytes for [u8]`
unsafe impl OrderedBytes for Vec<u8> {}

impl AsBytes for str {
    fn as_bytes(&self) -> &[u8] {
        str::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the lexicographic
// ordering of bytes and `Ord` implementation are the same
unsafe impl OrderedBytes for str {}

impl AsBytes for String {
    fn as_bytes(&self) -> &[u8] {
        str::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the lexicographic
// ordering of bytes and `Ord` implementation are the same
unsafe impl OrderedBytes for String {}

impl AsBytes for CStr {
    fn as_bytes(&self) -> &[u8] {
        self.to_bytes_with_nul()
    }
}

// SAFETY: The `as_bytes` implementation for `CStr` is guaranteed to always have
// a '\0' byte at the end, that is not present anywhere else in the string. This
// ensures there will never be a prefix value
unsafe impl NoPrefixesBytes for CStr {}

// SAFETY: This trait is safe to implement because the lexicographic
// ordering of bytes and `Ord` implementation are the same
unsafe impl OrderedBytes for CStr {}

impl AsBytes for CString {
    fn as_bytes(&self) -> &[u8] {
        self.to_bytes_with_nul()
    }
}

// SAFETY: The `as_bytes` implementation for `CStr` is guaranteed to always have
// a '\0' byte at the end, that is not present anywhere else in the string. This
// ensures there will never be a prefix value
unsafe impl NoPrefixesBytes for CString {}

// SAFETY: This trait is safe to implement because the lexicographic
// ordering of bytes and `Ord` implementation are the same
unsafe impl OrderedBytes for CString {}

#[cfg(unix)]
impl AsBytes for OsStr {
    fn as_bytes(&self) -> &[u8] {
        use std::os::unix::prelude::OsStrExt;

        <OsStr as OsStrExt>::as_bytes(self)
    }
}

#[cfg(unix)]
impl AsBytes for OsString {
    fn as_bytes(&self) -> &[u8] {
        use std::os::unix::prelude::OsStrExt;

        <OsStr as OsStrExt>::as_bytes(self)
    }
}

#[cfg(target_os = "wasi")]
impl AsBytes for OsStr {
    fn as_bytes(&self) -> &[u8] {
        use std::os::wasi::prelude::OsStrExt;

        <OsStr as OsStrExt>::as_bytes(self)
    }
}

#[cfg(target_os = "wasi")]
impl AsBytes for OsString {
    fn as_bytes(&self) -> &[u8] {
        use std::os::wasi::prelude::OsStrExt;

        <OsStr as OsStrExt>::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the lexicographic
// ordering of bytes and `Ord` implementation are the same
#[cfg(any(unix, target_os = "wasi"))]
unsafe impl OrderedBytes for OsStr {}

// SAFETY: This trait is safe to implement because the lexicographic
// ordering of bytes and `Ord` implementation are the same
#[cfg(any(unix, target_os = "wasi"))]
unsafe impl OrderedBytes for OsString {}

#[cfg(any(unix, target_os = "wasi"))]
impl AsBytes for Path {
    fn as_bytes(&self) -> &[u8] {
        <OsStr as AsBytes>::as_bytes(self.as_os_str())
    }
}

// SAFETY: This trait is safe to implement because the lexicographic
// ordering of bytes and `Ord` implementation are the same
#[cfg(any(unix, target_os = "wasi"))]
unsafe impl OrderedBytes for Path {}

#[cfg(any(unix, target_os = "wasi"))]
impl AsBytes for PathBuf {
    fn as_bytes(&self) -> &[u8] {
        <OsStr as AsBytes>::as_bytes(self.as_os_str())
    }
}

// SAFETY: This trait is safe to implement because the lexicographic
// ordering of bytes and `Ord` implementation are the same
#[cfg(any(unix, target_os = "wasi"))]
unsafe impl OrderedBytes for PathBuf {}

impl<'a, B> AsBytes for Cow<'a, B>
where
    B: ToOwned + AsBytes + ?Sized,
{
    fn as_bytes(&self) -> &[u8] {
        <B as AsBytes>::as_bytes(self.as_ref())
    }
}

// SAFETY: This trait is safe to implement because the underlying owned/borrowed
// type is already implements `OrderedBytes`, and the `Ord` impl works the same
// way
unsafe impl<'a, B> OrderedBytes for Cow<'a, B>
where
    B: OrderedBytes + 'a + ToOwned + ?Sized,
    Cow<'a, B>: AsBytes,
{
}

// SAFETY: This trait is safe to implement because the underlying owned/borrowed
// type is already implements `NoPrefixesBytes`, and the wrapper type would not
// change that property
unsafe impl<'a, B> NoPrefixesBytes for Cow<'a, B>
where
    B: NoPrefixesBytes + ToOwned + ?Sized,
    Cow<'a, B>: AsBytes,
{
}

impl<'a, T> AsBytes for &'a T
where
    T: AsBytes + ?Sized,
{
    fn as_bytes(&self) -> &[u8] {
        <T as AsBytes>::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `OrderedBytes`, and the `Ord` impl works the same
// way
unsafe impl<'a, T> OrderedBytes for &'a T where T: OrderedBytes + ?Sized {}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `NoPrefixesBytes`, and the wrapper type would not
// change that property
unsafe impl<'a, T> NoPrefixesBytes for &'a T where T: NoPrefixesBytes + ?Sized {}

impl<'a, T> AsBytes for &'a mut T
where
    T: AsBytes + ?Sized,
{
    fn as_bytes(&self) -> &[u8] {
        <T as AsBytes>::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `OrderedBytes`, and the `Ord` impl works the same
// way
unsafe impl<'a, T> OrderedBytes for &'a mut T where T: OrderedBytes + ?Sized {}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `NoPrefixesBytes`, and the wrapper type would not
// change that property
unsafe impl<'a, T> NoPrefixesBytes for &'a mut T where T: NoPrefixesBytes + ?Sized {}

impl<T> AsBytes for Rc<T>
where
    T: AsBytes + ?Sized,
{
    fn as_bytes(&self) -> &[u8] {
        <T as AsBytes>::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `OrderedBytes`, and the `Ord` impl works the same
// way
unsafe impl<T> OrderedBytes for Rc<T> where T: OrderedBytes + ?Sized {}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `NoPrefixesBytes`, and the wrapper type would not
// change that property
unsafe impl<T> NoPrefixesBytes for Rc<T> where T: NoPrefixesBytes + ?Sized {}

impl<T> AsBytes for Arc<T>
where
    T: AsBytes + ?Sized,
{
    fn as_bytes(&self) -> &[u8] {
        <T as AsBytes>::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `OrderedBytes`, and the `Ord` impl works the same
// way
unsafe impl<T> OrderedBytes for Arc<T> where T: OrderedBytes + ?Sized {}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `NoPrefixesBytes`, and the wrapper type would not
// change that property
unsafe impl<T> NoPrefixesBytes for Arc<T> where T: NoPrefixesBytes + ?Sized {}

impl<T> AsBytes for Box<T>
where
    T: AsBytes + ?Sized,
{
    fn as_bytes(&self) -> &[u8] {
        <T as AsBytes>::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `OrderedBytes`, and the `Ord` impl works the same
// way
unsafe impl<T> OrderedBytes for Box<T> where T: OrderedBytes + ?Sized {}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `NoPrefixesBytes`, and the wrapper type would not
// change that property
unsafe impl<T> NoPrefixesBytes for Box<T> where T: NoPrefixesBytes + ?Sized {}

impl<T> AsBytes for ManuallyDrop<T>
where
    T: AsBytes + ?Sized,
{
    fn as_bytes(&self) -> &[u8] {
        <T as AsBytes>::as_bytes(self)
    }
}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `OrderedBytes`, and the `Ord` impl works the same
// way
unsafe impl<T> OrderedBytes for ManuallyDrop<T> where T: OrderedBytes + ?Sized {}

// SAFETY: This trait is safe to implement because the underlying
// type is already implements `NoPrefixesBytes`, and the wrapper type would not
// change that property
unsafe impl<T> NoPrefixesBytes for ManuallyDrop<T> where T: NoPrefixesBytes + ?Sized {}

impl<'a> AsBytes for IoSlice<'a> {
    fn as_bytes(&self) -> &[u8] {
        self
    }
}

impl<'a> AsBytes for IoSliceMut<'a> {
    fn as_bytes(&self) -> &[u8] {
        self
    }
}

/// Concats two or more types that implement [`AsBytes`]. The construction of
/// this type will allocate memory, since the concatenated bytes need to be in a
/// flat buffer. If the types are [`Copy`] use tuple syntax which avoids
/// allocating
///
/// If all of the types implement [`OrderedBytes`] then this type is also
/// implements [`OrderedBytes`]
///
/// If all of the types implement [`NoPrefixesBytes`] then this type is also
/// implements [`NoPrefixesBytes`]
#[derive(Debug)]
pub struct Concat<T>(Box<[u8]>, PhantomData<T>);

impl<T> AsBytes for Concat<T> {
    fn as_bytes(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

impl<T> PartialEq for Concat<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for Concat<T> {}

impl<T> PartialOrd for Concat<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for Concat<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
    }
}

macro_rules! as_bytes_for_concat {
    ($(($($ty:ident)+))+) => {
        $(
            paste! {
                impl<$($ty, [< Q $ty >],)+> From<($(&[< Q $ty >],)*)> for Concat<($($ty,)+)>
                where
                    $(
                        $ty: Borrow<[< Q $ty >]> + AsBytes,
                        [< Q $ty >]: AsBytes + ?Sized,
                    )+
                {
                    #[inline(always)]
                    fn from(value: ($(&[< Q $ty >],)+)) -> Self {
                        #[allow(non_snake_case)]
                        let ($($ty,)+) = value;

                        $(
                            #[allow(non_snake_case)]
                            let $ty = $ty.as_bytes();
                        )+

                        let mut sum = 0;
                        $(sum += $ty.len();)+

                        let mut v = box_new_uninit_slice(sum);

                        let mut sum = 0;
                        $(
                            let new_sum = sum + $ty.len();
                            // SAFETY: This is safe because `sum` and `new_sum` are
                            // being updated by the right amount for each of the concated
                            // types `as_bytes` representation (i.e length), so it's impossible
                            // for the `new_sum` in this case to exceed the original box length
                            unsafe {
                                v
                                .get_unchecked_mut(sum..new_sum)
                                .copy_from_slice(
                                    std::mem::transmute::<&[u8], &[std::mem::MaybeUninit<u8>]>($ty));
                            }
                            sum = new_sum;
                        )+

                        let _ = sum;

                        // SAFETY: We just filled the box with data, so it's safe
                        Self(unsafe { box_assume_init(v) }, PhantomData)
                    }
                }
            }

            // SAFETY: This trait is safe to implement because the underlying
            // type is already implements `OrderedBytes`, and the `Ord` impl works the same
            // way
            unsafe impl<$($ty: OrderedBytes,)+> OrderedBytes for Concat<($($ty,)+)> {}

            // SAFETY: This trait is safe to implement because the underlying
            // type is already implements `NoPrefixesBytes`, and the wrapper type would not
            // change that property
            unsafe impl<$($ty: NoPrefixesBytes,)+> NoPrefixesBytes for Concat<($($ty,)+)> {}
        )*
    };
}

as_bytes_for_concat!(
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

macro_rules! as_bytes_for_tuples {
    ($(($($ty:ident)+))+) => {
        $(
            impl<$($ty: AsBytes + Copy,)+> AsBytes for ($($ty,)+)
            {
                #[inline(always)]
                fn as_bytes(&self) -> &[u8] {
                    // SAFETY: All the types of this tuple are `Copy`
                    // (they are trivial), so we can just reinterpret the
                    // whole type as a slice of `u8`s
                    unsafe {
                        std::slice::from_raw_parts(
                            self as *const Self as *const u8,
                            std::mem::size_of::<Self>()
                        )
                    }
                }
            }

            // SAFETY: This trait is safe to implement because the underlying
            // type is already implements `OrderedBytes`, and the `Ord` impl works the same
            // way
            unsafe impl<$($ty: OrderedBytes + Copy,)+> OrderedBytes for ($($ty,)+) {}

            // SAFETY: This trait is safe to implement because the underlying
            // type is already implements `NoPrefixesBytes`, and the wrapper type would not
            // change that property
            unsafe impl<$($ty: NoPrefixesBytes + Copy,)+> NoPrefixesBytes for ($($ty,)+) {}
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
mod tests {
    use std::fmt;

    use mapped::tests::assert_ordered_bytes_mapping_contract;

    use super::*;

    #[test]
    fn various_numeric_types_as_bytes() {
        assert_eq!(u8::MAX.as_bytes(), &[u8::MAX]);
        assert_eq!(i8::MAX.as_bytes(), &[i8::MAX as u8]);
        assert_eq!(65535u16.as_bytes(), 65535u16.to_ne_bytes());
        assert_eq!(32767i16.as_bytes(), 32767i16.to_ne_bytes());
        assert_eq!(2387u32.as_bytes(), 2387u32.to_ne_bytes());
        assert_eq!(2387i32.as_bytes(), 2387i32.to_ne_bytes());

        // numeric arrays
        assert_eq!(
            [26343u16, 0, u16::MAX].as_bytes(),
            &[
                26343u16.to_ne_bytes()[0],
                26343u16.to_ne_bytes()[1],
                0,
                0,
                255,
                255
            ]
        );
        assert_eq!(
            Box::<[u16]>::from([26343u16, 0, u16::MAX]).as_bytes(),
            &[
                26343u16.to_ne_bytes()[0],
                26343u16.to_ne_bytes()[1],
                0,
                0,
                255,
                255
            ]
        );
        assert_eq!(
            Vec::<u16>::from([26343u16, 0, u16::MAX]).as_bytes(),
            &[
                26343u16.to_ne_bytes()[0],
                26343u16.to_ne_bytes()[1],
                0,
                0,
                255,
                255
            ]
        );

        // sorta numeric types
        assert_eq!(
            NonZeroU32::try_from(u32::MAX).unwrap().as_bytes(),
            &[255, 255, 255, 255]
        );
        assert_eq!('Z'.as_bytes(), 90u32.to_ne_bytes());
        assert_eq!(false.as_bytes(), &[0]);
    }

    #[test]
    fn various_string_types_as_bytes() {
        assert_eq!(<str as AsBytes>::as_bytes("hello world"), b"hello world");
        assert_eq!(
            <String as AsBytes>::as_bytes(&"hello world".into()),
            b"hello world"
        );
        assert_eq!(
            <CStr as AsBytes>::as_bytes(CStr::from_bytes_with_nul(b"hello world\0").unwrap()),
            b"hello world\0"
        );
        assert_eq!(
            <CString as AsBytes>::as_bytes(
                &CStr::from_bytes_with_nul(b"hello world\0").unwrap().into()
            ),
            b"hello world\0"
        );
        assert_eq!(
            <CString as AsBytes>::as_bytes(
                &CStr::from_bytes_with_nul(b"hello world\0").unwrap().into()
            ),
            b"hello world\0"
        );
        #[cfg(any(unix, target_os = "wasi"))]
        {
            assert_eq!(
                <OsStr as AsBytes>::as_bytes(OsStr::new("hello world")),
                b"hello world"
            );
            assert_eq!(
                <OsString as AsBytes>::as_bytes(&OsStr::new("hello world").into()),
                b"hello world"
            );
        }
        #[cfg(any(unix, target_os = "wasi"))]
        {
            assert_eq!(
                <Path as AsBytes>::as_bytes(Path::new("hello/world")),
                b"hello/world"
            );
            assert_eq!(
                <PathBuf as AsBytes>::as_bytes(&Path::new("hello/world").into()),
                b"hello/world"
            );
        }
    }

    #[test]
    fn various_wrapper_types_as_bytes() {
        assert_eq!(
            <&[u8] as AsBytes>::as_bytes(&&b"hello world"[..]),
            b"hello world"
        );
        assert_eq!(
            <Box<&[u8]> as AsBytes>::as_bytes(&Box::new(b"hello world")),
            b"hello world"
        );
        assert_eq!(
            <Box<[u8]> as AsBytes>::as_bytes(&b"hello world".to_vec().into_boxed_slice()),
            b"hello world"
        );
        assert_eq!(
            <Arc<&[u8]> as AsBytes>::as_bytes(&Arc::new(b"hello world")),
            b"hello world"
        );
        assert_eq!(
            <Rc<&[u8]> as AsBytes>::as_bytes(&Rc::new(b"hello world")),
            b"hello world"
        );
        assert_eq!(
            <Cow<[u8]> as AsBytes>::as_bytes(&Cow::Borrowed(b"hello world")),
            b"hello world"
        );
        assert_eq!(
            <ManuallyDrop<&[u8]> as AsBytes>::as_bytes(&ManuallyDrop::new(b"hello world")),
            b"hello world"
        );
        assert_eq!(
            <IoSlice as AsBytes>::as_bytes(&IoSlice::new(b"hello world")),
            b"hello world"
        );
        let mut buffer = [104u8, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100];
        assert_eq!(
            <IoSliceMut as AsBytes>::as_bytes(&IoSliceMut::new(&mut buffer)),
            b"hello world"
        )
    }

    #[test]
    fn copy_tuple_as_bytes() {
        let tup1 = ([0u8; 5], [10u8; 5]);
        assert_eq!(tup1.as_bytes(), &[0, 0, 0, 0, 0, 10, 10, 10, 10, 10]);
    }

    // TODO: Resolve https://github.com/declanvk/blart/issues/31
    #[test]
    fn concat_tuple_ord_matches_tuple_ord() {
        let t1 = ("aa".to_owned(), "abb".to_owned());
        let t2 = ("aaa".to_owned(), "bb".to_owned());
        assert!(t1 < t2);

        let c1: Concat<(String, String)> = Concat::from(("aa", "abb"));
        let c2: Concat<(String, String)> = Concat::from(("aaa", "bb"));
        assert_ordered_bytes_contract(c1, c2)
    }

    #[test]
    fn copy_mapped_tuple_ordering() {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        enum Weird {
            Short([u8; 1]),
            Long([u8; 2]),
        }

        #[derive(Debug, Clone, Copy)]
        enum WeirdBytes {
            Short([u8; 2]),
            Long([u8; 3]),
        }

        impl AsRef<[u8]> for WeirdBytes {
            fn as_ref(&self) -> &[u8] {
                match self {
                    WeirdBytes::Short(bytes) => bytes.as_ref(),
                    WeirdBytes::Long(bytes) => bytes.as_ref(),
                }
            }
        }

        struct WeirdToBytes;

        unsafe impl BytesMapping for WeirdToBytes {
            type Bytes = WeirdBytes;
            type Domain = Weird;

            fn to_bytes(value: Self::Domain) -> Self::Bytes {
                match value {
                    Weird::Short(inner) => WeirdBytes::Short([0, inner[0]]),
                    Weird::Long(inner) => WeirdBytes::Long([1, inner[0], inner[1]]),
                }
            }

            fn from_bytes(bytes: Self::Bytes) -> Self::Domain {
                match bytes {
                    WeirdBytes::Short(bytes) => Weird::Short([bytes[1]]),
                    WeirdBytes::Long(bytes) => Weird::Long([bytes[1], bytes[2]]),
                }
            }
        }

        assert_ordered_bytes_mapping_contract::<WeirdToBytes>(
            Weird::Short([u8::MIN]),
            Weird::Short([u8::MAX]),
        );
        assert_ordered_bytes_mapping_contract::<WeirdToBytes>(
            Weird::Short([u8::MAX]),
            Weird::Long([u8::MIN, u8::MIN]),
        );
        assert_ordered_bytes_mapping_contract::<WeirdToBytes>(
            Weird::Long([u8::MIN, u8::MIN]),
            Weird::Long([u8::MAX, u8::MAX]),
        );

        unsafe impl OrderedBytes for Mapped<WeirdToBytes> {}

        let t1 = (
            Mapped::<WeirdToBytes>::new(Weird::Long([u8::MIN, u8::MIN])),
            Mapped::<WeirdToBytes>::new(Weird::Short([u8::MAX])),
        );
        let t2 = (
            Mapped::<WeirdToBytes>::new(Weird::Short([u8::MIN])),
            Mapped::<WeirdToBytes>::new(Weird::Long([u8::MIN, u8::MAX])),
        );

        assert_ordered_bytes_contract(t1, t2);
    }

    fn assert_ordered_bytes_contract<T>(a: T, b: T)
    where
        T: Ord + fmt::Debug + OrderedBytes,
    {
        let a_bytes = a.as_bytes();
        let b_bytes = b.as_bytes();

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
    }
}

use std::{
    borrow::Cow,
    ffi::{CStr, CString, OsStr, OsString},
    io::{IoSlice, IoSliceMut},
    mem::ManuallyDrop,
    num::{
        NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
        NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
    },
    path::{Path, PathBuf},
    rc::Rc,
    sync::Arc,
};

/// Any type implementing `AsBytes` can be decomposed into bytes.
///
/// The primary purpose of this trait is to allow different types to be used as
/// keys on the [`TreeMap`][crate::map::TreeMap] and `TreeSet` types.
pub trait AsBytes {
    /// View the current value as a byte array.
    fn as_bytes(&self) -> &[u8];
}

/// This trait is used to mark types which have a byte representation which is
/// guaranteed to not be a prefix of any other value of the same type.
///
/// # Safety
///
/// This trait can only be implemented if the above condition holds.
pub unsafe trait NoPrefixesBytes: AsBytes {}

/// This trait is used to mark types where the lexicographic ordering of their
/// byte representation (as output by [`AsBytes::as_bytes`]) matches their
/// normal ordering (as determined by [`Ord`]).
///
/// # Safety
///
/// This trait can only be implemented if the above condition holds.
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

            // SAFETY: This trait is safe to implement because the lexicographic
            // ordering of bytes and `Ord` implementation are the same
            unsafe impl OrderedBytes for [$type] {}

            impl AsBytes for Vec<$type> {
                fn as_bytes(&self) -> &[u8] {
                    bytemuck::cast_slice(self)
                }
            }

            // SAFETY: This trait is safe to implement because the lexicographic
            // ordering of bytes and `Ord` implementation are the same
            unsafe impl OrderedBytes for Vec<$type> {}
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
    <B as ToOwned>::Owned: AsBytes,
{
    fn as_bytes(&self) -> &[u8] {
        match self {
            Cow::Borrowed(borrowed) => <B as AsBytes>::as_bytes(borrowed),
            Cow::Owned(owned) => <<B as ToOwned>::Owned as AsBytes>::as_bytes(owned),
        }
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
unsafe impl<'a, T> NoPrefixesBytes for &'a T where T: NoPrefixesBytes {}

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

#[cfg(test)]
mod tests {
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
}

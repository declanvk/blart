//! This module contains type relating to indexing in
//! [`InnerNodeIndirect`][super::InnerNodeIndirect].

use core::{cmp::Ordering, error::Error, fmt, num::NonZeroU8};

/// This type represents an index into an array that has a maximum length of
/// 256.
///
/// # Layout
///
/// `NonMaxIndex` is guaranteed to have the same layout and bit validity as `u8`
/// with the exception that `u8::MAX` is not a valid instance.
///
/// `Option<NonMaxIndex>` is guaranteed to be compatible with `u8`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct NonMaxIndex(NonZeroU8);

impl NonMaxIndex {
    /// Creates a new index if the given value is not [`u8::MAX`].
    #[inline]
    pub const fn new(value: u8) -> Option<Self> {
        match NonZeroU8::new(value ^ u8::MAX) {
            None => None,
            Some(value) => Some(Self(value)),
        }
    }

    /// Creates a new index without checking the value.
    ///
    /// # Safety
    ///
    /// The value must not equal [`u8::MAX`].
    #[inline]
    pub const unsafe fn new_unchecked(value: u8) -> Self {
        // SAFETY: So long as the safety condition of the function is obeyed, then the
        // argument to `NonZeroU8::new_unchecked` will not be zero.
        let inner = unsafe { NonZeroU8::new_unchecked(value ^ u8::MAX) };
        Self(inner)
    }

    /// Returns the value as a primitive type.
    #[inline]
    pub const fn get(&self) -> u8 {
        self.0.get() ^ u8::MAX
    }
}

impl Default for NonMaxIndex {
    fn default() -> Self {
        unsafe { Self::new_unchecked(0) }
    }
}

impl From<NonMaxIndex> for u8 {
    fn from(value: NonMaxIndex) -> Self {
        value.get()
    }
}

impl From<NonMaxIndex> for usize {
    fn from(value: NonMaxIndex) -> Self {
        usize::from(value.get())
    }
}

impl TryFrom<u8> for NonMaxIndex {
    type Error = TryFromByteError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Self::new(value).ok_or(TryFromByteError(()))
    }
}

impl TryFrom<usize> for NonMaxIndex {
    type Error = TryFromByteError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value >= (u8::MAX as usize) {
            Err(TryFromByteError(()))
        } else {
            // SAFETY: Checked by conditional, value is not equal to `u8::MAX`
            Ok(unsafe { Self::new_unchecked(value as u8) })
        }
    }
}

impl Ord for NonMaxIndex {
    fn cmp(&self, other: &Self) -> Ordering {
        self.get().cmp(&other.get())
    }
}

impl PartialOrd for NonMaxIndex {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// The error type returned when attempting to construct an index outside
/// the accepted range of a [`NonMaxIndex`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TryFromByteError(());

impl fmt::Display for TryFromByteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "out of range integral type conversion attempted".fmt(f)
    }
}

impl Error for TryFromByteError {}

#[cfg(test)]
mod tests {
    use core::mem::size_of;

    use super::*;

    #[test]
    fn construct() {
        let zero = NonMaxIndex::new(0).unwrap();
        assert_eq!(zero.get(), 0);

        let some = NonMaxIndex::new(19).unwrap();
        assert_eq!(some.get(), 19);

        let max = NonMaxIndex::new(u8::MAX);
        assert_eq!(max, None);
    }

    #[test]
    fn sizes_correct() {
        assert_eq!(size_of::<u8>(), size_of::<NonMaxIndex>());
        assert_eq!(size_of::<NonMaxIndex>(), size_of::<Option<NonMaxIndex>>());
    }

    #[test]
    fn convert() {
        use core::convert::TryFrom;
        let zero = NonMaxIndex::try_from(0u8).unwrap();
        let zero = u8::from(zero);
        assert_eq!(zero, 0);

        NonMaxIndex::try_from(u8::MAX).unwrap_err();
    }

    #[test]
    fn cmp() {
        let zero = NonMaxIndex::new(0).unwrap();
        let one = NonMaxIndex::new(1).unwrap();
        let two = NonMaxIndex::new(2).unwrap();
        assert!(zero < one);
        assert!(one < two);
        assert!(two > one);
        assert!(one > zero);
    }
}

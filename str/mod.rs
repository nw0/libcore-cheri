#![stable(feature = "rust1", since = "1.0.0")]

/// Converts a slice of bytes to a string slice without checking
/// that the string contains valid UTF-8; mutable version.
///
/// See the immutable version, [`from_utf8_unchecked()`][fromutf8], for more information.
///
/// [fromutf8]: fn.from_utf8_unchecked.html
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use std::str;
///
/// let mut heart = vec![240, 159, 146, 150];
/// let heart = unsafe { str::from_utf8_unchecked_mut(&mut heart) };
///
/// assert_eq!("💖", heart);
/// ```
#[inline]
#[stable(feature = "str_mut_extras", since = "1.20.0")]
pub unsafe fn from_utf8_unchecked_mut(v: &mut [u8]) -> &mut str {
    &mut *(v as *mut [u8] as *mut str)
}

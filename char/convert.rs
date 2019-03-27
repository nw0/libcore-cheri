// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Character conversions.

use convert::TryFrom;
use mem::transmute;
use super::MAX;

/// Converts a `u32` to a `char`.
///
/// Note that all [`char`]s are valid [`u32`]s, and can be cast to one with
/// `as`:
///
/// ```
/// let c = '💯';
/// let i = c as u32;
///
/// assert_eq!(128175, i);
/// ```
///
/// However, the reverse is not true: not all valid [`u32`]s are valid
/// [`char`]s. `from_u32()` will return `None` if the input is not a valid value
/// for a [`char`].
///
/// [`char`]: ../../std/primitive.char.html
/// [`u32`]: ../../std/primitive.u32.html
///
/// For an unsafe version of this function which ignores these checks, see
/// [`from_u32_unchecked`].
///
/// [`from_u32_unchecked`]: fn.from_u32_unchecked.html
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use std::char;
///
/// let c = char::from_u32(0x2764);
///
/// assert_eq!(Some('❤'), c);
/// ```
///
/// Returning `None` when the input is not a valid [`char`]:
///
/// ```
/// use std::char;
///
/// let c = char::from_u32(0x110000);
///
/// assert_eq!(None, c);
/// ```
#[inline]
#[stable(feature = "rust1", since = "1.0.0")]
pub fn from_u32(i: u32) -> Option<char> {
    char::try_from(i).ok()
}

/// Converts a `u32` to a `char`, ignoring validity.
///
/// Note that all [`char`]s are valid [`u32`]s, and can be cast to one with
/// `as`:
///
/// ```
/// let c = '💯';
/// let i = c as u32;
///
/// assert_eq!(128175, i);
/// ```
///
/// However, the reverse is not true: not all valid [`u32`]s are valid
/// [`char`]s. `from_u32_unchecked()` will ignore this, and blindly cast to
/// [`char`], possibly creating an invalid one.
///
/// [`char`]: ../../std/primitive.char.html
/// [`u32`]: ../../std/primitive.u32.html
///
/// # Safety
///
/// This function is unsafe, as it may construct invalid `char` values.
///
/// For a safe version of this function, see the [`from_u32`] function.
///
/// [`from_u32`]: fn.from_u32.html
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use std::char;
///
/// let c = unsafe { char::from_u32_unchecked(0x2764) };
///
/// assert_eq!('❤', c);
/// ```
#[inline]
#[stable(feature = "char_from_unchecked", since = "1.5.0")]
pub unsafe fn from_u32_unchecked(i: u32) -> char {
    transmute(i)
}

#[stable(feature = "char_convert", since = "1.13.0")]
impl From<char> for u32 {
    /// Converts a [`char`] into a [`u32`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::mem;
    ///
    /// fn main() {
    ///     let c = 'c';
    ///     let u = u32::from(c);
    ///     assert!(4 == mem::size_of_val(&u))
    /// }
    /// ```
    #[inline]
    fn from(c: char) -> Self {
        c as u32
    }
}

/// Maps a byte in 0x00...0xFF to a `char` whose code point has the same value, in U+0000 to U+00FF.
///
/// Unicode is designed such that this effectively decodes bytes
/// with the character encoding that IANA calls ISO-8859-1.
/// This encoding is compatible with ASCII.
///
/// Note that this is different from ISO/IEC 8859-1 a.k.a. ISO 8859-1 (with one less hyphen),
/// which leaves some "blanks", byte values that are not assigned to any character.
/// ISO-8859-1 (the IANA one) assigns them to the C0 and C1 control codes.
///
/// Note that this is *also* different from Windows-1252 a.k.a. code page 1252,
/// which is a superset ISO/IEC 8859-1 that assigns some (not all!) blanks
/// to punctuation and various Latin characters.
///
/// To confuse things further, [on the Web](https://encoding.spec.whatwg.org/)
/// `ascii`, `iso-8859-1`, and `windows-1252` are all aliases
/// for a superset of Windows-1252 that fills the remaining blanks with corresponding
/// C0 and C1 control codes.
#[stable(feature = "char_convert", since = "1.13.0")]
impl From<u8> for char {
    /// Converts a [`u8`] into a [`char`].
    ///
    /// # Examples
    ///
    /// ```
    /// use std::mem;
    ///
    /// fn main() {
    ///     let u = 32 as u8;
    ///     let c = char::from(u);
    ///     assert!(4 == mem::size_of_val(&c))
    /// }
    /// ```
    #[inline]
    fn from(i: u8) -> Self {
        i as char
    }
}


/// An error which can be returned when parsing a char.
#[stable(feature = "char_from_str", since = "1.20.0")]
#[derive(Clone, PartialEq, Eq)]
pub struct ParseCharError {
    kind: CharErrorKind,
}

impl ParseCharError {
    #[unstable(feature = "char_error_internals",
               reason = "this method should not be available publicly",
               issue = "0")]
    #[doc(hidden)]
    pub fn __description(&self) -> &str {
        match self.kind {
            CharErrorKind::EmptyString => {
                "cannot parse char from empty string"
            },
            CharErrorKind::TooManyChars => "too many characters in string"
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum CharErrorKind {
    EmptyString,
    TooManyChars,
}



#[unstable(feature = "try_from", issue = "33417")]
impl TryFrom<u32> for char {
    type Error = CharTryFromError;

    #[inline]
    fn try_from(i: u32) -> Result<Self, Self::Error> {
        if (i > MAX as u32) || (i >= 0xD800 && i <= 0xDFFF) {
            Err(CharTryFromError(()))
        } else {
            Ok(unsafe { from_u32_unchecked(i) })
        }
    }
}

/// The error type returned when a conversion from u32 to char fails.
#[unstable(feature = "try_from", issue = "33417")]
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct CharTryFromError(());

/// Converts a digit in the given radix to a `char`.
///
/// A 'radix' here is sometimes also called a 'base'. A radix of two
/// indicates a binary number, a radix of ten, decimal, and a radix of
/// sixteen, hexadecimal, to give some common values. Arbitrary
/// radices are supported.
///
/// `from_digit()` will return `None` if the input is not a digit in
/// the given radix.
///
/// # Panics
///
/// Panics if given a radix larger than 36.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use std::char;
///
/// let c = char::from_digit(4, 10);
///
/// assert_eq!(Some('4'), c);
///
/// // Decimal 11 is a single digit in base 16
/// let c = char::from_digit(11, 16);
///
/// assert_eq!(Some('b'), c);
/// ```
///
/// Returning `None` when the input is not a digit:
///
/// ```
/// use std::char;
///
/// let c = char::from_digit(20, 10);
///
/// assert_eq!(None, c);
/// ```
///
/// Passing a large radix, causing a panic:
///
/// ```
/// use std::thread;
/// use std::char;
///
/// let result = thread::spawn(|| {
///     // this panics
///     let c = char::from_digit(1, 37);
/// }).join();
///
/// assert!(result.is_err());
/// ```
#[inline]
#[stable(feature = "rust1", since = "1.0.0")]
pub fn from_digit(num: u32, radix: u32) -> Option<char> {
    if radix > 36 {
        panic!("from_digit: radix is too high (maximum 36)");
    }
    if num < radix {
        let num = num as u8;
        if num < 10 {
            Some((b'0' + num) as char)
        } else {
            Some((b'a' + num - 10) as char)
        }
    } else {
        None
    }
}

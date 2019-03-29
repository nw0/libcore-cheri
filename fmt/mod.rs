#![stable(feature = "rust1", since = "1.0.0")]

use marker::PhantomData;
use mem;
use num::flt2dec;
use result;
use slice;
use str;

mod builders;

#[stable(feature = "fmt_flags_align", since = "1.28.0")]
/// Possible alignments returned by `Formatter::align`
pub enum Alignment {
    #[stable(feature = "fmt_flags_align", since = "1.28.0")]
    /// Indication that contents should be left-aligned.
    Left,
    #[stable(feature = "fmt_flags_align", since = "1.28.0")]
    /// Indication that contents should be right-aligned.
    Right,
    #[stable(feature = "fmt_flags_align", since = "1.28.0")]
    /// Indication that contents should be center-aligned.
    Center,
}

#[unstable(feature = "fmt_internals", reason = "internal to format_args!",
           issue = "0")]
#[doc(hidden)]
pub mod rt {
    pub mod v1;
}

/// The type returned by formatter methods.
///
/// # Examples
///
/// ```
/// use std::fmt;
///
/// #[derive(Debug)]
/// struct Triangle {
///     a: f32,
///     b: f32,
///     c: f32
/// }
///
/// impl fmt::Display for Triangle {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         write!(f, "({}, {}, {})", self.a, self.b, self.c)
///     }
/// }
///
/// let pythagorean_triple = Triangle { a: 3.0, b: 4.0, c: 5.0 };
///
/// println!("{}", pythagorean_triple);
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub type Result = result::Result<(), Error>;

/// The error type which is returned from formatting a message into a stream.
///
/// This type does not support transmission of an error other than that an error
/// occurred. Any extra information must be arranged to be transmitted through
/// some other means.
///
/// An important thing to remember is that the type `fmt::Error` should not be
/// confused with [`std::io::Error`] or [`std::error::Error`], which you may also
/// have in scope.
///
/// [`std::io::Error`]: ../../std/io/struct.Error.html
/// [`std::error::Error`]: ../../std/error/trait.Error.html
///
/// # Examples
///
/// ```rust
/// use std::fmt::{self, write};
///
/// let mut output = String::new();
/// if let Err(fmt::Error) = write(&mut output, format_args!("Hello {}!", "world")) {
///     panic!("An error occurred");
/// }
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct Error;

/// A collection of methods that are required to format a message into a stream.
///
/// This trait is the type which this modules requires when formatting
/// information. This is similar to the standard library's [`io::Write`] trait,
/// but it is only intended for use in libcore.
///
/// This trait should generally not be implemented by consumers of the standard
/// library. The [`write!`] macro accepts an instance of [`io::Write`], and the
/// [`io::Write`] trait is favored over implementing this trait.
///
/// [`write!`]: ../../std/macro.write.html
/// [`io::Write`]: ../../std/io/trait.Write.html
#[stable(feature = "rust1", since = "1.0.0")]
pub trait Write {
    /// Writes a slice of bytes into this writer, returning whether the write
    /// succeeded.
    ///
    /// This method can only succeed if the entire byte slice was successfully
    /// written, and this method will not return until all data has been
    /// written or an error occurs.
    ///
    /// # Errors
    ///
    /// This function will return an instance of [`Error`] on error.
    ///
    /// [`Error`]: struct.Error.html
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt::{Error, Write};
    ///
    /// fn writer<W: Write>(f: &mut W, s: &str) -> Result<(), Error> {
    ///     f.write_str(s)
    /// }
    ///
    /// let mut buf = String::new();
    /// writer(&mut buf, "hola").unwrap();
    /// assert_eq!(&buf, "hola");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    fn write_str(&mut self, s: &str) -> Result;

    /// Writes a [`char`] into this writer, returning whether the write succeeded.
    ///
    /// A single [`char`] may be encoded as more than one byte.
    /// This method can only succeed if the entire byte sequence was successfully
    /// written, and this method will not return until all data has been
    /// written or an error occurs.
    ///
    /// # Errors
    ///
    /// This function will return an instance of [`Error`] on error.
    ///
    /// [`char`]: ../../std/primitive.char.html
    /// [`Error`]: struct.Error.html
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt::{Error, Write};
    ///
    /// fn writer<W: Write>(f: &mut W, c: char) -> Result<(), Error> {
    ///     f.write_char(c)
    /// }
    ///
    /// let mut buf = String::new();
    /// writer(&mut buf, 'a').unwrap();
    /// writer(&mut buf, 'b').unwrap();
    /// assert_eq!(&buf, "ab");
    /// ```
    #[stable(feature = "fmt_write_char", since = "1.1.0")]
    fn write_char(&mut self, c: char) -> Result {
        self.write_str(c.encode_utf8(&mut [0; 4]))
    }

    /// Glue for usage of the [`write!`] macro with implementors of this trait.
    ///
    /// This method should generally not be invoked manually, but rather through
    /// the [`write!`] macro itself.
    ///
    /// [`write!`]: ../../std/macro.write.html
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt::{Error, Write};
    ///
    /// fn writer<W: Write>(f: &mut W, s: &str) -> Result<(), Error> {
    ///     f.write_fmt(format_args!("{}", s))
    /// }
    ///
    /// let mut buf = String::new();
    /// writer(&mut buf, "world").unwrap();
    /// assert_eq!(&buf, "world");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    fn write_fmt(mut self: &mut Self, args: Arguments) -> Result {
        write(&mut self, args)
    }
}

#[stable(feature = "fmt_write_blanket_impl", since = "1.4.0")]
impl<W: Write + ?Sized> Write for &mut W {
    fn write_str(&mut self, s: &str) -> Result {
        (**self).write_str(s)
    }

    fn write_char(&mut self, c: char) -> Result {
        (**self).write_char(c)
    }

    fn write_fmt(&mut self, args: Arguments) -> Result {
        (**self).write_fmt(args)
    }
}

#[allow(missing_debug_implementations)]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Formatter<'a> {
    flags: u32,
    fill: char,
    align: rt::v1::Alignment,
    width: Option<usize>,
    precision: Option<usize>,

    buf: &'a mut (dyn Write+'a),
    curarg: slice::Iter<'a, ArgumentV1<'a>>,
    args: &'a [ArgumentV1<'a>],
}

// NB. Argument is essentially an optimized partially applied formatting function,
// equivalent to `exists T.(&T, fn(&T, &mut Formatter) -> Result`.

struct Void {
    _priv: (),
    /// Erases all oibits, because `Void` erases the type of the object that
    /// will be used to produce formatted output. Since we do not know what
    /// oibits the real types have (and they can have any or none), we need to
    /// take the most conservative approach and forbid all oibits.
    ///
    /// It was added after #45197 showed that one could share a `!Sync`
    /// object across threads by passing it into `format_args!`.
    _oibit_remover: PhantomData<*mut dyn Fn()>,
}

/// This struct represents the generic "argument" which is taken by the Xprintf
/// family of functions. It contains a function to format the given value. At
/// compile time it is ensured that the function and the value have the correct
/// types, and then this struct is used to canonicalize arguments to one type.
#[derive(Copy, Clone)]
#[allow(missing_debug_implementations)]
#[unstable(feature = "fmt_internals", reason = "internal to format_args!",
           issue = "0")]
#[doc(hidden)]
pub struct ArgumentV1<'a> {
    value: &'a Void,
    formatter: fn(&Void, &mut Formatter) -> Result,
}

impl<'a> ArgumentV1<'a> {
    #[inline(never)]
    fn show_usize(x: &usize, f: &mut Formatter) -> Result {
        Ok(())
    }

    #[doc(hidden)]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn new<'b, T>(x: &'b T,
                      f: fn(&T, &mut Formatter) -> Result) -> ArgumentV1<'b> {
        unsafe {
            ArgumentV1 {
                formatter: mem::transmute(f),
                value: mem::transmute(x)
            }
        }
    }

    #[doc(hidden)]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn from_usize(x: &usize) -> ArgumentV1 {
        ArgumentV1::new(x, ArgumentV1::show_usize)
    }

    fn as_usize(&self) -> Option<usize> {
        if self.formatter as usize == ArgumentV1::show_usize as usize {
            Some(unsafe { *(self.value as *const _ as *const usize) })
        } else {
            None
        }
    }
}

// flags available in the v1 format of format_args
#[derive(Copy, Clone)]
enum FlagV1 { SignPlus, SignMinus, Alternate, SignAwareZeroPad, DebugLowerHex, DebugUpperHex }

impl<'a> Arguments<'a> {
    /// When using the format_args!() macro, this function is used to generate the
    /// Arguments structure.
    #[doc(hidden)] #[inline]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn new_v1(pieces: &'a [&'a str],
                  args: &'a [ArgumentV1<'a>]) -> Arguments<'a> {
        Arguments {
            pieces,
            fmt: None,
            args,
        }
    }

    /// This function is used to specify nonstandard formatting parameters.
    /// The `pieces` array must be at least as long as `fmt` to construct
    /// a valid Arguments structure. Also, any `Count` within `fmt` that is
    /// `CountIsParam` or `CountIsNextParam` has to point to an argument
    /// created with `argumentusize`. However, failing to do so doesn't cause
    /// unsafety, but will ignore invalid .
    #[doc(hidden)] #[inline]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn new_v1_formatted(pieces: &'a [&'a str],
                            args: &'a [ArgumentV1<'a>],
                            fmt: &'a [rt::v1::Argument]) -> Arguments<'a> {
        Arguments {
            pieces,
            fmt: Some(fmt),
            args,
        }
    }

    /// Estimates the length of the formatted text.
    ///
    /// This is intended to be used for setting initial `String` capacity
    /// when using `format!`. Note: this is neither the lower nor upper bound.
    #[doc(hidden)] #[inline]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn estimated_capacity(&self) -> usize {
        let pieces_length: usize = self.pieces.iter()
            .map(|x| x.len()).sum();

        if self.args.is_empty() {
            pieces_length
        } else if self.pieces[0] == "" && pieces_length < 16 {
            // If the format string starts with an argument,
            // don't preallocate anything, unless length
            // of pieces is significant.
            0
        } else {
            // There are some arguments, so any additional push
            // will reallocate the string. To avoid that,
            // we're "pre-doubling" the capacity here.
            pieces_length.checked_mul(2).unwrap_or(0)
        }
    }
}

/// This structure represents a safely precompiled version of a format string
/// and its arguments. This cannot be generated at runtime because it cannot
/// safely be done, so no constructors are given and the fields are private
/// to prevent modification.
///
/// The [`format_args!`] macro will safely create an instance of this structure.
/// The macro validates the format string at compile-time so usage of the
/// [`write`] and [`format`] functions can be safely performed.
///
/// You can use the `Arguments<'a>` that [`format_args!`] returns in `Debug`
/// and `Display` contexts as seen below. The example also shows that `Debug`
/// and `Display` format to the same thing: the interpolated format string
/// in `format_args!`.
///
/// ```rust
/// let debug = format!("{:?}", format_args!("{} foo {:?}", 1, 2));
/// let display = format!("{}", format_args!("{} foo {:?}", 1, 2));
/// assert_eq!("1 foo 2", display);
/// assert_eq!(display, debug);
/// ```
///
/// [`format_args!`]: ../../std/macro.format_args.html
/// [`format`]: ../../std/fmt/fn.format.html
/// [`write`]: ../../std/fmt/fn.write.html
#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Copy, Clone)]
pub struct Arguments<'a> {
    // Format string pieces to print.
    pieces: &'a [&'a str],

    // Placeholder specs, or `None` if all specs are default (as in "{}{}").
    fmt: Option<&'a [rt::v1::Argument]>,

    // Dynamic arguments for interpolation, to be interleaved with string
    // pieces. (Every argument is preceded by a string piece.)
    args: &'a [ArgumentV1<'a>],
}

/// `?` formatting.
///
/// `Debug` should format the output in a programmer-facing, debugging context.
///
/// Generally speaking, you should just `derive` a `Debug` implementation.
///
/// When used with the alternate format specifier `#?`, the output is pretty-printed.
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// [module]: ../../std/fmt/index.html
///
/// This trait can be used with `#[derive]` if all fields implement `Debug`. When
/// `derive`d for structs, it will use the name of the `struct`, then `{`, then a
/// comma-separated list of each field's name and `Debug` value, then `}`. For
/// `enum`s, it will use the name of the variant and, if applicable, `(`, then the
/// `Debug` values of the fields, then `)`.
///
/// # Examples
///
/// Deriving an implementation:
///
/// ```
/// #[derive(Debug)]
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// let origin = Point { x: 0, y: 0 };
///
/// println!("The origin is: {:?}", origin);
/// ```
///
/// Manually implementing:
///
/// ```
/// use std::fmt;
///
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl fmt::Debug for Point {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         write!(f, "Point {{ x: {}, y: {} }}", self.x, self.y)
///     }
/// }
///
/// let origin = Point { x: 0, y: 0 };
///
/// println!("The origin is: {:?}", origin);
/// ```
///
/// This outputs:
///
/// ```text
/// The origin is: Point { x: 0, y: 0 }
/// ```
///
/// There are a number of `debug_*` methods on [`Formatter`] to help you with manual
/// implementations, such as [`debug_struct`][debug_struct].
///
/// `Debug` implementations using either `derive` or the debug builder API
/// on [`Formatter`] support pretty-printing using the alternate flag: `{:#?}`.
///
/// [debug_struct]: ../../std/fmt/struct.Formatter.html#method.debug_struct
/// [`Formatter`]: ../../std/fmt/struct.Formatter.html
///
/// Pretty-printing with `#?`:
///
/// ```
/// #[derive(Debug)]
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// let origin = Point { x: 0, y: 0 };
///
/// println!("The origin is: {:#?}", origin);
/// ```
///
/// This outputs:
///
/// ```text
/// The origin is: Point {
///     x: 0,
///     y: 0
/// }
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_on_unimplemented(
    on(crate_local, label="`{Self}` cannot be formatted using `{{:?}}`",
                    note="add `#[derive(Debug)]` or manually implement `{Debug}`"),
    message="`{Self}` doesn't implement `{Debug}`",
    label="`{Self}` cannot be formatted using `{{:?}}` because it doesn't implement `{Debug}`",
)]
#[doc(alias = "{:?}")]
#[lang = "debug_trait"]
pub trait Debug {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// Format trait for an empty format, `{}`.
///
/// `Display` is similar to [`Debug`][debug], but `Display` is for user-facing
/// output, and so cannot be derived.
///
/// [debug]: trait.Debug.html
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// [module]: ../../std/fmt/index.html
///
/// # Examples
///
/// Implementing `Display` on a type:
///
/// ```
/// use std::fmt;
///
/// struct Point {
///     x: i32,
///     y: i32,
/// }
///
/// impl fmt::Display for Point {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         write!(f, "({}, {})", self.x, self.y)
///     }
/// }
///
/// let origin = Point { x: 0, y: 0 };
///
/// println!("The origin is: {}", origin);
/// ```
#[rustc_on_unimplemented(
    on(
        _Self="std::path::Path",
        label="`{Self}` cannot be formatted with the default formatter; call `.display()` on it",
        note="call `.display()` or `.to_string_lossy()` to safely print paths, \
              as they may contain non-Unicode data"
    ),
    message="`{Self}` doesn't implement `{Display}`",
    label="`{Self}` cannot be formatted with the default formatter",
    note="in format strings you may be able to use `{{:?}}` (or {{:#?}} for pretty-print) instead",
)]
#[doc(alias = "{}")]
#[stable(feature = "rust1", since = "1.0.0")]
pub trait Display {
    /// Formats the value using the given formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Position {
    ///     longitude: f32,
    ///     latitude: f32,
    /// }
    ///
    /// impl fmt::Display for Position {
    ///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    ///         write!(f, "({}, {})", self.longitude, self.latitude)
    ///     }
    /// }
    ///
    /// assert_eq!("(1.987, 2.983)".to_owned(),
    ///            format!("{}", Position { longitude: 1.987, latitude: 2.983, }));
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// `o` formatting.
///
/// The `Octal` trait should format its output as a number in base-8.
///
/// For primitive signed integers (`i8` to `i128`, and `isize`),
/// negative values are formatted as the two’s complement representation.
///
/// The alternate flag, `#`, adds a `0o` in front of the output.
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// [module]: ../../std/fmt/index.html
///
/// # Examples
///
/// Basic usage with `i32`:
///
/// ```
/// let x = 42; // 42 is '52' in octal
///
/// assert_eq!(format!("{:o}", x), "52");
/// assert_eq!(format!("{:#o}", x), "0o52");
///
/// assert_eq!(format!("{:o}", -16), "37777777760");
/// ```
///
/// Implementing `Octal` on a type:
///
/// ```
/// use std::fmt;
///
/// struct Length(i32);
///
/// impl fmt::Octal for Length {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         let val = self.0;
///
///         write!(f, "{:o}", val) // delegate to i32's implementation
///     }
/// }
///
/// let l = Length(9);
///
/// println!("l as octal is: {:o}", l);
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub trait Octal {
    /// Formats the value using the given formatter.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// `b` formatting.
///
/// The `Binary` trait should format its output as a number in binary.
///
/// For primitive signed integers ([`i8`] to [`i128`], and [`isize`]),
/// negative values are formatted as the two’s complement representation.
///
/// The alternate flag, `#`, adds a `0b` in front of the output.
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// # Examples
///
/// Basic usage with [`i32`]:
///
/// ```
/// let x = 42; // 42 is '101010' in binary
///
/// assert_eq!(format!("{:b}", x), "101010");
/// assert_eq!(format!("{:#b}", x), "0b101010");
///
/// assert_eq!(format!("{:b}", -16), "11111111111111111111111111110000");
/// ```
///
/// Implementing `Binary` on a type:
///
/// ```
/// use std::fmt;
///
/// struct Length(i32);
///
/// impl fmt::Binary for Length {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         let val = self.0;
///
///         write!(f, "{:b}", val) // delegate to i32's implementation
///     }
/// }
///
/// let l = Length(107);
///
/// println!("l as binary is: {:b}", l);
/// ```
///
/// [module]: ../../std/fmt/index.html
/// [`i8`]: ../../std/primitive.i8.html
/// [`i128`]: ../../std/primitive.i128.html
/// [`isize`]: ../../std/primitive.isize.html
/// [`i32`]: ../../std/primitive.i32.html
#[stable(feature = "rust1", since = "1.0.0")]
pub trait Binary {
    /// Formats the value using the given formatter.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// `x` formatting.
///
/// The `LowerHex` trait should format its output as a number in hexadecimal, with `a` through `f`
/// in lower case.
///
/// For primitive signed integers (`i8` to `i128`, and `isize`),
/// negative values are formatted as the two’s complement representation.
///
/// The alternate flag, `#`, adds a `0x` in front of the output.
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// [module]: ../../std/fmt/index.html
///
/// # Examples
///
/// Basic usage with `i32`:
///
/// ```
/// let x = 42; // 42 is '2a' in hex
///
/// assert_eq!(format!("{:x}", x), "2a");
/// assert_eq!(format!("{:#x}", x), "0x2a");
///
/// assert_eq!(format!("{:x}", -16), "fffffff0");
/// ```
///
/// Implementing `LowerHex` on a type:
///
/// ```
/// use std::fmt;
///
/// struct Length(i32);
///
/// impl fmt::LowerHex for Length {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         let val = self.0;
///
///         write!(f, "{:x}", val) // delegate to i32's implementation
///     }
/// }
///
/// let l = Length(9);
///
/// println!("l as hex is: {:x}", l);
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub trait LowerHex {
    /// Formats the value using the given formatter.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// `X` formatting.
///
/// The `UpperHex` trait should format its output as a number in hexadecimal, with `A` through `F`
/// in upper case.
///
/// For primitive signed integers (`i8` to `i128`, and `isize`),
/// negative values are formatted as the two’s complement representation.
///
/// The alternate flag, `#`, adds a `0x` in front of the output.
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// [module]: ../../std/fmt/index.html
///
/// # Examples
///
/// Basic usage with `i32`:
///
/// ```
/// let x = 42; // 42 is '2A' in hex
///
/// assert_eq!(format!("{:X}", x), "2A");
/// assert_eq!(format!("{:#X}", x), "0x2A");
///
/// assert_eq!(format!("{:X}", -16), "FFFFFFF0");
/// ```
///
/// Implementing `UpperHex` on a type:
///
/// ```
/// use std::fmt;
///
/// struct Length(i32);
///
/// impl fmt::UpperHex for Length {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         let val = self.0;
///
///         write!(f, "{:X}", val) // delegate to i32's implementation
///     }
/// }
///
/// let l = Length(9);
///
/// println!("l as hex is: {:X}", l);
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub trait UpperHex {
    /// Formats the value using the given formatter.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// `p` formatting.
///
/// The `Pointer` trait should format its output as a memory location. This is commonly presented
/// as hexadecimal.
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// [module]: ../../std/fmt/index.html
///
/// # Examples
///
/// Basic usage with `&i32`:
///
/// ```
/// let x = &42;
///
/// let address = format!("{:p}", x); // this produces something like '0x7f06092ac6d0'
/// ```
///
/// Implementing `Pointer` on a type:
///
/// ```
/// use std::fmt;
///
/// struct Length(i32);
///
/// impl fmt::Pointer for Length {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         // use `as` to convert to a `*const T`, which implements Pointer, which we can use
///
///         write!(f, "{:p}", self as *const Length)
///     }
/// }
///
/// let l = Length(42);
///
/// println!("l is in memory here: {:p}", l);
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub trait Pointer {
    /// Formats the value using the given formatter.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// `e` formatting.
///
/// The `LowerExp` trait should format its output in scientific notation with a lower-case `e`.
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// [module]: ../../std/fmt/index.html
///
/// # Examples
///
/// Basic usage with `i32`:
///
/// ```
/// let x = 42.0; // 42.0 is '4.2e1' in scientific notation
///
/// assert_eq!(format!("{:e}", x), "4.2e1");
/// ```
///
/// Implementing `LowerExp` on a type:
///
/// ```
/// use std::fmt;
///
/// struct Length(i32);
///
/// impl fmt::LowerExp for Length {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         let val = self.0;
///         write!(f, "{}e1", val / 10)
///     }
/// }
///
/// let l = Length(100);
///
/// println!("l in scientific notation is: {:e}", l);
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub trait LowerExp {
    /// Formats the value using the given formatter.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// `E` formatting.
///
/// The `UpperExp` trait should format its output in scientific notation with an upper-case `E`.
///
/// For more information on formatters, see [the module-level documentation][module].
///
/// [module]: ../../std/fmt/index.html
///
/// # Examples
///
/// Basic usage with `f32`:
///
/// ```
/// let x = 42.0; // 42.0 is '4.2E1' in scientific notation
///
/// assert_eq!(format!("{:E}", x), "4.2E1");
/// ```
///
/// Implementing `UpperExp` on a type:
///
/// ```
/// use std::fmt;
///
/// struct Length(i32);
///
/// impl fmt::UpperExp for Length {
///     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
///         let val = self.0;
///         write!(f, "{}E1", val / 10)
///     }
/// }
///
/// let l = Length(100);
///
/// println!("l in scientific notation is: {:E}", l);
/// ```
#[stable(feature = "rust1", since = "1.0.0")]
pub trait UpperExp {
    /// Formats the value using the given formatter.
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter) -> Result;
}

/// The `write` function takes an output stream, and an `Arguments` struct
/// that can be precompiled with the `format_args!` macro.
///
/// The arguments will be formatted according to the specified format string
/// into the output stream provided.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use std::fmt;
///
/// let mut output = String::new();
/// fmt::write(&mut output, format_args!("Hello {}!", "world"))
///     .expect("Error occurred while trying to write in String");
/// assert_eq!(output, "Hello world!");
/// ```
///
/// Please note that using [`write!`] might be preferable. Example:
///
/// ```
/// use std::fmt::Write;
///
/// let mut output = String::new();
/// write!(&mut output, "Hello {}!", "world")
///     .expect("Error occurred while trying to write in String");
/// assert_eq!(output, "Hello world!");
/// ```
///
/// [`write!`]: ../../std/macro.write.html
#[stable(feature = "rust1", since = "1.0.0")]
pub fn write(output: &mut dyn Write, args: Arguments) -> Result {
    let mut formatter = Formatter {
        flags: 0,
        width: None,
        precision: None,
        buf: output,
        align: rt::v1::Alignment::Unknown,
        fill: ' ',
        args: args.args,
        curarg: args.args.iter(),
    };

    let mut idx = 0;

    for (arg, piece) in args.args.iter().zip(args.pieces.iter()) {
        formatter.buf.write_str(*piece)?;
        (arg.formatter)(arg.value, &mut formatter)?;
        idx += 1;
    }

    // There can be only one trailing string piece left.
    if let Some(piece) = args.pieces.get(idx) {
        formatter.buf.write_str(*piece)?;
    }

    Ok(())
}

/// Padding after the end of something. Returned by `Formatter::padding`.
#[must_use = "don't forget to write the post padding"]
struct PostPadding {
    fill: char,
    padding: usize,
}

impl PostPadding {
    fn new(fill: char, padding: usize) -> PostPadding {
        PostPadding { fill, padding }
    }

    /// Write this post padding.
    fn write(self, buf: &mut dyn Write) -> Result {
        for _ in 0..self.padding {
            buf.write_char(self.fill)?;
        }
        Ok(())
    }
}

impl<'a> Formatter<'a> {
    fn wrap_buf<'b, 'c, F>(&'b mut self, wrap: F) -> Formatter<'c>
        where 'b: 'c, F: FnOnce(&'b mut (dyn Write+'b)) -> &'c mut (dyn Write+'c)
    {
        Formatter {
            // We want to change this
            buf: wrap(self.buf),

            // And preserve these
            flags: self.flags,
            fill: self.fill,
            align: self.align,
            width: self.width,
            precision: self.precision,

            // These only exist in the struct for the `run` method,
            // which won’t be used together with this method.
            curarg: self.curarg.clone(),
            args: self.args,
        }
    }

    fn getcount(&mut self, cnt: &rt::v1::Count) -> Option<usize> {
        match *cnt {
            rt::v1::Count::Is(n) => Some(n),
            rt::v1::Count::Implied => None,
            rt::v1::Count::Param(i) => {
                self.args[i].as_usize()
            }
            rt::v1::Count::NextParam => {
                self.curarg.next()?.as_usize()
            }
        }
    }

    // Helper methods used for padding and processing formatting arguments that
    // all formatting traits can use.

    /// Performs the correct padding for an integer which has already been
    /// emitted into a str. The str should *not* contain the sign for the
    /// integer, that will be added by this method.
    ///
    /// # Arguments
    ///
    /// * is_nonnegative - whether the original integer was either positive or zero.
    /// * prefix - if the '#' character (Alternate) is provided, this
    ///   is the prefix to put in front of the number.
    /// * buf - the byte array that the number has been formatted into
    ///
    /// This function will correctly account for the flags provided as well as
    /// the minimum width. It will not take precision into account.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo { nb: i32 };
    ///
    /// impl Foo {
    ///     fn new(nb: i32) -> Foo {
    ///         Foo {
    ///             nb,
    ///         }
    ///     }
    /// }
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         // We need to remove "-" from the number output.
    ///         let tmp = self.nb.abs().to_string();
    ///
    ///         formatter.pad_integral(self.nb > 0, "Foo ", &tmp)
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{}", Foo::new(2)), "2");
    /// assert_eq!(&format!("{}", Foo::new(-1)), "-1");
    /// assert_eq!(&format!("{:#}", Foo::new(-1)), "-Foo 1");
    /// assert_eq!(&format!("{:0>#8}", Foo::new(-1)), "00-Foo 1");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pad_integral(&mut self,
                        is_nonnegative: bool,
                        prefix: &str,
                        buf: &str)
                        -> Result {
        let mut width = buf.len();

        let mut sign = None;
        if !is_nonnegative {
            sign = Some('-'); width += 1;
        } else if self.sign_plus() {
            sign = Some('+'); width += 1;
        }

        let prefix = if self.alternate() {
            width += prefix.chars().count();
            Some(prefix)
        } else {
            None
        };

        // Writes the sign if it exists, and then the prefix if it was requested
        #[inline(never)]
        fn write_prefix(f: &mut Formatter, sign: Option<char>, prefix: Option<&str>) -> Result {
            if let Some(c) = sign {
                f.buf.write_char(c)?;
            }
            if let Some(prefix) = prefix {
                f.buf.write_str(prefix)
            } else {
                Ok(())
            }
        }

        // The `width` field is more of a `min-width` parameter at this point.
        match self.width {
            // If there's no minimum length requirements then we can just
            // write the bytes.
            None => {
                write_prefix(self, sign, prefix)?;
                self.buf.write_str(buf)
            }
            // Check if we're over the minimum width, if so then we can also
            // just write the bytes.
            Some(min) if width >= min => {
                write_prefix(self, sign, prefix)?;
                self.buf.write_str(buf)
            }
            // The sign and prefix goes before the padding if the fill character
            // is zero
            Some(min) if self.sign_aware_zero_pad() => {
                self.fill = '0';
                self.align = rt::v1::Alignment::Right;
                write_prefix(self, sign, prefix)?;
                let post_padding = self.padding(min - width, rt::v1::Alignment::Right)?;
                self.buf.write_str(buf)?;
                post_padding.write(self.buf)
            }
            // Otherwise, the sign and prefix goes after the padding
            Some(min) => {
                let post_padding = self.padding(min - width, rt::v1::Alignment::Right)?;
                write_prefix(self, sign, prefix)?;
                self.buf.write_str(buf)?;
                post_padding.write(self.buf)
            }
        }
    }

    /// This function takes a string slice and emits it to the internal buffer
    /// after applying the relevant formatting flags specified. The flags
    /// recognized for generic strings are:
    ///
    /// * width - the minimum width of what to emit
    /// * fill/align - what to emit and where to emit it if the string
    ///                provided needs to be padded
    /// * precision - the maximum length to emit, the string is truncated if it
    ///               is longer than this length
    ///
    /// Notably this function ignores the `flag` parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo;
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         formatter.pad("Foo")
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{:<4}", Foo), "Foo ");
    /// assert_eq!(&format!("{:0>4}", Foo), "0Foo");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pad(&mut self, s: &str) -> Result {
        self.buf.write_str(s)
    }

    /// Write the pre-padding and return the unwritten post-padding. Callers are
    /// responsible for ensuring post-padding is written after the thing that is
    /// being padded.
    fn padding(
        &mut self,
        padding: usize,
        default: rt::v1::Alignment
    ) -> result::Result<PostPadding, Error> {
        let align = match self.align {
            rt::v1::Alignment::Unknown => default,
            _ => self.align
        };

        let (pre_pad, post_pad) = match align {
            rt::v1::Alignment::Left => (0, padding),
            rt::v1::Alignment::Right |
            rt::v1::Alignment::Unknown => (padding, 0),
            rt::v1::Alignment::Center => (padding / 2, (padding + 1) / 2),
        };

        for _ in 0..pre_pad {
            self.buf.write_char(self.fill)?;
        }

        Ok(PostPadding::new(self.fill, post_pad))
    }

    /// Takes the formatted parts and applies the padding.
    /// Assumes that the caller already has rendered the parts with required precision,
    /// so that `self.precision` can be ignored.
    fn pad_formatted_parts(&mut self, formatted: &flt2dec::Formatted) -> Result {
        if let Some(mut width) = self.width {
            // for the sign-aware zero padding, we render the sign first and
            // behave as if we had no sign from the beginning.
            let mut formatted = formatted.clone();
            let old_fill = self.fill;
            let old_align = self.align;
            let mut align = old_align;
            if self.sign_aware_zero_pad() {
                // a sign always goes first
                let sign = unsafe { str::from_utf8_unchecked(formatted.sign) };
                self.buf.write_str(sign)?;

                // remove the sign from the formatted parts
                formatted.sign = b"";
                width = width.saturating_sub(sign.len());
                align = rt::v1::Alignment::Right;
                self.fill = '0';
                self.align = rt::v1::Alignment::Right;
            }

            // remaining parts go through the ordinary padding process.
            let len = formatted.len();
            let ret = if width <= len { // no padding
                self.write_formatted_parts(&formatted)
            } else {
                let post_padding = self.padding(width - len, align)?;
                self.write_formatted_parts(&formatted)?;
                post_padding.write(self.buf)
            };
            self.fill = old_fill;
            self.align = old_align;
            ret
        } else {
            // this is the common case and we take a shortcut
            self.write_formatted_parts(formatted)
        }
    }

    fn write_formatted_parts(&mut self, formatted: &flt2dec::Formatted) -> Result {
        fn write_bytes(buf: &mut dyn Write, s: &[u8]) -> Result {
            buf.write_str(unsafe { str::from_utf8_unchecked(s) })
        }

        if !formatted.sign.is_empty() {
            write_bytes(self.buf, formatted.sign)?;
        }
        for part in formatted.parts {
            match *part {
                flt2dec::Part::Zero(mut nzeroes) => {
                    const ZEROES: &str = // 64 zeroes
                        "0000000000000000000000000000000000000000000000000000000000000000";
                    while nzeroes > ZEROES.len() {
                        self.buf.write_str(ZEROES)?;
                        nzeroes -= ZEROES.len();
                    }
                    if nzeroes > 0 {
                        self.buf.write_str(&ZEROES[..nzeroes])?;
                    }
                }
                flt2dec::Part::Num(mut v) => {
                    let mut s = [0; 5];
                    let len = part.len();
                    for c in s[..len].iter_mut().rev() {
                        *c = b'0' + (v % 10) as u8;
                        v /= 10;
                    }
                    write_bytes(self.buf, &s[..len])?;
                }
                flt2dec::Part::Copy(buf) => {
                    write_bytes(self.buf, buf)?;
                }
            }
        }
        Ok(())
    }

    /// Writes some data to the underlying buffer contained within this
    /// formatter.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo;
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         formatter.write_str("Foo")
    ///         // This is equivalent to:
    ///         // write!(formatter, "Foo")
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{}", Foo), "Foo");
    /// assert_eq!(&format!("{:0>8}", Foo), "Foo");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn write_str(&mut self, data: &str) -> Result {
        self.buf.write_str(data)
    }

    /// Writes some formatted information into this instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo(i32);
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         formatter.write_fmt(format_args!("Foo {}", self.0))
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{}", Foo(-1)), "Foo -1");
    /// assert_eq!(&format!("{:0>8}", Foo(2)), "Foo 2");
    /// ```
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn write_fmt(&mut self, fmt: Arguments) -> Result {
        write(self.buf, fmt)
    }

    /// Flags for formatting
    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_deprecated(since = "1.24.0",
                       reason = "use the `sign_plus`, `sign_minus`, `alternate`, \
                                 or `sign_aware_zero_pad` methods instead")]
    pub fn flags(&self) -> u32 { self.flags }

    /// Character used as 'fill' whenever there is alignment.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo;
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         let c = formatter.fill();
    ///         if let Some(width) = formatter.width() {
    ///             for _ in 0..width {
    ///                 write!(formatter, "{}", c)?;
    ///             }
    ///             Ok(())
    ///         } else {
    ///             write!(formatter, "{}", c)
    ///         }
    ///     }
    /// }
    ///
    /// // We set alignment to the left with ">".
    /// assert_eq!(&format!("{:G>3}", Foo), "GGG");
    /// assert_eq!(&format!("{:t>6}", Foo), "tttttt");
    /// ```
    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn fill(&self) -> char { self.fill }

    /// Flag indicating what form of alignment was requested.
    ///
    /// # Examples
    ///
    /// ```
    /// extern crate core;
    ///
    /// use std::fmt::{self, Alignment};
    ///
    /// struct Foo;
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         let s = if let Some(s) = formatter.align() {
    ///             match s {
    ///                 Alignment::Left    => "left",
    ///                 Alignment::Right   => "right",
    ///                 Alignment::Center  => "center",
    ///             }
    ///         } else {
    ///             "into the void"
    ///         };
    ///         write!(formatter, "{}", s)
    ///     }
    /// }
    ///
    /// fn main() {
    ///     assert_eq!(&format!("{:<}", Foo), "left");
    ///     assert_eq!(&format!("{:>}", Foo), "right");
    ///     assert_eq!(&format!("{:^}", Foo), "center");
    ///     assert_eq!(&format!("{}", Foo), "into the void");
    /// }
    /// ```
    #[stable(feature = "fmt_flags_align", since = "1.28.0")]
    pub fn align(&self) -> Option<Alignment> {
        match self.align {
            rt::v1::Alignment::Left => Some(Alignment::Left),
            rt::v1::Alignment::Right => Some(Alignment::Right),
            rt::v1::Alignment::Center => Some(Alignment::Center),
            rt::v1::Alignment::Unknown => None,
        }
    }

    /// Optionally specified integer width that the output should be.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo(i32);
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         if let Some(width) = formatter.width() {
    ///             // If we received a width, we use it
    ///             write!(formatter, "{:width$}", &format!("Foo({})", self.0), width = width)
    ///         } else {
    ///             // Otherwise we do nothing special
    ///             write!(formatter, "Foo({})", self.0)
    ///         }
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{:10}", Foo(23)), "Foo(23)   ");
    /// assert_eq!(&format!("{}", Foo(23)), "Foo(23)");
    /// ```
    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn width(&self) -> Option<usize> { self.width }

    /// Optionally specified precision for numeric types.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo(f32);
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         if let Some(precision) = formatter.precision() {
    ///             // If we received a precision, we use it.
    ///             write!(formatter, "Foo({1:.*})", precision, self.0)
    ///         } else {
    ///             // Otherwise we default to 2.
    ///             write!(formatter, "Foo({:.2})", self.0)
    ///         }
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{:.4}", Foo(23.2)), "Foo(23.2000)");
    /// assert_eq!(&format!("{}", Foo(23.2)), "Foo(23.20)");
    /// ```
    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn precision(&self) -> Option<usize> { self.precision }

    /// Determines if the `+` flag was specified.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo(i32);
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         if formatter.sign_plus() {
    ///             write!(formatter,
    ///                    "Foo({}{})",
    ///                    if self.0 < 0 { '-' } else { '+' },
    ///                    self.0)
    ///         } else {
    ///             write!(formatter, "Foo({})", self.0)
    ///         }
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{:+}", Foo(23)), "Foo(+23)");
    /// assert_eq!(&format!("{}", Foo(23)), "Foo(23)");
    /// ```
    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn sign_plus(&self) -> bool { self.flags & (1 << FlagV1::SignPlus as u32) != 0 }

    /// Determines if the `-` flag was specified.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo(i32);
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         if formatter.sign_minus() {
    ///             // You want a minus sign? Have one!
    ///             write!(formatter, "-Foo({})", self.0)
    ///         } else {
    ///             write!(formatter, "Foo({})", self.0)
    ///         }
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{:-}", Foo(23)), "-Foo(23)");
    /// assert_eq!(&format!("{}", Foo(23)), "Foo(23)");
    /// ```
    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn sign_minus(&self) -> bool { self.flags & (1 << FlagV1::SignMinus as u32) != 0 }

    /// Determines if the `#` flag was specified.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo(i32);
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         if formatter.alternate() {
    ///             write!(formatter, "Foo({})", self.0)
    ///         } else {
    ///             write!(formatter, "{}", self.0)
    ///         }
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{:#}", Foo(23)), "Foo(23)");
    /// assert_eq!(&format!("{}", Foo(23)), "23");
    /// ```
    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn alternate(&self) -> bool { self.flags & (1 << FlagV1::Alternate as u32) != 0 }

    /// Determines if the `0` flag was specified.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::fmt;
    ///
    /// struct Foo(i32);
    ///
    /// impl fmt::Display for Foo {
    ///     fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
    ///         assert!(formatter.sign_aware_zero_pad());
    ///         assert_eq!(formatter.width(), Some(4));
    ///         // We ignore the formatter's options.
    ///         write!(formatter, "{}", self.0)
    ///     }
    /// }
    ///
    /// assert_eq!(&format!("{:04}", Foo(23)), "23");
    /// ```
    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn sign_aware_zero_pad(&self) -> bool {
        self.flags & (1 << FlagV1::SignAwareZeroPad as u32) != 0
    }
}

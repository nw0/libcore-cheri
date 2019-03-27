#![stable(feature = "rust1", since = "1.0.0")]

use marker::PhantomData;
use mem;
use result;
use slice;

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

#[stable(feature = "rust1", since = "1.0.0")]
pub type Result = result::Result<(), Error>;

#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Copy, Clone, Default, Eq, Ord, PartialEq, PartialOrd)]
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
        Ok(())
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
        Ok(())
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

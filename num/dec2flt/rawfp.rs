//! Bit fiddling on positive IEEE 754 floats. Negative numbers aren't and needn't be handled.
//! Normal floating point numbers have a canonical representation as (frac, exp) such that the
//! value is 2<sup>exp</sup> * (1 + sum(frac[N-i] / 2<sup>i</sup>)) where N is the number of bits.
//! Subnormals are slightly different and weird, but the same principle applies.
//!
//! Here, however, we represent them as (sig, k) with f positive, such that the value is f *
//! 2<sup>e</sup>. Besides making the "hidden bit" explicit, this changes the exponent by the
//! so-called mantissa shift.
//!
//! Put another way, normally floats are written as (1) but here they are written as (2):
//!
//! 1. `1.101100...11 * 2^m`
//! 2. `1101100...11 * 2^n`
//!
//! We call (1) the **fractional representation** and (2) the **integral representation**.
//!
//! Many functions in this module only handle normal numbers. The dec2flt routines conservatively
//! take the universally-correct slow path (Algorithm M) for very small and very large numbers.
//! That algorithm needs only next_float() which does handle subnormals and zeros.

use convert::{TryFrom};
use ops::{Add, Mul, Div, Neg};
use fmt::{Debug, LowerExp};
use num::FpCategory;

#[derive(Copy, Clone)]
pub struct Unpacked {
    pub sig: u64,
    pub k: i16,
}

impl Unpacked {
    pub fn new(sig: u64, k: i16) -> Self {
        Unpacked { sig, k }
    }
}

/// A helper trait to avoid duplicating basically all the conversion code for `f32` and `f64`.
///
/// See the parent module's doc comment for why this is necessary.
///
/// Should **never ever** be implemented for other types or be used outside the dec2flt module.
pub trait RawFloat
    : Copy
    + Debug
    + LowerExp
    + Mul<Output=Self>
    + Div<Output=Self>
    + Neg<Output=Self>
{
    const INFINITY: Self;
    const NAN: Self;
    const ZERO: Self;

    /// Type used by `to_bits` and `from_bits`.
    type Bits: Add<Output = Self::Bits> + From<u8> + TryFrom<u64>;

    /// Performs a raw transmutation to an integer.
    fn to_bits(self) -> Self::Bits;

    /// Performs a raw transmutation from an integer.
    fn from_bits(v: Self::Bits) -> Self;

    /// Returns the category that this number falls into.
    fn classify(self) -> FpCategory;

    /// Returns the mantissa, exponent and sign as integers.
    fn integer_decode(self) -> (u64, i16, i8);

    /// Decodes the float.
    fn unpack(self) -> Unpacked;

    /// Casts from a small integer that can be represented exactly. Panic if the integer can't be
    /// represented, the other code in this module makes sure to never let that happen.
    fn from_int(x: u64) -> Self;

    /// Gets the value 10<sup>e</sup> from a pre-computed table.
    /// Panics for `e >= CEIL_LOG5_OF_MAX_SIG`.
    fn short_fast_pow10(e: usize) -> Self;

    /// What the name says. It's easier to hard code than juggling intrinsics and
    /// hoping LLVM constant folds it.
    const CEIL_LOG5_OF_MAX_SIG: i16;

    // A conservative bound on the decimal digits of inputs that can't produce overflow or zero or
    /// subnormals. Probably the decimal exponent of the maximum normal value, hence the name.
    const MAX_NORMAL_DIGITS: usize;

    /// When the most significant decimal digit has a place value greater than this, the number
    /// is certainly rounded to infinity.
    const INF_CUTOFF: i64;

    /// When the most significant decimal digit has a place value less than this, the number
    /// is certainly rounded to zero.
    const ZERO_CUTOFF: i64;

    /// The number of bits in the exponent.
    const EXP_BITS: u8;

    /// The number of bits in the significand, *including* the hidden bit.
    const SIG_BITS: u8;

    /// The number of bits in the significand, *excluding* the hidden bit.
    const EXPLICIT_SIG_BITS: u8;

    /// The maximum legal exponent in fractional representation.
    const MAX_EXP: i16;

    /// The minimum legal exponent in fractional representation, excluding subnormals.
    const MIN_EXP: i16;

    /// `MAX_EXP` for integral representation, i.e., with the shift applied.
    const MAX_EXP_INT: i16;

    /// `MAX_EXP` encoded (i.e., with offset bias)
    const MAX_ENCODED_EXP: i16;

    /// `MIN_EXP` for integral representation, i.e., with the shift applied.
    const MIN_EXP_INT: i16;

    /// The maximum normalized significand in integral representation.
    const MAX_SIG: u64;

    /// The minimal normalized significand in integral representation.
    const MIN_SIG: u64;
}

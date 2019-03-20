#![stable(feature = "rust1", since = "1.0.0")]

mod arith;
mod bit;
mod deref;
mod drop;
mod function;
mod index;
mod range;
mod try;
mod unsize;

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::arith::{Add, Sub, Mul, Div, Rem, Neg};
#[stable(feature = "op_assign_traits", since = "1.8.0")]
pub use self::arith::{AddAssign, SubAssign, MulAssign, DivAssign, RemAssign};

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::bit::{Not, BitAnd, BitOr, BitXor, Shl, Shr};
#[stable(feature = "op_assign_traits", since = "1.8.0")]
pub use self::bit::{BitAndAssign, BitOrAssign, BitXorAssign, ShlAssign, ShrAssign};

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::deref::{Deref, DerefMut};

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::drop::Drop;

#[unstable(feature = "receiver_trait", issue = "0")]
pub use self::deref::Receiver;

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::function::{Fn, FnMut, FnOnce};

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::index::{Index, IndexMut};

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::range::{Range, RangeFrom, RangeFull, RangeTo};

#[stable(feature = "inclusive_range", since = "1.26.0")]
pub use self::range::{RangeInclusive, RangeToInclusive, RangeBounds, Bound};

#[unstable(feature = "try_trait", issue = "42327")]
pub use self::try::Try;

#[unstable(feature = "coerce_unsized", issue = "27732")]
pub use self::unsize::CoerceUnsized;

#[unstable(feature = "dispatch_from_dyn", issue = "0")]
pub use self::unsize::DispatchFromDyn;

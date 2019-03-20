#![stable(feature = "rust1", since = "1.0.0")]

mod arith;
mod bit;
mod deref;
mod drop;
mod function;
mod index;

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

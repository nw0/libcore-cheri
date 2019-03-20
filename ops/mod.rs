#![stable(feature = "rust1", since = "1.0.0")]

mod arith;
mod deref;
mod index;

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::arith::{Add, Sub, Mul, Div, Rem, Neg};
#[stable(feature = "op_assign_traits", since = "1.8.0")]
pub use self::arith::{AddAssign, SubAssign, MulAssign, DivAssign, RemAssign};

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::deref::{Deref, DerefMut};

#[unstable(feature = "receiver_trait", issue = "0")]
pub use self::deref::Receiver;

#[stable(feature = "rust1", since = "1.0.0")]
pub use self::index::{Index, IndexMut};

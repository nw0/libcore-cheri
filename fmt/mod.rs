#![stable(feature = "rust1", since = "1.0.0")]

use marker::PhantomData;
use result;

#[stable(feature = "rust1", since = "1.0.0")]
pub type Result = result::Result<(), Error>;

#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Copy, Clone, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Error;

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

#[allow(missing_debug_implementations)]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Formatter<'a> {
    flags: u32,
    fill: char,
    phantom: PhantomData<&'a ()>,
}

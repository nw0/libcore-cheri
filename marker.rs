#[lang = "sized"]
pub trait Sized {}

// This trait is also Clone
#[lang = "copy"]
pub trait Copy {}

#[lang = "sync"]
pub unsafe auto trait Sync {}

#[lang = "freeze"]
pub(crate) unsafe auto trait Freeze {}

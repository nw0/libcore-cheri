#[lang = "sized"]
pub trait Sized {}

// This trait is also Clone
#[lang = "copy"]
pub trait Copy {}

#[lang = "sync"]
pub unsafe auto trait Sync {}

#[lang = "freeze"]
pub(crate) unsafe auto trait Freeze {}

mod copy_impls {
    use super::{Copy,Sized};

    macro_rules! impl_copy {
        ($($t:ty)*) => {
            $(
                impl Copy for $t {}
            )*
        }
    }

    impl_copy! {
        usize u8 u16 u32 u64 u128
        isize i8 i16 i32 i64 i128
        f32 f64
        bool char
    }

    impl Copy for ! {}
    impl<T: ?Sized> Copy for *const T {}
    impl<T: ?Sized> Copy for *mut T {}
    impl<T: ?Sized> Copy for &T {}
}

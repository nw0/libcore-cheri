#![stable(feature = "rust1", since = "1.0.0")]

#[stable(feature = "rust1", since = "1.0.0")]
#[lang = "sized"]
#[fundamental]
pub trait Sized {}

#[stable(feature = "rust1", since = "1.0.0")]
#[lang = "copy"]
pub trait Copy : Clone {}

#[stable(feature = "rust1", since = "1.0.0")]
#[lang = "sync"]
pub unsafe auto trait Sync {}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> !Sync for *const T { }
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> !Sync for *mut T { }

#[lang = "phantom_data"]
#[structural_match]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct PhantomData<T:?Sized>;

#[lang = "freeze"]
pub(crate) unsafe auto trait Freeze {}

mod copy_impls {
    use super::{Copy,Sized};

    macro_rules! impl_copy {
        ($($t:ty)*) => {
            $(
                #[stable(feature = "rust1", since = "1.0.0")]
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

    #[unstable(feature = "never_type", issue = "35121")]
    impl Copy for ! {}

    #[stable(feature = "rust1", since = "1.0.0")]
    impl<T: ?Sized> Copy for *const T {}

    #[stable(feature = "rust1", since = "1.0.0")]
    impl<T: ?Sized> Copy for *mut T {}

    #[stable(feature = "rust1", since = "1.0.0")]
    impl<T: ?Sized> Copy for &T {}
}

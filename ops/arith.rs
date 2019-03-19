#[lang = "add"]
pub trait Add<RHS=Self> {
    type Output;

    #[must_use]
    fn add(self, rhs: RHS) -> Self::Output;
}

macro_rules! add_impl {
    ($($t:ty)*) => ($(
        impl Add for $t {
            type Output = $t;

            #[inline]
            #[rustc_inherit_overflow_checks]
            fn add(self, other: $t) -> $t { self + other }
        }

//         forward_ref_binop! { impl Add, add for $t, $t }
    )*)
}

add_impl! { usize u8 u16 u32 u64 u128 isize i8 i16 i32 i64 i128 f32 f64 }

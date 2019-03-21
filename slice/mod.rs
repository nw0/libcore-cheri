#![stable(feature = "rust1", since = "1.0.0")]

use ops::{FnMut, Try, self};

#[repr(C)]
union Repr<'a, T: 'a> {
    rust: &'a [T],
    rust_mut: &'a mut [T],
    raw: FatPtr<T>,
}

#[repr(C)]
struct FatPtr<T> {
    data: *const T,
    len: usize,
}

#[lang = "slice"]
impl<T> [T] {
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    #[rustc_const_unstable(feature = "const_slice_len")]
    pub const fn len(&self) -> usize {
        unsafe {
            Repr { rust: self }.raw.len
        }
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    #[rustc_const_unstable(feature = "const_slice_len")]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&I::Output>
        where I: SliceIndex<Self>
    {
        index.get(self)
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut I::Output>
        where I: SliceIndex<Self>
    {
        index.get_mut(self)
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub unsafe fn get_unchecked<I>(&self, index: I) -> &I::Output
        where I: SliceIndex<Self>
    {
        index.get_unchecked(self)
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub unsafe fn get_unchecked_mut<I>(&mut self, index: I) -> &mut I::Output
        where I: SliceIndex<Self>
    {
        index.get_unchecked_mut(self)
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self as *const [T] as *const T
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self as *mut [T] as *mut T
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_on_unimplemented = "slice indices are of type `usize` or ranges of `usize`"]
impl<T, I> ops::Index<I> for [T]
    where I: SliceIndex<[T]>
{
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_on_unimplemented = "slice indices are of type `usize` or ranges of `usize`"]
impl<T, I> ops::IndexMut<I> for [T]
    where I: SliceIndex<[T]>
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}

mod private_slice_index {
    use super::ops;
    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    pub trait Sealed {}

    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for usize {}
    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::Range<usize> {}
    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeTo<usize> {}
    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeFrom<usize> {}
    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeFull {}
    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeInclusive<usize> {}
    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeToInclusive<usize> {}
}

#[stable(feature = "slice_get_slice", since = "1.28.0")]
#[rustc_on_unimplemented = "slice indices are of type `usize` or ranges of `usize`"]
pub trait SliceIndex<T: ?Sized>: private_slice_index::Sealed {
    /// The output type returned by methods.
    #[stable(feature = "slice_get_slice", since = "1.28.0")]
    type Output: ?Sized;

    /// Returns a shared reference to the output at this location, if in
    /// bounds.
    #[unstable(feature = "slice_index_methods", issue = "0")]
    fn get(self, slice: &T) -> Option<&Self::Output>;

    /// Returns a mutable reference to the output at this location, if in
    /// bounds.
    #[unstable(feature = "slice_index_methods", issue = "0")]
    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;

    /// Returns a shared reference to the output at this location, without
    /// performing any bounds checking.
    #[unstable(feature = "slice_index_methods", issue = "0")]
    unsafe fn get_unchecked(self, slice: &T) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, without
    /// performing any bounds checking.
    #[unstable(feature = "slice_index_methods", issue = "0")]
    unsafe fn get_unchecked_mut(self, slice: &mut T) -> &mut Self::Output;

    /// Returns a shared reference to the output at this location, panicking
    /// if out of bounds.
    #[unstable(feature = "slice_index_methods", issue = "0")]
    fn index(self, slice: &T) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, panicking
    /// if out of bounds.
    #[unstable(feature = "slice_index_methods", issue = "0")]
    fn index_mut(self, slice: &mut T) -> &mut Self::Output;
}

#[stable(feature = "slice_get_slice_impls", since = "1.15.0")]
impl<T> SliceIndex<[T]> for usize {
    type Output = T;

    #[inline]
    fn get(self, slice: &[T]) -> Option<&T> {
        if self < slice.len() {
            unsafe {
                Some(self.get_unchecked(slice))
            }
        } else {
            None
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut T> {
        if self < slice.len() {
            unsafe {
                Some(self.get_unchecked_mut(slice))
            }
        } else {
            None
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: &[T]) -> &T {
        &*slice.as_ptr().add(self)
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: &mut [T]) -> &mut T {
        &mut *slice.as_mut_ptr().add(self)
    }

    #[inline]
    fn index(self, slice: &[T]) -> &T {
        // N.B., use intrinsic indexing
        &(*slice)[self]
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut T {
        // N.B., use intrinsic indexing
        &mut (*slice)[self]
    }
}

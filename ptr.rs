#![stable(feature = "rust1", since = "1.0.0")]

use intrinsics;

#[lang = "const_ptr"]
impl<T: ?Sized> *const T {
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub unsafe fn offset(self, count: isize) -> *const T where T: Sized {
        intrinsics::offset(self, count)
    }

    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline]
    pub unsafe fn add(self, count: usize) -> Self
        where T: Sized,
    {
        self.offset(count as isize)
    }
}

#[lang = "mut_ptr"]
impl<T: ?Sized> *mut T {
    #[stable(feature = "rust1", since = "1.0.0")]
    #[inline]
    pub unsafe fn offset(self, count: isize) -> *mut T where T: Sized {
        intrinsics::offset(self, count) as *mut T
    }

    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline]
    pub unsafe fn add(self, count: usize) -> Self
        where T: Sized,
    {
        self.offset(count as isize)
    }
}

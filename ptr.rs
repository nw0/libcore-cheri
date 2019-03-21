#![stable(feature = "rust1", since = "1.0.0")]

use intrinsics;
use mem::{self, MaybeUninit};

#[stable(feature = "rust1", since = "1.0.0")]
pub use intrinsics::copy_nonoverlapping;

#[stable(feature = "rust1", since = "1.0.0")]
pub use intrinsics::write_bytes;
#[inline]
#[stable(feature = "swap_nonoverlapping", since = "1.27.0")]
pub unsafe fn swap_nonoverlapping<T>(x: *mut T, y: *mut T, count: usize) {
    let x = x as *mut u8;
    let y = y as *mut u8;
    let len = mem::size_of::<T>() * count;
    swap_nonoverlapping_bytes(x, y, len)
}

#[inline]
pub(crate) unsafe fn swap_nonoverlapping_one<T>(x: *mut T, y: *mut T) {
    // For types smaller than the block optimization below,
    // just swap directly to avoid pessimizing codegen.
    if mem::size_of::<T>() < 32 {
        let z = read(x);
        copy_nonoverlapping(y, x, 1);
        write(y, z);
    } else {
        swap_nonoverlapping(x, y, 1);
    }
}

#[inline]
unsafe fn swap_nonoverlapping_bytes(x: *mut u8, y: *mut u8, len: usize) {
    // The approach here is to utilize simd to swap x & y efficiently. Testing reveals
    // that swapping either 32 bytes or 64 bytes at a time is most efficient for Intel
    // Haswell E processors. LLVM is more able to optimize if we give a struct a
    // #[repr(simd)], even if we don't actually use this struct directly.
    //
    // FIXME repr(simd) broken on emscripten and redox
    // It's also broken on big-endian powerpc64 and s390x.  #42778
    #[cfg_attr(not(any(target_os = "emscripten", target_os = "redox",
                       target_endian = "big")),
               repr(simd))]
    struct Block(u64, u64, u64, u64);
    struct UnalignedBlock(u64, u64, u64, u64);

    let block_size = mem::size_of::<Block>();

    // Loop through x & y, copying them `Block` at a time
    // The optimizer should unroll the loop fully for most types
    // N.B. We can't use a for loop as the `range` impl calls `mem::swap` recursively
    let mut i = 0;
    while i + block_size <= len {
        // Create some uninitialized memory as scratch space
        // Declaring `t` here avoids aligning the stack when this loop is unused
        let mut t = mem::MaybeUninit::<Block>::uninitialized();
        let t = t.as_mut_ptr() as *mut u8;
        let x = x.add(i);
        let y = y.add(i);

        // Swap a block of bytes of x & y, using t as a temporary buffer
        // This should be optimized into efficient SIMD operations where available
        copy_nonoverlapping(x, t, block_size);
        copy_nonoverlapping(y, x, block_size);
        copy_nonoverlapping(t, y, block_size);
        i += block_size;
    }

    if i < len {
        // Swap any remaining bytes
        let mut t = mem::MaybeUninit::<UnalignedBlock>::uninitialized();
        let rem = len - i;

        let t = t.as_mut_ptr() as *mut u8;
        let x = x.add(i);
        let y = y.add(i);

        copy_nonoverlapping(x, t, rem);
        copy_nonoverlapping(y, x, rem);
        copy_nonoverlapping(t, y, rem);
    }
}

#[stable(feature = "drop_in_place", since = "1.8.0")]
#[inline(always)]
pub unsafe fn drop_in_place<T: ?Sized>(to_drop: *mut T) {
    real_drop_in_place(&mut *to_drop)
}

#[lang = "drop_in_place"]
#[allow(unconditional_recursion)]
unsafe fn real_drop_in_place<T: ?Sized>(to_drop: &mut T) {
    // Code here does not matter - this is replaced by the
    // real drop glue by the compiler.
    real_drop_in_place(to_drop)
}

#[inline]
#[stable(feature = "rust1", since = "1.0.0")]
pub unsafe fn read<T>(src: *const T) -> T {
    let mut tmp = MaybeUninit::<T>::uninitialized();
    copy_nonoverlapping(src, tmp.as_mut_ptr(), 1);
    tmp.into_inner()
}

#[inline]
#[stable(feature = "rust1", since = "1.0.0")]
pub unsafe fn write<T>(dst: *mut T, src: T) {
    intrinsics::move_val_init(&mut *dst, src)
}

#[inline]
#[stable(feature = "ptr_unaligned", since = "1.17.0")]
pub unsafe fn read_unaligned<T>(src: *const T) -> T {
    let mut tmp = MaybeUninit::<T>::uninitialized();
    copy_nonoverlapping(src as *const u8,
                        tmp.as_mut_ptr() as *mut u8,
                        mem::size_of::<T>());
    tmp.into_inner()
}

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

    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline]
    pub unsafe fn read_unaligned(self) -> T
        where T: Sized,
    {
        read_unaligned(self)
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

    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline]
    pub unsafe fn write_bytes(self, val: u8, count: usize)
        where T: Sized,
    {
        write_bytes(self, val, count)
    }

    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline]
    pub unsafe fn drop_in_place(self) {
        drop_in_place(self)
    }

    #[stable(feature = "pointer_methods", since = "1.26.0")]
    #[inline]
    pub unsafe fn read_unaligned(self) -> T
        where T: Sized,
    {
        read_unaligned(self)
    }
}

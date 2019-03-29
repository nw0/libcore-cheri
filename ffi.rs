#![stable(feature = "", since = "1.30.0")]

#![allow(non_camel_case_types)]

//! Utilities related to FFI bindings.

use ::fmt;

/// Equivalent to C's `void` type when used as a [pointer].
///
/// In essence, `*const c_void` is equivalent to C's `const void*`
/// and `*mut c_void` is equivalent to C's `void*`. That said, this is
/// *not* the same as C's `void` return type, which is Rust's `()` type.
///
/// To model pointers to opaque types in FFI, until `extern type` is
/// stabilized, it is recommended to use a newtype wrapper around an empty
/// byte array. See the [Nomicon] for details.
///
/// [pointer]: ../../std/primitive.pointer.html
/// [Nomicon]: https://doc.rust-lang.org/nomicon/ffi.html#representing-opaque-structs
// N.B., for LLVM to recognize the void pointer type and by extension
//     functions like malloc(), we need to have it represented as i8* in
//     LLVM bitcode. The enum used here ensures this and prevents misuse
//     of the "raw" type by only having private variants. We need two
//     variants, because the compiler complains about the repr attribute
//     otherwise and we need at least one variant as otherwise the enum
//     would be uninhabited and at least dereferencing such pointers would
//     be UB.
#[repr(u8)]
#[stable(feature = "raw_os", since = "1.1.0")]
pub enum c_void {
    #[unstable(feature = "c_void_variant", reason = "temporary implementation detail",
               issue = "0")]
    #[doc(hidden)] __variant1,
    #[unstable(feature = "c_void_variant", reason = "temporary implementation detail",
               issue = "0")]
    #[doc(hidden)] __variant2,
}

#[stable(feature = "std_debug", since = "1.16.0")]
impl fmt::Debug for c_void {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("c_void")
    }
}

/// Basic implementation of a `va_list`.
#[cfg(any(all(not(target_arch = "aarch64"), not(target_arch = "powerpc"),
              not(target_arch = "x86_64")),
          all(target_arch = "aarch4", target_os = "ios"),
          windows))]
#[unstable(feature = "c_variadic",
           reason = "the `c_variadic` feature has not been properly tested on \
                     all supported platforms",
           issue = "44930")]
extern {
    type VaListImpl;
}

#[cfg(any(all(not(target_arch = "aarch64"), not(target_arch = "powerpc"),
              not(target_arch = "x86_64")),
          windows))]
impl fmt::Debug for VaListImpl {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "va_list* {:p}", self)
    }
}

/// x86_64 ABI implementation of a `va_list`.
#[cfg(all(target_arch = "x86_64", not(windows)))]
#[repr(C)]
#[unstable(feature = "c_variadic",
           reason = "the `c_variadic` feature has not been properly tested on \
                     all supported platforms",
           issue = "44930")]
struct VaListImpl {
    gp_offset: i32,
    fp_offset: i32,
    overflow_arg_area: *mut c_void,
    reg_save_area: *mut c_void,
}

/// A wrapper for a `va_list`
#[lang = "va_list"]
#[unstable(feature = "c_variadic",
           reason = "the `c_variadic` feature has not been properly tested on \
                     all supported platforms",
           issue = "44930")]
#[repr(transparent)]
pub struct VaList<'a>(&'a mut VaListImpl);

// The VaArgSafe trait needs to be used in public interfaces, however, the trait
// itself must not be allowed to be used outside this module. Allowing users to
// implement the trait for a new type (thereby allowing the va_arg intrinsic to
// be used on a new type) is likely to cause undefined behavior.
//
// FIXME(dlrobertson): In order to use the VaArgSafe trait in a public interface
// but also ensure it cannot be used elsewhere, the trait needs to be public
// within a private module. Once RFC 2145 has been implemented look into
// improving this.
mod sealed_trait {
    /// Trait which whitelists the allowed types to be used with [VaList::arg]
    ///
    /// [VaList::va_arg]: struct.VaList.html#method.arg
    #[unstable(feature = "c_variadic",
               reason = "the `c_variadic` feature has not been properly tested on \
                         all supported platforms",
               issue = "44930")]
    pub trait VaArgSafe {}
}

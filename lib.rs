// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
// This library, libcore_cheri, is intended to contain a minimal set
// of Rust libcore code to work with CHERI temporarily.

#![stable(feature = "core", since = "1.6.0")]

#![no_core]

#![feature(allow_internal_unstable)]
#![feature(arbitrary_self_types)]
#![feature(asm)]
#![feature(associated_type_defaults)]
#![feature(cfg_target_has_atomic)]
#![feature(concat_idents)]
#![feature(const_fn)]
// #![feature(const_int_ops)]
#![feature(const_fn_union)]
#![feature(custom_attribute)]
#![feature(doc_cfg)]
#![feature(doc_spotlight)]
#![feature(extern_types)]
#![feature(fundamental)]
#![feature(intrinsics)]
#![feature(lang_items)]
#![feature(link_llvm_intrinsics)]
#![feature(never_type)]
#![feature(nll)]
#![feature(bind_by_move_pattern_guards)]
#![feature(exhaustive_patterns)]
#![feature(no_core)]
#![feature(on_unimplemented)]
#![feature(optin_builtin_traits)]
#![feature(prelude_import)]
#![feature(repr_simd, platform_intrinsics)]
#![feature(rustc_attrs)]
#![feature(rustc_const_unstable)]
#![feature(simd_ffi)]
#![feature(specialization)]
#![feature(staged_api)]
#![feature(stmt_expr_attributes)]
#![feature(unboxed_closures)]
#![feature(unsized_locals)]
#![feature(untagged_unions)]
#![feature(unwind_attributes)]
#![feature(doc_alias)]
#![feature(mmx_target_feature)]
#![feature(tbm_target_feature)]
#![feature(sse4a_target_feature)]
#![feature(arm_target_feature)]
#![feature(powerpc_target_feature)]
#![feature(mips_target_feature)]
#![feature(aarch64_target_feature)]
#![feature(wasm_target_feature)]
// #![feature(const_slice_len)]
// #![feature(const_str_as_bytes)]
// #![feature(const_str_len)]
// #![feature(const_int_rotate)]
// #![feature(const_int_wrapping)]
// #![feature(const_int_sign)]
// #![feature(const_int_conversion)]
#![feature(const_transmute)]
// #![feature(reverse_bits)]
#![feature(non_exhaustive)]
#![feature(structural_match)]

#[prelude_import]
#[allow(unused)]
use prelude::*;

#[macro_use]
mod internal_macros;

/* The libcore prelude, not as all-encompassing as the libstd prelude */
pub mod prelude;

/* Core language traits */
pub mod marker;
pub mod ops;
pub mod clone;
pub mod default;
pub mod borrow;

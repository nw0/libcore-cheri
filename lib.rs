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

#![no_core]

#![feature(never_type)]
#![feature(no_core)]
#![feature(lang_items)]
#![feature(optin_builtin_traits)]
#![feature(rustc_attrs)]

#[macro_use]
mod internal_macros;

/* Core language traits */
pub mod marker;
pub mod ops;

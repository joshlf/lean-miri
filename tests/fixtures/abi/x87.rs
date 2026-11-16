#![no_std]
#![feature(x87_f80)]

use core::arch::x86_64::x87_f80;

#[repr(transparent)]
pub struct Transparent(pub x87_f80);
#[repr(C)]
pub struct Pair(pub x87_f80, pub u64);
#[repr(C)]
pub union Mixed {
    pub float: x87_f80,
    pub double: f64,
}

#[unsafe(no_mangle)]
pub extern "C" fn aligned(value: x87_f80) -> x87_f80 { value }
#[unsafe(no_mangle)]
pub extern "C" fn transparent(value: Transparent) -> Transparent { value }
#[unsafe(no_mangle)]
pub extern "C" fn aggregate(value: Pair) -> Pair { value }
#[unsafe(no_mangle)]
pub extern "C" fn mixed(value: Mixed) -> Mixed { value }

#[unsafe(no_mangle)]
pub fn higher_ranked(_: for<'a> fn(&'a u8) -> &'a u8) {}

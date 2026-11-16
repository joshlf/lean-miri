#![no_std]
#![no_main]
#![feature(cfi_encoding)]

#[repr(C)]
#[derive(Clone, Copy)]
#[cfi_encoding = "4Twin"]
pub struct First { x: u32, y: u32 }
#[repr(C)]
#[derive(Clone, Copy)]
#[cfi_encoding = "4Twin"]
pub struct Second { x: u32, y: u32 }

#[inline(never)]
extern "C" fn identity(value: First) -> First { value }

#[unsafe(no_mangle)]
pub fn miri_start(_: isize, _: *const *const u8) -> isize {
    let function: extern "C" fn(Second) -> Second = unsafe {
        core::mem::transmute(identity as extern "C" fn(First) -> First)
    };
    let result = function(Second { x: 2, y: 6 });
    if result.x == 2 && result.y == 6 { 0 } else { 1 }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

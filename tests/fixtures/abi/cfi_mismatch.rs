#![no_std]
#![no_main]
#![feature(cfi_encoding)]

#[repr(C)]
#[cfi_encoding = "Other"]
pub struct Encoded { x: u32, y: u32 }
#[repr(C)]
pub struct Other { x: u32, y: u32 }

#[inline(never)]
extern "C" fn identity(value: Encoded) -> Encoded { value }

#[unsafe(no_mangle)]
pub fn miri_start(_: isize, _: *const *const u8) -> isize {
    let function: extern "C" fn(Other) -> Other = unsafe {
        core::mem::transmute(identity as extern "C" fn(Encoded) -> Encoded)
    };
    let result = function(Other { x: 2, y: 6 });
    if result.x == 2 && result.y == 6 { 0 } else { 1 }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

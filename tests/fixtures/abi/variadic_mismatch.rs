#![no_std]
#![no_main]
#![feature(c_variadic)]

#[inline(never)]
unsafe extern "C" fn fixed(_: u32) -> u64 { 0 }

#[unsafe(no_mangle)]
pub fn miri_start(_: isize, _: *const *const u8) -> isize {
    let function: unsafe extern "C" fn(u32, ...) -> u64 = unsafe {
        core::mem::transmute(fixed as unsafe extern "C" fn(u32) -> u64)
    };
    unsafe { function(1, 10u64) as isize }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

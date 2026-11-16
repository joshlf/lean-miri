#![no_std]
#![no_main]
#![feature(c_variadic)]

#[inline(never)]
unsafe extern "C" fn collect(_: u32, mut values: ...) -> u64 {
    let first = unsafe { values.next_arg::<u64>() };
    let second = unsafe { values.next_arg::<u64>() };
    first.wrapping_add(second)
}

#[unsafe(no_mangle)]
pub fn miri_start(_: isize, _: *const *const u8) -> isize {
    let value = unsafe { collect(2, 10u64, 20u64) };
    if value == 30 { 0 } else { 1 }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

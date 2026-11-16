#![no_std]
#![no_main]

pub struct Large([u64; 8]);

#[inline(never)]
pub fn transfer(mut value: Large) -> Large {
    value.0[0] = value.0[0].wrapping_add(1);
    value
}

#[unsafe(no_mangle)]
pub fn miri_start(argc: isize, _: *const *const u8) -> isize {
    let value = transfer(Large([argc as u64; 8]));
    if value.0[0] == (argc as u64).wrapping_add(1) { 0 } else { 1 }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

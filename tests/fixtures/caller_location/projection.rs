#![no_std]
#![no_main]

use core::panic::Location;
unsafe extern "Rust" {
    fn miri_get_alloc_id(pointer: *const ()) -> u64;
    fn miri_write_to_stdout(bytes: &[u8]);
}
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

fn emit_ids(root: u64, file: u64) {
    let mut bytes = *b"caller-ids:0000000000000000:0000000000000000\n";
    for index in 0..16 {
        let shift = 4 * (15 - index);
        bytes[11 + index] = b"0123456789abcdef"[((root >> shift) & 15) as usize];
        bytes[28 + index] = b"0123456789abcdef"[((file >> shift) & 15) as usize];
    }
    unsafe { miri_write_to_stdout(&bytes); }
}

#[track_caller]
#[inline(never)]
fn forward() -> &'static Location<'static> { Location::caller() }

macro_rules! observe {
    () => { (forward(), file!(), line!(), column!()) };
}

#[unsafe(no_mangle)]
pub fn miri_start(_: isize, _: *const *const u8) -> isize {
    let mut previous_root = 0;
    let mut previous_file = 0;
    let mut round = 0;
    while round < 3 {
        let π = 7;	let (location, file, line, column) = observe!();
        let expected_file = if cfg!(redact_file) { "<redacted>" } else { file };
        let expected_line = if cfg!(redact_line) { 0 } else { line };
        // rustc caller locations display a tab as four columns; column! counts one character.
        let expected_column = if cfg!(redact_column) { 0 } else { column + 3 };
        if π != 7 { return 10; }
        if location.file() != expected_file { return 11; }
        if location.line() != expected_line { return 12; }
        if location.column() != expected_column { return 13; }
        let root = unsafe { miri_get_alloc_id((location as *const Location<'_>).cast()) };
        let filename = unsafe { miri_get_alloc_id(location.file().as_ptr().cast()) };
        if round != 0 && (root == previous_root || filename != previous_file) { return 2; }
        let ordinary_filename = if cfg!(redact_file) { "<redacted>\0" } else { concat!(file!(), "\0") };
        let ordinary_id = unsafe { miri_get_alloc_id(ordinary_filename.as_ptr().cast()) };
        if ordinary_id != filename { return 3; }
        emit_ids(root, filename);
        previous_root = root;
        previous_file = filename;
        round += 1;
    }
    0
}

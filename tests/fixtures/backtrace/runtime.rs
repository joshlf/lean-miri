#![no_main]

#[repr(C)]
struct MiriFrame {
    name_len: usize,
    filename_len: usize,
    lineno: u32,
    colno: u32,
    fn_ptr: *mut core::ffi::c_void,
}
unsafe extern "Rust" {
    fn miri_backtrace_size(flags: u64) -> usize;
    fn miri_get_backtrace(flags: u64, buffer: *mut *mut ());
    fn miri_resolve_frame(frame: *mut (), flags: u64) -> MiriFrame;
    fn miri_resolve_frame_names(frame: *mut (), flags: u64, name: *mut u8, filename: *mut u8);
    fn miri_get_alloc_id(pointer: *const ()) -> u64;
    fn miri_write_to_stdout(bytes: &[u8]);
}

fn emit(round: u64, index: usize, function: u64, position: u64, resolved: &MiriFrame,
    name: &[u8], filename: &[u8]) {
    let header = [round.to_le(), (index as u64).to_le(), function.to_le(), position.to_le(),
        (resolved.lineno as u64).to_le(), (resolved.colno as u64).to_le(),
        (name.len() as u64).to_le(), (filename.len() as u64).to_le()];
    let mut output = [0u8; 2048];
    let prefix = b"\0backtrace-event\xff";
    let suffix = b"\xffbacktrace-end\0\n";
    let mut used = 0;
    unsafe {
        core::ptr::copy_nonoverlapping(prefix.as_ptr(), output.as_mut_ptr(), prefix.len());
        used += prefix.len();
        core::ptr::copy_nonoverlapping(header.as_ptr().cast::<u8>(), output.as_mut_ptr().add(used), 64);
        used += 64;
        core::ptr::copy_nonoverlapping(name.as_ptr(), output.as_mut_ptr().add(used), name.len());
        used += name.len();
        core::ptr::copy_nonoverlapping(filename.as_ptr(), output.as_mut_ptr().add(used), filename.len());
        used += filename.len();
        core::ptr::copy_nonoverlapping(suffix.as_ptr(), output.as_mut_ptr().add(used), suffix.len());
        used += suffix.len();
        miri_write_to_stdout(&output[..used]);
    }
}

// All captured functions are nongeneric and inline(never), so pinned Miri gives them unique function allocation identities.
#[inline(never)]
fn capture(round: u64) -> isize {
    let count = unsafe { miri_backtrace_size(0) };
    if count == 0 || count > 64 { return 1; }
    let mut frames = [core::ptr::null_mut(); 64];
    unsafe { miri_get_backtrace(1, frames.as_mut_ptr()); }
    for index in 0..count {
        let frame = frames[index];
        let resolved = unsafe { miri_resolve_frame(frame, 1) };
        if resolved.name_len > 512 || resolved.filename_len > 512 { return 2; }
        let mut name = [0; 512];
        let mut filename = [0; 512];
        unsafe { miri_resolve_frame_names(frame, 0, name.as_mut_ptr(), filename.as_mut_ptr()); }
        let function = unsafe { miri_get_alloc_id(resolved.fn_ptr.cast()) };
        if function != unsafe { miri_get_alloc_id(frame) } { return 4; }
        let position = frame.addr().wrapping_sub(resolved.fn_ptr.addr()) as u64;
        emit(round, index, function, position, &resolved,
            &name[..resolved.name_len], &filename[..resolved.filename_len]);
    }
    0
}

#[collapse_debuginfo(no)]
macro_rules! visible { ($round:expr) => { capture($round) }; }
#[collapse_debuginfo(yes)]
macro_rules! collapsed { ($round:expr) => { visible!($round) }; }
#[collapse_debuginfo(no)]
macro_rules! nested { ($round:expr) => { collapsed!($round) }; }

#[collapse_debuginfo(yes)]
macro_rules! define_generated {
    () => { #[inline(never)] fn generated() -> isize { visible!(3) } };
}
define_generated!();

#[inline(never)]
fn deep(depth: u32) -> isize {
    if depth == 0 { nested!(2) } else { deep(depth - 1) }
}

#[collapse_debuginfo(no)]
macro_rules! scope_0 { () => { capture(4) }; }

#[collapse_debuginfo(yes)]
macro_rules! scope_1 { () => { scope_0!() }; }

#[collapse_debuginfo(no)]
macro_rules! scope_2 { () => { scope_1!() }; }

#[collapse_debuginfo(yes)]
macro_rules! scope_3 { () => { scope_2!() }; }

#[collapse_debuginfo(no)]
macro_rules! scope_4 { () => { scope_3!() }; }

#[collapse_debuginfo(yes)]
macro_rules! scope_5 { () => { scope_4!() }; }

#[collapse_debuginfo(no)]
macro_rules! scope_6 { () => { scope_5!() }; }

#[collapse_debuginfo(yes)]
macro_rules! scope_7 { () => { scope_6!() }; }

#[collapse_debuginfo(no)]
macro_rules! scope_8 { () => { scope_7!() }; }

#[collapse_debuginfo(yes)]
macro_rules! scope_9 { () => { scope_8!() }; }

#[collapse_debuginfo(no)]
macro_rules! scope_10 { () => { scope_9!() }; }

#[collapse_debuginfo(yes)]
macro_rules! scope_11 { () => { scope_10!() }; }

#[collapse_debuginfo(no)]
macro_rules! scope_12 { () => { scope_11!() }; }

#[collapse_debuginfo(yes)]
macro_rules! scope_13 { () => { scope_12!() }; }

#[collapse_debuginfo(no)]
macro_rules! scope_14 { () => { scope_13!() }; }

#[collapse_debuginfo(yes)]
macro_rules! scope_15 { () => { scope_14!() }; }

#[unsafe(no_mangle)]
#[inline(never)]
pub fn miri_start(_: isize, _: *const *const u8) -> isize {
    let π = 7;	let first = collapsed!(0);
    if π != 7 || first != 0 { return 3; }
    let second = nested!(1);
    if second != 0 { return second; }
    let third = deep(12);
    if third != 0 { return third; }
    let fourth = generated();
    if fourth != 0 { return fourth; }
    scope_15!()
}

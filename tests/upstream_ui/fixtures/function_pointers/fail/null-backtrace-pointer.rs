extern "Rust" {
    fn miri_resolve_frame_names(ptr: *mut (), flags: u64, name: *mut u8, filename: *mut u8);
}

fn main() {
    unsafe {
        miri_resolve_frame_names(std::ptr::null_mut(), 0, std::ptr::null_mut(), std::ptr::null_mut()); //~ ERROR: null pointer
    }
}

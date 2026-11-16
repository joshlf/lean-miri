//@only-target: x86_64-unknown-linux-gnu
use std::sync::atomic::{AtomicUsize, Ordering::SeqCst};

static PHASE: AtomicUsize = AtomicUsize::new(0);
extern "C" {
    fn pthread_key_create(key: *mut u32, destructor: Option<unsafe extern "C" fn(*mut ())>) -> i32;
    fn pthread_setspecific(key: u32, value: *const ()) -> i32;
    fn pthread_key_delete(key: u32) -> i32;
}
unsafe extern "C" fn pthread_destructor(_: *mut ()) {
    assert_eq!(PHASE.swap(2, SeqCst), 1);
}
struct Native;
impl Drop for Native {
    fn drop(&mut self) {
        assert_eq!(PHASE.swap(1, SeqCst), 0);
    }
}
thread_local! { static NATIVE: Native = const { Native }; }
fn main() {
    let key = std::thread::spawn(|| unsafe {
        let mut key = 0;
        assert_eq!(pthread_key_create(&mut key, Some(pthread_destructor)), 0);
        assert_eq!(pthread_setspecific(key, std::ptr::without_provenance(1)), 0);
        NATIVE.with(|_| {});
        key
    }).join().unwrap();
    assert_eq!(PHASE.load(SeqCst), 2);
    unsafe { assert_eq!(pthread_key_delete(key), 0); }
}

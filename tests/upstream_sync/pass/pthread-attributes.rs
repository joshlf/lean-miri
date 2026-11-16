//@only-target: x86_64-unknown-linux-gnu
use std::mem::MaybeUninit;

extern "C" {
    fn pthread_mutexattr_init(attr: *mut u8) -> i32;
    fn pthread_mutexattr_settype(attr: *mut u8, kind: i32) -> i32;
    fn pthread_mutexattr_destroy(attr: *mut u8) -> i32;
    fn pthread_mutex_init(mutex: *mut u8, attr: *const u8) -> i32;
    fn pthread_mutex_lock(mutex: *mut u8) -> i32;
    fn pthread_mutex_unlock(mutex: *mut u8) -> i32;
    fn pthread_mutex_destroy(mutex: *mut u8) -> i32;
    fn pthread_condattr_init(attr: *mut u8) -> i32;
    fn pthread_condattr_setclock(attr: *mut u8, clock: i32) -> i32;
    fn pthread_condattr_getclock(attr: *const u8, clock: *mut i32) -> i32;
    fn pthread_condattr_destroy(attr: *mut u8) -> i32;
}

fn main() {
    // Exact Linux x86_64 pthread storage sizes; this fixture is target restricted.
    let mut mutex_attr = MaybeUninit::<[u32; 1]>::uninit();
    let mut mutex = MaybeUninit::<[u64; 5]>::uninit();
    let mut cond_attr = MaybeUninit::<[u32; 1]>::uninit();
    unsafe {
        let attr = mutex_attr.as_mut_ptr().cast();
        let mutex = mutex.as_mut_ptr().cast();
        assert_eq!(pthread_mutexattr_init(attr), 0);
        assert_eq!(pthread_mutexattr_settype(attr, 1), 0); // PTHREAD_MUTEX_RECURSIVE
        assert_eq!(pthread_mutex_init(mutex, attr), 0);
        assert_eq!(pthread_mutexattr_destroy(attr), 0);
        assert_eq!(pthread_mutex_lock(mutex), 0);
        assert_eq!(pthread_mutex_lock(mutex), 0);
        assert_eq!(pthread_mutex_unlock(mutex), 0);
        assert_eq!(pthread_mutex_unlock(mutex), 0);
        assert_eq!(pthread_mutex_destroy(mutex), 0);
        let attr = cond_attr.as_mut_ptr().cast();
        assert_eq!(pthread_condattr_init(attr), 0);
        let mut clock = -1;
        assert_eq!(pthread_condattr_getclock(attr, &mut clock), 0);
        assert_eq!(clock, 0); // CLOCK_REALTIME
        assert_eq!(pthread_condattr_setclock(attr, 1), 0); // CLOCK_MONOTONIC
        assert_eq!(pthread_condattr_getclock(attr, &mut clock), 0);
        assert_eq!(clock, 1);
        assert_eq!(pthread_condattr_destroy(attr), 0);
    }
}

#![no_std]
#![feature(coroutines, coroutine_trait)]

pub async fn saved_cell() -> u32 {
    let cell = core::cell::UnsafeCell::new(7);
    core::future::pending::<()>().await;
    unsafe { *cell.get() }
}

pub async fn saved_scalar() -> u32 {
    let value = 7;
    core::future::pending::<()>().await;
    value
}

pub async fn captured_cell(cell: core::cell::UnsafeCell<u32>) -> u32 {
    core::future::pending::<()>().await;
    unsafe { *cell.get() }
}

pub fn movable() -> impl core::ops::Coroutine<Yield = (), Return = ()> {
    #[coroutine]
    || {
        let pinned = core::marker::PhantomPinned;
        yield ();
        core::hint::black_box(pinned);
    }
}

pub fn root() -> (
    impl core::future::Future<Output = u32>,
    impl core::future::Future<Output = u32>,
    impl core::future::Future<Output = u32>,
    impl core::ops::Coroutine<Yield = (), Return = ()>,
) {
    (
        saved_cell(),
        saved_scalar(),
        captured_cell(core::cell::UnsafeCell::new(7)),
        movable(),
    )
}

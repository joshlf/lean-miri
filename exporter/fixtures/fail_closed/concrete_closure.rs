#![no_std]

pub struct UncalledDrop;

pub struct SizedTail<T>(T);
pub struct UnsizedTail<T: ?Sized>(T);

impl Drop for UncalledDrop {
    fn drop(&mut self) {}
}

fn uncalled() {}

fn identity<T>(value: T) -> T {
    value
}

pub fn root(
    _pointer: *const UncalledDrop,
    _sized: *const SizedTail<u32>,
    _unsized: *const UnsizedTail<u32>,
) -> u32 {
    let function = uncalled;
    let _reference = &function;
    identity(7_u32)
}

pub fn pointer_root() -> fn() {
    uncalled
}

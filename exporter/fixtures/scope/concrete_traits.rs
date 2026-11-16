#![no_std]

use core::cell::{Cell, UnsafeCell};
use core::marker::{PhantomData, PhantomPinned};
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ptr::NonNull;

pub struct UnsizedTail<T: ?Sized>(T);
pub struct Pinned(PhantomPinned);
pub struct Dropper;
impl Drop for Dropper {
    fn drop(&mut self) {}
}
pub struct Manual<T>(ManuallyDrop<T>);
pub struct Explicit<T>(T);
impl<T> Unpin for Explicit<T> {}
pub struct Conditional<T>(PhantomData<fn() -> T>);
impl<T: Unpin> Unpin for Conditional<T> {}

pub fn root(
    _: &UnsafeCell<u32>,
    _: &Cell<u8>,
    _: &Pinned,
    _: &PhantomData<*const u32>,
    _: &Manual<Dropper>,
    _: &MaybeUninit<UnsafeCell<u32>>,
    _: &UnsizedTail<[u8]>,
    _: NonNull<u8>,
    _: Option<&u32>,
    _: &Explicit<PhantomPinned>,
    _: &Conditional<PhantomPinned>,
) {
}

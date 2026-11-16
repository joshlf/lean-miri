#![no_std]

use core::marker::PhantomData;

pub trait Marker<T> {}
pub trait Super<T> {}
pub trait Sub: Super<u8> {}

pub struct Direct<T: ?Sized>(PhantomData<*const T>);
impl<T: ?Sized + Marker<u16>> Unpin for Direct<T> {}
pub struct Inherited<T: ?Sized>(PhantomData<*const T>);
impl<T: ?Sized + Super<u16>> Unpin for Inherited<T> {}
pub struct Matching<T: ?Sized>(PhantomData<*const T>);
impl<T: ?Sized + Super<u8>> Unpin for Matching<T> {}

pub fn root(
    _: &Direct<dyn Marker<u8>>,
    _: &Direct<dyn Marker<u16>>,
    _: &Inherited<dyn Sub>,
    _: &Matching<dyn Sub>,
) {
}

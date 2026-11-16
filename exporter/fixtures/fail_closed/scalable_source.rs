#![no_core]
#![feature(no_core, lang_items, rustc_attrs, auto_traits)]
#![allow(internal_features)]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
#[lang = "freeze"]
pub unsafe auto trait Freeze {}
#[lang = "unpin"]
pub auto trait Unpin {}
#[lang = "unsafe_unpin"]
pub unsafe auto trait UnsafeUnpin {}

#[rustc_scalable_vector(3)]
pub struct Vector(u32);

#[rustc_scalable_vector]
pub struct Vector8(
    Vector,
    Vector,
    Vector,
    Vector,
    Vector,
    Vector,
    Vector,
    Vector,
);

pub fn root(_: &Vector8) {}

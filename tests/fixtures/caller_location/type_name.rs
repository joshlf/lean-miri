#![no_std]

pub fn root() -> &'static str { core::any::type_name::<u32>() }

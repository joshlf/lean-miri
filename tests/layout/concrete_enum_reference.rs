#![allow(dead_code)]
use std::convert::Infallible;
use std::mem::{align_of, size_of};
use std::num::NonZeroU32;

enum Direct {
    A(u64),
    B(u64),
}
#[repr(C)]
enum C {
    A(u8),
    B(u64),
}
#[repr(i8)]
enum Signed {
    A = -1,
    B = 1,
}
#[repr(u64)]
enum Unsigned {
    A = 0,
    B = 1 << 63,
}
enum Absent {
    A(Infallible),
    B(u32),
}
enum Partial {
    A(Infallible, u32),
    B(u8),
}

fn main() {
    macro_rules! case {
        ($name:literal, $ty:ty) => {
            println!("{} {} {}", $name, size_of::<$ty>(), align_of::<$ty>());
        };
    }
    case!("bool", Option<bool>);
    case!("nonzero", Option<NonZeroU32>);
    case!("reference", Option<&'static u8>);
    case!("direct", Direct);
    case!("c", C);
    case!("signed", Signed);
    case!("unsigned", Unsigned);
    case!("absent", Absent);
    case!("partial", Partial);
}

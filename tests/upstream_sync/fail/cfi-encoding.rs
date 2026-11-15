#![feature(cfi_encoding)]

mod encoded {
    #[repr(C)]
    #[cfi_encoding = "4Same"]
    pub struct Same(pub i32, pub i32);
}
mod plain {
    #[repr(C)]
    pub struct Same(pub i32, pub i32);
}
extern "C" fn take(_: encoded::Same) {}
fn main() {
    // Equal fields and item names do not erase the presence of a CFI encoding.
    let f: extern "C" fn(plain::Same) = unsafe { std::mem::transmute(take as extern "C" fn(encoded::Same)) };
    f(plain::Same(1, 2)); //~ ERROR: calling a function whose parameter
}

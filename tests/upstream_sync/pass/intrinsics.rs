#![feature(core_intrinsics)]
#![allow(internal_features)]

fn main() {
    // Keep values dynamic so that execution reaches the generic intrinsics.
    let x = std::hint::black_box(4.0f64);
    assert_eq!(core::intrinsics::sqrt(x), 2.0);
    assert_eq!(core::intrinsics::floor(x + 0.75), 4.0);
    assert_eq!(core::intrinsics::ceil(-x - 0.75), -4.0);
    assert_eq!(core::intrinsics::trunc(-x - 0.75), -4.0);
    assert_eq!(core::intrinsics::round_ties_even(x + 0.5), 4.0);
    assert_eq!(core::intrinsics::powi(x, 0), 1.0);
    assert_eq!(core::intrinsics::powf(x, 0.0), 1.0);
    let a = std::hint::black_box(0x1234u16);
    let b = std::hint::black_box(0x5678u16);
    unsafe {
        assert_eq!(core::intrinsics::unchecked_funnel_shl(a, b, 4), 0x2345);
        assert_eq!(core::intrinsics::unchecked_funnel_shr(a, b, 4), 0x4567);
        assert_eq!(core::intrinsics::unchecked_funnel_shl(a, b, 0), a);
        assert_eq!(core::intrinsics::unchecked_funnel_shr(a, b, 0), b);
    }
}

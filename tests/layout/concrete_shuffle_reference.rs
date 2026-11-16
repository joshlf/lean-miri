#![feature(rustc_private)]
extern crate rand;
extern crate rand_xoshiro;
extern crate rustc_driver;
use rand::{seq::SliceRandom, SeedableRng};
fn main() {
    for seed in [0, 1, 42, u64::MAX] {
        for size in [0, 1, 2, 3, 4, 7, 13, 32, 257] {
            let mut v: Vec<usize> = (0..size).collect();
            v.shuffle(&mut rand_xoshiro::Xoshiro128StarStar::seed_from_u64(seed));
            println!("{seed} {size} {v:?}");
        }
    }
}

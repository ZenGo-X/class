#[cfg(feature = "flame_it")]
extern crate flame;
#[cfg(feature = "flame_it")]
#[macro_use] extern crate flamer;

// as well as the following instead of `#[flame]`
#[cfg_attr(feature = "flame_it", flame)]
// The item to apply `flame` to goes here.

use std::fs::File;

use flame as f;
use flamer::flame;

#[flame]
fn make_vec(size: usize) -> Vec<u32> {
    // using the original lib is still possible
    let mut res = f::span_of("vec init", || vec![0_u32; size]);
    for x in 0..size {
        res[x] = ((x + 10)/3) as u32;
    }
    let mut waste_time = 0;
    for i in 0..size*10 {
        waste_time += i
    }
    res
}
#[flame]
fn more_computing(i: usize) {
    for x in 0..(i * 100) {
        let mut v = make_vec(x);
        let x = Vec::from(&v[..]);
        for i in 0..v.len() {
            let flip = (v.len() - 1) - i as usize;
            v[i] = x[flip];
        }
    }
}
#[flame]
fn some_computation() {
    for i in 0..15 {
        more_computing(i);
    }
}

#[flame]
fn main() {
    some_computation();
    // in order to create the flamegraph you must call one of the
    // flame::dump_* functions.
    f::dump_stdout();
}

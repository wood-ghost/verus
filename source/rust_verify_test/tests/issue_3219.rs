#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Reproducers for https://github.com/verus-lang/verus/issues/3219.
// #3195 introduced the pattern-equality check that rejects these cases.
// These tests expect successful verification and intentionally remain failing
// regressions until support is restored. They do not bypass the equality check.
//
// Observed 2026-10-16 on Verus 5c8133a2e with Rust 1.98.1:
//   From source/: vargo test -p rust_verify_test --test issue_3219
//   Each of the four cases below was rejected during translation with
//   "equality-testing this type in pattern", for the following types:
//     test_issue_str_literal_pattern: &'{erased} str
//     test_enum_const_pattern:        E
//     test_struct_const_pattern:      P
//     test_phantom_const_pattern:     G
// This run checks verification only; the issue's runtime results were not rerun.

// The four verification cases from #3219; unverified runtime drivers are omitted.
test_verify_one_file! {
    #[test] test_enum_const_pattern verus_code! {
        use vstd::prelude::*;

        #[derive(PartialEq, Eq)]
        pub enum E { A, B(u8) }

        const EB: E = E::B(3);

        fn m(e: E) -> (r: bool)
            ensures r == (e == E::B(3)),
        {
            match e {
                EB => true,
                _ => false,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_struct_const_pattern verus_code! {
        use vstd::prelude::*;

        #[derive(PartialEq, Eq)]
        pub struct P { pub x: u8, pub y: u8 }

        const ORIGIN: P = P { x: 0, y: 0 };

        fn m(p: P) -> (r: bool)
            ensures r == (p.x == 0 && p.y == 0),
        {
            match p {
                ORIGIN => true,
                _ => false,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_phantom_const_pattern verus_code! {
        use vstd::prelude::*;
        use core::marker::PhantomData;

        #[derive(PartialEq, Eq)]
        pub struct G { pub a: u8, pub p: PhantomData<u8> }

        const C: G = G { a: 1, p: PhantomData };

        fn m(v: G) -> (r: bool)
            ensures r == (v.a == 1),
        {
            match v {
                C => true,
                _ => false,
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_issue_str_literal_pattern verus_code! {
        use vstd::prelude::*;

        fn m(s: &str) -> u8 {
            match s {
                "abc" => 1,
                _ => 0,
            }
        }
    } => Ok(())
}

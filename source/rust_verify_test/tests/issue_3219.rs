#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Reproducers for https://github.com/verus-lang/verus/issues/3219.
// #3195 introduced the pattern-equality check that rejects these cases.
// The original cases expect successful verification. Additional negative tests
// below check that unsupported comparisons and false postconditions stay rejected.
//
// Observed 2026-10-16 on Verus 5c8133a2e with Rust 1.98.1:
//   From source/: vargo test -p rust_verify_test --test issue_3219
//   Each of the four cases below was rejected during translation with
//   "equality-testing this type in pattern", for the following types:
//     test_issue_str_literal_pattern: &'{erased} str
//     test_enum_const_pattern:        E
//     test_struct_const_pattern:      P
//     test_phantom_const_pattern:     G
// This historical run checked verification only. A compile-and-run test is now
// included below to compare the restored cases with executable Rust behavior.
// With the local fix based on 9bb6a3bf3 (Rust 1.98.1), all ten tests pass,
// including the negative controls and the compile-and-run test (2026-10-16).

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
        broadcast use vstd::string::group_string_axioms;

        fn m(s: &str) -> (r: u8)
            ensures (r == 1) <==> (s@ == "abc"@),
                r == 0 || r == 1,
        {
            match s {
                "abc" => {
                    assert(s@ =~= "abc"@);
                    1
                }
                _ => {
                    assert(s@ != "abc"@);
                    0
                }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_pattern_contents verus_code! {
        use vstd::prelude::*;
        use vstd::string::StringExecFns;
        broadcast use vstd::string::group_string_axioms;

        const TEXT: &'static str = "é🦀";
        struct Labels;
        impl Labels { const EMPTY: &'static str = ""; }

        fn classify(s: &str) -> (r: u8)
            ensures
                (r == 1) <==> (s@ == TEXT@),
                (r == 2) <==> (s@ == Labels::EMPTY@),
                r <= 2,
        {
            proof {
                reveal(TEXT);
                reveal(Labels::EMPTY);
                reveal_strlit("é🦀");
                reveal_strlit("");
            }
            match s {
                TEXT => {
                    assert(s@ =~= TEXT@);
                    1
                }
                Labels::EMPTY => {
                    assert(s@ =~= Labels::EMPTY@);
                    2
                }
                _ => 0,
            }
        }

        fn owned_string() {
            proof {
                reveal(TEXT);
                reveal(Labels::EMPTY);
            }
            let a = String::from_str("é🦀");
            let b = String::from_str("é🦀");
            let ra = classify(a.as_str());
            let rb = classify(b.as_str());
            assert(ra == 1 && rb == 1);
            let empty = classify("");
            assert(empty == 2);
            let other = classify("different");
            proof {
                reveal_strlit("different");
                reveal_strlit("é🦀");
                reveal_strlit("");
            }
            assert(other == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_string_pattern_wrong_result verus_code! {
        use vstd::prelude::*;

        fn wrong(s: &str) -> (r: bool)
            requires s@ == "abc"@,
            ensures !r, // FAILS
        {
            match s { "abc" => true, _ => false }
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_nested_float_pattern_rejected verus_code! {
        #[derive(PartialEq)]
        struct Inner { x: f64 }
        #[derive(PartialEq)]
        struct Outer { inner: Inner }
        const ZERO: Outer = Outer { inner: Inner { x: 0.0 } };

        fn test(x: Outer) -> bool {
            match x { ZERO => true, _ => false }
        }
    } => Err(err) => assert_vir_error_msg(err, "equality-testing this type in pattern: Outer")
}

test_verify_one_file! {
    #[test] test_nested_structural_pattern verus_code! {
        use vstd::prelude::*;

        #[derive(PartialEq, Eq)]
        struct Inner<T> { value: T }
        #[derive(PartialEq, Eq)]
        struct Outer { inner: Inner<(u8, bool)> }
        const VALUE: Outer = Outer { inner: Inner { value: (7, true) } };

        fn test(x: Outer) -> (r: bool)
            ensures r == (x.inner.value == (7u8, true)),
        {
            match x { VALUE => true, _ => false }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_string_pattern_stays_unsupported verus_code! {
        #[derive(PartialEq, Eq)]
        struct S { text: &'static str }
        const VALUE: S = S { text: "abc" };

        fn test(x: S) -> bool {
            match x { VALUE => true, _ => false }
        }
    } => Err(err) => assert_vir_error_msg(err, "equality-testing this type in pattern: S")
}

#[test]
fn test_pattern_matching_runtime() {
    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let source = tempdir.path().join("test.rs");
    let binary = tempdir.path().join(if cfg!(windows) { "test.exe" } else { "test" });
    let program = code! {
        use vstd::prelude::*;
        use core::marker::PhantomData;

        verus! {
            broadcast use vstd::string::group_string_axioms;

            #[derive(PartialEq, Eq)]
            enum E { A, B(u8) }
            const EB: E = E::B(3);
            fn enum_matches(e: E) -> (r: bool)
                ensures r == (e == E::B(3)),
            {
                match e { EB => true, _ => false }
            }

            #[derive(PartialEq, Eq)]
            struct P { x: u8, y: u8 }
            const ORIGIN: P = P { x: 0, y: 0 };
            fn struct_matches(p: P) -> (r: bool)
                ensures r == (p.x == 0 && p.y == 0),
            {
                match p { ORIGIN => true, _ => false }
            }

            #[derive(PartialEq, Eq)]
            struct G { a: u8, p: PhantomData<u8> }
            const C: G = G { a: 1, p: PhantomData };
            fn phantom_matches(v: G) -> (r: bool)
                ensures r == (v.a == 1),
            {
                match v { C => true, _ => false }
            }

            fn string_matches(s: &str) -> (r: bool)
                ensures r == (s@ == "é🦀"@),
            {
                match s {
                    "é🦀" => { assert(s@ =~= "é🦀"@); true }
                    _ => false,
                }
            }
        }

        fn main() {
            assert!(enum_matches(E::B(3)));
            assert!(!enum_matches(E::A));
            assert!(!enum_matches(E::B(4)));
            assert!(struct_matches(P { x: 0, y: 0 }));
            assert!(!struct_matches(P { x: 0, y: 1 }));
            assert!(phantom_matches(G { a: 1, p: PhantomData }));
            assert!(!phantom_matches(G { a: 2, p: PhantomData }));
            let a = String::from("é🦀");
            let b = String::from("é🦀");
            assert!(string_matches(&a));
            assert!(string_matches(&b));
            assert!(!string_matches(""));
            assert!(!string_matches("different"));
        }
    };
    std::fs::write(&source, program).expect("write source");
    let output = run_verus_raw(
        &["--compile", source.to_str().unwrap(), "-o", binary.to_str().unwrap()],
        tempdir.path(),
    );
    assert!(
        output.status.success(),
        "verification/compilation failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let output = std::process::Command::new(&binary).output().expect("run compiled test");
    assert!(
        output.status.success(),
        "runtime assertions failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

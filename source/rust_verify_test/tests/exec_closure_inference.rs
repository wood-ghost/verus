#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Baseline for https://github.com/verus-lang/verus/discussions/1759.
// The unannotated closure should eventually expose the same result relation
// as the explicitly annotated closure below.
test_verify_one_file_with_options! {
    #[test] identity_without_contract ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn(x: u8) {
            let f = |y: u8| y;
            let result = f(x);
            assert(result == x); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] identity_with_contract ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn testfn(x: u8) {
            let f = |y: u8| -> (result: u8)
                ensures result == y
            {
                y
            };
            let result = f(x);
            assert(result == x);
        }
    } => Ok(())
}

// A zero-argument closure captures x and forwards a call to a contracted function.
// Until contract inference is implemented, only the unannotated wrapper should fail.
test_verify_one_file_with_options! {
    #[test] contracted_function_wrapper ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(x: u8) -> (result: u8)
            ensures result == x,
        {
            x
        }

        fn direct_call(x: u8) {
            let result = foo(x);
            assert(result == x);
        }

        fn closure_call(x: u8) {
            let f = || foo(x);
            let result = f();
            assert(result == x); // FAILS
        }

        fn annotated_closure_call(x: u8) {
            let f = || -> (result: u8)
                ensures result == x
            {
                foo(x)
            };
            let result = f();
            assert(result == x);
        }
    } => Err(err) => assert_one_fails(err)
}

// Substitute both a captured value and a closure parameter, preserving argument order.
test_verify_one_file_with_options! {
    #[test] forwarded_parameter_and_capture ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(left: u8, right: u8) -> (result: (u8, u8))
            ensures result == (left, right),
        {
            (left, right)
        }

        fn direct_call(x: u8, captured: u8) {
            let result = foo(captured, x);
            assert(result == (captured, x));
        }

        fn closure_call(x: u8, captured: u8) {
            let f = |value: u8| foo(captured, value);
            let result = f(x);
            assert(result == (captured, x)); // FAILS
        }

        fn annotated_closure_call(x: u8, captured: u8) {
            let f = |value: u8| -> (result: (u8, u8))
                ensures result == (captured, value)
            {
                foo(captured, value)
            };
            let result = f(x);
            assert(result == (captured, x));
        }
    } => Err(err) => assert_one_fails(err)
}

// Preserve multiple method postconditions referring to the receiver and a borrowed argument.
test_verify_one_file_with_options! {
    #[test] captured_method_contract ["vstd"] => verus_code! {
        use vstd::prelude::*;

        struct Reader {
            tag: u8,
        }

        impl Reader {
            fn read(&self, data: &[u8]) -> (result: (u8, usize))
                ensures
                    result.0 == self.tag,
                    result.1 == data.len(),
            {
                (self.tag, data.len())
            }
        }

        fn direct_call(reader: &Reader, data: &[u8]) {
            let result = reader.read(data);
            assert(result == (reader.tag, data.len()));
        }

        fn closure_call(reader: &Reader, data: &[u8]) {
            let f = || reader.read(data);
            let result = f();
            assert(result == (reader.tag, data.len())); // FAILS
        }

        fn annotated_closure_call(reader: &Reader, data: &[u8]) {
            let f = || -> (result: (u8, usize))
                ensures result == (reader.tag, data.len())
            {
                reader.read(data)
            };
            let result = f();
            assert(result == (reader.tag, data.len()));
        }
    } => Err(err) => assert_one_fails(err)
}

// Without inferred requires, verification fails inside the unannotated closure.
// The invalid annotated call is a negative control that must continue to fail.
test_verify_one_file_with_options! {
    #[test] forwarded_precondition ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn increment(x: u8) -> (result: u8)
            requires x < 255,
            ensures result == x + 1,
        {
            x + 1
        }

        fn direct_call() {
            let result = increment(254);
            assert(result == 255);
        }

        fn closure_call() {
            let f = |value: u8| increment(value); // FAILS
            let _result = f(254);
        }

        fn annotated_closure_call() {
            let f = |value: u8| -> (result: u8)
                requires value < 255,
                ensures result == value + 1,
            {
                increment(value)
            };
            let result = f(254);
            assert(result == 255);
        }

        fn invalid_call() {
            let f = |value: u8| -> (result: u8)
                requires value < 255,
                ensures result == value + 1,
            {
                increment(value)
            };
            let _result = f(255); // FAILS
        }
    } => Err(err) => assert_fails(err, 2)
}

// Each move closure must retain its own captured value after the outer variable changes.
test_verify_one_file_with_options! {
    #[test] move_capture_snapshot ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(x: u8) -> (result: u8)
            ensures result == x,
        {
            x
        }

        fn direct_call() {
            let mut x = 3u8;
            let first = foo(x);
            x = 9;
            let second = foo(x);
            assert(first == 3);
            assert(second == 9);
        }

        fn closure_call() {
            let mut x = 3u8;
            let f = move || foo(x);
            x = 9;
            let g = move || foo(x);
            let first = f();
            let second = g();
            assert(first == 3); // FAILS
            assert(second == 9); // FAILS
        }

        fn annotated_closure_call() {
            let mut x = 3u8;
            let f = move || -> (result: u8)
                ensures result == x
            {
                foo(x)
            };
            x = 9;
            let g = move || -> (result: u8)
                ensures result == x
            {
                foo(x)
            };
            let first = f();
            let second = g();
            assert(first == 3);
            assert(second == 9);
        }
    } => Err(err) => assert_fails(err, 2)
}

// A user-defined higher-order helper exposes only the callback's exported contract.
test_verify_one_file_with_options! {
    #[test] forwarded_contract_through_apply ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(x: u8) -> (result: u8)
            ensures result == x,
        {
            x
        }

        fn apply<F: FnOnce() -> u8>(f: F) -> (result: u8)
            requires call_requires(f, ()),
            ensures call_ensures(f, (), result),
        {
            f()
        }

        fn direct_call(x: u8) {
            let result = foo(x);
            assert(result == x);
        }

        fn closure_call(x: u8) {
            let result = apply(|| foo(x));
            assert(result == x); // FAILS
        }

        fn annotated_closure_call(x: u8) {
            let result = apply(|| -> (result: u8)
                ensures result == x
            {
                foo(x)
            });
            assert(result == x);
        }
    } => Err(err) => assert_one_fails(err)
}

// Returning the callee's result through a local binding or an explicit return is equivalent.
test_verify_one_file_with_options! {
    #[test] forwarded_call_return_shapes ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(x: u8) -> (result: u8)
            ensures result == x,
        {
            x
        }

        fn direct_call(x: u8) {
            let result = foo(x);
            assert(result == x);
        }

        fn local_binding(x: u8) {
            let f = || {
                let result = foo(x);
                result
            };
            let result = f();
            assert(result == x); // FAILS
        }

        fn explicit_return(x: u8) {
            let f = || {
                return foo(x);
            };
            let result = f();
            assert(result == x); // FAILS
        }

        fn annotated_local_binding(x: u8) {
            let f = || -> (result: u8)
                ensures result == x
            {
                let result = foo(x);
                result
            };
            let result = f();
            assert(result == x);
        }

        fn annotated_explicit_return(x: u8) {
            let f = || -> (result: u8)
                ensures result == x
            {
                return foo(x);
            };
            let result = f();
            assert(result == x);
        }
    } => Err(err) => assert_fails(err, 2)
}

// Contract forwarding alone cannot supply a postcondition missing from the callee.
test_verify_one_file_with_options! {
    #[test] missing_callee_postcondition ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(x: u8) -> u8 {
            x
        }

        fn direct_call(x: u8) {
            let result = foo(x);
            assert(result == x); // FAILS
        }

        fn closure_call(x: u8) {
            let f = || foo(x);
            let result = f();
            assert(result == x); // FAILS
        }

        fn annotated_closure_call(x: u8) {
            let f = || -> (result: u8)
                ensures result == x // FAILS
            {
                foo(x)
            };
            let _result = f();
        }
    } => Err(err) => assert_fails(err, 3)
}

// A discarded call's postcondition must not be attached to a different returned value.
test_verify_one_file_with_options! {
    #[test] discarded_callee_result ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn foo(x: u8) -> (result: u8)
            ensures result == x,
        {
            x
        }

        fn closure_call() {
            let f = || {
                foo(7);
                0u8
            };
            let result = f();
            assert(result == 7); // FAILS
        }

        fn annotated_closure_call() {
            let f = || -> (result: u8)
                ensures result == 0
            {
                foo(7);
                0u8
            };
            let result = f();
            assert(result == 0);
        }
    } => Err(err) => assert_one_fails(err)
}

// Inference must not replace an explicit postcondition or strengthen an explicit requires.
test_verify_one_file_with_options! {
    #[test] explicit_contract_is_preserved ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn increment(x: u8) -> (result: u8)
            requires x < 255,
            ensures result == x + 1,
        {
            x + 1
        }

        fn incorrect_postcondition() {
            let _f = |value: u8| -> (result: u8)
                requires value < 255,
                ensures result == value, // FAILS
            {
                increment(value)
            };
        }

        fn insufficient_precondition() {
            let _f = |value: u8| -> (result: u8)
                requires true,
                ensures result == value + 1,
            {
                increment(value) // FAILS
            };
        }
    } => Err(err) => assert_fails(err, 2)
}

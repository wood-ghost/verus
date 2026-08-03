#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test]
    extendible_spec_call_ensures_cycle verus_code! {
        trait T {
            fn f<A: T>();
        }

        impl T for u8 {
            fn f<A: T>()
                ensures
                    !call_ensures(u8::f::<A>, (), ()),
            {
            }
        }
    } => Err(err) => assert_vir_error_msg(
        err,
        "found a cyclic self-reference in a definition",
    )
}

test_verify_one_file! {
    #[test]
    non_extendible_spec_fixed_ensures verus_code! {
        uninterp spec fn duck() -> bool;

        trait T {
            #[verifier::non_extendible_spec]
            fn f<A: T>()
                ensures
                    duck(),
            ;
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test]
    non_extendible_spec_references_other_method verus_code! {
        trait T {
            fn g();

            #[verifier::non_extendible_spec]
            fn f<A: T>()
                ensures
                    call_ensures(A::g, (), ()),
            ;
        }
    } => Ok(())
}

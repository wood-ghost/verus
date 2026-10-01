#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Paired probes for #3014: the true postcondition must verify, and its negation
// must fail. Tags distinguish source types that may share a logical representation.
const OPAQUE_RETURN_TAGS: &str = verus_code_str! {
    use vstd::prelude::*;
    use std::rc::Rc;
    use std::sync::Arc;

    trait TypeTag {
        spec fn tag(&self) -> int;
    }
    impl TypeTag for u64 { spec fn tag(&self) -> int { 0 } }
    impl TypeTag for i64 { spec fn tag(&self) -> int { 1 } }
    impl TypeTag for u32 { spec fn tag(&self) -> int { 2 } }
    impl TypeTag for u8 { spec fn tag(&self) -> int { 3 } }
    impl TypeTag for bool { spec fn tag(&self) -> int { 4 } }
    impl TypeTag for char { spec fn tag(&self) -> int { 5 } }
    impl TypeTag for *mut u64 { spec fn tag(&self) -> int { 6 } }
    impl TypeTag for *const u64 { spec fn tag(&self) -> int { 7 } }
    impl TypeTag for &u64 { spec fn tag(&self) -> int { 8 } }
    impl TypeTag for Box<u64> { spec fn tag(&self) -> int { 9 } }
    impl TypeTag for Rc<u64> { spec fn tag(&self) -> int { 10 } }
    impl TypeTag for Arc<u64> { spec fn tag(&self) -> int { 11 } }
    impl TypeTag for (u64, bool) { spec fn tag(&self) -> int { 12 } }
    struct Record { value: i64 }
    impl TypeTag for Record { spec fn tag(&self) -> int { 13 } }
    struct Wrapper<T> { value: T }
    impl<T> TypeTag for Wrapper<T> { spec fn tag(&self) -> int { 14 } }
    enum Small { A, B }
    impl TypeTag for Small { spec fn tag(&self) -> int { 15 } }
};

// EXPECTED_TAG is replaced in the source before invoking Verus. Keep each
// positive/negative pair separate so accepting a false property is visible.
macro_rules! test_opaque_return_type {
    ($positive:ident, $negative:ident, $tag:literal, $program:expr) => {
        test_verify_one_file_with_options! {
            #[test] $positive ["vstd"] =>
                OPAQUE_RETURN_TAGS.to_string()
                    + &$program.replace("EXPECTED_TAG", stringify!($tag))
                => Ok(())
        }
        test_verify_one_file_with_options! {
            #[test] $negative ["vstd"] =>
                OPAQUE_RETURN_TAGS.to_string()
                    + &$program.replace("== EXPECTED_TAG", "!= EXPECTED_TAG")
                        .replace("EXPECTED_TAG", stringify!($tag))
                => Err(err) => assert_one_fails(err)
        }
    };
}

test_opaque_return_type! {
    probe_literal_ok, probe_literal_rejects_false, 0, verus_code_str! {
        fn make() -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { 0u64 }
    }
}

test_opaque_return_type! {
    probe_widening_cast_ok, probe_widening_cast_rejects_false, 0, verus_code_str! {
        fn make(x: u32) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x as u64 }
    }
}

test_opaque_return_type! {
    probe_narrowing_cast_ok, probe_narrowing_cast_rejects_false, 3, verus_code_str! {
        fn make(x: u64) -> (ret: impl TypeTag)
            requires x < 256
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x as u8 }
    }
}

test_opaque_return_type! {
    probe_char_cast_ok, probe_char_cast_rejects_false, 2, verus_code_str! {
        fn make(x: char) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x as u32 }
    }
}

test_opaque_return_type! {
    probe_enum_cast_ok, probe_enum_cast_rejects_false, 0, verus_code_str! {
        fn make(x: Small) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x as u64 }
    }
}

test_opaque_return_type! {
    probe_bool_not_ok, probe_bool_not_rejects_false, 4, verus_code_str! {
        fn make(x: bool) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { !x }
    }
}

test_opaque_return_type! {
    probe_arithmetic_ok, probe_arithmetic_rejects_false, 1, verus_code_str! {
        fn make(x: i64) -> (ret: impl TypeTag)
            requires 0 <= x < 100
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { -x }
    }
}

test_opaque_return_type! {
    probe_field_ok, probe_field_rejects_false, 1, verus_code_str! {
        fn make(x: Record) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x.value }
    }
}

test_opaque_return_type! {
    probe_tuple_field_ok, probe_tuple_field_rejects_false, 0, verus_code_str! {
        fn make(x: (u64, bool)) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x.0 }
    }
}

test_opaque_return_type! {
    probe_generic_field_ok, probe_generic_field_rejects_false, 0, verus_code_str! {
        fn make(x: Wrapper<u64>) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x.value }
    }
}

test_opaque_return_type! {
    probe_borrow_ok, probe_borrow_rejects_false, 8, verus_code_str! {
        fn make<'a>(x: &'a u64) -> (ret: impl TypeTag + 'a)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { &*x }
    }
}

test_opaque_return_type! {
    probe_deref_ok, probe_deref_rejects_false, 0, verus_code_str! {
        fn make(x: &u64) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { *x }
    }
}

test_opaque_return_type! {
    probe_box_new_ok, probe_box_new_rejects_false, 9, verus_code_str! {
        fn make(x: u64) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { Box::new(x) }
    }
}

test_opaque_return_type! {
    probe_box_deref_ok, probe_box_deref_rejects_false, 0, verus_code_str! {
        fn make(x: Box<u64>) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { *x }
    }
}

test_opaque_return_type! {
    probe_rc_new_ok, probe_rc_new_rejects_false, 10, verus_code_str! {
        fn make(x: u64) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { Rc::new(x) }
    }
}

test_opaque_return_type! {
    probe_arc_new_ok, probe_arc_new_rejects_false, 11, verus_code_str! {
        fn make(x: u64) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { Arc::new(x) }
    }
}

test_opaque_return_type! {
    probe_rc_deref_ok, probe_rc_deref_rejects_false, 0, verus_code_str! {
        fn make(x: Rc<u64>) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { *x }
    }
}

test_opaque_return_type! {
    probe_arc_deref_ok, probe_arc_deref_rejects_false, 0, verus_code_str! {
        fn make(x: Arc<u64>) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { *x }
    }
}

test_opaque_return_type! {
    probe_pointer_cast_ok, probe_pointer_cast_rejects_false, 7, verus_code_str! {
        fn make(x: *mut u64) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x as *const u64 }
    }
}

test_opaque_return_type! {
    probe_if_cast_ok, probe_if_cast_rejects_false, 7, verus_code_str! {
        fn make(x: *mut u64, y: *const u64, b: bool) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { if b { x as *const u64 } else { y } }
    }
}

test_opaque_return_type! {
    probe_constructor_ok, probe_constructor_rejects_false, 14, verus_code_str! {
        fn make<T>(x: T) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { Wrapper { value: x } }
    }
}

test_opaque_return_type! {
    probe_array_index_ok, probe_array_index_rejects_false, 0, verus_code_str! {
        fn make(x: [u64; 1]) -> (ret: impl TypeTag)
            ensures ret.tag() == EXPECTED_TAG // FAILS
        { x[0] }
    }
}

test_opaque_return_type! {
    probe_nested_array_ok, probe_nested_array_rejects_false, 0, verus_code_str! {
        fn make() -> (ret: [impl TypeTag; 1])
            ensures ret[0].tag() == EXPECTED_TAG // FAILS
        { [0u64] }
    }
}

test_opaque_return_type! {
    probe_concrete_array_ok, probe_concrete_array_rejects_false, 0, verus_code_str! {
        fn make() -> (ret: [u64; 1])
            ensures ret[0].tag() == EXPECTED_TAG // FAILS
        { [0u64] }
    }
}

test_opaque_return_type! {
    probe_nested_tuple_ok, probe_nested_tuple_rejects_false, 0, verus_code_str! {
        fn make() -> (ret: (impl TypeTag,))
            ensures ret.0.tag() == EXPECTED_TAG // FAILS
        { (0u64,) }
    }
}

test_opaque_return_type! {
    probe_nested_struct_ok, probe_nested_struct_rejects_false, 0, verus_code_str! {
        fn make() -> (ret: Wrapper<impl TypeTag>)
            ensures ret.value.tag() == EXPECTED_TAG // FAILS
        { Wrapper { value: 0u64 } }
    }
}

test_opaque_return_type! {
    probe_nested_option_ok, probe_nested_option_rejects_false, 0, verus_code_str! {
        fn make() -> (ret: Option<impl TypeTag>)
            ensures ret is Some, ret->Some_0.tag() == EXPECTED_TAG // FAILS
        { Some(0u64) }
    }
}

test_opaque_return_type! {
    probe_nested_vec_ok, probe_nested_vec_rejects_false, 0, verus_code_str! {
        fn make() -> (ret: Vec<impl TypeTag>)
            ensures ret.len() == 1, ret[0].tag() == EXPECTED_TAG // FAILS
        { let mut v = Vec::new(); v.push(0u64); v }
    }
}

test_opaque_return_type! {
    probe_nested_slice_ok, probe_nested_slice_rejects_false, 0, verus_code_str! {
        fn make<'a>(x: &'a [u64]) -> (ret: &'a [impl TypeTag])
            requires x.len() > 0
            ensures ret.len() == x.len(), ret[0].tag() == EXPECTED_TAG // FAILS
        { x }
    }
}

test_opaque_return_type! {
    probe_concrete_vec_ok, probe_concrete_vec_rejects_false, 0, verus_code_str! {
        fn make() -> (ret: Vec<u64>)
            ensures ret.len() == 1, ret[0].tag() == EXPECTED_TAG // FAILS
        { let mut v = Vec::new(); v.push(0u64); v }
    }
}

test_opaque_return_type! {
    probe_concrete_slice_ok, probe_concrete_slice_rejects_false, 0, verus_code_str! {
        fn make<'a>(x: &'a [u64]) -> (ret: &'a [u64])
            requires x.len() > 0
            ensures ret.len() == x.len(), ret[0].tag() == EXPECTED_TAG // FAILS
        { x }
    }
}

// Minimal reproducers, independent of the tag-based probes above.
test_verify_one_file! {
    #[test] probe_deref_false_property_minimal verus_code! {
        trait Tr { spec fn is_ref(&self) -> bool; }
        impl Tr for u64 { spec fn is_ref(&self) -> bool { false } }
        impl Tr for &u64 { spec fn is_ref(&self) -> bool { true } }

        fn deref(x: &u64) -> (ret: impl Tr)
            ensures ret.is_ref() // FAILS
        {
            *x
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] probe_box_deref_false_property_minimal ["vstd"] => verus_code! {
        trait Tr { spec fn is_box(&self) -> bool; }
        impl Tr for u64 { spec fn is_box(&self) -> bool { false } }
        impl Tr for Box<u64> { spec fn is_box(&self) -> bool { true } }

        fn unbox(x: Box<u64>) -> (ret: impl Tr)
            ensures ret.is_box() // FAILS
        {
            *x
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] probe_vec_opaque_minimal ["vstd"] => verus_code! {
        fn empty() -> (ret: Vec<impl Sized>)
            ensures ret.len() == 0
        {
            Vec::<u64>::new()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] probe_slice_opaque_minimal ["vstd"] => verus_code! {
        fn identity(x: &[u64]) -> (ret: &[impl Sized])
            ensures ret.len() == x.len()
        {
            x
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_opaque_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{}
        impl DummyTrait for bool{}
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_opaque_type_hides_real_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{}
        impl DummyTrait for bool{}
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            assert(x);
        }
    } => Err(err) => assert_rust_error_msg_all(err, "mismatched types")
}

test_verify_one_file! {
    #[test] test_return_opaque_type_allows_trait_functions verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
        }
        impl DummyTrait for bool{
            fn foo(&self) -> (ret: bool)
            {
                false
            }
        }
        fn return_opaque_variable() -> impl DummyTrait{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            let ret = x.foo();
            assert(ret == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_return_opaque_type_reveal_real_type verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
            fn get_output(&self) -> (ret : Self::Output);
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            fn get_output(&self) -> (ret : Self::Output){
                *self
            }
        }
        fn return_opaque_variable() -> impl DummyTrait<Output = bool>{
            true
        }
        fn test(){
            let x = return_opaque_variable();
            let output = x.get_output();
            // Here Verus should be able to infer the type of output, but assertion should fail
            assert(output);  // FAILS
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_no_opaque_types_from_traits verus_code! {
    use vstd::prelude::*;
    trait DummyTraitA{}
    impl<T> DummyTraitA for T {}
    trait DummyTraitB {
        fn foo(&self) -> impl DummyTraitA;
    }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not yet support Opaque types in trait def")
}

test_verify_one_file! {
    #[test] test_opaque_function_with_ensures verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{}
        impl<T> DummyTraitA for T {}
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret
        {
            true
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_function_return_value_type verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{}
        impl<T> DummyTraitA for T {}
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret == true,
        {
            true
        }
    } => Err(err) => assert_rust_error_msg(err, "the trait bound")
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_without_annotation  verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{
            type Output;
            spec fn get_output(&self) -> Self::Output;
        }
        impl<T> DummyTraitA for T {
            type Output = T;
            uninterp spec fn get_output(&self) -> Self::Output;
        }
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret.get_output() == true,
        {
            true
        }
    } => Err(err) => assert_rust_error_msg(err, "the trait bound")
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_with_annotation verus_code! {
        use vstd::prelude::*;
        trait DummyTraitA{
            type Output;
            spec fn get_output(&self) -> Self::Output;
        }
        impl<T> DummyTraitA for T {
            type Output = T;
            uninterp spec fn get_output(&self) -> Self::Output;
        }
        fn foo() -> (ret: impl DummyTraitA)
            ensures
                ret == ret,
                ret.get_output() == true,  // FAILS
        {
            true
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_opaque_type_external_body_function verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool {
                true
            }
        }

        #[verifier::external_body]
        fn return_opaque_variable() -> (ret: impl DummyTrait)
            ensures
                ret.bar() == false,
        {
            true
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
        {
            x
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T) -> (ret: impl DummyTrait<Output = T>)
            ensures ret.bar();
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_tuple_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T, y:T) -> (impl DummyTrait<Output = T>, impl DummyTrait<Output = T>)
        {
            (x, y)
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T, y:T) -> (ret: (impl DummyTrait<Output = T>, impl DummyTrait<Output = T>))
            ensures ret.0.bar();
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_assume_spec_fail verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        #[verifier::external]
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
        {
            x
        }
        assume_specification<T> [ return_opaque_variable::<T> ](x:T) -> (ret: impl DummyTrait)
            ensures ret.bar();
    }  => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_assume_spec_ok verus_code! {
        use vstd::prelude::*;
         trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
            spec fn get_self(&self) -> Self::Output;
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }

            spec fn get_self(&self) -> Self::Output{
                *self
            }
        }
        #[verifier::external]
        fn return_opaque_variable() -> impl DummyTrait<Output = impl DummyTrait>
        {
            true
        }
        assume_specification [ return_opaque_variable ]() -> (ret: impl DummyTrait<Output = impl DummyTrait>)
            ensures ret.get_self().bar()
            ;

        fn test(){
            let ret = return_opaque_variable();
            assert(ret.get_self().bar());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_nested_opaque_type_assume_spec_fail verus_code! {
        use vstd::prelude::*;
         trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
            spec fn get_self(&self) -> Self::Output;
        }
        impl DummyTrait for bool{
            type Output = bool;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }

            spec fn get_self(&self) -> Self::Output{
                *self
            }
        }
        #[verifier::external]
        fn return_opaque_variable() -> impl DummyTrait<Output = impl DummyTrait<Output = bool>>
        {
            true
        }
        assume_specification [ return_opaque_variable ]() -> (ret: impl DummyTrait<Output = impl DummyTrait>)
            ensures ret.get_self().bar()
            ;
    } => Err(err) => assert_vir_error_msg(err, "assume_specification requires function type signature to match")
}

test_verify_one_file! {
    #[test] test_opaque_type_returns_error verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            type Output;
            fn foo(&self) -> (ret: bool)
            ensures
                ret == false;

            spec fn bar(&self) -> bool;
        }
        impl<T> DummyTrait for T{
            type Output = T;
            fn foo(&self) -> (ret: bool)
            {
                false
            }
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn return_opaque_variable<T>(x:T) -> impl DummyTrait<Output = T>
            returns x
        {
            x
        }
    }  => Err(err) => assert_vir_error_msg(err, "`returns` clause is not allowed for function that returns opaque type")
}

test_verify_one_file! {
    #[test] test_tuple_of_opaque_types_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn foo() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            (true, true)
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_from_opaque_type_ok verus_code! {
        use vstd::prelude::*;
        trait DummyTrait{
            spec fn bar(&self) -> bool;
        }
        impl DummyTrait for bool{
            spec fn bar(&self) -> bool{
                true
            }
        }
        fn foo() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            (true, true)
        }
        fn bar() -> (ret:(impl DummyTrait, impl DummyTrait))
            ensures
                ret.0.bar(),
                ret.1.bar(),
        {
            foo()
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_fail verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }
        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = impl Tr<T = bool>>)
            ensures
                // ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(), // FAILS
        {
            boo()
        }
    } => Err(err) => assert_fails(err, 1)
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_ok verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }

        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            boo()
        }
    }  => Ok(())
}

test_verify_one_file! {
    #[test] test_opaque_type_projection_inherent_ok verus_code! {
        use vstd::prelude::*;
        trait Tr{
            spec fn dummy_spec(&self) -> bool;
            type T;
            type Y;
            spec fn ret_y(&self) -> Self::Y;
        }
        impl Tr for bool{
            spec fn dummy_spec(&self) -> bool{
                true
            }
            type T = bool;
            type Y = Self;
            uninterp spec fn ret_y(&self) -> Self::Y;
        }

        fn boo() -> (ret: impl Tr<T = impl Tr<T = bool>, Y = bool>)
            ensures
                // ret.ret_y().dummy_spec(),
        {
            true
        }
        fn bar() -> (ret: impl Tr<Y = impl Tr<T = bool>, T = impl Tr<T = bool>>)
            ensures
                ret.ret_y().dummy_spec(),
        {
            boo()
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // Regression test for ensuring opaque type constructor context is present
    // in spinoff queries. -V spinoff-all verifies every function in its own context.
    #[test] opaque_type_in_spinoff_context ["-V spinoff-all"] => verus_code! {
        trait DummyTrait {}
        impl DummyTrait for bool {}
        fn return_opaque() -> impl DummyTrait {
            true
        }
        fn test() {
            let x = return_opaque();
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] issue2541 ["--no-lifetime"] => code! {
        use std::future::Future;
        #[allow(unused_imports)]
        use vstd::prelude::*;

        pub trait F<T> {
            fn f(x: &T) -> impl Future + Send;
        }

        struct E;
        struct S;

        #[allow(refining_impl_trait)]
        impl F<E> for S {
            async fn f(_x: &E) {}
        }

        fn main() {}
    } => Ok(())
}

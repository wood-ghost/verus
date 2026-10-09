#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

fn checks(result: &TestErr) -> &Vec<serde_json::Value> {
    let json = result.json_output.as_ref().expect("JSON output");
    assert_eq!(json["smoke-results"]["completed"], true);
    json["smoke-results"]["checks"].as_array().expect("smoke checks")
}

fn status(result: &TestErr, function: &str, expected: &str) {
    let name = format!("test_crate::{function}");
    let found: Vec<_> = checks(result).iter().filter(|r| r["function"] == name).collect();
    assert_eq!(found.len(), 1, "expected exactly one entry check for {name}");
    assert_eq!(found[0]["status"], expected);
}

test_verify_one_file_with_options! {
    #[test] contradictory_requires ["--smoke-entry", "--output-json"] => verus_code! {
        fn target(x: i32) -> (r: i32)
            requires x < 0, x > 0,
            ensures r == 42,
        { x }
    } => Ok(out) => {
        status(&out, "target", "false_proved");
        assert_eq!(checks(&out).len(), 1);
        assert_eq!(out.warnings.iter().filter(|w|
            w.message == "smoke test detected an inconsistent function-entry context"
        ).count(), 1);
        let json = out.json_output.as_ref().unwrap();
        assert_eq!(json["verification-results"]["verified"], 1);
        assert_eq!(json["verification-results"]["errors"], 0);
        assert_eq!(json["func-details"]["test_crate::target"]["obligation_proof_notes"], serde_json::json!([]));
    }
}

test_verify_one_file_with_options! {
    #[test] consistent_requires ["--smoke-entry", "--output-json"] => verus_code! {
        fn target(x: i32) -> (r: i32)
            requires x == 42,
            ensures r == 42,
        { x }
    } => Ok(out) => {
        status(&out, "target", "false_not_proved");
        assert!(out.warnings.is_empty());
        assert_eq!(out.json_output.as_ref().unwrap()["verification-results"]["verified"], 1);
    }
}

test_verify_one_file_with_options! {
    #[test] empty_function ["--smoke-entry", "--output-json"] => verus_code! {
        proof fn target(x: int)
            requires x < 0, x > 0,
        {}
    } => Ok(out) => { status(&out, "target", "false_proved"); }
}

test_verify_one_file_with_options! {
    #[test] later_assumption_does_not_leak ["--smoke-entry", "--output-json"] => verus_code! {
        proof fn target(x: int)
            requires x == 0,
        {
            assume(x != 0);
        }
    } => Ok(out) => { status(&out, "target", "false_not_proved"); }
}

test_verify_one_file_with_options! {
    #[test] own_postcondition_is_not_assumed ["--smoke-entry", "--output-json"] => verus_code! {
        proof fn target()
            ensures false,
        {
            assume(false);
        }
    } => Ok(out) => { status(&out, "target", "false_not_proved"); }
}

test_verify_one_file_with_options! {
    #[test] probes_do_not_contaminate_each_other ["--smoke-entry", "--output-json"] => verus_code! {
        proof fn bad(x: int) requires x < 0, x > 0, {}
        proof fn good(x: int) requires x == 0, {}
    } => Ok(out) => {
        status(&out, "bad", "false_proved");
        status(&out, "good", "false_not_proved");
        assert_eq!(checks(&out).len(), 2);
    }
}

test_verify_one_file_with_options! {
    #[test] multiple_buckets ["--smoke-entry", "--output-json", "--num-threads=2"] => verus_code! {
        mod a {
            use verus_builtin::*;
            pub proof fn bad() requires false, {}
        }
        mod b {
            use verus_builtin::*;
            pub proof fn good() {}
        }
    } => Ok(out) => {
        status(&out, "a::bad", "false_proved");
        status(&out, "b::good", "false_not_proved");
        assert_eq!(checks(&out).len(), 2);
    }
}

test_verify_one_file_with_options! {
    #[test] ordinary_error_is_preserved ["--smoke-entry", "--output-json"] => verus_code! {
        fn target() -> (r: u64)
            ensures r == 1, // FAILS
        { 0 }
    } => Err(out) => {
        assert_one_fails(out.clone());
        status(&out, "target", "false_not_proved");
        assert_eq!(out.json_output.as_ref().unwrap()["verification-results"]["errors"], 1);
    }
}

test_verify_one_file_with_options! {
    #[test] function_filter ["--smoke-entry", "--output-json", "--verify-root", "--verify-function=chosen"] => verus_code! {
        proof fn chosen() requires false, {}
        proof fn other() requires false, {}
    } => Ok(out) => {
        status(&out, "chosen", "false_proved");
        assert_eq!(checks(&out).len(), 1);
    }
}

test_verify_one_file_with_options! {
    #[test] specialized_query_is_skipped ["--smoke-entry", "--output-json"] => verus_code! {
        #[verifier::nonlinear]
        proof fn target() requires false, {}
    } => Ok(out) => { status(&out, "target", "skipped"); }
}

test_verify_one_file_with_options! {
    #[test] loop_query_is_not_function_entry ["--smoke-entry", "--output-json"] => verus_code! {
        fn target() {
            let mut i: u64 = 0;
            while i < 1
                invariant i <= 1,
                decreases 1 - i,
            {
                i = i + 1;
            }
        }
    } => Ok(out) => {
        status(&out, "target", "false_not_proved");
        assert_eq!(checks(&out).len(), 1);
    }
}

test_verify_one_file_with_options! {
    #[test] disabled_by_default ["--output-json"] => verus_code! {
        proof fn target() requires false, {}
    } => Ok(out) => {
        assert!(out.warnings.is_empty());
        assert!(out.json_output.as_ref().unwrap().get("smoke-results").is_none());
    }
}

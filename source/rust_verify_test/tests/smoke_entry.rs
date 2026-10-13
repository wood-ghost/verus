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
    let found: Vec<_> = checks(result)
        .iter()
        .filter(|r| r["function"] == name && r["kind"] == "function_entry")
        .collect();
    assert_eq!(found.len(), 1, "expected exactly one entry check for {name}");
    assert_eq!(found[0]["status"], expected);
}

fn guard_status(result: &TestErr, function: &str, clause: usize, expected: &str) {
    let name = format!("test_crate::{function}");
    let found: Vec<_> = checks(result)
        .iter()
        .filter(|r| {
            r["function"] == name && r["kind"] == "postcondition_guard" && r["clause"] == clause
        })
        .collect();
    assert_eq!(found.len(), 1, "expected one guard check for {name}, clause {clause}");
    assert_eq!(found[0]["status"], expected);
}

test_verify_one_file_with_options! {
    #[test] vacuous_guard ["--smoke-entry", "--smoke-guards", "--output-json"] => verus_code! {
        fn target(x: i32) -> (r: i32)
            requires x < 0,
            ensures x > 0 ==> r == 42,
        { x }
    } => Ok(out) => {
        status(&out, "target", "false_not_proved");
        guard_status(&out, "target", 0, "false_proved");
        assert_eq!(checks(&out).len(), 2);
        assert_eq!(out.warnings.iter().filter(|w|
            w.message == "smoke test detected an unreachable postcondition guard"
        ).count(), 1);
        assert_eq!(out.json_output.as_ref().unwrap()["verification-results"]["verified"], 1);
        assert_eq!(out.json_output.as_ref().unwrap()["func-details"]["test_crate::target"]["obligation_proof_notes"], serde_json::json!([]));
    }
}

test_verify_one_file_with_options! {
    #[test] reachable_guard ["--smoke-guards", "--output-json"] => verus_code! {
        fn target(x: i32) -> (r: i32)
            ensures x > 0 ==> r == 42,
        { if x > 0 { 42 } else { x } }
    } => Ok(out) => {
        guard_status(&out, "target", 0, "false_not_proved");
        assert_eq!(checks(&out).len(), 1);
        assert!(out.warnings.is_empty());
        assert_eq!(out.json_output.as_ref().unwrap()["smoke-results"]["scope"], "postcondition-guard");
    }
}

test_verify_one_file_with_options! {
    #[test] guards_are_independent ["--smoke-guards", "--output-json"] => verus_code! {
        fn target(x: i32) -> (r: i32)
            requires x < 0,
            ensures x > 0 ==> r == 42, x < 0 ==> r == x,
        { x }
    } => Ok(out) => {
        guard_status(&out, "target", 0, "false_proved");
        guard_status(&out, "target", 1, "false_not_proved");
        assert_eq!(checks(&out).len(), 2);
    }
}

test_verify_one_file_with_options! {
    #[test] guard_survives_implication_simplification ["--smoke-guards", "--output-json"] => verus_code! {
        proof fn target(x: int)
            requires x < 0,
            ensures x > 0 ==> true,
        {}
    } => Ok(out) => { guard_status(&out, "target", 0, "false_proved"); }
}

test_verify_one_file_with_options! {
    #[test] guard_uses_parameter_pre_state ["--smoke-guards", "--output-json"] => verus_code! {
        fn target(mut x: i32) -> (r: i32)
            requires x < 0,
            ensures x > 0 ==> r == 42,
        { x = 1; x }
    } => Ok(out) => { guard_status(&out, "target", 0, "false_proved"); }
}

test_verify_one_file_with_options! {
    #[test] guard_does_not_assume_postconditions_or_later_facts ["--smoke-guards", "--output-json"] => verus_code! {
        proof fn target(x: int)
            ensures x <= 0, x > 0 ==> false,
        { assume(x <= 0); }
    } => Ok(out) => { guard_status(&out, "target", 1, "false_not_proved"); }
}

test_verify_one_file_with_options! {
    #[test] return_value_guard_is_skipped ["--smoke-guards", "--output-json"] => verus_code! {
        fn target() -> (r: i32)
            ensures r > 0 ==> r == 42,
        { 0 }
    } => Ok(out) => { guard_status(&out, "target", 0, "skipped"); }
}

test_verify_one_file_with_options! {
    #[test] post_state_guard_is_skipped ["--smoke-guards", "--output-json"] => verus_code! {
        fn target(p: &mut i32)
            ensures *final(p) > 0 ==> *final(p) == 42,
        { *p = 0; }
    } => Ok(out) => { guard_status(&out, "target", 0, "skipped"); }
}

test_verify_one_file_with_options! {
    #[test] quantified_guard_is_skipped ["--smoke-guards", "--output-json"] => verus_code! {
        uninterp spec fn p(x: int) -> bool;
        proof fn target()
            requires forall |x: int| #[trigger] p(x),
            ensures (forall |x: int| #[trigger] p(x)) ==> p(0),
        {}
    } => Ok(out) => { guard_status(&out, "target", 0, "skipped"); }
}

test_verify_one_file_with_options! {
    #[test] guarded_ordinary_error_is_preserved ["--smoke-guards", "--output-json"] => verus_code! {
        fn target(x: i32) -> (r: i32)
            ensures x > 0 ==> r == 42, // FAILS
        { 0 }
    } => Err(out) => {
        assert_one_fails(out.clone());
        guard_status(&out, "target", 0, "false_not_proved");
        assert_eq!(out.json_output.as_ref().unwrap()["verification-results"]["errors"], 1);
    }
}

test_verify_one_file_with_options! {
    #[test] specialized_guard_is_skipped ["--smoke-guards", "--output-json"] => verus_code! {
        #[verifier::nonlinear]
        proof fn target(x: int)
            requires x < 0,
            ensures x > 0 ==> x == 42,
        {}
    } => Ok(out) => { guard_status(&out, "target", 0, "skipped"); }
}

test_verify_one_file_with_options! {
    #[test] guard_observer_coexists_with_test_observer ["--smoke-guards", "--output-json", "observers=test"] => verus_code! {
        fn target(x: i32) -> (r: i32)
            requires x < 0,
            ensures x > 0 ==> r == 42,
        { x }
    } => Ok(out) => {
        guard_status(&out, "target", 0, "false_proved");
        let report = out.notes.iter().find_map(|n| n.message.strip_prefix("OBSERVER:")).unwrap();
        let report: serde_json::Value = serde_json::from_str(report).unwrap();
        // The delegate sees the original proof, never our fresh-context probe.
        assert_eq!(report["query_lowered"], 1);
        assert_eq!(report["check_valid_valid"], 1);
    }
}

test_verify_one_file_with_options! {
    #[test] guard_observer_coexists_with_air_only ["--smoke-guards", "--output-json", "observers=air-only"] => verus_code! {
        fn target(x: i32) -> (r: i32)
            requires x < 0,
            ensures x > 0 ==> r == 42,
        { x }
    } => Ok(out) => {
        guard_status(&out, "target", 0, "false_proved");
        assert!(out.notes.iter().any(|n| n.message.starts_with("AIROBS:")));
    }
}

test_verify_one_file_with_options! {
    #[test] guard_function_filter ["--smoke-guards", "--output-json", "--verify-root", "--verify-function=chosen"] => verus_code! {
        proof fn chosen(x: int) requires x < 0, ensures x > 0 ==> x == 42, {}
        proof fn other(x: int) requires x < 0, ensures x > 0 ==> x == 42, {}
    } => Ok(out) => {
        guard_status(&out, "chosen", 0, "false_proved");
        assert_eq!(checks(&out).len(), 1);
    }
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

//! Function-entry smoke checks. These consume copies of completed AIR and never
//! run through the ordinary verification result/counter machinery.

use air::ast::{CommandX, Commands, Query, QueryX, StmtX};
use air::context::{Context, QueryContext, ValidityResult};
use air::messages::{ArcDynMessage, Diagnostics, MessageInterface, MessageLevel};
use std::cell::RefCell;
use std::fs::File;
use std::sync::Arc;
use vir::ast::Fun;
use vir::messages::{Span, ToAny, VirMessageInterface};

pub(crate) struct EntryInput {
    pub query: Query,
    pub prefix_len: usize,
    pub prelude: Commands,
    /// The ordered background at the original query, not at the end of its SCC.
    pub background: Vec<Commands>,
    pub rlimit_override: Option<f32>,
}

pub(crate) struct EntryJob {
    pub function: Fun,
    pub span: Span,
    pub input: Result<EntryInput, String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum EntryStatus {
    FalseProved,
    FalseNotProved,
    ResourceLimit,
    Skipped,
    Error,
}

#[derive(Debug, serde::Serialize)]
pub struct EntryResult {
    pub function: String,
    pub location: String,
    pub status: EntryStatus,
    pub detail: Option<String>,
}

#[derive(Default)]
pub(crate) struct EntryLogs {
    pub air: Option<File>,
    pub air_final: Option<File>,
    pub smt: Option<File>,
    pub transcript: Option<File>,
}

/// Keep auxiliary backend diagnostics out of rustc's ordinary error state.
#[derive(Default)]
struct SmokeDiagnostics {
    messages: RefCell<Vec<String>>,
}

impl Diagnostics for SmokeDiagnostics {
    fn report(&self, message: &ArcDynMessage) {
        self.messages.borrow_mut().extend(VirMessageInterface {}.all_msgs(message));
    }

    fn report_now(&self, message: &ArcDynMessage) {
        self.report(message);
    }

    fn report_as(&self, message: &ArcDynMessage, _level: MessageLevel) {
        self.report(message);
    }

    fn report_as_now(&self, message: &ArcDynMessage, _level: MessageLevel) {
        self.report(message);
    }
}

/// Pure construction: retain the original locals/setup and replace only the
/// copied suffix. No VIR translation, fresh normal names, or Assume(false).
fn entry_query(input: &EntryInput, span: &Span) -> Result<Query, String> {
    let mut prefix = match &*input.query.assertion {
        StmtX::Block(stmts) => stmts
            .get(..input.prefix_len)
            .ok_or_else(|| "invalid function-entry boundary in captured AIR".to_string())?
            .to_vec(),
        // one_stmt collapses the singleton prefix of an empty function.
        StmtX::Snapshot(_) if input.prefix_len == 1 => vec![input.query.assertion.clone()],
        _ => return Err("invalid function-entry boundary in captured AIR".to_string()),
    };
    let message = vir::messages::error(span, "function-entry smoke goal");
    prefix.push(Arc::new(StmtX::Assert(None, message.to_any(), None, air::ast_util::mk_false())));
    Ok(Arc::new(QueryX {
        local: input.query.local.clone(),
        assertion: Arc::new(StmtX::Block(Arc::new(prefix))),
    }))
}

pub(crate) fn run_entry(
    job: &EntryJob,
    args: &crate::config::Args,
    logs: EntryLogs,
) -> EntryResult {
    let (status, detail) = match &job.input {
        Err(reason) => (EntryStatus::Skipped, Some(reason.clone())),
        Ok(input) => match run_entry_query(input, &job.span, args, logs) {
            Ok(status) => (status, None),
            Err(reason) => (EntryStatus::Error, Some(reason)),
        },
    };
    EntryResult {
        function: vir::ast_util::fun_as_friendly_rust_name(&job.function),
        location: job.span.as_string.clone(),
        status,
        detail,
    }
}

fn run_entry_query(
    input: &EntryInput,
    span: &Span,
    args: &crate::config::Args,
    logs: EntryLogs,
) -> Result<EntryStatus, String> {
    let query = entry_query(input, span)?;
    let interface: Arc<dyn MessageInterface> = Arc::new(VirMessageInterface {});
    let diagnostics = SmokeDiagnostics::default();
    // A new context owns a new solver process. Ordinary query history, naming
    // counters, error localization, profiling, and result counters are not reused.
    let mut context = Context::new(interface.clone(), args.solver);
    context.set_ignore_unexpected_smt(args.ignore_unexpected_smt);
    if let Some(log) = logs.air {
        context.set_air_initial_log(Box::new(log));
    }
    if let Some(log) = logs.air_final {
        context.set_air_final_log(Box::new(log));
    }
    if let Some(log) = logs.smt {
        context.set_smt_log(Box::new(log));
    }
    if let Some(log) = logs.transcript {
        context.set_smt_transcript_log(Box::new(log));
    }
    context.set_solver_option("air_recommended_options", "true");
    crate::verifier::Verifier::set_rlimit(&mut context, args.rlimit);
    for (name, value) in &args.smt_options {
        context.set_solver_option(name, value);
    }
    if args.axiom_usage_info {
        context.enable_usage_info();
    }
    if args.solver_version_check {
        context.set_expected_solver_version(match args.solver {
            air::context::SmtSolver::Z3 => {
                cargo_verus_toolchains::external_deps::Z3_VERSION.to_string()
            }
            air::context::SmtSolver::Cvc5 => {
                cargo_verus_toolchains::external_deps::CVC5_VERSION.to_string()
            }
        });
    }
    for commands in std::iter::once(&input.prelude).chain(input.background.iter()) {
        for command in commands.iter() {
            // Replay only the captured logical background, never old proof jobs.
            if !matches!(
                &**command,
                CommandX::Global(_) | CommandX::Push | CommandX::Pop | CommandX::SetOption(..)
            ) {
                return Err("proof query found in captured smoke background".to_string());
            }
            match context.command(&*interface, &diagnostics, command, QueryContext::default()) {
                ValidityResult::Valid(_) => (),
                other => return Err(format!("could not replay smoke background: {other:?}")),
            }
        }
    }
    // Match ordinary setup order: a supported function-local budget overrides
    // the global/default options after constructing the query context.
    if let Some(rlimit) = input.rlimit_override {
        crate::verifier::Verifier::set_rlimit(&mut context, rlimit);
    }
    context.comment("Independent function-entry smoke query");
    let result = context.check_valid(&*interface, &diagnostics, &query, QueryContext::default());
    let status = match result {
        ValidityResult::Valid(_) => EntryStatus::FalseProved,
        // AIR also uses Invalid for some incomplete/unknown solver results.
        ValidityResult::Invalid(..) => EntryStatus::FalseNotProved,
        ValidityResult::Canceled => EntryStatus::ResourceLimit,
        ValidityResult::TypeError(error) => return Err(format!("smoke AIR type error: {error}")),
        ValidityResult::UnexpectedOutput(output) => {
            return Err(format!("unexpected smoke solver output: {output}"));
        }
    };
    context.finish_query();
    let messages = diagnostics.messages.into_inner();
    if messages.is_empty() { Ok(status) } else { Err(messages.join("\n")) }
}

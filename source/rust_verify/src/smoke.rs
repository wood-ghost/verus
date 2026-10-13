//! Entry-context smoke checks, collected through the verification observer.
//! These consume copies of completed AIR and never run through the ordinary
//! verification result/counter machinery.

use air::ast::{CommandX, Commands, Expr, Query, QueryX, StmtX};
use air::context::{Context, QueryContext, ValidityResult};
use air::messages::{ArcDynMessage, Diagnostics, MessageInterface, MessageLevel};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::rc::Rc;
use std::sync::Arc;
use vir::ast::Fun;
use vir::messages::{Span, ToAny, VirMessageInterface};
use vir::vir_observer::VirObserver;

#[derive(Clone)]
pub(crate) struct Guard {
    pub clause: usize,
    pub span: Span,
    pub condition: Result<Expr, String>,
}

#[derive(Clone)]
pub(crate) struct Body {
    pub query: Query,
    pub prefix_len: usize,
    pub guards: Vec<Guard>,
}

/// Read-only consumer of Matthew Dwyer's observer interface. A delegate keeps
/// other registered observers operational without changing their assertion IDs.
#[derive(Default)]
pub(crate) struct SmokeObserver {
    pub delegate: Option<Rc<RefCell<dyn VirObserver>>>,
    pending: Vec<(usize, vir::sst::Exp, Expr)>,
    // Every stored value owns its query Arc, so keys cannot be reused while live.
    bodies: HashMap<usize, Body>,
}

impl SmokeObserver {
    pub fn new(delegate: Option<Rc<RefCell<dyn VirObserver>>>) -> Self {
        Self { delegate, ..Self::default() }
    }

    fn forward(&self, f: impl FnOnce(&mut dyn VirObserver)) {
        if let Some(delegate) = &self.delegate {
            f(&mut *delegate.borrow_mut());
        }
    }

    pub fn body(&self, query: &Query) -> Option<&Body> {
        self.bodies.get(&(Arc::as_ptr(query) as usize))
    }
}

fn input_state_guard(exp: &vir::sst::Exp, inputs: &HashSet<vir::ast::VarIdent>) -> bool {
    use vir::sst::ExpX;
    match &exp.x {
        ExpX::Const(_) => true,
        ExpX::Var(x) | ExpX::VarAt(x, vir::ast::VarAt::Pre) => inputs.contains(x),
        ExpX::Unary(_, e) | ExpX::UnaryOpr(_, e) => input_state_guard(e, inputs),
        ExpX::Binary(_, lhs, rhs) | ExpX::BinaryOpr(_, lhs, rhs) => {
            input_state_guard(lhs, inputs) && input_state_guard(rhs, inputs)
        }
        ExpX::If(c, t, e) => {
            input_state_guard(c, inputs)
                && input_state_guard(t, inputs)
                && input_state_guard(e, inputs)
        }
        ExpX::Call(vir::sst::CallFun::Fun(..), _, args) => {
            args.iter().all(|e| input_state_guard(e, inputs))
        }
        // Return variables, mutable-reference state, binders, closures, and
        // other expression forms require a separate checkpoint correspondence.
        _ => false,
    }
}

impl VirObserver for SmokeObserver {
    fn on_krate(
        &mut self,
        krate: &vir::ast::Krate,
        names: &vir::def::NameCtxt,
        id: &vir::ast::CrateId,
    ) {
        self.forward(|o| o.on_krate(krate, names, id));
    }
    fn on_havoc(&mut self, stm: &vir::sst::Stm, var: &vir::ast::VarIdent) {
        self.forward(|o| o.on_havoc(stm, var));
    }
    fn on_assign(&mut self, stm: &vir::sst::Stm, var: &vir::ast::VarIdent) {
        self.forward(|o| o.on_assign(stm, var));
    }
    fn on_variable_def(&mut self, stm: &vir::sst::Stm, var: &vir::ast::VarIdent) {
        self.forward(|o| o.on_variable_def(stm, var));
    }
    fn on_for_loop(&mut self, stm: &vir::sst::Stm) {
        self.forward(|o| o.on_for_loop(stm));
    }
    fn on_quantifier_binder(
        &mut self,
        binder: &vir::ast::VarBinder<vir::ast::Typ>,
        exp: &vir::sst::Exp,
    ) {
        self.forward(|o| o.on_quantifier_binder(binder, exp));
    }
    fn on_reveal_string(&mut self, lit: &Arc<String>) {
        self.forward(|o| o.on_reveal_string(lit));
    }
    fn make_assert_id(
        &mut self,
        kind: vir::vir_observer::AssertIdKind,
        index: usize,
        parent: &Option<air::ast::AssertId>,
    ) -> Option<air::ast::AssertId> {
        self.delegate
            .as_ref()
            .map_or_else(|| parent.clone(), |o| o.borrow_mut().make_assert_id(kind, index, parent))
    }
    fn on_binder_decl(&mut self, decl: &vir::sst::LocalDecl) {
        self.forward(|o| o.on_binder_decl(decl));
    }
    fn on_body_lowering_start(&mut self) {
        self.pending.clear();
        self.forward(|o| o.on_body_lowering_start());
    }
    fn on_function_lowered(&mut self) {
        self.forward(|o| o.on_function_lowered());
    }
    fn on_postcondition_guard(&mut self, clause: usize, guard: &vir::sst::Exp, guard_air: &Expr) {
        self.pending.push((clause, guard.clone(), guard_air.clone()));
        self.forward(|o| o.on_postcondition_guard(clause, guard, guard_air));
    }
    fn on_body_query_lowered(
        &mut self,
        function: &Fun,
        query: &Query,
        entry_prefix_len: usize,
        params: &vir::sst::Pars,
    ) {
        let inputs: HashSet<_> = params
            .iter()
            .filter(|p| {
                matches!(
                    &*p.x.typ,
                    vir::ast::TypX::Bool | vir::ast::TypX::Int(_) | vir::ast::TypX::Real
                )
            })
            .map(|p| p.x.name.clone())
            .collect();
        let guards = self.pending.iter().map(|(clause, guard, condition)| Guard {
            clause: *clause,
            span: guard.span.clone(),
            condition: if input_state_guard(guard, &inputs) {
                Ok(condition.clone())
            } else {
                Err("guard is not a supported scalar input-state expression (return/post-state values and binders are unchecked)".to_string())
            },
        }).collect();
        self.bodies.insert(
            Arc::as_ptr(query) as usize,
            Body { query: query.clone(), prefix_len: entry_prefix_len, guards },
        );
        self.forward(|o| o.on_body_query_lowered(function, query, entry_prefix_len, params));
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ProbeKind {
    FunctionEntry,
    PostconditionGuard,
}

#[derive(Clone)]
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
    pub kind: ProbeKind,
    pub clause: Option<usize>,
    pub condition: Option<Expr>,
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
    pub kind: ProbeKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub clause: Option<usize>,
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
/// copied suffix. Only the selected source guard is assumed; false is the goal.
fn entry_query(input: &EntryInput, span: &Span, condition: &Option<Expr>) -> Result<Query, String> {
    let mut prefix = match &*input.query.assertion {
        StmtX::Block(stmts) => stmts
            .get(..input.prefix_len)
            .ok_or_else(|| "invalid function-entry boundary in captured AIR".to_string())?
            .to_vec(),
        // one_stmt collapses the singleton prefix of an empty function.
        StmtX::Snapshot(_) if input.prefix_len == 1 => vec![input.query.assertion.clone()],
        _ => return Err("invalid function-entry boundary in captured AIR".to_string()),
    };
    if let Some(condition) = condition {
        prefix.push(Arc::new(StmtX::Assume(condition.clone())));
    }
    let message = vir::messages::error(span, "entry-context smoke goal");
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
        Ok(input) => match run_entry_query(input, &job.span, &job.condition, args, logs) {
            Ok(status) => (status, None),
            Err(reason) => (EntryStatus::Error, Some(reason)),
        },
    };
    EntryResult {
        function: vir::ast_util::fun_as_friendly_rust_name(&job.function),
        location: job.span.as_string.clone(),
        kind: job.kind,
        clause: job.clause,
        status,
        detail,
    }
}

fn run_entry_query(
    input: &EntryInput,
    span: &Span,
    condition: &Option<Expr>,
    args: &crate::config::Args,
    logs: EntryLogs,
) -> Result<EntryStatus, String> {
    let query = entry_query(input, span, condition)?;
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
    context.comment("Independent entry-context smoke query");
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

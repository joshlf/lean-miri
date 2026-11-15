//! Small, compilation-scoped experiment: Lean asks a live rustc TyCtxt for layouts.
#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};
use std::time::Instant;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_middle::ty::{self, TyCtxt};
use serde_json::{Value, json};

const PIN: &str = "8144389c895da997dbdecaa635e41d6a50be6ffd";

struct Probe {
    lean: String,
    script: String,
    result: Option<Result<Value, String>>,
}

impl Callbacks for Probe {
    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.result = Some(probe(tcx, &self.lean, &self.script));
        Compilation::Stop
    }
}

fn probe(tcx: TyCtxt<'_>, lean: &str, script: &str) -> Result<Value, String> {
    let foo = tcx.hir_crate_items(()).definitions().find(|&id| {
        tcx.def_path_str(id.to_def_id()) == "Foo"
    }).ok_or_else(|| format!("fixture must define Foo<T>; found {:?}",
        tcx.hir_crate_items(()).definitions().map(|id| tcx.def_path_str(id.to_def_id())).collect::<Vec<_>>()))?;
    let adt = tcx.adt_def(foo.to_def_id());
    let mut child = Command::new(lean).args(["--run", script])
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit())
        .spawn().map_err(|e| format!("spawn Lean: {e}"))?;
    let mut stdin = child.stdin.take().ok_or("Lean stdin unavailable")?;
    let mut stdout = BufReader::new(child.stdout.take().ok_or("Lean stdout unavailable")?);
    let started = Instant::now();
    let mut startup_ns = None;
    let mut requests = Vec::new();
    let lean_roundtrip_ns = loop {
        let mut line = String::new();
        if stdout.read_line(&mut line).map_err(|e| e.to_string())? == 0 {
            return Err("Lean exited before protocol completion".into());
        }
        let request: Value = serde_json::from_str(&line)
            .map_err(|e| format!("Lean protocol JSON: {e}: {line}"))?;
        if request["op"] == "ready" {
            startup_ns = Some(started.elapsed().as_nanos());
            continue;
        }
        if request["op"] == "done" {
            break request["lean_roundtrip_ns"].clone();
        }
        if request["op"] != "layout_of" {
            return Err(format!("unsupported request: {request}"));
        }
        let name = request["type"].as_str().ok_or("missing type")?;
        let arg = match name {
            "u8" => ty::Ty::new_uint(tcx, ty::UintTy::U8),
            "u64" => ty::Ty::new_uint(tcx, ty::UintTy::U64),
            _ => return Err(format!("unsupported type: {name}")),
        };
        let concrete = ty::Ty::new_adt(tcx, adt, tcx.mk_args(&[arg.into()]));
        let query_start = Instant::now();
        let layout = tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(concrete))
            .map_err(|e| format!("layout_of({concrete}): {e:?}"))?;
        let query_ns = query_start.elapsed().as_nanos();
        let response = json!({"size":layout.size.bytes(), "align":layout.align.abi.bytes()});
        writeln!(stdin, "{response}").map_err(|e| e.to_string())?;
        stdin.flush().map_err(|e| e.to_string())?;
        requests.push(json!({"type":name,"query_ns":query_ns,"size":layout.size.bytes(),"align":layout.align.abi.bytes()}));
    };
    drop(stdin);
    let status = child.wait().map_err(|e| e.to_string())?;
    if !status.success() { return Err(format!("Lean exited with {status}")); }
    Ok(json!({"rustc_context":"after_analysis callback, live until Lean child exit",
        "lean_startup_ns":startup_ns,"callback_wall_ns":started.elapsed().as_nanos(),
        "query_count":requests.len(),"requests":requests,
        "lean_roundtrip_ns":lean_roundtrip_ns}))
}

fn main() {
    if let Err(e) = run() {
        eprintln!("provider probe: {e}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    if env!("LEAN_MIRI_PINNED_RUSTC_COMMIT") != PIN {
        return Err("compiler pin mismatch".into());
    }
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 3 { return Err("usage: lean-rustc-provider-probe LEAN SCRIPT FIXTURE".into()); }
    let mut callbacks = Probe { lean: args[0].clone(), script: args[1].clone(), result: None };
    let rustc_args = vec!["rustc".into(), "--crate-name".into(), "provider_probe".into(),
        "--crate-type".into(), "lib".into(), "--edition".into(), "2024".into(),
        "--emit".into(), "metadata".into(), args[2].clone()];
    let status = rustc_driver::catch_with_exit_code(||
        rustc_driver::compiler_entrypoint(&rustc_args, &mut callbacks));
    if status != std::process::ExitCode::SUCCESS { return Err("rustc failed".into()); }
    let result = callbacks.result.ok_or("after_analysis did not run")??;
    println!("{result}");
    Ok(())
}

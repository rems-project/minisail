(**************************************************************************)
(*     MiniSail                                                           *)
(*                                                                        *)
(**************************************************************************)

open Ast
open Ast_util


let options =
  Arg.align ([
      ( "-dump_raw_ast",
        Arg.String (fun file -> Minisail.opt_dump := Some file),
        "<filename> Dump type check Sail AST to file");
      ( "-validate",
        Arg.Set Minisail.opt_validate,
        " Validate type checked Sail");
      ( "-convert",
        Arg.String (fun s -> Minisail.opt_convert := Some s),
        "<filename> Convert Sail to MiniSail and write to file");
      ( "-spec",
        Arg.Set Minisail.opt_spec,
        "Specialise Type and Order polymorphism (from toplevel lets)");
      ( "-smt_solver",
        Arg.String (fun s -> Constraint.set_solver (String.trim s)),
        "<solver> choose SMT solver. Supported solvers are z3 (default), alt-ergo, cvc4, mathsat, vampire and yices.");
      ( "-smt_linearize",
        Arg.Set Type_check.opt_smt_linearize,
        "(experimental) force linearization for constraints involving exponentials");
      ( "-new_bitfields",
        Arg.Set Type_check.opt_new_bitfields,
        " use new bitfield syntax");
      ( "-non_lexical_flow",
        Arg.Set Nl_flow.opt_nl_flow,
        " allow non-lexical flow typing");
    ] )

let usage_msg = "usage: minisail <options> <file1.sail> ... <fileN.sail>\n"


let main () =
  let open Process_file in
  let opt_file_arguments = ref [] in
  Arg.parse options (fun s ->
      opt_file_arguments := (!opt_file_arguments) @ [s])
    usage_msg;

  (* These options are either needed for ARM, or increase performance significantly (memo_z3) *)
  Nl_flow.opt_nl_flow := true;
  Type_check.opt_no_lexp_bounds_check := true;
  Process_file.opt_memo_z3 := true;
  Reporting.opt_warnings := false;
  Initial_check.opt_magic_hash := true;
  Type_check.opt_no_effects := true;

  let _, ast, env = load_files options Type_check.initial_env !opt_file_arguments in

  (* Combined scattered defs *)
  let ast, env = descatter env ast in

  (* Desugar bidirectional mappings *)
  let ast = Rewrites.rewrite_ast_realise_mappings env ast in 

  
  (* Note that this will throw out functions not accessible from top level let-binds *)
  let ast, env =
    (if !Minisail.opt_spec then
      Specialize.(specialize typ_ord_specialization env ast)
    else
      (ast,env) ) in 

  (*let _ = Sail_show.show_ast ast in*)
  
  Minisail.minisail env ast
  
let () =
  try main () with
  | Reporting.Fatal_error e ->
     Reporting.print_error e;
     exit 1

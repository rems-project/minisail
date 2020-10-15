open Ast
open Ast_defs
open Minisail_isa
open Type_check

open PPrintEngine
open PPrintCombinators
open Sail_pp
open Annot_pp
   
let opt_validate  = ref false
let opt_convert : string option ref = ref None
let opt_dump : string option ref = ref None
let opt_spec = ref false 

let _ = Sail_pp.pp_json_annot_ref := (Some Annot_pp.pp_json_annot)
             
let check_def env n i sdef =
  Printf.eprintf "Checking def %d/%d:\n" i n;
  PPrintEngine.ToChannel.compact stderr ((pp_def sdef) ^^ string "\n");
  let def = Convert.convert_def env sdef in 
  let (Set.Set res) = Predicate.set_of_pred
             {equal=fun x y -> (x == y)} (Validator.check_def_i_i Minisail_isa.SailEnv.emptyEnv def) in
  match res with
    [] -> Printf.eprintf "Failed. No derivations.\n\n";
          (*          ToChannel.pretty 1. 80 stderr (Sail_pp.pp_raw_def sdef); *)
          (*Printf.eprintf "\n";*)
          exit(2)
  |  xs -> Printf.eprintf "OK.\n\n"

                   
let tc_check env ast  : unit = List.iteri (check_def env (List.length ast.defs)) ast.defs


let opt_dtc_convert = ref false

let pp_ms_def_aux = function
    SailToMs.MS_type_def tdef -> Minisail_pp.pp_tdef tdef ^^ hardline
  | MS_fun_def  fdef -> Minisail_pp.pp_fdef fdef ^^ hardline
  | MS_val_spec (f,x,b,c,t) -> string "val " ^^ string (Stringa.implode f) ^^ string " : " ^^
                                 Minisail_pp.pp_x x ^^
                                 string " : " ^^ Minisail_pp.pp_b b ^^ string "[" ^^
                                   Minisail_pp.pp_c c ^^ string "] -->"  ^^
                                     Minisail_pp.pp_t t ^^ hardline
  | MS_register (u,t,v) -> string "register " ^^ Minisail_pp.pp_t t ^^ string " = " ^^ Minisail_pp.pp_v v ^^ hardline

let pp_ms_def = function
    Some td -> pp_ms_def_aux td
  | None -> string ""

let convert_def c env n i sdef =
  Printf.eprintf "Converting def %d/%d:\n" (i+1) n;
  PPrintEngine.ToChannel.compact stderr ((pp_def sdef) ^^ string "\n");
  let def = Convert.convert_def env sdef in 
  let (Set.Set res) = Predicate.set_of_pred
             {equal=fun x y -> (x == y)} (SailToMs.def_conv_i_i_o Minisail_isa.SailEnv.emptyEnv def) in
  match res with
    [] -> Printf.eprintf "Failed. No derivations.\n\n";
  (*          ToChannel.pretty 1. 80 stderr (Sail_pp.pp_raw_def sdef);  *)
          (*Printf.eprintf "\n";*)

  |  (x :: xs) -> Printf.eprintf "OK.\n";
                  ToChannel.pretty 1. 80 c (pp_ms_def x);
                  Printf.eprintf "\n"

(* Pretty_print_sail.pp_defs_ott_pp c ast; close_out c) in*)
                   
let tc_convert env  ast fname : unit =
  let c = open_out fname in   
  let _ = List.iteri (convert_def c env (List.length ast.defs)) ast.defs in
  close_out c

let pp_raw_defs ast = string "[" ^^ separate (string ",\n") (List.map pp_json_def ast.defs) ^^ string "]"
  
let minisail env ast =
  let _ = match !opt_dump with
      Some file -> (let c = open_out file in ToChannel.pretty 1. 80 c (pp_raw_defs ast); close_out c)  
    | None -> () in

  let _ = if ! opt_validate then  tc_check env ast else () in
  
  let _ = match !opt_convert with
      Some file -> tc_convert env ast file
    | None -> () in

  ()

                                                  
    

theory MiniSailPP
(*imports Utils Env AstUtils ShowAST MiniSail.IVSubst   CodeGenPrelude "HOL-Library.Debug" *)
imports SailToMS

begin

value "mk_x 0"

fun pp_atom :: "atom \<Rightarrow> string" where
  "pp_atom ((Atom  (Sort _ _)  i)) = ((STR ''x'') + (String.implode (show i)))"

lift_definition pp_x :: "x \<Rightarrow> string" is pp_atom .

fun concat_str :: "('a \<Rightarrow> string)  \<Rightarrow> 'a list \<Rightarrow> string" where
 "concat_str _ [] = STR ''''"
| "concat_str f (x#xs) = f x + (concat_str f xs)"

fun pp_bit :: "bit \<Rightarrow> string" where
  "pp_bit BitOne = STR ''1''"
| "pp_bit BitZero = STR ''0''"

fun pp_l :: "l \<Rightarrow> string" where
  "pp_l L_true = STR ''T''"
|  "pp_l L_false = STR ''F''"
|  "pp_l L_unit = STR ''()''"
| "pp_l (L_num n) = String.implode (show n)"
| "pp_l (L_bitvec s) = STR ''0b'' + (concat_str pp_bit s)"

fun pp_v :: "v \<Rightarrow> string" where
  "pp_v (V_var x) = pp_x x"
| "pp_v (V_pair v1 v2) = STR ''('' + (pp_v v1) + STR '','' + (pp_v v2) + STR '')''"
| "pp_v (V_lit l) = pp_l l"
| "pp_v (V_cons tyid dc v) = (String.implode dc) + (pp_v v)"
| "pp_v (V_consp tyid dc b v) = (String.implode dc) + (pp_v v)"

fun pp_e :: "e \<Rightarrow> string" where
  "pp_e (AE_val v) = pp_v v"

(*
fun pp_raw_s :: "s_raw \<Rightarrow> string " where
  "pp_raw_s (AS_val_raw v) = pp_v v"

lift_definition pp_s :: "s \<Rightarrow> string" is pp_raw_s .
*)

(*
fun pp_s :: "s \<Rightarrow> string" where
  "pp_s (Abs_s s) = STR ''s''"
*)
(*
fun pp_s :: "s \<Rightarrow> String.string" and
    pp_branch :: "branch_s \<Rightarrow> String.string" and
    pp_branchs :: "branch_list \<Rightarrow> String.string" 
    where
  "pp_s (AS_val v) = String.explode (pp_v v)"
| "pp_s (AS_let x e s) = String.explode (STR ''let '' + (pp_x x) + STR ''='' + (pp_e e) + STR ''in'') @ pp_s s"
| "pp_branch (AS_branch dc x1 s1) = dc @ '' '' @ pp_s s1 "
| "pp_branchs (AS_final cs) = pp_branch cs"
| "pp_branchs (AS_cons cs css) = pp_branch cs @ '' | ''@ pp_branchs css"
  sorry

(*  "pp_s (AS_val v) = pp_v v"
| "pp_s (AS_let x e s) = STR ''let '' + (pp_x x) + STR ''='' + (pp_e e) + STR ''in'' + pp_s s"
| "pp_branch (AS_branch dc x1 s1) = (String.implode dc) + STR '' '' + pp_x x1 + STR ''=>'' + pp_s s1 "
| "pp_branchs (AS_final cs) = pp_branch cs"
| "pp_branchs (AS_cons cs css) = pp_branch cs + STR '' | '' + pp_branchs css"*)

thm Abs_s_cases

value "pp_s (AS_val (V_var (mk_x 0)))"
*)
end
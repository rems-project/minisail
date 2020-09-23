theory TypeChecker
(* Analog of Sails type checker. Model the functions and their signatures in type_check.ml *)
imports "HOL-Library.Monad_Syntax"  Env Native_Word.Uint32 AstUtils ShowAST  "HOL-Library.Debug" Checker
begin

(* 
let rec check_exp env (E_aux (exp_aux, (l, ())) as exp : unit exp) (Typ_aux (typ_aux, _) as typ) : tannot exp =
  let annot_exp_effect exp typ' eff = E_aux (exp, (l, mk_expected_tannot env typ' eff (Some typ))) in
  let add_effect exp eff = match exp with
    | E_aux (exp, (l, Some tannot)) -> E_aux (exp, (l, Some { tannot with effect = eff }))
    | _ -> failwith "Tried to add effect to unannoted expression"
  in
  let annot_exp exp typ = annot_exp_effect exp typ no_effect in
  match (exp_aux, typ_aux) with
  | E_block exps, _ ->
     annot_exp (E_block (check_block l env exps (Some typ))) typ
*)

fun  mk_effect ::  "base_effect_aux list \<Rightarrow> effect" where
  "mk_effect effs =  Effect_aux (Effect_set (List.map (\<lambda>be_aux. BE_aux be_aux) effs))"

definition "no_effect = mk_effect []"


fun mk_expected_tannot :: "env \<Rightarrow> typp \<Rightarrow> effect \<Rightarrow> typp option \<Rightarrow> tannot exp" where
  "mk_expected_tannot env typp eff typ' = undefined"

(* This style following the ML isn't going to fly. We need to put all functions and match-statements as the 
top level
fun check_exp :: "env \<Rightarrow> unit exp \<Rightarrow> typp \<Rightarrow> tannot exp" where
  "check_exp env (E_aux exp_aux ()) typ = (
    let annot_exp_effect = \<lambda>exp typ' eff. E_aux exp (mk_expected_tannot env typ' eff (Some typ)) in
    let annot_exp = \<lambda>exp typ. annot_exp_effect exp typ no_effect in
    undefined)
"
*)

datatype fail_reason = Lookup | Subtype

datatype 'a error_ok = OK 'a | Error fail_reason

definition return :: "'a \<Rightarrow> 'a error_ok" where
  "return x = OK x"

definition fail :: "fail_reason \<Rightarrow> 'a error_ok" where
  "fail r = Error r"

fun error_ok_bind :: "'a error_ok \<Rightarrow> ('a \<Rightarrow> 'b error_ok) \<Rightarrow> 'b error_ok" where
  "error_ok_bind (Error r) f = Error r"
| "error_ok_bind (OK x) f = f x"
                        

adhoc_overloading
  Monad_Syntax.bind error_ok_bind


fun annot_exp :: "env \<Rightarrow> typp \<Rightarrow> tannot exp_aux \<Rightarrow> tannot exp" where
  "annot_exp env typp exp = E_aux exp None"

value "bool_typ True"

fun check_lit :: "lit \<Rightarrow> typp \<Rightarrow> bool" where
  "check_lit (L_aux L_unit) typ = (typ = unit_typ)"
| "check_lit (L_aux L_true) typ = (typ = bool_typ True)"
| "check_lit (L_aux L_false) typ = (typ = bool_typ False)"

fun check_exp :: "env \<Rightarrow> unit exp \<Rightarrow> typp \<Rightarrow> (tannot exp) error_ok " and
    check_exp_aux :: "env \<Rightarrow> unit exp_aux \<Rightarrow> typp \<Rightarrow> (tannot exp) error_ok" and
    check_block :: "env \<Rightarrow> (unit exp) list \<Rightarrow> typp option \<Rightarrow> ((tannot exp) list) error_ok"
    where
  "check_exp env (E_aux exp_aux ()) typ = check_exp_aux env exp_aux typ"
| "check_exp_aux env (E_block exps) typ = (check_block env exps (Some typ) \<bind> (\<lambda>x. return (annot_exp env typ (E_block x))))"
| "check_exp_aux env (E_lit l) typ = (if check_lit l typ then return (annot_exp env typ (E_lit l)) else fail Subtype)"
| "check_exp_aux _ _ _ = fail Subtype"
| "check_block env [exp] (Some typ) = check_exp env exp typ \<bind> (\<lambda>x. return [x])"
| "check_block env [exp] (None) = check_exp env exp unit_typ \<bind> (\<lambda>x. return [x])"
| "check_block env (exp#exps) typ = (check_exp env exp unit_typ \<bind> (\<lambda>x. 
                                    check_block env exps typ \<bind> (\<lambda>xs. return (x#xs))))"
| "check_block env [] typ = fail Subtype"


value "check_exp emptyEnv (E_aux (E_lit (L_aux L_true)) ()) (bool_typ True)"

value "check_exp emptyEnv (E_aux (E_block [E_aux (E_lit (L_aux L_true)) ()]) ()) (bool_typ True)"

value "check_exp emptyEnv (E_aux (E_block [E_aux (E_lit (L_aux L_true)) () , E_aux (E_lit (L_aux L_true)) ()]) ()) (bool_typ True)"

value "check_exp emptyEnv (E_aux (E_block [E_aux (E_lit (L_aux L_unit)) () , E_aux (E_lit (L_aux L_true)) ()]) ()) (bool_typ True)"

section \<open>Soundness\<close>

thm check_exp_check_exp_aux_check_block.induct

(* For this to work, we need a Checker.check_exp_aux and Checker.check_block *)
lemma 
  shows  "check_exp env exp typ = (OK exp') \<Longrightarrow> Checker.check_exp exp' []" and
         "check_exp_aux env exp_aux typ = OK exp_aux' \<Longrightarrow> True"  and
         "check_block env exp_block typ_opt = OK exp_block' \<Longrightarrow> True"  
proof(induct rule: check_exp_check_exp_aux_check_block.induct)
case (1 env exp_aux "typ")
then show ?case 
next
case (2 env exps "typ")
then show ?case sorry
next
  case (3 env l "typ")
  then show ?case sorry
next
  case ("4_1" uu v uw)
  then show ?case sorry
next
  case ("4_2" uu v va uw)
  then show ?case sorry
next
  case ("4_3" uu v uw)
  then show ?case sorry
next
  case ("4_4" uu v va uw)
  then show ?case sorry
next
  case ("4_5" uu v va vb uw)
  then show ?case sorry
next
  case ("4_6" uu v va vb uw)
  then show ?case sorry
next
  case ("4_7" uu v va vb vc uw)
  then show ?case sorry
next
  case ("4_8" uu v va vb vc vd ve uw)
  then show ?case sorry
next
  case ("4_9" uu v uw)
  then show ?case sorry
next
  case ("4_10" uu v va uw)
  then show ?case sorry
next
  case ("4_11" uu v va vb uw)
  then show ?case sorry
next
  case ("4_12" uu v va vb uw)
  then show ?case sorry
next
  case ("4_13" uu v va vb vc uw)
  then show ?case sorry
next
  case ("4_14" uu v va uw)
  then show ?case sorry
next
  case ("4_15" uu v uw)
  then show ?case sorry
next
  case ("4_16" uu v va uw)
  then show ?case sorry
next
  case ("4_17" uu v uw)
  then show ?case sorry
next
  case ("4_18" uu v va uw)
  then show ?case sorry
next
  case ("4_19" uu v va uw)
  then show ?case sorry
next
  case ("4_20" uu v va uw)
  then show ?case sorry
next
  case ("4_21" uu v va uw)
  then show ?case sorry
next
  case ("4_22" uu v va uw)
  then show ?case sorry
next
  case ("4_23" uu v uw)
  then show ?case sorry
next
  case ("4_24" uu v uw)
  then show ?case sorry
next
  case ("4_25" uu v uw)
  then show ?case sorry
next
  case ("4_26" uu v uw)
  then show ?case sorry
next
  case ("4_27" uu v uw)
  then show ?case sorry
next
  case ("4_28" uu v va uw)
  then show ?case sorry
next
  case ("4_29" uu v va uw)
  then show ?case sorry
next
  case ("4_30" uu v va vb uw)
  then show ?case sorry
next
  case ("4_31" uu v va vb uw)
  then show ?case sorry
next
  case ("4_32" uu v uw)
  then show ?case sorry
next
  case ("4_33" uu v uw)
  then show ?case sorry
next
  case ("4_34" uu v uw)
  then show ?case sorry
next
  case (5 env exp "typ")
  then show ?case sorry
next
case (6 env exp)
  then show ?case sorry
next
case ("7_1" env exp v va "typ")
then show ?case sorry
next
  case ("7_2" env exp v va)
  then show ?case sorry
next
  case (8 env "typ")
  then show ?case sorry
qed


end


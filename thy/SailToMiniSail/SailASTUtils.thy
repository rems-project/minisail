theory SailASTUtils
  imports  SailAST.SailAST
begin

section \<open>AST Utils\<close>

definition unit_typ where
  "unit_typ \<equiv> ( (Typ_id  ( (id  (STR ''unit'')) )) )"

definition num_typ where
  "num_typ n \<equiv>  ( (Typ_app  ( (id  (STR ''atom''))  ) 
     [( (A_nexp  ( (Nexp_constant  n)  ))  ) ] )  )"

definition int_typ where 
  "int_typ \<equiv>  ( (Typ_id  ( (id  (STR ''int'')) )) )"

fun bool_typ where
  "bool_typ b =  ( (Typ_app  ( (id  (STR ''atom_bool''))  ) 
     [( (A_bool  ( (if b then NC_true  else NC_false )  ))  ) ] )  )"

definition bool_all_typ where
  "bool_all_typ = ( (Typ_id  ( (id  (STR ''bool'')) )) )"

abbreviation "nc_eq \<equiv> \<lambda>n1 n2.  (NC_equal  n1 n2) "

abbreviation "nint \<equiv> \<lambda>i.  (Nexp_constant  i) "

abbreviation "nc_pos \<equiv> \<lambda>ne.  (NC_bounded_ge  ne (nint 0))"

abbreviation "nc_true \<equiv>  NC_true"


(*
abbreviation "nexp_simp \<equiv> \<lambda>n. n"
*)



abbreviation nexp_var where
  "nexp_var s \<equiv>  (Nexp_var  ( (var  s)))"

abbreviation atom_typ_var where
  "atom_typ_var s \<equiv>  (Typ_app  ( (id  (STR ''atom''))) [  (A_nexp   ( (Nexp_var  ( (var  s))))) ] )"

abbreviation nexp_const where
  "nexp_const s \<equiv>  (Nexp_constant  s)"

abbreviation num_or where
 "num_or n1 n2 \<equiv>  (Typ_exist  [] ( (NC_or  (nc_eq  (nexp_var  (STR ''n'')) (nexp_const  1)) 
(nc_eq (nexp_var (STR ''n'')) (nexp_const 2)))) (atom_typ_var (STR ''n'') ))"

(* Should be possible to setup a deriving generator for this *)
fun collect_pat :: " 'a pat \<Rightarrow>  id list" where
  "collect_pat  (P_or t p1 p2)  =  collect_pat p1 @ collect_pat p2"
| "collect_pat  (P_not t p)  =  collect_pat p"
| "collect_pat  (P_tup t pats)  =  concat (map (collect_pat) pats)"
| "collect_pat  (P_as t pat i ) =  collect_pat pat @ [i]"
| "collect_pat  (P_typ t typ pat) = collect_pat pat"
| "collect_pat  (P_app t ff pats) =concat (map (collect_pat) pats)"
| "collect_pat  (P_vector t  pats) =  concat (map (collect_pat) pats)"
| "collect_pat  (P_vector_concat  t pats) = concat (map (collect_pat) pats)"
| "collect_pat  (P_list t pats) =  concat (map (collect_pat) pats)"
| "collect_pat  (P_cons t p1 p2) =  collect_pat p1 @ collect_pat p2"
| "collect_pat  (P_string_append t pats) = concat (map (collect_pat) pats)"
| "collect_pat  (P_id _ i) = [i]"
| "collect_pat  p = []"




fun collect_e ::  "'a exp \<Rightarrow>  id list" and 
    collect_pexp ::  "'a pexp \<Rightarrow>  id list" and
    collect_lexp :: "'a lexp \<Rightarrow> id list" and
    collect_letbind :: "'a letbind \<Rightarrow> id list"

  where
 "collect_pexp  (Pat_exp t p e) = collect_pat p @ collect_e e"

| "collect_e  (E_block t es) = (concat (map (collect_e ) es))"
| "collect_e  (E_if t e1 e2 e3) = collect_e  e1 @ collect_e  e2 @ collect_e  e3"
| "collect_e  (E_case t e1 pexps) =  concat (map (collect_pexp ) pexps)"
| "collect_e  (E_app t f es) =  concat (map (collect_e ) es)"
| "collect_e  (E_let t lb e) =  collect_letbind lb @ collect_e e"
| "collect_e  (E_assign t lexp e1) =  collect_lexp lexp @ collect_e e1"
| "collect_e  (E_id _ i) = [i]"
| "collect_e (E_lit _ _ ) = []"
| "collect_e (E_tuple _ es) =  concat (map (collect_e ) es)"

| "collect_lexp (LEXP_id _ i) = [i]"
| "collect_lexp (LEXP_cast _ _ i) = [i]"

| "collect_letbind (LB_val _ pat exp) = collect_pat pat @ collect_e exp"

fun collect_pexp_funcl_ids :: "'a pexp_funcl \<Rightarrow> id list" where
   "collect_pexp_funcl_ids (PEXP_funcl pexp) = collect_pexp pexp" 

fun collect_ids :: "'a funcl \<Rightarrow> id list" where
  "collect_ids (FCL_Funcl _ _ pf) = remdups (collect_pexp_funcl_ids pf)"

end

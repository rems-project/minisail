theory ConvertDBI
imports  WellformedDBI MiniSail.Wellformed 
begin



section \<open>Conversion of terms\<close>

(* At each new binder we stack a fresh atom onto a list and then use index of variable in DBI form to 
   get the appropriate Nominal variable.
   We need 3 of these lists *)

type_synonym x_list = "Syntax.x list"
type_synonym bv_list = "Syntax.bv list"
type_synonym u_list = "Syntax.u list"

(*
fun mk_x :: "nat \<Rightarrow> Syntax.x" where
  "mk_x k = Abs_x (Atom (Sort ''Syntax.x'' []) k)"
*)

setup_lifting type_definition_x
(* And I guess more for those with binders *)

fun mk_atom_x :: "nat \<Rightarrow> atom" where
  "mk_atom_x n = Atom (Sort ''Syntax.x'' []) n"

lift_definition mk_x :: "nat \<Rightarrow> x" is mk_atom_x using mk_atom_x.simps by auto

fun fresh_x :: "x_list \<Rightarrow> Syntax.x" where
   "fresh_x xlist = mk_x (length xlist)"

fun mk_bv :: "nat \<Rightarrow> Syntax.bv" where
   "mk_bv k  = Abs_bv (Atom (Sort ''Syntax.bv'' []) k)"

fun fresh_bv :: "bv_list \<Rightarrow> Syntax.bv" where
   "fresh_bv bs = mk_bv  (length bs)"

fun mk_u :: "nat \<Rightarrow> Syntax.u" where
   "mk_u k = Abs_u (Atom (Sort ''Syntax.u'' []) k)"

fun fresh_u :: "u_list \<Rightarrow> Syntax.u" where
   "fresh_u us = mk_u (length us)"

fun convert_l :: "SyntaxDBI.l \<Rightarrow> Syntax.l" where
  "convert_l SyntaxDBI.L_true = Syntax.L_true"

fun convert_v :: "x_list \<Rightarrow> SyntaxDBI.v \<Rightarrow> Syntax.v" where
  "convert_v x_list (SyntaxDBI.V_var (XBVar k)) = Syntax.V_var (x_list!k)"
| "convert_v _ (SyntaxDBI.V_lit l) = Syntax.V_lit (convert_l l)"
| "convert_v xs (SyntaxDBI.V_pair v1 v2) = Syntax.V_pair (convert_v xs v1) (convert_v xs v2)"

fun convert_ce :: "x_list \<Rightarrow> SyntaxDBI.ce \<Rightarrow> Syntax.ce" where
  "convert_ce xlist (SyntaxDBI.CE_val v) = Syntax.CE_val (convert_v xlist v)"

fun convert_e :: "bv_list \<Rightarrow> x_list \<Rightarrow> u_list \<Rightarrow> SyntaxDBI.e \<Rightarrow> Syntax.e" where
  "convert_e _ xlist _ (SyntaxDBI.AE_val v) = Syntax.AE_val (convert_v xlist v)"

fun convert_c :: "x_list \<Rightarrow> SyntaxDBI.c \<Rightarrow> Syntax.c" where
  "convert_c xlist (SyntaxDBI.C_eq ce1 ce2) = Syntax.C_eq (convert_ce xlist ce1) (convert_ce xlist ce2)"
| "convert_c xlist (SyntaxDBI.C_true) = Syntax.C_true"
| "convert_c xlist (SyntaxDBI.C_false) = Syntax.C_false"
| "convert_c xlist (SyntaxDBI.C_conj c1 c2) = Syntax.C_conj (convert_c xlist c1)  (convert_c xlist c2) "
| "convert_c xlist (SyntaxDBI.C_disj c1 c2) = Syntax.C_disj (convert_c xlist c1)  (convert_c xlist c2) "
| "convert_c xlist (SyntaxDBI.C_imp c1 c2) = Syntax.C_imp (convert_c xlist c1)  (convert_c xlist c2) "
| "convert_c xlist (SyntaxDBI.C_not c1) = Syntax.C_not (convert_c xlist c1)"

fun convert_b :: "bv_list \<Rightarrow> SyntaxDBI.b \<Rightarrow> Syntax.b" where
  "convert_b _ SyntaxDBI.B_int = Syntax.B_int"
| "convert_b _ SyntaxDBI.B_bool = Syntax.B_bool"
| "convert_b _ SyntaxDBI.B_unit = Syntax.B_unit"
| "convert_b bs (SyntaxDBI.B_pair b1 b2) = Syntax.B_pair (convert_b bs b1)  (convert_b bs b2)"

fun convert_t :: "bv_list \<Rightarrow> x_list \<Rightarrow> SyntaxDBI.\<tau> \<Rightarrow> Syntax.\<tau>" where
 "convert_t bv_list xlist (SyntaxDBI.T_refined_type b c) = (let x = fresh_x xlist in
                     Syntax.T_refined_type x (convert_b bv_list b) (convert_c xlist c))"

fun convert_s :: "bv_list \<Rightarrow> x_list \<Rightarrow> u_list \<Rightarrow> SyntaxDBI.s \<Rightarrow> Syntax.s" 
  and convert_branch_s ::  "bv_list \<Rightarrow> x_list \<Rightarrow> u_list \<Rightarrow> SyntaxDBI.branch_s \<Rightarrow> Syntax.branch_s"
  and convert_branch_list ::  "bv_list \<Rightarrow> x_list \<Rightarrow> u_list \<Rightarrow> SyntaxDBI.branch_list \<Rightarrow> Syntax.branch_list"  
where
"convert_s _ xlist _ (SyntaxDBI.AS_val v) = Syntax.AS_val (convert_v xlist v)"
| "convert_branch_s bs xs us (SyntaxDBI.AS_branch dc s) = (let x = fresh_x xs in Syntax.AS_branch dc x  (convert_s bs xs us s))"
| "convert_branch_list bs xs us (SyntaxDBI.AS_final cs ) = Syntax.AS_final (convert_branch_s bs xs us cs)"
| "convert_branch_list bs xs us (SyntaxDBI.AS_cons cs css) = Syntax.AS_cons  (convert_branch_s bs xs us cs)  (convert_branch_list bs xs us css)"

fun convert_bset :: "SyntaxDBI.\<B> \<Rightarrow> Syntax.\<B>" where
  "convert_bset _ = {||}"

fun convert_tdef :: "SyntaxDBI.type_def \<Rightarrow> Syntax.type_def" where
  "convert_tdef  (SyntaxDBI.AF_typedef tyid dclist) = (Syntax.AF_typedef tyid (List.map (\<lambda>(dc,t) . (dc,convert_t [] [] t)) dclist))"

fun convert_th :: "SyntaxLemmasDBI.\<Theta> \<Rightarrow> Syntax.\<Theta>"  where
  "convert_th [] = []"
| "convert_th (tdef # th) = (convert_tdef tdef) # (convert_th th)"

fun tolist :: "Syntax.\<Gamma> \<Rightarrow> (x*b*c) list" where
   "tolist GNil = []"
|  "tolist (GCons xbc g) = xbc # tolist g"


fun convert_g :: "SyntaxDBI.\<Gamma> \<Rightarrow> Syntax.\<Gamma>" where
  "convert_g SyntaxDBI.GNil = Syntax.GNil"
| "convert_g (SyntaxDBI.GCons (b,c) G) = (let g = convert_g G in 
                                let xlist = map fst (tolist g) in 
                                let x = mk_x (length xlist) in 
                                Syntax.GCons (x, convert_b [] b , convert_c (x#xlist) c) g)" 


fun mk_v_eq :: "SyntaxDBI.l \<Rightarrow> SyntaxDBI.c" where
 "mk_v_eq l = (SyntaxDBI.C_eq (SyntaxDBI.CE_val (SyntaxDBI.V_var (XBVar 0))) (SyntaxDBI.CE_val (SyntaxDBI.V_lit l)))"

fun mk_v_eq_x :: "nat \<Rightarrow> SyntaxDBI.c" where
 "mk_v_eq_x k = (SyntaxDBI.C_eq (SyntaxDBI.CE_val (SyntaxDBI.V_var (XBVar 0))) (SyntaxDBI.CE_val (SyntaxDBI.V_var (XBVar k))))"

(*
lemma "convert_g (SyntaxDBI.GCons (SyntaxDBI.B_int, SyntaxDBI.C_true) SyntaxDBI.GNil) = (mk_x 0, B_int, C_true) # GNil"
  unfolding convert_g.simps  tolist.simps convert_c.simps convert_b.simps mk_x.simps using tolist.simps convert_c.simps 
  sledgehammer
*)

section \<open>Wellformedness\<close>

lemmas wf_intros = Wellformed.wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.intros Wellformed.wfE_wfS_wfCS_wfCSS_wfPhi_wfD_wfFTQ_wfFT.intros

lemma convert_lookup:
  assumes "Some (b, c) = SyntaxLemmasDBI.lookup \<Gamma> x" and "V_var xx = convert_v (map fst (tolist (convert_g \<Gamma>))) (v.V_var x) " and
           "bb = convert_b [] b" and "cc = convert_c (map fst (tolist (convert_g \<Gamma>))) c" and "G = convert_g \<Gamma>"       
         shows "Some (bb,cc) = Syntax.lookup G xx" 
using assms proof(induct \<Gamma>  arbitrary: b c x xx bb cc  )
  case GNil  
  then show ?case using GNil by auto
next
  case (GCons bc G')
  then show ?case 
qed

  

lemma convert_wf:
  fixes T::SyntaxLemmasDBI.\<Theta> and G::SyntaxDBI.\<Gamma> and v::SyntaxDBI.v
  shows "WellformedDBI.wfV T B G v b \<Longrightarrow> Wellformed.wfV (convert_th T) (convert_bset B) (convert_g G) (convert_v   (map fst (tolist (convert_g G))) v) (convert_b [] b)" and
 "WellformedDBI.wfC T B G c \<Longrightarrow> Wellformed.wfC (convert_th T) (convert_bset B) (convert_g G) (convert_c   (map fst (tolist (convert_g G))) c)" and
 "WellformedDBI.wfG T B G  \<Longrightarrow> Wellformed.wfG (convert_th T) (convert_bset B) (convert_g G)" and
 "WellformedDBI.wfT T B G t  \<Longrightarrow> Wellformed.wfT (convert_th T) (convert_bset B) (convert_g G) (convert_t [] (map fst (tolist (convert_g G))) t)" and
 "WellformedDBI.wfTs T B G ts  \<Longrightarrow> Wellformed.wfTs (convert_th T) (convert_bset B) (convert_g G) (convert_ts  (map fst (tolist (convert_g G))) t)" and
 "WellformedDBI.wfTh T  \<Longrightarrow> Wellformed.wfTh (convert_th T)" and
 "WellformedDBI.wfB T B b \<Longrightarrow> Wellformed.wfB (convert_th T) (convert_bset B) (convert_b ([]) b)" and
 "WellformedDBI.wfCE T B G ce b \<Longrightarrow> Wellformed.wfCE (convert_th T) (convert_bset B) (convert_g G) (convert_ce  (map fst (tolist (convert_g G))) ce) (convert_b [] b)" and
 "WellformedDBI.wfTD T tdef  \<Longrightarrow> Wellformed.wfTD (convert_th T) (convert_tdef tdef)"
proof(induct rule: WellformedDBI.wfV_wfC_wfG_wfT_wfTs_wfTh_wfB_wfCE_wfTD.inducts)
  case (wfB_intI \<Theta> \<B>)
  then show ?case using wf_intros by simp
next
  case (wfB_boolI \<Theta> \<B>)
  then show ?case using wf_intros by simp
next
  case (wfB_unitI \<Theta> \<B>)
  then show ?case using wf_intros by simp
next
  case (wfB_bitvecI \<Theta> \<B>)
  then show ?case sorry
next
  case (wfB_pairI \<Theta> \<B> b1 b2)
  then show ?case using wf_intros by simp
next
  case (wfB_consI \<Theta> s dclist \<B>)
  then show ?case sorry
next
  case (wfV_varI \<Theta> \<B> \<Gamma> b c x)
  obtain xx where xx: "V_var xx = convert_v (map fst (tolist (convert_g \<Gamma>))) (v.V_var x) " 
    by (metis (no_types) convert_v.simps(1) xb.exhaust)
  moreover have "Wellformed.wfV (convert_th \<Theta>) (convert_bset \<B>) (convert_g \<Gamma>)  (Syntax.V_var xx) (convert_b [] b)"
  proof
    show "convert_th \<Theta> ; convert_bset \<B>  \<turnstile>\<^sub>w\<^sub>f convert_g \<Gamma> " using wfV_varI by auto
    show "Some (convert_b [] b, convert_c (map fst (tolist (convert_g \<Gamma>))) c) = Syntax.lookup (convert_g \<Gamma>) xx" 
       using wfV_varI convert_lookup xx by simp
  qed
  ultimately show ?case by auto
next
  case (wfV_litI \<Theta> \<B> \<Gamma> l)
  then show ?case using wf_intros sorry
next
  case (wfV_pairI \<Theta> \<B> \<Gamma> v1 b1 v2 b2)
  then show ?case using wf_intros by simp
next
  case (wfV_consI s dclist \<Theta> dc b' c \<B> \<Gamma> v)
  then show ?case sorry
next
  case (wfCE_valI \<Theta> \<B> \<Gamma> v b)
  then show ?case using wf_intros by simp
next
  case (wfCE_plusI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case sorry
next
  case (wfCE_leqI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case sorry
next
  case (wfCE_fstI \<Theta> \<B> \<Gamma> v1 b1 b2)
  then show ?case sorry
next
  case (wfCE_sndI \<Theta> \<B> \<Gamma> v1 b1 b2)
  then show ?case sorry
next
  case (wfCE_concatI \<Theta> \<B> \<Gamma> v1 v2)
  then show ?case sorry
next
  case (wfCE_lenI \<Theta> \<B> \<Gamma> v1)
  then show ?case sorry
next
  case (wfTI \<Theta> \<B> b \<Gamma> c)
  then show ?case sorry
next
  case (wfC_eqI \<Theta> \<B> \<Gamma> e1 b e2)
  then show ?case using wf_intros by simp
next
  case (wfC_trueI \<Theta> \<B> \<Gamma>)
  then show ?case using wf_intros by simp
next
  case (wfC_falseI \<Theta> \<B> \<Gamma>)
  then show ?case using wf_intros by simp
next
  case (wfC_conjI \<Theta> \<B> \<Gamma> c1 c2)
  then show ?case using wf_intros by simp
next
  case (wfC_disjI \<Theta> \<B> \<Gamma> c1 c2)
  then show ?case using wf_intros by simp
next
  case (wfC_notI \<Theta> \<B> \<Gamma> c1)
  then show ?case using wf_intros by simp
next
  case (wfC_impI \<Theta> \<B> \<Gamma> c1 c2)
  then show ?case using wf_intros by simp
next
  case (wfG_nilI \<Theta> \<B>)
  then show ?case using wf_intros by simp
next
  case (wfG_cons1I c \<Theta> \<B> \<Gamma> b)
  then show ?case sorry
next
  case (wfG_cons2I c \<Theta> \<B> \<Gamma> b)
  then show ?case sorry
next
  case wfTh_emptyI
  then show ?case using wf_intros by simp
next
  case (wfTh_consI tdef \<Theta>)
  then show ?case sorry
next
  case (wfTD_simpleI \<Theta> lst s)
  then show ?case sorry
next
  case (wfTs_nil \<Theta> \<B> \<Gamma>)
  then show ?case sorry
next
  case (wfTs_cons \<Theta> \<B> \<Gamma> \<tau> dc ts)
  then show ?case sorry
qed

section \<open>Typing\<close>


section \<open>Operational Semantics\<close>
 

end
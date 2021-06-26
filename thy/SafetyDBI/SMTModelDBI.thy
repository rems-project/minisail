(*<*)
theory SMTModelDBI
  imports WellformedDBI
begin
(*>*)



chapter \<open>SMT Model\<close>

text {* A model for the SMT language/logic  the type system uses *}



section \<open>Evaluation and Satisfiability\<close>

subsection \<open>Valuation\<close>

text {* SMT values. SUt is a value for uninterpreted sort that corresponds to base type variables. For now we only need one of these universes *}
datatype smt_val = SBitvec "bit list" | SNum nat | SBool bool | SPair smt_val smt_val | SCons tyid string smt_val | SUnit | SUt smt_val (* | SFst smt_val | SSnd smt_val*)

(*
instantiation smt_val ::  pt
begin


primrec permute_smt_val where
  "p \<bullet> (SBitvec bv) = SBitvec (p \<bullet> bv)"
| "p \<bullet> (SNum n) = SNum (p \<bullet> n)"
| "p \<bullet> ( SBool b) = SBool (p \<bullet> b)"
| "p \<bullet> (SPair s1 s2) = SPair (p \<bullet> s1) (p \<bullet> s2)"
| "p \<bullet> (SCons tyid s smt_val) = SCons (p \<bullet> tyid) (p \<bullet> s) (p \<bullet> smt_val)"
| "p \<bullet> SUnit = SUnit"
| " p \<bullet> (SUt s) = SUt (p \<bullet> s)"


instance
apply standard
   apply(simp_all add: permute_smt_val_def)
  
  sory

end


lemmas [eqvt] =  permute_smt_val.simps
*)
(*
lemma supp_smt_val_empty:
  fixes s::smt_val and x::x
  shows "supp s = {}" and "atom x \<sharp> s"
by(nominal_induct s rule:smt_val.strong_induct, (auto simp add: pure_supp smt_val.supp supp_bitvec_empty fresh_def )+)
*)

type_synonym valuation = "(xf,smt_val) map"

(*
lemma valuation_flip1:
  fixes x::x and y::x
  shows "(x \<leftrightarrow> y ) \<bullet> (i x ) = ((x \<leftrightarrow> y ) \<bullet> i) y" by simp

lemma valuation_flip:
  fixes x::x and y::x and i::valuation
  shows "i x  = ((x \<leftrightarrow> y ) \<bullet> i) y"
proof -
  have "None = i x \<or> (\<exists>s. Some s = i x)" using option.exhaust by metis
  hence "atom x \<sharp> (i x) \<and> atom y \<sharp> (i x)" using supp_smt_val_empty fresh_None fresh_Some by metis
  hence  "(x \<leftrightarrow> y ) \<bullet> (i x ) = i x" using flip_fresh_fresh by blast
  thus ?thesis using valuation_flip1 by auto
qed
*)
(* TODO FIXME. Some experiments on helping to understand why adding B_var didn't break this - problem
 with using inductive predicates *)

(*
nominal_function base_of_f :: "\<Theta> \<Rightarrow> smt_val \<Rightarrow> b \<Rightarrow> bool" where
  "base_of_f P (SBitvec bv)  B_bitvec = True"
| "base_of_f P (SNum n)  B_int = True"
| "base_of_f P (SBool b)  B_bool = True"
| "base_of_f P (SCons dc s1) (B_id s) =  (\<exists>dclist x b c .  (AF_typedef s dclist \<in> set P \<and>
      (dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist \<and>
     base_of_f P s1 b))"
| "base_of_f P (SPair s1 s2) (B_pair b1 b2) =  (base_of_f P s1 b1 \<and> base_of_f P s2 b2 )"
| "base_of_f P SUnit B_unit = True"
apply(auto simp: eqvt_def base_of_f_graph_aux_def)
by (metis b.exhaust)
nominal_termination (eqvt) by lexicographic_order
*)

(*
nominal_function base_of2 :: "smt_val \<Rightarrow> b"  where
  "base_of2 (SBool _ ) = B_bool"
| "base_of2 (SNum _ ) = B_int"
| "base_of2 (SBitvec _) = B_bitvec"
| "base_of2 (SCons dc s1) = B_id dc"
| "base_of2 (SPair s1 s2) = B_pair (base_of2 s1) (base_of2 s2)"
| "base_of2 SUnit = B_unit"
| "base_of2 (SUt _

apply(auto simp: eqvt_def base_of2_graph_aux_def)
by (metis smt_val.exhaust)
nominal_termination (eqvt) by lexicographic_order

nominal_function base_ok :: "\<Theta> \<Rightarrow> smt_val \<Rightarrow> b \<Rightarrow> bool" where
  "base_ok P s B_int = (base_of2 s = B_int)"
| "base_ok P s B_bool = True"
| "base_ok P s B_unit = True"
| "base_ok P s (B_pair b1 b2) = ((base_ok P s b1) \<and> (base_ok P s b2))"
| "base_ok P s B_bitvec = True"
| "base_ok P s (B_id str) = True"
| "base_ok P s (B_var bv) = True"
apply(auto simp: eqvt_def base_ok_graph_aux_def)
by (metis b.exhaust)
nominal_termination (eqvt) by lexicographic_order
*)

inductive base_of:: "\<Theta> \<Rightarrow> smt_val \<Rightarrow> b \<Rightarrow> bool" ( " _  \<turnstile> _ ~ _" [50,50] 50) where
base_of_BBitvecI:  "P \<turnstile> (SBitvec bv)  ~ B_bitvec"
| base_of_BIntI:  "P \<turnstile> (SNum n)  ~ B_int"
| base_of_BBoolI: "P \<turnstile> (SBool b) ~ B_bool"
| base_of_BPairI: "\<lbrakk> P \<turnstile> s1 ~ b1 ; P \<turnstile> s2 ~ b2 \<rbrakk> \<Longrightarrow> P \<turnstile> (SPair s1 s2) ~ (B_pair b1 b2)"
| base_of_BConsI: "\<lbrakk>  AF_typedef s dclist \<in> set \<Theta>;
      (dc, \<lbrace>  : b  | c \<rbrace>) \<in> set dclist ;
     \<Theta> \<turnstile> s1 ~ b \<rbrakk> \<Longrightarrow> \<Theta> \<turnstile>(SCons s dc s1) ~ (B_id s)"
| base_of_BUnitI: "P \<turnstile> SUnit ~ B_unit"
| base_of_BVarI: "P \<turnstile> (SUt n) ~ (B_var bv)"


inductive_cases base_of_elims :
 "base_of P s  B_bitvec"
 "base_of P s (B_pair b1 b2)"
 "base_of P s (B_int)"
 "base_of P s (B_bool)"
 "base_of P s (B_id ss)"
 "base_of P s (B_var bv)"
 "base_of P s (B_unit)"

text \<open> Sometimes we want to do @{text "P \<turnstile> s ~ b[bv=b']"} and we want to know what b is however substitution is not
injective so we can't write this in terms of @{text "base_of"} \<close>

inductive base_of_subst:: "\<Theta> \<Rightarrow> smt_val \<Rightarrow> b \<Rightarrow> (bv*b) option \<Rightarrow> bool" where
base_of_subst_BBitvecI:  "base_of_subst P (SBitvec bv) B_bitvec  x "
| base_of_subst_BIntI:  "base_of_subst P (SNum n)  B_int x "
| base_of_subst_BBoolI: "base_of_subst P (SBool b)  B_bool x  "
| base_of_subst_BPairI: "\<lbrakk> base_of_subst P s1 b1 sub ; base_of_subst P s2 b2 sub \<rbrakk> \<Longrightarrow> base_of_subst P (SPair s1 s2) (B_pair b1 b2) sub"
| base_of_subst_BConsI: "\<lbrakk>  AF_typedef s dclist \<in> set \<Theta>;
      (dc, \<lbrace>  : b  | c \<rbrace>) \<in> set dclist ;
     base_of_subst \<Theta> s1 b None \<rbrakk> \<Longrightarrow> base_of_subst \<Theta> (SCons s dc s1) (B_id s) sub"
| base_of_subst_BUnitI: "base_of_subst P SUnit B_unit _ "
| base_of_subst_BVar1I: "bvar \<noteq> bv \<Longrightarrow> base_of_subst P (SUt n) (B_var bv)  (Some (bvar,bin))"
| base_of_subst_BVar2I: "\<lbrakk> bvar = bv; base_of_subst P s bin None \<rbrakk> \<Longrightarrow> base_of_subst P s (B_var bv)  (Some (bvar,bin))"
| base_of_subst_BVar3I: "base_of_subst P (SUt n) (B_var bv)  None"




subsection \<open>Wellformed Evaluation\<close>

definition wfI ::  "\<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> valuation \<Rightarrow> bool" ( " _ ; _ \<turnstile> _" )  where
  "\<Theta> ; \<Gamma> \<turnstile> i = (\<forall> (x,b,c) \<in> setG \<Gamma>. \<exists>s. Some s = i x \<and> \<Theta> \<turnstile> s ~ b)"


lemma wfI_domi:
  assumes "\<Theta> ; \<Gamma> \<turnstile> i"
  shows "fst ` setG \<Gamma> \<subseteq> dom i"
  using wfI_def setG.simps assms by fastforce

lemma wfI_lookup:
  fixes G::\<Gamma>
  assumes "Some (b,c) = lookup G x" and "P ; G \<turnstile> i" and "Some s = i x" and "P ; B \<turnstile>\<^sub>b G"
  shows "P \<turnstile> s ~ b"
proof -
  have "(x,b,c) \<in> setG G" using lookup.simps assms
    using lookup_in_g by blast
  then obtain s' where *:"Some s' = i x \<and> base_of P s' b" using wfI_def assms by auto
  hence "s' = s" using assms  by (metis option.inject)
  thus ?thesis using * by auto
qed

lemma wfI_restrict_weakening:
  assumes "wfI \<Theta> \<Gamma>' i'" and "i =  restrict_map i' (fst `setG \<Gamma>)" and "setG \<Gamma> \<subseteq> setG \<Gamma>'"
  shows  "\<Theta> ; \<Gamma> \<turnstile> i"
proof -
  { fix x
  assume "x \<in> setG \<Gamma>"
  have "case x of (x, b, c) \<Rightarrow> \<exists>s. Some s = i x \<and> \<Theta> \<turnstile> s ~ b" using assms wfI_def
  proof -
    have "case x of (x, b, c) \<Rightarrow> \<exists>s. Some s = i' x \<and> \<Theta> \<turnstile> s ~ b"
      using \<open>x \<in> setG \<Gamma>\<close>  assms wfI_def by auto
    then have "\<exists>s. Some s = i (fst x) \<and> base_of \<Theta> s (fst (snd x))"
      by (simp add: \<open>x \<in> setG \<Gamma>\<close> assms(2) case_prod_unfold)
    then show ?thesis
      by (simp add: case_prod_unfold)
  qed
  }
  thus ?thesis using wfI_def assms by auto
qed

lemma wfI_suffix:
  fixes G::\<Gamma>
  assumes "wfI P (G'@G) i" and "P ; B \<turnstile>\<^sub>b G"
  shows "P ; G \<turnstile> i"
using wfI_def append_g.simps assms setG.simps by simp

lemma wfI_replace_inside:
  assumes "wfI \<Theta> (\<Gamma>' @ (x, b, c) # \<Gamma>) i"
  shows  "wfI \<Theta> (\<Gamma>' @ (x, b, c') # \<Gamma>) i"
  using wfI_def setG_splitP assms by simp

(*
lemma wfI_subst:
  fixes v::v
  assumes "eval_v i  v  s" and "wfI \<Theta> \<Gamma>  (i ( x \<mapsto> s))" and "has_b \<Gamma> x b" and  "\<Theta> ; B ; \<Gamma> \<turnstile>\<^sub>b v : b"
  shows  "wfI \<Theta> \<Gamma>[x::=v]\<^sub>\<Gamma>\<^sub>v i"
proof(subst  wfI_def)
  {
  fix x' b' c'
  assume "(x',b',c') \<in> setG \<Gamma>[x::=v]\<^sub>\<Gamma>\<^sub>v"
  then obtain c1 where *: "(x',b',c1) \<in> setG \<Gamma> \<and> x' \<noteq> x" using wb_subst subst_g_member
    by (meson assms(4) wbV_wbG)
  then obtain s where "Some s = (i ( x \<mapsto> s)) x' \<and>  \<Theta> \<turnstile> s ~ b'" using  assms wfI_def by auto
  moreover hence "Some s = i x'" using * by auto
  ultimately have "\<exists>s. Some s = i x' \<and> \<Theta> \<turnstile> s ~ b'" using assms by auto

  }
  thus  "\<forall>(x', b', c')\<in>setG \<Gamma>[x::=v]\<^sub>\<Gamma>\<^sub>v. \<exists>s. Some s = i x' \<and> \<Theta> \<turnstile> s ~ b'" by auto
qed
*)

subsection \<open>Evaluating Terms\<close>

fun eval_l :: "l \<Rightarrow> smt_val" ( "\<lbrakk> _ \<rbrakk> " ) where
   "\<lbrakk> L_true \<rbrakk> = SBool True"
|  "\<lbrakk> L_false \<rbrakk> = SBool False"
|  "\<lbrakk> L_num n \<rbrakk> = SNum n"
|  "\<lbrakk> L_unit \<rbrakk> = SUnit"
|  "\<lbrakk> L_bitvec n \<rbrakk> = SBitvec n"


inductive eval_v :: "valuation \<Rightarrow> v \<Rightarrow> smt_val \<Rightarrow> bool"  ( "_ \<lbrakk> _ \<rbrakk> ~ _ " ) where
eval_v_litI:   "i \<lbrakk> V_lit l \<rbrakk> ~ \<lbrakk> l \<rbrakk> "
 | eval_v_varI: "Some sv = i x  \<Longrightarrow> i \<lbrakk> V_var (Inl x) \<rbrakk> ~ sv"
 | eval_v_pairI: "\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ s1 ; i \<lbrakk> v2 \<rbrakk> ~ s2 \<rbrakk> \<Longrightarrow> i \<lbrakk> V_pair v1 v2 \<rbrakk> ~ SPair s1 s2"
 | eval_v_consI: "i \<lbrakk> v \<rbrakk> ~ s \<Longrightarrow> i \<lbrakk> V_cons tyid dc v \<rbrakk> ~ SCons tyid dc s"



inductive_cases eval_v_elims:
  "i \<lbrakk> V_lit l \<rbrakk> ~  s"
  "i \<lbrakk> V_var x \<rbrakk> ~  s"
  "i \<lbrakk> V_pair v1 v2 \<rbrakk> ~ s"
  "i \<lbrakk> V_cons tyid dc v \<rbrakk> ~ s"


inductive eval_e :: "valuation \<Rightarrow> ce \<Rightarrow> smt_val \<Rightarrow> bool" ( "_ \<lbrakk> _ \<rbrakk> ~ _ " )  where
  eval_e_valI: "i \<lbrakk> v \<rbrakk> ~  sv \<Longrightarrow> i \<lbrakk> CE_val v \<rbrakk> ~ sv"
| eval_e_plusI: "\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ SNum n1; i \<lbrakk> v2 \<rbrakk> ~ SNum n2  \<rbrakk>  \<Longrightarrow> i \<lbrakk> (CE_op Plus v1 v2) \<rbrakk> ~ (SNum (n1+n2))"
| eval_e_leqI: "\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ (SNum n1); i \<lbrakk> v2 \<rbrakk> ~ (SNum n2) \<rbrakk>  \<Longrightarrow> i \<lbrakk> (CE_op LEq v1 v2) \<rbrakk> ~ (SBool (n1 \<le> n2))"
| eval_e_fstI: "\<lbrakk> i \<lbrakk> v \<rbrakk> ~ SPair v1 v2  \<rbrakk> \<Longrightarrow> i \<lbrakk> (CE_fst v) \<rbrakk> ~ v1"
| eval_e_sndI: "\<lbrakk> i \<lbrakk> v \<rbrakk> ~ SPair v1 v2  \<rbrakk> \<Longrightarrow> i \<lbrakk> (CE_snd v) \<rbrakk> ~ v2"
| eval_e_concatI:"\<lbrakk> i \<lbrakk> v1 \<rbrakk> ~ (SBitvec bv1); i \<lbrakk> v2 \<rbrakk> ~ (SBitvec bv2) \<rbrakk> \<Longrightarrow> i \<lbrakk> (CE_concat v1 v2) \<rbrakk> ~ (SBitvec (bv1@bv2))"
| eval_e_lenI:"\<lbrakk> i \<lbrakk> v \<rbrakk>  ~ (SBitvec bv) \<rbrakk> \<Longrightarrow> i \<lbrakk> (CE_len v) \<rbrakk> ~ (SNum (List.length bv))"



inductive_cases eval_e_elims:
 "i \<lbrakk> (CE_val v) \<rbrakk> ~ s"
 "i \<lbrakk> (CE_op Plus v1 v2) \<rbrakk> ~ s"
 "i \<lbrakk> (CE_op LEq v1 v2) \<rbrakk> ~ s"
 "i \<lbrakk> (CE_fst v) \<rbrakk> ~ s"
 "i \<lbrakk> (CE_snd v) \<rbrakk> ~ s"
 "i \<lbrakk> (CE_concat v1 v2) \<rbrakk> ~ s"
 "i \<lbrakk> (CE_len v) \<rbrakk> ~ s"


inductive eval_c :: "valuation \<Rightarrow> c \<Rightarrow> bool \<Rightarrow> bool" ( " _ \<lbrakk> _ \<rbrakk> ~ _ ")  where
  eval_c_trueI:  "i \<lbrakk> C_true \<rbrakk> ~ True"
| eval_c_falseI:"i \<lbrakk> C_false \<rbrakk> ~ False"
| eval_c_conjI: "\<lbrakk> i \<lbrakk> c1 \<rbrakk> ~ b1 ; i \<lbrakk> c2 \<rbrakk> ~ b2 \<rbrakk> \<Longrightarrow>  i \<lbrakk> (C_conj c1 c2) \<rbrakk> ~  (b1 \<and> b2)"
| eval_c_disjI: "\<lbrakk> i \<lbrakk> c1 \<rbrakk> ~ b1 ; i \<lbrakk> c2 \<rbrakk> ~ b2 \<rbrakk> \<Longrightarrow>  i \<lbrakk> (C_disj c1 c2) \<rbrakk> ~ (b1 \<or> b2)"
| eval_c_impI:"\<lbrakk> i \<lbrakk> c1 \<rbrakk> ~ b1 ; i \<lbrakk> c2 \<rbrakk> ~ b2 \<rbrakk> \<Longrightarrow>  i \<lbrakk> (C_imp c1 c2) \<rbrakk> ~ (b1 \<longrightarrow> b2)"
| eval_c_notI:"\<lbrakk> i \<lbrakk> c \<rbrakk> ~ b \<rbrakk> \<Longrightarrow> i \<lbrakk> (C_not c) \<rbrakk> ~ (\<not> b)"
| eval_c_eqI:"\<lbrakk> i \<lbrakk> e1 \<rbrakk> ~ sv1; i \<lbrakk> e2 \<rbrakk> ~ sv2 \<rbrakk> \<Longrightarrow> i \<lbrakk> (C_eq e1 e2) \<rbrakk> ~ (sv1=sv2)"


inductive_cases eval_c_elims:
 "i \<lbrakk> C_true \<rbrakk> ~  True"
 "i \<lbrakk> C_false \<rbrakk> ~ False"
 "i \<lbrakk> (C_conj c1 c2)\<rbrakk> ~ s"
 "i \<lbrakk> (C_disj c1 c2)\<rbrakk> ~ s"
 "i \<lbrakk> (C_imp c1 c2)\<rbrakk> ~ s"
 "i \<lbrakk> (C_not c) \<rbrakk> ~ s"
 "i \<lbrakk> (C_eq e1 e2)\<rbrakk> ~ s"
 "i \<lbrakk> C_true \<rbrakk> ~ s"
 "i \<lbrakk> C_false \<rbrakk> ~ s"



subsection \<open>Satisfiability\<close>

inductive  is_satis :: "valuation \<Rightarrow> c \<Rightarrow> bool" ( " _ \<Turnstile> _ " ) where
  "i \<lbrakk> c \<rbrakk> ~ True \<Longrightarrow> i \<Turnstile> c"


fun is_satis_g :: "valuation \<Rightarrow> \<Gamma> \<Rightarrow> bool" ( " _ \<Turnstile> _ " ) where
  "i \<Turnstile> GNil = True"
| "i \<Turnstile> ((x,b,c)#G) = ( i \<Turnstile> c \<and>  i \<Turnstile> G)"



section \<open>Validity\<close>

fun valid :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> c \<Rightarrow> bool"  ("_ ; _ ; _  \<Turnstile> _ " [50, 50] 50)  where
 "P ; B ; G \<Turnstile> c = ( P ; B ; G \<turnstile>\<^sub>b c \<and> (\<forall>i. P ; G \<turnstile> i \<and>  (i \<Turnstile> G) \<longrightarrow> (i \<Turnstile> c)))"


end
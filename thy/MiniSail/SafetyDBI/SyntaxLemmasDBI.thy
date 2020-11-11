theory SyntaxLemmasDBI
  imports SyntaxDBI
begin
subsection \<open>Lemmas\<close>

subsubsection \<open>Types\<close>


fun b_of :: "\<tau> \<Rightarrow> b" where
  "b_of \<lbrace>  : b | c \<rbrace> = b"



section \<open>Context\<close>

subsection \<open>Datatypes\<close>

(* Type and function/type definition contexts *)
type_synonym \<Phi> = "fun_def list"
type_synonym \<Theta> = "type_def list"
type_synonym \<B> = "bvf set"

lemma \<Phi>_induct [case_names PNil PConsNone PConsSome] : "P [] \<Longrightarrow> (\<And>f  b c \<tau> s' \<Phi>'. P \<Phi>' \<Longrightarrow> P ((AF_fundef f (AF_fun_typ_none (AF_fun_typ  b c \<tau> s'))) # \<Phi>')) \<Longrightarrow>
                                                                  (\<And>f  b c \<tau> s' \<Phi>'. P \<Phi>' \<Longrightarrow> P ((AF_fundef f (AF_fun_typ_some  (AF_fun_typ  b c \<tau> s'))) # \<Phi>'))  \<Longrightarrow> P \<Phi>"
proof(induct \<Phi> rule: list.induct)
case Nil
  then show ?case by auto 
next
  case (Cons x1 x2)
  then obtain f and t where ft: "x1 = (AF_fundef f t)" 
    by (meson fun_def.exhaust)
  then show ?case proof(induct t rule:fun_typ_q.induct)
    case (AF_fun_typ_some  ft)
    then show ?case using Cons ft 
      by (metis fun_typ.exhaust)
  next
    case (AF_fun_typ_none ft)
 then show ?case using Cons ft 
      by (metis fun_typ.exhaust)
qed
qed

lemma \<Theta>_induct [case_names TNil AF_typedef AF_typedef_poly] : "P [] \<Longrightarrow> (\<And>tid dclist \<Theta>'. P \<Theta>' \<Longrightarrow> P ((AF_typedef tid dclist) # \<Theta>')) \<Longrightarrow>
                                                                  (\<And>tid  dclist \<Theta>'. P \<Theta>' \<Longrightarrow> P ((AF_typedef_poly tid dclist ) # \<Theta>'))  \<Longrightarrow> P \<Theta>"
proof(induct \<Theta> rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons td T)
  show ?case by(cases td rule: type_def.exhaust, (simp add: Cons)+)
qed


lemma neq_GNil_conv: "(xs \<noteq> GNil) = (\<exists>y ys. xs = y # ys)"
by (induct xs) auto

lemma append_g_assoc:
  fixes xs::\<Gamma> 
  shows  "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by (induct xs) simp_all

lemma append_g_inside:
  fixes xs::\<Gamma> 
  shows "xs @ (x # ys) = (xs @ (x#GNil)) @ ys"
by(induct xs,auto+)

lemma finite_\<Gamma>:
  "finite (setG \<Gamma>)" 
by(induct \<Gamma> rule: \<Gamma>_induct,auto)
(*
lemma supp_\<Gamma>:
  "supp \<Gamma> = supp (setG \<Gamma>)"
proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case using supp_GNil setG.simps
    by (simp add: supp_set_empty)
next
  case (GCons x b c \<Gamma>')
  then show ?case using  supp_GCons setG.simps finite_\<Gamma> supp_of_finite_union 
    using supp_of_finite_insert by fastforce
qed
*)
(*
lemma supp_of_subset:
  fixes G::"('a::fs set)"
  assumes "finite G" and "finite G'" and "G \<subseteq> G'" 
  shows "supp G \<subseteq> supp G'"
  using supp_of_finite_sets assms  by (metis subset_Un_eq supp_of_finite_union)

lemma supp_weakening:
  assumes "setG G \<subseteq> setG G'"
  shows "supp G \<subseteq> supp G'"
  using supp_\<Gamma> finite_\<Gamma> by (simp add: supp_of_subset assms)

lemma fresh_weakening[ms_fresh]:
  assumes "setG G \<subseteq> setG G'" and "x \<notin> fvs_x G'" 
  shows "x \<notin> fvs_x G"
proof(rule ccontr)
  assume "\<not> x \<notin> fvs_x G"
  hence "x \<in> supp G" using fresh_def by auto
  hence "x \<in> supp G'" using supp_weakening assms by auto
  thus False using fresh_def assms by auto
qed

instance \<Gamma> :: fs
by (standard, induct_tac x, simp_all add: supp_GNil supp_GCons  finite_supp)
*)
subsection \<open>Variable Context Lookup\<close>

fun lookup :: "\<Gamma> \<Rightarrow> x \<Rightarrow> (b*c) option" where
  "lookup GNil x = None"
| "lookup ((b,c)#G) (XBVar i) = (if i=0 then Some (b,c) else lookup G (XBVar (i-1)))"


(*
fun replace_in_g :: "\<Gamma> \<Rightarrow> xf \<Rightarrow> c \<Rightarrow> \<Gamma>"  ("_[_\<longmapsto>_]" [1000,0,0] 200) where
  "replace_in_g GNil _ _ = GNil"
| "replace_in_g ((x,b,c)#G) x' c' = (if x=x' then ((x,b,c')#G) else (x,b,c)#(replace_in_g G x' c'))"
(*
apply(auto,simp add: eqvt_def replace_in_g_graph_aux_def)
using surj_pair \<Gamma>.exhaust by metis
nominal_termination (eqvt) by lexicographic_order
*)
lemma rig_dom_eq:
 "domG (replace_in_g G x c) = domG G"
proof(induct G rule: \<Gamma>.induct)
  case GNil
  then show ?case using replace_in_g.simps by presburger
next
  case (GCons xbc \<Gamma>')
  obtain x' and b' and c' where xbc: "xbc=(x',b',c')" using prod_cases3 by blast
  then show ?case using replace_in_g.simps GCons by simp
qed

lemma lookup_in_rig_eq:
  assumes "Some (b,c) = lookup \<Gamma> x" 
  shows "Some (b,c') = lookup (\<Gamma>[x\<longmapsto>c']) x"
using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x b c \<Gamma>')
  then show ?case using replace_in_g.simps lookup.simps by auto
qed

lemma lookup_in_rig_neq:
  assumes "Some (b,c) = lookup \<Gamma> y" and "x\<noteq>y"
  shows "Some (b,c) = lookup (\<Gamma>[x\<longmapsto>c']) y"
using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  then show ?case using replace_in_g.simps lookup.simps by auto
qed

lemma lookup_in_rig:
  assumes "Some (b,c) = lookup \<Gamma> y" 
  shows "\<exists>c''. Some (b,c'') = lookup (\<Gamma>[x\<longmapsto>c']) y"
proof(cases "x=y")
  case True
  then show ?thesis using lookup_in_rig_eq using assms by blast
next
  case False
   then show ?thesis using lookup_in_rig_neq using assms by blast
 qed
(*
lemma replace_in_g_forget:
  assumes "atom x \<notin> fvs_x \<Gamma>"
  shows "\<Gamma>[x \<longmapsto> c] = \<Gamma>"
using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  show ?case using replace_in_g.simps GCons fresh_GCons by simp
qed
*)

lemma lookup_inside[simp]:
  assumes "x \<notin> fst ` setG \<Gamma>'"
  shows "Some (b1,c1) = lookup (\<Gamma>'@(x,b1,c1)#\<Gamma>) x"
  using assms by(induct \<Gamma>',auto)

lemma lookup_inside2:
  assumes "Some (b1,c1) = lookup (\<Gamma>'@((x,b0,c0)#\<Gamma>)) y" and "x\<noteq>y"
  shows "Some (b1,c1) = lookup (\<Gamma>'@((x,b0,c0')#\<Gamma>)) y" 
  using assms by(induct \<Gamma>' rule: \<Gamma>.induct,auto+)

fun tail:: "'a list \<Rightarrow> 'a list" where
  "tail [] = []"
| "tail (x#xs) = xs"

lemma lookup_options:
  assumes "Some (b,c) = lookup (xt#G) x"
  shows  "((x,b,c) = xt) \<or> (Some (b,c) = lookup G x)"
by (metis assms lookup.simps(2) option.inject surj_pair)

lemma lookup_x:
  assumes "Some (b,c) = lookup G x"
  shows "x \<in> fst ` setG G"
  using assms
  by(induct "G" rule: \<Gamma>.induct ,auto+)

lemma eq_GNil_appendI: "xs = ys ==> xs = GNil @ ys"
by simp

lemma GCons_eq_appendI:
  fixes xs1::\<Gamma>
  shows "[| x # xs1 = ys; xs = xs1 @ zs |] ==> x # xs = ys @ zs"
by (drule sym) simp

lemma split_G: "x : setG xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs"
proof (induct xs)
  case GNil thus ?case by simp
next
  case GCons thus ?case using  GCons_eq_appendI 
    by (metis Un_iff append_g.simps(1) singletonD setG.simps(2))
qed

lemma lookup_not_empty:
  assumes "Some \<tau> = lookup G x"
  shows "G \<noteq> GNil"
  using assms by auto

lemma lookup_in_g:
 assumes "Some (b,c) = lookup \<Gamma> x"
 shows "(x,b,c) \<in> setG \<Gamma>"
using assms apply(induct \<Gamma>, simp)
using lookup_options by fastforce

lemma lookup_split:
  fixes \<Gamma>::\<Gamma>
  assumes "Some (b,c) = lookup \<Gamma> x"
  shows "\<exists>G G' . \<Gamma> =  G'@(x,b,c)#G"
  by (meson assms(1) lookup_in_g split_G)

(*
lemma fresh_dom_free:
  assumes "atom x \<notin> fvs_x \<Gamma>" 
  shows "(x,b,c) \<notin> setG \<Gamma>"
using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  hence "x\<noteq>x'" using fresh_def fresh_GCons fresh_Pair supp_at_base by blast
  moreover have "atom x \<notin> fvs_x \<Gamma>'" using fresh_GCons GCons by auto
  ultimately show ?case using setG.simps GCons by auto
qed

lemma fresh_dom_free2:
  assumes "atom x \<notin> atom_dom \<Gamma>" 
  shows "(x,b,c) \<notin> setG \<Gamma>"
using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  hence "x\<noteq>x'" using fresh_def fresh_GCons fresh_Pair supp_at_base by auto
  moreover have "atom x \<notin> atom_dom \<Gamma>'" using fresh_GCons GCons by auto
  ultimately show ?case using setG.simps GCons by auto
qed
*)
subsection \<open>Function Definition  Lookup\<close>

text \<open> Functions for looking up data-constructors in the Pi context \<close> 

*)

fun lookup_x :: "\<Gamma> \<Rightarrow> x  \<Rightarrow> (b*c) option" where
   "lookup_x GNil x = None"
 |  "lookup_x (GCons (b,c) G) (XBVar 0) = Some (b,c)"

fun lookup_u :: "\<Delta> \<Rightarrow> u  \<Rightarrow> \<tau> option" where
   "lookup_u DNil u = None"
 |  "lookup_u (DCons t G) (UBVar 0) = Some t"



fun lookup_fun :: "\<Phi> \<Rightarrow> f  \<Rightarrow> fun_def option" where
   "lookup_fun [] g = None"
 |  "lookup_fun ((AF_fundef f ft)#\<Pi>) g = (if (f=g) then Some (AF_fundef f ft) else lookup_fun \<Pi> g)"
(* |  "lookup_fun ((AF_typedef s lst )#\<Pi>) g = lookup_fun \<Pi> g"*)
(*
  apply(auto,simp add: eqvt_def lookup_fun_graph_aux_def )
  by (metis fun_def.exhaust neq_Nil_conv)
nominal_termination (eqvt)  by lexicographic_order
*)

fun lookup_td :: "\<Theta> \<Rightarrow> string  \<Rightarrow> type_def option" where
   "lookup_td [] g = None"
|  "lookup_td ((AF_typedef s lst ) # (\<Theta>::\<Theta>)) g = (if (s = g) then Some (AF_typedef s lst ) else lookup_td \<Theta> g)"
|  "lookup_td ((AF_typedef_poly s lst ) # (\<Theta>::\<Theta>)) g = (if (s = g) then Some (AF_typedef_poly s lst ) else lookup_td \<Theta> g)"
(*
  apply(auto,simp add: eqvt_def lookup_td_graph_aux_def )
  by (metis type_def.exhaust neq_Nil_conv)
nominal_termination (eqvt)  by lexicographic_order
*)
(*
lemma lookup_td_mem:
  assumes "Some (AF_typedef tid dclist) = lookup_td \<Theta> tid"
  shows "AF_typedef tid dclist \<in> set \<Theta>"
using assms proof(induct \<Theta>)
  case Nil
  then show ?case using lookup_td.simps by auto
next
  case (Cons a \<Theta>)
  then show ?case using lookup_td.simps 
  proof -
obtain ccs :: "type_def \<Rightarrow> char list" and pps :: "type_def \<Rightarrow> (char list \<times> \<tau>) list" and ccsa :: "type_def \<Rightarrow> char list" and ppsa :: "type_def \<Rightarrow> (char list \<times> \<tau>) list" where
f1: "\<And>t. AF_typedef_poly (ccs t) (pps t) = t \<or> AF_typedef (ccsa t) (ppsa t) = t"
  by (metis (no_types) type_def.exhaust) (* 93 ms *)
  then have f2: "AF_typedef (ccsa a) (ppsa a) = a \<or> ccs a = tid \<or> lookup_td \<Theta> tid = Some (AF_typedef tid dclist)"
    by (metis (full_types) Cons.prems lookup_td.simps(3)) (* 0.0 ms *)
{ assume "\<exists>t. Some a = Some t \<and> AF_typedef tid dclist \<noteq> t"
  then have "AF_typedef_poly tid (pps a) \<noteq> a"
    by (metis (no_types) Cons.prems lookup_td.simps(3) option.inject) (* 62 ms *)
  then have ?thesis
using f2 f1 by (metis (no_types) Cons.hyps Cons.prems list.set_intros(1) list.set_intros(2) lookup_td.simps(2) option.inject) (* 78 ms *) }
  then show ?thesis
    by auto (* 0.0 ms *)
qed
qed
*)

fun lookup_dc :: "(string * \<tau>) list \<Rightarrow> string  \<Rightarrow> (string*\<tau>) option" where
   "lookup_dc [] s = None"
|  "lookup_dc ((s',t)#ts) s = (if (s = s') then Some (s',t) else lookup_dc ts s)"


(*
lemma lookup_dc_mem:
  assumes "Some (cons, \<lbrace>  : ba  | ca \<rbrace>) = lookup_dc dclist cons" 
  shows "(cons, \<lbrace>  : ba  | ca \<rbrace>) \<in> set dclist " 
using assms proof(induct dclist)
  case Nil
  then show ?case using lookup_dc.simps by auto
next
  case (Cons a dclist)
  then show ?case using lookup_dc.simps  UnCI  insertCI option.sel surj_pair 
    by (metis list.set_intros(1) list.set_intros(2))
qed

fun lookup_d :: "\<Delta> \<Rightarrow> uf  \<Rightarrow> (uf*\<tau>) option" where
   "lookup_d [] s = None"
 |  "lookup_d ((u',t)#ts) u = (if (u = u') then Some (u',t) else lookup_d ts u)"

lemma lookup_d_mem:
  assumes "Some (u,t) = lookup_d D u"
  shows "(u,t) \<in> setD D"
using assms proof(induct D)
  case DNil
  then show ?case using lookup_d.simps by auto
next
  case (DCons a D')
  then show ?case using lookup_d.simps 
    by (metis UnCI \<Delta>.distinct(1) \<Delta>.inject insertCI option.sel setD.elims surj_pair)
qed

*)

fun name_of_type  ::"type_def \<Rightarrow> f "  where
  "name_of_type (AF_typedef f _ ) = f"
| "name_of_type (AF_typedef_poly f _) = f"
(*
apply(auto,simp add: eqvt_def name_of_type_graph_aux_def )
using type_def.exhaust by blast
nominal_termination (eqvt)  by lexicographic_order
*)

fun name_of_fun  ::"fun_def \<Rightarrow> f "  where
  "name_of_fun  (AF_fundef f ft) = f"
(*
apply(auto,simp add: eqvt_def name_of_fun_graph_aux_def )
using fun_def.exhaust by blast
nominal_termination (eqvt)  by lexicographic_order
*)
(*
fun remove2 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"remove2 x [] = []" |
"remove2 x (y # xs) = (if x = y then xs else y # remove2 x xs)"
(*
apply (simp add: eqvt_def remove2_graph_aux_def )
apply auto+
by (meson list.exhaust)
nominal_termination (eqvt)  by lexicographic_order
*)

lemma lookup_fun_member:
  assumes "Some (AF_fundef f ft) = lookup_fun \<Phi> f"
  shows "AF_fundef f ft \<in> set \<Phi>"
using assms proof (induct \<Phi>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Phi>)
  then show ?case using lookup_fun.simps
    by (metis fun_def.exhaust insert_iff list.simps(15) option.inject)
qed


lemma lookup_in_atoms:
  assumes "Some (b,c) = lookup \<Gamma> x"
  shows "x \<in> domG \<Gamma>"
  using assms apply(induct \<Gamma>, simp)
  using lookup_options by fastforce

lemma lookup_restrict:
  assumes "Some (b',c') = lookup (\<Gamma>'@(x,b,c)#\<Gamma>) y" and "x \<noteq> y" 
  shows "Some (b',c') = lookup (\<Gamma>'@\<Gamma>) y"
using assms  proof(induct \<Gamma>' rule:\<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x1 b1 c1 \<Gamma>')
  then show ?case by auto
qed

fun domD where
  "domD DNil = {}"
| "domD (DCons (u,t) D) = {u} \<union> domD D"

lemma domG[simp]:
 "domD D = fst`setD D"
by(induct D rule: \<Delta>_induct,auto+)


lemma setG_domG:
  assumes "(x,b,c) \<in> setG G" 
  shows "x \<in> domG G" using assms by force

lemma setD_domD:
  assumes "(u,\<tau>) \<in> setD \<Delta>" 
  shows "u \<in> domD \<Delta>" using assms by force


(*
lemma supp_v_tau [simp]:
  assumes "atom z \<notin> fvs_x v"
  shows "supp (\<lbrace> z : b | CE_val (V_var zz)  ==  CE_val v  \<rbrace>) = supp v \<union> supp b" 
  using assms \<tau>.supp c.supp cfvs_x_e.simps 
  by (simp add: fresh_def supp_at_base)

lemma supp_v_var_tau [simp]:
  assumes "z \<noteq> x"
  shows  "supp (\<lbrace> z : b | CE_val (V_var zz)  ==  CE_val (V_var x)  \<rbrace>) = { atom x } \<union> supp b"
  using supp_v_tau assms
  using supp_at_base by fastforce


lemma eqvt_flip:
  fixes P :: "'a::fs \<Rightarrow> bool" and c::x and x::x and y::x
  assumes "eqvt P" and "atom c \<notin> fvs_x (x,y,cx,cy)"  and "(x\<leftrightarrow>c) \<bullet> cx = (y\<leftrightarrow>c) \<bullet> cy"  and "P cx"
  shows "P cy"
proof - 
  have "(x\<leftrightarrow>c) \<bullet> (P cx)" using assms True_eqvt by auto
  hence "P ((x\<leftrightarrow>c) \<bullet> cx)" using eqvt_def  by (metis assms(1) eqvt_apply)
  hence  "P ((y\<leftrightarrow>c) \<bullet> cy)" using assms by auto
  hence  "(y\<leftrightarrow>c) \<bullet> (P cy)" using eqvt_def  by (metis assms(1) eqvt_apply)
  thus ?thesis  using assms True_eqvt  using permute_boolE by blast
qed

text \<open> Sometimes we need to work with a version of a binder where the variable is fresh in something else, such as 
a bigger context. I think these could be generated automatically \<close>
lemma obtain_fresh_let:
  fixes t::"'b::fs" 
  shows  "\<exists>y::x. atom y \<notin> fvs_x (s,t) \<and> (AS_let x e s = AS_let y e ((y \<leftrightarrow> x) \<bullet> s))"
  proof -
    obtain y::x where "atom y \<notin> fvs_x (s,t)" using obtain_fresh by blast
    moreover hence "(AS_let x e s = AS_let y e ((y \<leftrightarrow> x) \<bullet> s))" 
      using case_s_s.eq_iff Abs1_eq_iff by (metis flip_commute flip_fresh_fresh fresh_PairD(1))
    ultimately show ?thesis by auto
  qed

lemma obtain_fresh_let2:
  fixes t::"'b::fs" 
  shows  "\<exists>y::x. atom y \<notin> fvs_x (s,t) \<and> (AS_let2 x tt s1 s = AS_let2 y tt s1 ((y \<leftrightarrow> x) \<bullet> s))"
  proof -
    obtain y::x where "atom y \<notin> fvs_x (s,t)" using obtain_fresh by blast
    moreover hence "(AS_let2 x tt s1 s = AS_let2 y tt  s1 ((y \<leftrightarrow> x) \<bullet> s))" 
      using case_s_s.eq_iff Abs1_eq_iff  by (metis flip_commute flip_fresh_fresh fresh_PairD(1))
    ultimately show ?thesis by auto
  qed

lemma obtain_fresh_final:
  fixes t::"'b::fs" 
  shows  "\<exists>y::x. atom y \<notin> fvs_x (s,t) \<and> (C_final dc x s = C_final dc y ((y \<leftrightarrow> x) \<bullet> s))"
  proof -
    obtain y::x where "atom y \<notin> fvs_x (s,t)" using obtain_fresh by blast
    moreover hence "C_final dc x s = C_final dc y ((y \<leftrightarrow> x) \<bullet> s)" 
      using case_s_s.eq_iff Abs1_eq_iff  by (metis flip_commute flip_fresh_fresh fresh_PairD(1))
    ultimately show ?thesis by auto
  qed

lemma obtain_fresh_branch:
  fixes t::"'b::fs" 
  shows  "\<exists>y::x. atom y \<notin> fvs_x (s,t) \<and> (C_branch dc x s cs = C_branch dc y ((y \<leftrightarrow> x) \<bullet> s) cs)"
  proof -
    obtain y::x where "atom y \<notin> fvs_x (s,t)" using obtain_fresh by blast
    moreover hence "C_branch dc x s cs  = C_branch dc y ((y \<leftrightarrow> x) \<bullet> s) cs" 
      using case_s_s.eq_iff Abs1_eq_iff     by (metis flip_commute flip_fresh_fresh fresh_PairD(1))
    ultimately show ?thesis by auto
  qed


lemma obtain_fresh_fun_def:
  fixes t::"'b::fs" 
  shows  "\<exists>y::x. atom y \<notin> fvs_x (s,c,\<tau>,t) \<and> (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))  = AF_fundef f (AF_fun_typ_none (AF_fun_typ y b ((y \<leftrightarrow> x) \<bullet> c ) ((y \<leftrightarrow> x) \<bullet> \<tau>) ((y \<leftrightarrow> x) \<bullet> s))))"
proof -
  obtain y::x where y: "atom y \<notin> fvs_x (s,c,\<tau>,t)" using obtain_fresh by blast
  moreover have "AF_fundef f (AF_fun_typ_none (AF_fun_typ y b ((y \<leftrightarrow> x) \<bullet> c ) ((y \<leftrightarrow> x) \<bullet> \<tau>) ((y \<leftrightarrow> x) \<bullet> s))) =  (AF_fundef f (AF_fun_typ_none (AF_fun_typ  x b c \<tau> s)))" 
  proof(cases "x=y")
    case True
    then show ?thesis  using fun_def.eq_iff Abs1_eq_iff(3)  flip_commute flip_fresh_fresh fresh_PairD by auto
  next
    case False
    thm fun_typ.eq_iff
    have  "(AF_fun_typ y b ((y \<leftrightarrow> x) \<bullet> c) ((y \<leftrightarrow> x) \<bullet> \<tau>) ((y \<leftrightarrow> x) \<bullet> s)) =(AF_fun_typ x b c \<tau> s)" proof(subst fun_typ.eq_iff, subst Abs1_eq_iff(3))
      show  \<open>(y = x \<and> (((y \<leftrightarrow> x) \<bullet> c, (y \<leftrightarrow> x) \<bullet> \<tau>), (y \<leftrightarrow> x) \<bullet> s) = ((c, \<tau>), s) \<or>
         y \<noteq> x \<and> (((y \<leftrightarrow> x) \<bullet> c, (y \<leftrightarrow> x) \<bullet> \<tau>), (y \<leftrightarrow> x) \<bullet> s) = (y \<leftrightarrow> x) \<bullet> ((c, \<tau>), s) \<and> atom y \<notin> fvs_x ((c, \<tau>), s)) \<and>
         b = b\<close> using False flip_commute flip_fresh_fresh fresh_PairD y by auto
    qed
    thus ?thesis by metis
  qed
  ultimately show  ?thesis using y fresh_Pair by metis
qed

lemma supp_b_v_disjoint:
  fixes x::x and bv::bv
  shows "supp (V_var x) \<inter> supp (B_var bv) = {}" 
  by (simp add: supp_at_base)

lemma supp_b_v_disjoint2:
  fixes v::v and bv::bv
  shows "supp v \<inter> supp (B_var bv) = {}" 
proof(induct v rule:v.induct)
  case (V_lit x)
  then show ?case using supp_l_empty by auto
next
case (V_var x)
  then show ?case using supp_b_v_disjoint by auto
next
  case (V_pair x1a x2a)
  then show ?case using v.supp by auto
next
  case (V_cons tyid x1a x2a)
  then show ?case using  v.supp by auto
qed

lemma supp_b_u_disjoint[simp]:
  fixes b::b and u::u
  shows "supp u \<inter> supp b = {}" 
by(induct b rule:b.induct,(auto simp add:  b.supp supp_at_base)+)


lemma supp_b_v_disjoint3:
  fixes v::v and b::b
  shows "supp v \<inter> supp b = {}" 
proof(induct b rule:b.induct)
  case (B_id x)
  then show ?case using  b.supp by auto
next
  case (B_var x)
  then show ?case using supp_b_v_disjoint2 by auto
qed(auto simp add: b.supp  supp_b_v_disjoint2)+


lemma u_notin_supp_v:
  fixes u::u and v::v
  shows "atom u \<notin> supp v" 
proof(induct v rule: v.induct)
  case (V_lit l)
  then show ?case  using supp_l_empty by auto
next
  case (V_var x)
  then show ?case 
    by (simp add: supp_at_base)
next
  case (V_pair v1 v2)
  then show ?case by auto
next
  case (V_cons tyid list v)
  then show ?case using  by auto
qed

lemma u_fresh_xv:
  fixes u::u and x::x and v::v
  shows "atom u \<notin> fvs_x  (x,v)"
proof - 
  have "atom u \<notin> fvs_x x" using fresh_def by fastforce
  moreover have "atom u \<notin> fvs_x v" using fresh_def u_notin_supp_v by metis
  ultimately show ?thesis using fresh_prod2 by auto
qed

lemma bv_notin_supp_v:
  fixes u::bv and v::v
  shows "atom u \<notin> supp v" 
proof(induct v rule: v.induct)
  case (V_lit l)
  then show ?case  using supp_l_empty by auto
next
  case (V_var x)
  then show ?case 
    by (simp add: supp_at_base)
next
  case (V_pair v1 v2)
  then show ?case by auto
next
  case (V_cons tyid list v)
  then show ?case using  by auto
qed

lemma bv_fresh_v:
  fixes bv::bv and v::v
  shows "atom bv \<notin> fvs_x v"
  using bv_notin_supp_v fresh_def by metis

lemma u_fresh_b:
  fixes  u::u and b::b
  shows "atom u \<notin> fvs_x b"
apply (induct b rule: b.induct, auto simp: )
using  fresh_def by blast

lemma bv_fresh_ce:
  fixes bv::bv and ce::ce
  shows "atom bv \<notin> fvs_x ce"
proof(induct ce rule: ce.induct)
  case (CE_val x)
  then show ?case using bv_fresh_v ce.fresh by metis
next
  case (CE_op x1a x2 x3)
  have "atom bv \<notin> fvs_x x1a" using opp.supp fresh_def opp.exhaust[of x1a "atom bv \<notin> fvs_x x1a"] by simp
  then show ?case using bv_fresh_v ce.fresh by simp
next
  case (CE_concat x1a x2)
  then show ?case using bv_fresh_v ce.fresh by metis
next
  case (CE_fst x)
  then show ?case using bv_fresh_v ce.fresh by metis
next
  case (CE_snd x)
then show ?case using bv_fresh_v ce.fresh by metis
next
  case (CE_len x)
then show ?case using bv_fresh_v ce.fresh by metis
qed

(* FIXME - Same as above? *)
lemma bv_not_in_ce:
  fixes bv::bv and ce::ce
  shows  "atom bv \<notin> supp ce"
  apply(induct ce rule:ce.induct,(auto simp add: bv_notin_supp_v supp_at_base  cfvs_x_e.simps)+)
  using  fresh_def 
  by (metis empty_iff opp.exhaust opp.supp(1) opp.supp(2))


lemma bv_not_in_c:
  fixes bv::bv and c::c
  shows  "atom bv \<notin> supp c"
  by(induct c rule:c.induct,(auto simp add: bv_not_in_ce)+)

lemma bv_fresh_c:
  fixes bv::bv and c::c
  shows "atom bv \<notin> fvs_x c"
  using bv_not_in_c fresh_def by auto


lemma flip_collapse[simp]:
  fixes b1::"'a::pt" and bv1::"'b::at" and bv2::"'b::at"
  assumes "atom bv2 \<notin> fvs_x b1" and "atom c \<notin> fvs_x (bv1,bv2,b1)" and "bv1 \<noteq> bv2" 
  shows "(bv2 \<leftrightarrow> c) \<bullet> (bv1 \<leftrightarrow> bv2) \<bullet> b1 = (bv1 \<leftrightarrow> c) \<bullet> b1"
proof - 
  have "c  \<noteq> bv1" and "bv2 \<noteq> bv1" using assms by auto+
  hence "(bv2 \<leftrightarrow> c) + (bv1 \<leftrightarrow> bv2) + (bv2 \<leftrightarrow> c) =  (bv1 \<leftrightarrow> c)" using flip_triple[of c bv1 bv2] flip_commute by metis
  hence "(bv2 \<leftrightarrow> c)  \<bullet> (bv1 \<leftrightarrow> bv2)  \<bullet> (bv2 \<leftrightarrow> c) \<bullet> b1 =  (bv1 \<leftrightarrow> c) \<bullet> b1" using permute_plus by metis
  thus ?thesis using assms flip_fresh_fresh by force
qed
*)


section \<open>Junk\<close>
(*


(*
lemma subst_x_g_flip: 
  fixes x::xf and xa::xf and z::xf and c::c and b::b and \<Gamma>::\<Gamma>
  assumes "atom xa \<notin> fvs_x ((x, b, c[z::=V_var x]\<^sub>c\<^sub>v) # \<Gamma>)"  and "atom xa \<notin> fvs_x \<Gamma>" and "atom x \<notin> fvs_x \<Gamma>" and "atom x \<notin> fvs_x (z, c)" and "atom xa \<notin> fvs_x (z, c)"
  shows "(x \<leftrightarrow> xa) \<bullet>  ((x, b, c[z::=V_var x]\<^sub>c\<^sub>v) # \<Gamma>) = (xa, b, c[z::=V_var xa]\<^sub>c\<^sub>v) # \<Gamma>"
proof -
  have  "(x \<leftrightarrow> xa) \<bullet>  ((x, b, c[z::=V_var x]\<^sub>c\<^sub>v) # \<Gamma>) =  (( (x \<leftrightarrow> xa) \<bullet>  x, b, (x \<leftrightarrow> xa) \<bullet>  c[z::=V_var x]\<^sub>c\<^sub>v) # ((x \<leftrightarrow> xa) \<bullet>  \<Gamma>))" 
    using subst Cons_eqvt flip_fresh_fresh using G_cons_flip by simp
  also have "... = ((xa, b, (x \<leftrightarrow> xa) \<bullet> c[z::=V_var x]\<^sub>c\<^sub>v) # ((x \<leftrightarrow> xa) \<bullet>  \<Gamma>))" using assms by fastforce
  also have "... =  ((xa, b,  c[z::=V_var xa]\<^sub>c\<^sub>v) # ((x \<leftrightarrow> xa) \<bullet>  \<Gamma>))" using assms subst_x_c_v_flip1[of x z c xa "V_var x" ] by fastforce
  also have "... =  ((xa, b,  c[z::=V_var xa]\<^sub>c\<^sub>v) # \<Gamma>)"  using assms flip_fresh_fresh by blast 
  finally show ?thesis by simp
qed

lemma subst_x_g_flip2[simp]: 
  fixes x1::x and x1'::x and c1::c and z1::x and b::b  and \<Gamma>::\<Gamma>
  assumes "atom x1' \<notin> fvs_x (z1,c1,\<Gamma>) \<and> atom x1 \<notin> fvs_x (z1,c1,\<Gamma>)"
  shows "((x1 \<leftrightarrow> x1') \<bullet> (((x1, b, c1[z1::=V_var x1]\<^sub>c\<^sub>v) # \<Gamma>))) = ((x1', b, c1[z1::=V_var x1']\<^sub>c\<^sub>v) # \<Gamma>)"
proof - 
  have "((x1 \<leftrightarrow> x1') \<bullet> (((x1, b, c1[z1::=V_var x1]\<^sub>c\<^sub>v) # \<Gamma>))) = ((x1 \<leftrightarrow> x1') \<bullet> (x1, b, c1[z1::=V_var x1]\<^sub>c\<^sub>v) # \<Gamma>)"
    using assms flip_fresh_fresh by force
  also have "... = ((x1 \<leftrightarrow> x1') \<bullet> x1, (x1 \<leftrightarrow> x1') \<bullet> b , (x1 \<leftrightarrow> x1') \<bullet> c1[z1::=V_var x1]\<^sub>c\<^sub>v) # \<Gamma>" by simp
  also have "... = (x1', b ,c1[z1::=V_var x1']\<^sub>c\<^sub>v ) # \<Gamma>" proof -
    have "(x1 \<leftrightarrow> x1') \<bullet> b = b" using supp_b_empty flip_fresh_fresh fresh_def by blast
    moreover have "(x1 \<leftrightarrow> x1') \<bullet> x1 = x1'" by simp
    moreover have "(x1 \<leftrightarrow> x1') \<bullet> c1[z1::=V_var x1]\<^sub>c\<^sub>v = c1[z1::=V_var x1']\<^sub>c\<^sub>v" using assms by force
    ultimately show ?thesis by blast
  qed
  finally show  ?thesis by auto
qed

lemma subst_x_g_flip3[simp]: 
  fixes x1::x and x1'::x and c1::c and z1::x and b::b  and \<Gamma>::\<Gamma>
  assumes "atom x1' \<notin> fvs_x (c1,\<Gamma>) \<and> atom x1 \<notin> fvs_x (c1,\<Gamma>)"
  shows "((x1 \<leftrightarrow> x1') \<bullet> (((x1, b, c1[z1::=V_var x1]\<^sub>c\<^sub>v) # \<Gamma>))) = ((x1', b, c1[z1::=V_var x1']\<^sub>c\<^sub>v) # \<Gamma>)"
proof -
  have "((x1 \<leftrightarrow> x1') \<bullet> (((x1, b, c1[z1::=V_var x1]\<^sub>c\<^sub>v) # \<Gamma>))) = ((x1 \<leftrightarrow> x1') \<bullet> (x1, b, c1[z1::=V_var x1]\<^sub>c\<^sub>v) # \<Gamma>)"
    using assms flip_fresh_fresh by force
  also have "... = ((x1 \<leftrightarrow> x1') \<bullet> x1, (x1 \<leftrightarrow> x1') \<bullet> b , (x1 \<leftrightarrow> x1') \<bullet> c1[z1::=V_var x1]\<^sub>c\<^sub>v) # \<Gamma>" by simp
  also have "... = (x1', b ,c1[z1::=V_var x1']\<^sub>c\<^sub>v ) # \<Gamma>" proof -
    have "(x1 \<leftrightarrow> x1') \<bullet> b = b" using supp_b_empty flip_fresh_fresh fresh_def by blast
    moreover have "(x1 \<leftrightarrow> x1') \<bullet> x1 = x1'" by simp
    moreover have "(x1 \<leftrightarrow> x1') \<bullet> c1[z1::=V_var x1]\<^sub>c\<^sub>v = c1[z1::=V_var x1']\<^sub>c\<^sub>v" using assms  subst_x_c_v_flip3 by auto
    ultimately show ?thesis by blast
  qed
  finally show  ?thesis by auto
qed

lemma G_cons_flip_tau_eq[simp]:
  fixes y::x and x::x and \<Gamma>::\<Gamma>
  assumes "\<lbrace> z1 : b  | c1 \<rbrace> = \<lbrace> z : ba  | c \<rbrace>" and "atom y \<notin> fvs_x (z1,c1,\<Gamma>)" and  "atom x \<notin> fvs_x (z, c, \<Gamma>)"
  shows "((y \<leftrightarrow> x) \<bullet> ((y, b, (c1[z1::=V_var y]\<^sub>c\<^sub>v)) # \<Gamma>)) = (((x, b, (c[z::=V_var x]\<^sub>c\<^sub>v)) # \<Gamma>))"
proof - 
  have c1: "[[atom z1]]lst. c1 = [[atom z]]lst. c" using \<tau>.eq_iff assms by meson
  have f1: "atom y \<notin> fvs_x (z1, c1) \<and> atom x \<notin> fvs_x (z, c)" using assms by simp

  have *:"((y \<leftrightarrow> x) \<bullet> ((y, b, (c1[z1::=V_var y]\<^sub>c\<^sub>v)) # \<Gamma>)) = ( ((x, b, (y \<leftrightarrow> x) \<bullet> (c1[z1::=V_var y]\<^sub>c\<^sub>v)) # \<Gamma>))"
    using G_cons_flip_fresh3 fresh_prod3 assms flip_commute by metis
  thm  Abs1_eq_iff_all subst_x_c_flip
  obtain za::x where za:"atom za \<notin> fvs_x (c1,z1,c,z)" using obtain_fresh by metis
  hence " (z1 \<leftrightarrow> za) \<bullet> c1 = (z \<leftrightarrow> za) \<bullet> c" using Abs1_eq_iff_all c1 by simp
  moreover have " atom za \<notin> fvs_x (c1, c) \<and> atom za \<notin> fvs_x (z1, z, c1, c) " using za fresh_prod4 by simp
  ultimately  have "(c1[z1::=V_var y]\<^sub>c\<^sub>v) =  (c[z::=V_var y]\<^sub>c\<^sub>v)" using subst_x_c_flip[of za c1 c z1 z] za by auto
  moreover have  "(y \<leftrightarrow> x) \<bullet> (c1[z1::=V_var y]\<^sub>c\<^sub>v) = (c1[z1::=V_var x]\<^sub>c\<^sub>v)" using subst_x_c_v_flip3[of y c1 x z1] 
    
    by (metis calculation f1 flip_at_simps(1) fresh_Pair _permute_iff fresh_subst_x_c_if subst_x_c_v_flip subst_x_c_var_flip subst_x_c_var_flip1)
  ultimately show ?thesis using * 
    by (metis \<open>(z1 \<leftrightarrow> za) \<bullet> c1 = (z \<leftrightarrow> za) \<bullet> c\<close> \<open>atom za \<notin> fvs_x (c1, c) \<and> atom za \<notin> fvs_x (z1, z, c1, c)\<close> subst_x_c_flip)
qed
*)









fun subst_d :: "\<Delta> \<Rightarrow> xf \<Rightarrow> v \<Rightarrow> \<Delta>" where
  "subst_d  DNil  x v = DNil"
| "subst_d ((u,t)#\<Delta>)   x v = ((u,t[x::=v]\<^sub>\<tau>\<^sub>v) # (subst_d \<Delta>  x v ))"


abbreviation 
  subst_d_abbrev :: "\<Delta> \<Rightarrow> xf \<Rightarrow> v \<Rightarrow> \<Delta>" ("_[_::=_]\<^sub>\<Delta>\<^sub>v" [1000,50,50] 1000)
where 
  "\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v  \<equiv> subst_d \<Delta>   x v" 

fun dmap :: "(uf*\<tau> \<Rightarrow> uf*\<tau>) \<Rightarrow> \<Delta> \<Rightarrow> \<Delta>" where
  "dmap f DNil  = DNil"
| "dmap  f ((u,t)#\<Delta>)  = (f (u,t) # (dmap f \<Delta> ))"


lemma subst_d_iff:
  "\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v = dmap (\<lambda>(u,t). (u, t[x::=v]\<^sub>\<tau>\<^sub>v)) \<Delta>"
by(induct \<Delta>, auto)

lemma size_subst_d [simp]: "size ( subst_d G i x) \<le> size G"
  by (induct G,auto) 


lemma supp_DNil: 
  shows "supp DNil = {}"
by (simp add: supp_def Collect_imp_eq Collect_neg_eq)

lemma supp_DCons: 
  fixes xs::\<Delta>
  shows "supp (x # xs) = supp x \<union> supp xs"
by (simp add: supp_def Collect_imp_eq Collect_neg_eq)

lemma fresh_DNil[ms_fresh]:
  shows "a \<notin> fvs_x DNil"
  by (simp add: fresh_def supp_DNil)

lemma fresh_DCons[ms_fresh]: 
  fixes xs::\<Delta>
  shows "a \<notin> fvs_x (x # xs) \<longleftrightarrow> a \<notin> fvs_x x \<and> a \<notin> fvs_x xs"
  by (simp add: fresh_def supp_DCons)

lemma neq_DNil_conv: "(xs \<noteq> DNil) = (\<exists>y ys. xs = y # ys)"
by (induct xs) auto


lemma forget_subst_d [simp]: "atom a \<notin> fvs_x G \<Longrightarrow> subst_d G a x = G"
  apply (induct G ,auto) 
  using \<Delta>.fresh fresh_PairD(1)  
  done



lemma subst_d_member:
  assumes "(u,\<tau>) \<in> setD \<Delta>"
  shows  "(u, \<tau>[x::=v]\<^sub>\<tau>\<^sub>v) \<in> setD (\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v)"
using assms  by(induct \<Delta> rule: \<Delta>_induct,auto)

subsection \<open>Statements\<close>

text \<open> Using ideas from proof at top of AFP/Launchbury/Substitution.thy.
   Chunks borrow from there; hence the apply style proofs. \<close>

(*
proof(goal_cases)

  have eqvt_at_fvs_x_s: "\<And> \<Gamma> y z . eqvt_at fvs_x_s_subst_x_case_s_sumC (Inl (\<Gamma>, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). fvs_x_s a b c) (\<Gamma>, y, z)" 
  apply(simp add: eqvt_at_def fvs_x_s_def)  (* Copy and paste with slight modification from Substitution.thy *)
  apply(rule)
  apply(subst Projl_permute)
  apply(thin_tac _)+
  apply (simp add: fvs_x_s_subst_x_case_s_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (fvs_x_s_subst_x_case_s_graph (Inl (\<Gamma>, y, z)))")
  apply simp
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: fvs_x_s_subst_x_case_s_graph.cases)
  apply(assumption)
  apply(rule_tac x="Sum_Type.projl x" in exI,clarify,rule the1_equality,blast,simp (no_asm) only: sum.sel)+
  apply blast +
  apply(simp)
  done

  have eqvt_at_subst_x_case_s: "\<And> \<Gamma> y z . eqvt_at fvs_x_s_subst_x_case_s_sumC (Inr (\<Gamma>, y, z)) \<Longrightarrow> eqvt_at (\<lambda>(a, b, c). subst_x_case_s a b c) (\<Gamma>, y, z)"   
  apply(simp add: eqvt_at_def subst_x_case_s_def) 
  apply(rule)
  apply(subst Projr_permute)
  apply(thin_tac _)+
  apply (simp add: fvs_x_s_subst_x_case_s_sumC_def)
  apply (simp add: THE_default_def)
  apply (case_tac "Ex1 (fvs_x_s_subst_x_case_s_graph (Inr (\<Gamma>, y, z)))")
  apply simp
  apply(auto)[1]
  apply (erule_tac x="x" in allE)
  apply simp
  apply(cases rule: fvs_x_s_subst_x_case_s_graph.cases)
  apply(assumption)
  apply(rule_tac x="Sum_Type.projr x" in exI,clarify,rule)+
  apply blast +
  apply(simp)
  done

  {
  case (1 P x') (* Whilst the premises/goal look non-trivial, intuitively it is easy to see what is going on. Some unpacking is needed though to get automatic methods to work *)
  then show ?case proof(cases "\<exists>w. x' = Inr w")
    case True
    then obtain w where "x' = Inr w" by blast
    then obtain x'' and v'' and s'' where "w=(x'',v'',s'')" 
      by (metis old.prod.exhaust)
    then show ?thesis using 1(6) 1(8) case_s_s.exhaust(1)
      using \<open>x' = Inr w\<close> fresh_star_insert 1 by metis
  next
    case False
    then obtain w where a1: "x' = Inl w" using sum.exhaust by blast
    then obtain x'' and v'' and s'' where a2: "w=(x'',v'',s'')" 
      by (metis old.prod.exhaust)

    have "(\<And>v. s'' = AS_val v \<Longrightarrow> P)" using 1 a1 a2 by simp
    moreover have "(\<And>x e s. {atom x} \<notin> fvs_x* (x'', v'') \<Longrightarrow> s'' = AS_let x  e s \<Longrightarrow> P)"  using 1 a1 a2 
      by (metis fresh_star_insert option.exhaust)
    moreover have "(\<And>x \<tau> s1 s2. {atom x} \<notin> fvs_x* (x'', v'') \<Longrightarrow> s'' = AS_let2 x \<tau> s1 s2 \<Longrightarrow> P)" using 1 a1 a2  by (metis fresh_star_insert option.exhaust)
    moreover have "(\<And>v s1 s2. s'' = AS_if v s1 s2 \<Longrightarrow> P)"  using 1 a1 a2 by simp
    moreover have "(\<And>u \<tau> v s. {atom u} \<notin> fvs_x* (x'', v'') \<Longrightarrow> s'' = AS_var u \<tau> v s \<Longrightarrow> P)"  using 1 a1 a2  by (metis fresh_star_insert option.exhaust)
    moreover have "(\<And>u v. s'' = AS_assign u v \<Longrightarrow> P)"  using 1 a1 a2 by simp
    moreover have "(\<And>v list x s case_s. {atom x} \<notin> fvs_x* (x'', v'') \<Longrightarrow> s'' = AS_match v case_s \<Longrightarrow> P)"  using 1 a1 a2  by (metis fresh_star_insert option.exhaust)
    moreover have "(\<And>s1 s2. s'' = AS_while s1 s2 \<Longrightarrow> P)"  using 1 a1 a2 using 1 a1 a2  by (metis fresh_star_insert option.exhaust)
    moreover have "(\<And>s1 s2. s'' = AS_seq s1 s2 \<Longrightarrow> P)"  using 1 a1 a2  by (metis fresh_star_insert option.exhaust)

    ultimately show ?thesis using case_s_s.exhaust(2)[where c="(x'',v'')" and ya=s'' and P=P] 
      using "1"(4) a1 a2 by blast
  qed
next
  case (2 y s ya xa va sa c) thus ?case
  apply -
  apply (drule eqvt_at_fvs_x_s)+
  apply (simp only: meta_eq_to_obj_eq[OF fvs_x_s_def, symmetric, unfolded fun_eq_iff])
  proof goal_cases (* Want to get the A in A \<Longrightarrow> B as a premise and B as a subgoal *)
    case 1
    hence "(y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s = fvs_x_s ((y \<leftrightarrow> c) \<bullet> xa) ((y \<leftrightarrow> c) \<bullet> va) ((y \<leftrightarrow> c) \<bullet> s)"  proof -
      have " (y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s = (y \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, s)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> (xa, va, s))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> xa, (y \<leftrightarrow> c) \<bullet> va, (y \<leftrightarrow> c) \<bullet> s)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va sa = fvs_x_s ((ya \<leftrightarrow> c) \<bullet> xa) ((ya \<leftrightarrow> c) \<bullet> va) ((ya \<leftrightarrow> c) \<bullet> sa)" proof - 
      have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va sa = (ya \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, sa)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> (xa, va, sa))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> xa, (ya \<leftrightarrow> c) \<bullet> va, (ya \<leftrightarrow> c) \<bullet> sa)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (y \<leftrightarrow> c) \<bullet> s = (ya \<leftrightarrow> c) \<bullet> sa" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> xa) =  ((ya \<leftrightarrow> c) \<bullet> xa)" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> va) =  ((ya \<leftrightarrow> c) \<bullet> va)" using 1 by simp
    ultimately show ?case by argo
  qed   
next
  case (3 y s ya xa va s1a sa c)
  then show ?case 
  apply -
  apply (drule eqvt_at_fvs_x_s)+
  apply (simp only: meta_eq_to_obj_eq[OF fvs_x_s_def, symmetric, unfolded fun_eq_iff])
  proof goal_cases (* Want to get the A in A \<Longrightarrow> B as a premise and B as a subgoal *)
    case 1
    hence "(y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s = fvs_x_s ((y \<leftrightarrow> c) \<bullet> xa) ((y \<leftrightarrow> c) \<bullet> va) ((y \<leftrightarrow> c) \<bullet> s)"  proof -
      have " (y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s = (y \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, s)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> (xa, va, s))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> xa, (y \<leftrightarrow> c) \<bullet> va, (y \<leftrightarrow> c) \<bullet> s)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va sa = fvs_x_s ((ya \<leftrightarrow> c) \<bullet> xa) ((ya \<leftrightarrow> c) \<bullet> va) ((ya \<leftrightarrow> c) \<bullet> sa)" proof - 
      have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va sa = (ya \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, sa)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> (xa, va, sa))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> xa, (ya \<leftrightarrow> c) \<bullet> va, (ya \<leftrightarrow> c) \<bullet> sa)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (y \<leftrightarrow> c) \<bullet> s = (ya \<leftrightarrow> c) \<bullet> sa" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> xa) =  ((ya \<leftrightarrow> c) \<bullet> xa)" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> va) =  ((ya \<leftrightarrow> c) \<bullet> va)" using 1 by simp
    ultimately show ?case by argo
  qed 
next
 case (4 y s2 ya xa va s2a  c)
  then show ?case   
  apply -
  apply (drule eqvt_at_fvs_x_s)+
  apply (simp only: meta_eq_to_obj_eq[OF fvs_x_s_def, symmetric, unfolded fun_eq_iff])
  proof goal_cases (* Want to get the A in A \<Longrightarrow> B as a premise and B as a subgoal *)
    case 1
    hence "(y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s2 = fvs_x_s ((y \<leftrightarrow> c) \<bullet> xa) ((y \<leftrightarrow> c) \<bullet> va) ((y \<leftrightarrow> c) \<bullet> s2)"  proof -
      have " (y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s2 = (y \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, s2)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> (xa, va, s2))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> xa, (y \<leftrightarrow> c) \<bullet> va, (y \<leftrightarrow> c) \<bullet> s2)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va s2a = fvs_x_s ((ya \<leftrightarrow> c) \<bullet> xa) ((ya \<leftrightarrow> c) \<bullet> va) ((ya \<leftrightarrow> c) \<bullet> s2a)" proof - 
      have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va s2a = (ya \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, s2a)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> (xa, va, s2a))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> xa, (ya \<leftrightarrow> c) \<bullet> va, (ya \<leftrightarrow> c) \<bullet> s2a)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (y \<leftrightarrow> c) \<bullet> s2 = (ya \<leftrightarrow> c) \<bullet> s2a" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> xa) =  ((ya \<leftrightarrow> c) \<bullet> xa)" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> va) =  ((ya \<leftrightarrow> c) \<bullet> va)" using 1 by simp
    ultimately show ?case by argo
  qed 
next
  case (5 y s ya xa va sa csa c)
then show ?case   apply -
  apply (drule eqvt_at_fvs_x_s)+
  apply (simp only: meta_eq_to_obj_eq[OF fvs_x_s_def, symmetric, unfolded fun_eq_iff])
  proof goal_cases (* Want to get the A in A \<Longrightarrow> B as a premise and B as a subgoal *)
    case 1
    hence "(y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s = fvs_x_s ((y \<leftrightarrow> c) \<bullet> xa) ((y \<leftrightarrow> c) \<bullet> va) ((y \<leftrightarrow> c) \<bullet> s)"  proof -
      have " (y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s = (y \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, s)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> (xa, va, s))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> xa, (y \<leftrightarrow> c) \<bullet> va, (y \<leftrightarrow> c) \<bullet> s)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va sa = fvs_x_s ((ya \<leftrightarrow> c) \<bullet> xa) ((ya \<leftrightarrow> c) \<bullet> va) ((ya \<leftrightarrow> c) \<bullet> sa)" proof - 
      have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va sa = (ya \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, sa)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> (xa, va, sa))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> xa, (ya \<leftrightarrow> c) \<bullet> va, (ya \<leftrightarrow> c) \<bullet> sa)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (y \<leftrightarrow> c) \<bullet> s = (ya \<leftrightarrow> c) \<bullet> sa" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> xa) =  ((ya \<leftrightarrow> c) \<bullet> xa)" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> va) =  ((ya \<leftrightarrow> c) \<bullet> va)" using 1 by simp
    ultimately show ?case by argo
  qed 
next
  case (6 y s ya xa va sa c) 

  then show ?case   apply -
  apply (drule eqvt_at_fvs_x_s)+
  apply (simp only: meta_eq_to_obj_eq[OF fvs_x_s_def, symmetric, unfolded fun_eq_iff])
  proof goal_cases (* Trick to get the Ai in A1 \<Longrightarrow> .. \<Longrightarrow> An \<Longrightarrow> B premises and B as a subgoal *)
    case 1
    hence "(y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s = fvs_x_s ((y \<leftrightarrow> c) \<bullet> xa) ((y \<leftrightarrow> c) \<bullet> va) ((y \<leftrightarrow> c) \<bullet> s)"  proof -
      have " (y \<leftrightarrow> c) \<bullet> fvs_x_s xa va s = (y \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, s)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> (xa, va, s))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((y \<leftrightarrow> c) \<bullet> xa, (y \<leftrightarrow> c) \<bullet> va, (y \<leftrightarrow> c) \<bullet> s)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va sa = fvs_x_s ((ya \<leftrightarrow> c) \<bullet> xa) ((ya \<leftrightarrow> c) \<bullet> va) ((ya \<leftrightarrow> c) \<bullet> sa)" proof - 
      have " (ya \<leftrightarrow> c) \<bullet> fvs_x_s xa va sa = (ya \<leftrightarrow> c) \<bullet> (\<lambda>(a,b,c). fvs_x_s a b c) (xa, va, sa)" by fast
      also have "...  =  (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> (xa, va, sa))" 
        using eqvt_at_def 1 by blast
      also have "... = (\<lambda>(a,b,c). fvs_x_s a b c) ((ya \<leftrightarrow> c) \<bullet> xa, (ya \<leftrightarrow> c) \<bullet> va, (ya \<leftrightarrow> c) \<bullet> sa)" by simp
      finally show ?thesis by simp
    qed
    moreover have " (y \<leftrightarrow> c) \<bullet> s = (ya \<leftrightarrow> c) \<bullet> sa" using 1 by simp
    moreover have  "((y \<leftrightarrow> c) \<bullet> xa) =  ((ya \<leftrightarrow> c) \<bullet> xa)" using 1 
      by (metis flip_commute flip_fresh_fresh fresh_Pair fresh_PairD(2))
    moreover have  "((y \<leftrightarrow> c) \<bullet> va) =  ((ya \<leftrightarrow> c) \<bullet> va)" using 1 
     by (metis flip_commute flip_fresh_fresh fresh_Pair fresh_PairD(2))
    ultimately show ?case using 1 by argo
  qed  
}
qed
nominal_termination (eqvt) by lexicographic_order
*)
abbreviation 
  fvs_x_s_abbrev :: "s \<Rightarrow> xf \<Rightarrow> v \<Rightarrow> s" ("_[_::=_]\<^sub>s\<^sub>v" [1000,50,50] 1000)
where 
  "s[x::=v]\<^sub>s\<^sub>v  \<equiv> subst_x_s s  x v" 

abbreviation 
  subst_x_case_s_abbrev :: "case_s \<Rightarrow> xf \<Rightarrow> v \<Rightarrow> case_s" ("_[_::=_]\<^sub>s\<^sub>v" [1000,50,50] 1000)
where 
  "s[x::=v]\<^sub>s\<^sub>v  \<equiv> subst_x_case_s  s  x v" 

(*
lemma size_fvs_x_s [simp]:   "size (subst_x_case_s i x B) = size B" and  "size (fvs_x_s i x A) = size A"
  by(induct B and A  rule: case_s_s.induct,auto)

lemma forget_fvs_x_s [simp]: shows "atom a \<notin> fvs_x B \<Longrightarrow> subst_x_case_s a x B = B" and "atom a \<notin> fvs_x A \<Longrightarrow> fvs_x_s a x A = A"
  by (induct B and A  rule: case_s_s.induct,auto simp: )

lemma fvs_x_s_id [simp]: "subst_x_case_s a (V_var a) B = B" and  "fvs_x_s a (V_var a) A = A"
proof(induct B and A  rule: case_s_s.induct) 
  case (AS_let x option e s)
  then show ?case 
    by (metis (no_types, lifting) fresh_Pair not_None_eq subst_x_e_id fvs_x_s.simps(2) fvs_x_s.simps(3) subst_x_t_id v.fresh(2))
next
  case (AS_match v case_s)
  then show ?case using fresh_Pair not_None_eq subst_x_e_id fvs_x_s.simps fvs_x_s.simps subst_x_t_id v.fresh subst_x_v_id
    by metis 
qed(auto)+ 
 
lemma fresh_fvs_x_s_if_rl:
  shows "(atom x \<notin> fvs_x cs \<and> j \<notin> fvs_x cs) \<or> (j \<notin> fvs_x v \<and> (j \<notin> fvs_x cs \<or> j = atom x)) \<Longrightarrow> j \<notin> fvs_x (subst_x_case_s  cs)" and
        "(atom x \<notin> fvs_x s \<and> j \<notin> fvs_x s) \<or> (j \<notin> fvs_x v \<and> (j \<notin> fvs_x s \<or> j = atom x)) \<Longrightarrow> j \<notin> fvs_x (fvs_x_s  s)"
  apply(induct cs and s  rule: case_s_s.induct)
  using by force+

lemma fresh_fvs_x_s_if_lr:
  shows "j \<notin> fvs_x (subst_x_case_s  cs) \<Longrightarrow> (atom x \<notin> fvs_x cs \<and> j \<notin> fvs_x cs) \<or> (j \<notin> fvs_x v \<and> (j \<notin> fvs_x cs \<or> j = atom x))" and
        "j \<notin> fvs_x (fvs_x_s  s) \<Longrightarrow> (atom x \<notin> fvs_x s \<and> j \<notin> fvs_x s) \<or> (j \<notin> fvs_x v \<and> (j \<notin> fvs_x s \<or> j = atom x))"
proof(induct cs and s  rule: case_s_s.induct)
  case (C_final list x s)
  then show ?case  using case_s_s.fresh fresh_Pair list.distinct(1) list.set_cases set_ConsD subst_x_case_s.simps by metis
next
  case (C_branch list x s case_s)
  then show ?case 
    by (metis case_s_s.fresh(2) fresh_Pair list.distinct(1) list.set_cases set_ConsD subst_x_case_s.simps(2))
next
  case (AS_let y e s')
  thus ?case proof(cases "atom x \<notin> fvs_x  (AS_let y e s')")
    case True
    hence "fvs_x_s   (AS_let y  e s') =  (AS_let y e s')" using forget_fvs_x_s by simp
    hence "j \<notin> fvs_x  (AS_let y  e s')" using AS_let by argo
    then show ?thesis using True by blast
  next
    case False

      have "fvs_x_s  (AS_let y  e s') = AS_let y  (e[x::=v]\<^sub>e\<^sub>v) (s'[x::=v]\<^sub>s\<^sub>v)" using fvs_x_s.simps(2) AS_let by force
      hence "((j \<notin> fvs_x s'[x::=v]\<^sub>s\<^sub>v \<or> j \<in> set [atom y]) \<and> j \<notin> fvs_x None \<and> j \<notin> fvs_x e[x::=v]\<^sub>e\<^sub>v)" using case_s_s.fresh AS_let 
        by (simp add: fresh_None)
      then show ?thesis using  AS_let  fresh_None fresh_subst_x_e_if list.discI list.set_cases case_s_s.fresh set_ConsD 
        by metis
  qed
next
    case (AS_let2 y \<tau> s1 s2)
    thus ?case proof(cases "atom x \<notin> fvs_x  (AS_let2 y \<tau> s1 s2)")
      case True
      hence "fvs_x_s   (AS_let2 y \<tau> s1 s2) =  (AS_let2 y \<tau> s1 s2)" using forget_fvs_x_s by simp
      hence "j \<notin> fvs_x  (AS_let2 y \<tau> s1 s2)" using AS_let2 by argo
      then show ?thesis using True by blast
    next
      case False
      have "fvs_x_s  (AS_let2 y \<tau> s1 s2) = AS_let2 y (\<tau>[x::=v]\<^sub>\<tau>\<^sub>v) (s1[x::=v]\<^sub>s\<^sub>v) (s2[x::=v]\<^sub>s\<^sub>v)" using fvs_x_s.simps AS_let2 by force
      then show ?thesis using  AS_let2
        fresh_subst_x_t_if list.discI list.set_cases case_s_s.fresh(4) set_ConsD by auto
    qed
qed(auto)+

lemma fresh_fvs_x_s_if[simp]:
  "j \<notin> fvs_x (fvs_x_s  s) \<longleftrightarrow> (atom x \<notin> fvs_x s \<and> j \<notin> fvs_x s) \<or> (j \<notin> fvs_x v \<and> (j \<notin> fvs_x s \<or> j = atom x))" and
  "j \<notin> fvs_x (subst_x_case_s  cs) \<longleftrightarrow> (atom x \<notin> fvs_x cs \<and> j \<notin> fvs_x cs) \<or> (j \<notin> fvs_x v \<and> (j \<notin> fvs_x cs \<or> j = atom x))"
  using fresh_fvs_x_s_if_lr fresh_fvs_x_s_if_rl by metis+

lemma fvs_x_s_commute [simp]:
  fixes A::s and t::v
  shows "atom j \<notin> fvs_x B \<Longrightarrow> (subst_x_case_s j u (subst_x_case_s i t B)) = subst_x_case_s i (subst_x_v t j u) B" and
   "atom j \<notin> fvs_x A \<Longrightarrow> (fvs_x_s j u (fvs_x_s i t A)) = fvs_x_s i (subst_x_v t j u ) A"
  apply(induct B and A avoiding: i j t u rule: case_s_s.induct) 
             apply(auto simp: )
  done

lemma eqvt_flip_eq:
  assumes "eqvt_at f x" and 
     "atom c \<notin> fvs_x x" and "atom a \<notin> fvs_x x" and "atom b \<notin> fvs_x x"
   shows "( (a \<leftrightarrow>c) \<bullet> f) ((a \<leftrightarrow> c) \<bullet> x) = ( (b \<leftrightarrow> c) \<bullet> f) ( (b \<leftrightarrow> c) \<bullet> x)"
  using assms eqvt_at_def flip_fresh_fresh eqvt_apply
  by (metis (full_types) eqvt_apply)

lemma c_eq_perm:
  assumes "( (atom z)  \<rightleftharpoons> (atom z') )  \<bullet> c = c'" and "atom z'  \<notin> fvs_x c"
  shows "\<lbrace> z : b | c \<rbrace> = \<lbrace> z' : b | c' \<rbrace>"
  using \<tau>.eq_iff Abs1_eq_iff(3) 
  by (metis Nominal2_Base.swap_commute assms(1) assms(2) flip_def swap_fresh_fresh)

lemma fvs_x_s_flip:
  fixes s::s and sa::s and v'::v
  assumes "atom c \<notin> fvs_x (s, sa)" and "atom c \<notin> fvs_x (v',x, xa, s, sa)" "atom x \<notin> fvs_x v'" and "atom xa \<notin> fvs_x v'" and "(x \<leftrightarrow> c) \<bullet> s = (xa \<leftrightarrow> c) \<bullet> sa" 
  shows "s[x::=v']\<^sub>s\<^sub>v = sa[xa::=v']\<^sub>s\<^sub>v"
proof - 
  have "atom x \<notin> fvs_x (s[x::=v']\<^sub>s\<^sub>v)" and xafr: "atom xa \<notin> fvs_x (sa[xa::=v']\<^sub>s\<^sub>v)" 
       and  "atom c \<notin> fvs_x ( s[x::=v']\<^sub>s\<^sub>v, sa[xa::=v']\<^sub>s\<^sub>v)" using assms using  fresh_fvs_x_s_if assms  by( blast+ ,force)

  hence "s[x::=v']\<^sub>s\<^sub>v = (x \<leftrightarrow> c) \<bullet> (s[x::=v']\<^sub>s\<^sub>v)"  by (simp add: flip_fresh_fresh fresh_Pair)
  also have " ... = ((x \<leftrightarrow> c) \<bullet> s)[ ((x \<leftrightarrow> c) \<bullet> x) ::= ((x \<leftrightarrow> c) \<bullet> v') ]\<^sub>s\<^sub>v" using fvs_x_s_subst_x_case_s.eqvt  by blast
  also have "... = ((xa \<leftrightarrow> c) \<bullet> sa)[ ((x \<leftrightarrow> c) \<bullet> x) ::= ((x \<leftrightarrow> c) \<bullet> v') ]\<^sub>s\<^sub>v" using assms by presburger
  also have "... = ((xa \<leftrightarrow> c) \<bullet> sa)[ ((xa \<leftrightarrow> c) \<bullet> xa) ::= ((xa \<leftrightarrow> c) \<bullet> v') ]\<^sub>s\<^sub>v" using assms 
    by (metis flip_at_simps(1) flip_fresh_fresh fresh_PairD(1))
  also have "... =  (xa \<leftrightarrow> c) \<bullet> (sa[xa::=v']\<^sub>s\<^sub>v)" using fvs_x_s_subst_x_case_s.eqvt  by presburger
  also have "... = sa[xa::=v']\<^sub>s\<^sub>v" using xafr assms by (simp add: flip_fresh_fresh fresh_Pair)
  finally show ?thesis by simp
qed


lemma if_type_eq:
  fixes \<Gamma>::\<Gamma>
  assumes "atom z1' \<notin> fvs_x (v, ca, (x, b, c) # \<Gamma>,  (CE_val v  ==  CE_val (V_lit ll) IMP  ca[za::=V_var z1]\<^sub>c\<^sub>v ))" and "atom z1 \<notin> fvs_x v" 
     and "atom z1 \<notin> fvs_x (za,ca)" and "atom z1' \<notin> fvs_x (za,ca)"
  shows "(\<lbrace> z1' : ba  | CE_val v  ==  CE_val (V_lit ll)   IMP  ca[za::=V_var z1']\<^sub>c\<^sub>v  \<rbrace>) = \<lbrace> z1 : ba  | CE_val v  ==  CE_val (V_lit ll) IMP  ca[za::=V_var z1]\<^sub>c\<^sub>v  \<rbrace>"
proof -
    have "atom z1' \<notin> fvs_x (CE_val v  ==  CE_val (V_lit ll) IMP  ca[za::=V_var z1]\<^sub>c\<^sub>v )" using assms fresh_prod4 by blast
    moreover hence "(CE_val v  ==  CE_val (V_lit ll)   IMP  ca[za::=V_var z1']\<^sub>c\<^sub>v) = (z1' \<leftrightarrow> z1) \<bullet> (CE_val v  ==  CE_val (V_lit ll)   IMP  ca[za::=V_var z1]\<^sub>c\<^sub>v )"
    proof -
      have "(z1' \<leftrightarrow> z1) \<bullet> (CE_val v  ==  CE_val (V_lit ll)   IMP  ca[za::=V_var z1]\<^sub>c\<^sub>v ) = ( (z1' \<leftrightarrow> z1) \<bullet> (CE_val v  ==  CE_val (V_lit ll)) IMP  ((z1' \<leftrightarrow> z1) \<bullet> ca[za::=V_var z1]\<^sub>c\<^sub>v ))"
        by auto
      also have "... = ((CE_val v  ==  CE_val (V_lit ll))   IMP  ((z1' \<leftrightarrow> z1) \<bullet> ca[za::=V_var z1]\<^sub>c\<^sub>v ))"
        using \<open>atom z1 \<notin> fvs_x v\<close> assms 
        by (metis (mono_tags) \<open>atom z1' \<notin> fvs_x (CE_val v == CE_val (V_lit ll) IMP ca[za::=V_var z1]\<^sub>c\<^sub>v )\<close> c.fresh(6) c.fresh(7) ce.fresh(1) flip_at_simps(2) flip_fresh_fresh _permute_iff fresh_def supp_l_empty v.fresh(1))
      also have "... =  ((CE_val v  ==  CE_val (V_lit ll))   IMP  (ca[za::=V_var z1']\<^sub>c\<^sub>v ))"
        using assms  subst_x_c_v_flip2 by fastforce
      finally show ?thesis by auto
    qed
    ultimately show ?thesis    
      using \<tau>.eq_iff Abs1_eq_iff(3)[of z1' "CE_val v  ==  CE_val (V_lit ll) IMP  ca[za::=V_var z1']\<^sub>c\<^sub>v" 
       z1 "CE_val v  ==  CE_val (V_lit ll)   IMP ca[za::=V_var z1]\<^sub>c\<^sub>v"] by blast
qed 
*)
subsection \<open>Type Definition\<close>



lemma fresh_gamma_elem:
  fixes \<Gamma>::\<Gamma>
  assumes "a \<notin> fvs_x \<Gamma>"
  and "e \<in> setG \<Gamma>"
  shows "a \<notin> fvs_x e"
using assms by(induct \<Gamma>,auto simp add: fresh_GCons)

lemma fresh_gamma_append:
  fixes xs::\<Gamma>
  shows "a \<notin> fvs_x (xs @ ys) \<longleftrightarrow> a \<notin> fvs_x xs \<and> a \<notin> fvs_x ys"
by (induct xs, simp_all add: fresh_GNil fresh_GCons)

lemma supp_triple[simp]:
  shows "supp (x, y, z) = supp x \<union> supp y \<union> supp z"
proof -
  have "supp (x,y,z) = supp (x,(y,z))"  by auto
  hence "supp (x,y,z) = supp x \<union> (supp y  \<union> supp z)" using supp_Pair by metis
  thus ?thesis by auto
qed

lemma supp_append_g:
  fixes xs::\<Gamma>
  shows "supp (xs @ ys) = supp xs \<union> supp ys"
by(induct xs,auto simp add: supp_GNil supp_GCons )


lemma fresh_in_g[simp]:
  fixes \<Gamma>::\<Gamma>
  shows "atom x' \<notin> fvs_x \<Gamma>' @ (x, b0, c0) # \<Gamma> = (atom x' \<notin> supp \<Gamma>' \<union> supp x \<union> supp b0 \<union> supp c0 \<union> supp \<Gamma>)"
proof - 
   have  "atom x' \<notin> fvs_x \<Gamma>' @ (x, b0, c0) # \<Gamma> = (atom x' \<notin> supp (\<Gamma>' @((x,b0,c0)#\<Gamma>)))"
     using fresh_def by auto
   also have "... = (atom x' \<notin> supp \<Gamma>' \<union> supp ((x,b0,c0)#\<Gamma>))" using supp_append_g by fast
   also have "... = (atom x' \<notin> supp \<Gamma>' \<union> supp x \<union> supp b0 \<union> supp c0 \<union> supp \<Gamma>)" using supp_GCons supp_append_g supp_triple  by auto
   finally show ?thesis by fast
 qed

subsection \<open>Variable Context\<close>

lemma fresh_suffix[ms_fresh]:
 fixes \<Gamma>::\<Gamma>
  assumes "atom x \<notin> fvs_x \<Gamma>'@\<Gamma>"
  shows "atom x \<notin> fvs_x \<Gamma>"
using assms proof(induct  \<Gamma>' rule: \<Gamma>_induct )
  case GNil
  then show ?thesis by auto
next
  case (GCons x' b' c' \<Gamma>')
  hence "atom x \<notin> fvs_x ((x', b', c') # (\<Gamma>' @ \<Gamma>))" using append_g.simps by auto
  hence "atom x \<notin> fvs_x  (\<Gamma>' @ \<Gamma>)" using fresh_GCons by auto
  then show ?thesis using GCons by auto
qed


lemma not_GCons_self [simp]:
  fixes xs::\<Gamma>
  shows "xs \<noteq> x # xs"
by (induct xs) auto

lemma not_GCons_self2 [simp]: 
  fixes xs::\<Gamma>
  shows "x # xs \<noteq> xs"
by (rule not_GCons_self [symmetric])


lemma fresh_restrict:
  fixes y::xf and \<Gamma>::\<Gamma>
  assumes  "atom y \<notin> fvs_x  (\<Gamma>' @ (x, b, c) # \<Gamma>)"
  shows "atom y \<notin> fvs_x (\<Gamma>'@\<Gamma>)"
using assms proof(induct \<Gamma>' rule: \<Gamma>_induct)
  case GNil
  then show ?case using fresh_GCons fresh_GNil by auto
next
  case (GCons x' b' c' \<Gamma>'')
  then show ?case using fresh_GCons fresh_GNil by auto
qed


lemma subst_d_fst_eq:
   "fst ` setD (\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v) = fst ` setD \<Delta>" 
by(induct \<Delta> rule: \<Delta>_induct,simp,force)

(*
lemma subst_x_g_member_iff:
  fixes x'::x and x::x and v::v and c'::c
  assumes "(x',b',c') \<in> setG \<Gamma>" and "atom x \<notin> atom_dom \<Gamma>" 
  shows "(x',b',c'[x::=v]\<^sub>c\<^sub>v) \<in> setG \<Gamma>[x::=v]\<^sub>\<Gamma>\<^sub>v"
proof -
  have "x' \<noteq> x" using assms fresh_dom_free2 by auto
  then show ?thesis  using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
    then show ?case by auto
  next
    case (GCons x1 b1 c1 \<Gamma>')
    show ?case proof(cases "(x',b',c') = (x1,b1,c1)")
      case True
      hence "((x1, b1, c1) # \<Gamma>')[x::=v]\<^sub>\<Gamma>\<^sub>v = ((x1, b1, c1[x::=v]\<^sub>c\<^sub>v) # (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v))"  using subst_x_g.simps  \<open>x'\<noteq>x\<close> by auto
      then show ?thesis using True by auto
    next
      case False
      have "x1\<noteq>x" using fresh_def fresh_GCons fresh_Pair supp_at_base GCons fresh_dom_free2 by auto
      hence "(x', b', c') \<in> setG \<Gamma>'" using GCons False setG.simps by auto
      moreover have "atom x \<notin> atom_dom \<Gamma>'" using fresh_GCons GCons dom.simps setG.simps by simp
      ultimately have  "(x', b', c'[x::=v]\<^sub>c\<^sub>v) \<in> setG \<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v" using GCons by auto
      hence "(x', b', c'[x::=v]\<^sub>c\<^sub>v) \<in> setG ((x1, b1, c1[x::=v]\<^sub>c\<^sub>v) # (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v))" by auto
      then show ?thesis using subst_x_g.simps \<open>x1\<noteq>x\<close> by auto
    qed
  qed
qed
*)

subsection \<open>Mutable Variable Context\<close>

(*
lemma subst_d_supp:
  fixes x::x and v::v and \<Delta>::\<Delta>
  shows "supp \<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v \<subseteq> supp \<Delta> - { atom x } \<union> supp v"
proof(induct \<Delta> rule: \<Delta>.induct)
  case DNil
  then show ?case using  supp_DNil by auto
next
  case (DCons ut \<Delta>')

  obtain u and t where ut: "ut = (u,t)"  by fastforce

  have "atom x \<noteq> atom u" by fastforce
  hence ux: "supp u - { atom x } = supp u" using supp_at_base by blast
 
  have "supp (ut # \<Delta>')[x::=v]\<^sub>\<Delta>\<^sub>v =  supp ((u,t) # \<Delta>')[x::=v]\<^sub>\<Delta>\<^sub>v " using ut by auto
  also have "... = supp ((u,t[x::=v]\<^sub>\<tau>\<^sub>v) # \<Delta>'[x::=v]\<^sub>\<Delta>\<^sub>v)"  using subst_d.simps by auto
  also have "... = supp u \<union> (supp (t[x::=v]\<^sub>\<tau>\<^sub>v)) \<union> (supp ((\<Delta>'[x::=v]\<^sub>\<Delta>\<^sub>v)))" using supp_DCons supp_Pair by blast
  also have "... \<subseteq>  supp u \<union> (supp t - { atom x } \<union> supp v) \<union> (supp ((\<Delta>'[x::=v]\<^sub>\<Delta>\<^sub>v)))" using subst_x_t_supp2 by blast
  also have "... \<subseteq>  supp u \<union> (supp t - { atom x } \<union> supp v) \<union> (supp \<Delta>' - { atom x } \<union> supp v)" using DCons by blast
  also have "... \<subseteq> (supp u \<union> supp t \<union> supp \<Delta>') -  { atom x } \<union> supp v"
    by (simp add: Un_Diff Un_assoc Un_left_commute ux )
  finally show ?case using ut supp_DCons supp_Pair by blast
qed

lemma subst_d_fresh:
  fixes u::u and x::x and v::v and \<Delta>::\<Delta>
  assumes "atom u \<notin> fvs_x \<Delta>" 
  shows  "atom u \<notin> fvs_x (\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v)"
proof - 
  have "atom x \<noteq> atom u" by fastforce
  hence ux: "supp u - { atom x } = supp u" using supp_at_base by blast
  moreover have "supp (\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v) \<subseteq> supp \<Delta> - { atom x } \<union> supp v"
    using  subst_d_supp by auto
  moreover have "atom u \<notin> supp \<Delta>" using fresh_def assms by auto
  moreover have "atom u \<notin> supp v" using u_notin_supp_v by auto
  ultimately show ?thesis using fresh_def by fast
qed

subsection \<open>Permuting Variables\<close>

lemma flip_subst:
  fixes xa::x and x::x and c::c
  assumes "atom xa \<notin> fvs_x (z,c)" and  "atom x \<notin> fvs_x (z,c)"
  shows  "(x \<leftrightarrow> xa) \<bullet> c[z::=V_var x]\<^sub>c\<^sub>v = c[z::=V_var xa]\<^sub>c\<^sub>v"
using subst_x_c_v_flip1 assms by simp
*)
subsection \<open>Lookup\<close>

lemma set_GConsD: "y \<in> setG (x # xs) \<Longrightarrow> y=x \<or> y \<in> setG xs"
by auto

lemma lookup_in_atoms:
  assumes "Some (b,c) = lookup \<Gamma> x"
  shows "x \<in> dom \<Gamma>"
  using assms apply(induct \<Gamma>, simp)
  using lookup_options by fastforce

(*
fun type_for_var :: "\<Gamma> \<Rightarrow> \<tau> \<Rightarrow> xf \<Rightarrow> \<tau>" where
  "type_for_var G \<tau> x = (case lookup G x of 
                       None \<Rightarrow> \<tau>
                  | Some (b,c) \<Rightarrow> (\<lbrace> : b | c[x::=V_var z]\<^sub>v \<rbrace>)) "  
apply auto  unfolding eqvt_def apply(rule allI)  unfolding type_for_var_graph_aux_def eqvt_def by simp
nominal_termination (eqvt) by lexicographic_order

lemma lookup_restrict:
  assumes "Some (b',c') = lookup (\<Gamma>'@(x,b,c)#\<Gamma>) y" and "x \<noteq> y" 
  shows "Some (b',c') = lookup (\<Gamma>'@\<Gamma>) y"
using assms  proof(induct \<Gamma>' rule:\<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x1 b1 c1 \<Gamma>')
  then show ?case by auto
qed
*)

*)
*)
end
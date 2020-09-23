theory SailToMsLemmas
imports SailToMs Checker MiniSail.Typing 
begin

type_synonym ba=b

inductive_cases lit_conv_elims:
  "lit_conv (L_aux lit_aux.L_unit uu) lit"
  "lit_conv (L_aux lit_aux.L_true uu) lit"
  "lit_conv (L_aux lit_aux.L_false uu) lit"
  "lit_conv (L_aux (lit_aux.L_num ii) uu) lit"

inductive_cases v_conv_elims:
  "v_conv G (E_aux (E_lit lit) (uu, tan)) va"
  "v_conv G (E_aux (E_tuple [exp1, exp2]) (uw, tan)) va"

inductive_cases t_conv_elims:
  "t_conv G typp ta"
  "t_conv G (Typ_aux (Typ_app (Id_aux (id_aux.id STR ''atom_bool'') uu) [A_aux (A_bool (NC_aux tt uv)) uw]) ux) ta"
  "t_conv G (Typ_aux (Typ_tup [t1,t2]) uu) ta"

inductive_cases et_conv_elims:
   "et_conv tv (E_aux e (l,tan)) ta \<Gamma>"
   "et_conv tv (E_aux (E_tuple [exp1, exp2]) (uw, tan)) ta \<Gamma>"

thm t_conv_elims

(*
inductive_cases ce_conv_elims:
  "ce_conv G (SyntaxVCT.CE_val v) cea"

inductive_cases c_conv_elims:
  "c_conv G (SyntaxVCT.C_eq ce1 ce2) ca"

inductive_cases t_conv_elims:
  "t_conv G (\<lbrace> VIndex : bp |  cp \<rbrace> ) ta"

inductive_cases b_conv_elims:
  "b_conv SyntaxVCT.B_bool bp"

inductive_cases e_conv_elims:
  "e_conv G (SyntaxPED.Ep_val loc vp) ea"
  "e_conv G (SyntaxPED.Ep_bop loc bop (Ep_val l1 cp1) (Ep_val l2 cp2)) ea"
*)

thm t_conv.simps

section \<open>Wellformedness 1\<close>

text \<open>Conversion preserves well-formedness\<close>

(* Probably need [] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ce' : B_int and ce'' *)

inductive_cases g_conv_aux_elims:
  " g_conv_aux env type_vars ((x,typp) # gs) G"

lemma ce_conv_wfCE:
  fixes  ce::ce and c::c and b::b
  shows  "wfNE env nexp K_int \<Longrightarrow> tv = mk_type_vars (typ_vars env) ce' \<Longrightarrow> tv \<turnstile> nexp \<leadsto> ce \<Longrightarrow> g_conv_aux env tv (locals env) \<Gamma> \<Longrightarrow> [] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ce : B_int" and
         "wfNC env nc \<Longrightarrow>  tv = mk_type_vars (typ_vars env) ce' \<Longrightarrow> tv \<turnstile> nc \<leadsto> c \<Longrightarrow> g_conv_aux env tv (locals env) \<Gamma> \<Longrightarrow> [] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c" and
         "wfTyp env typ \<Longrightarrow>  tv = mk_type_vars (typ_vars env) ce' \<Longrightarrow> t_conv_raw tv typ ce'' b c \<Longrightarrow> g_conv_aux env tv locls \<Gamma> \<Longrightarrow> ([] ; {||} ; (xa,b,TRUE) #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c \<and> [] ; {||}  \<turnstile>\<^sub>w\<^sub>f b)" and   
         "wfLocals env (locals env) \<Longrightarrow>  tv = mk_type_vars (typ_vars env) ce' \<Longrightarrow> g_conv_aux env tv (locals env) \<Gamma> \<Longrightarrow>  [] ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>"  and
        "Checker.wfE env \<Longrightarrow>  tv = mk_type_vars (typ_vars env) ce' \<Longrightarrow> g_conv_aux env tv (locals env) \<Gamma> \<Longrightarrow> [] ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma> " 
proof(induct arbitrary: \<Gamma> and \<Gamma> and \<Gamma> b c ce'' locls and \<Gamma> and \<Gamma> rule: wfNE_wfNC_wfTyp_wfLocals_wfE.inducts)
  case (wfNE_constI env n uu)
  then show ?case sorry
next
  case (wfNE_timesI env nexp1 nexp2 uv)
  then show ?case sorry
next
  case (wfNE_sumI env nexp1 nexp2 uw)
  then show ?case sorry
next
  case (wfNE_minusI env nexp1 nexp2 ux)
  then show ?case sorry
next
  case (wfNE_kid kind uy env kid uz)
  then show ?case sorry
next
  case (wfNC_eqI env nexp1 k1 nexp2 k2 va)
  then show ?case sorry
next
  case (wfTyp_idI kd env x vb)
  then show ?case sorry
next
  case (wfTyp_fnI env typs_in typp_ret vc vd)
  then show ?case sorry
next
  case (wfTyp_bidirI env t1 t2 ve vf)
  then show ?case sorry
next
  case (wfTyp_tup env typs vg)
  then show ?case sorry
next
  case (wfTyp_app env x args vh)
  then show ?case sorry
next
  case (wfTyp_exist env kids nc t vi)
  then show ?case sorry
next
  case (wfLocals_nilI env)
  then show ?case sorry
next
  case (wfLocals_consI env "typ" locs x)
  then obtain G xa ba ca where *:"\<Gamma> = (xa, ba, ca) #\<^sub>\<Gamma> G \<and> g_conv_aux env tv locs G \<and> Some xa = mk_prog_x env x \<and> x \<notin> fvs_x_gs locs \<and> t_conv_raw tv typ [ [ xa ]\<^sup>v ]\<^sup>c\<^sup>e ba ca "
    using g_conv_aux_elims[of env tv x "typ" locs \<Gamma>] by metis
  show ?case proof(cases "ca \<in> { TRUE, FALSE}")
    case True
    then have " [] ; {||}  \<turnstile>\<^sub>w\<^sub>f  (xa, ba, ca) #\<^sub>\<Gamma> G" proof(rule wfG_cons2I)
      show "[] ; {||}  \<turnstile>\<^sub>w\<^sub>f G" using wfLocals_consI * by auto
      show "atom xa \<sharp> G" sorry  (* ok? mk_prog_x produces fresh variables? *)
      show "[] ; {||}  \<turnstile>\<^sub>w\<^sub>f ba " using wfLocals_consI * by metis
    qed
    thus  ?thesis using * by auto
  next
    case False
    then have " [] ; {||}  \<turnstile>\<^sub>w\<^sub>f  (xa, ba, ca) #\<^sub>\<Gamma> G" proof(rule wfG_cons1I)
      show "[] ; {||}  \<turnstile>\<^sub>w\<^sub>f G" using wfLocals_consI * by auto
      show "atom xa \<sharp> G" sorry  (* ok? mk_prog_x produces fresh variables? *)
      show "[] ; {||}  \<turnstile>\<^sub>w\<^sub>f ba " using wfLocals_consI * by metis
      show "[] ; {||} ; (xa, ba, TRUE) #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f ca " sorry
    qed
    thus  ?thesis using * by auto
next
  case (wfEI env)
  then show ?case by auto
qed


section \<open>Wellformedness 2\<close>

text \<open>We need this so that we can introduce contexts when, for example, lifting from literals to values or from values to expressions.
      We rely on the conversion system only giving us well-formed things - FIXME. Think not. Perhaps better to leave wf on the checker side and
that conversion respects wf\<close>

thm ce_conv_c_conv_t_conv_raw_g_conv_aux.inducts

lemma ce_conv_wfCE2:
  fixes  ce::ce and c::c and b::b
  shows  "type_vars \<turnstile> nexp \<leadsto> ce \<Longrightarrow> g_conv_aux env type_vars local_vars \<Gamma> \<Longrightarrow> [] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ce : B_int" and
         "type_vars \<turnstile> nc \<leadsto> c \<Longrightarrow> g_conv_aux env type_vars local_vars \<Gamma> \<Longrightarrow> [] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c" and
         "t_conv_raw type_vars typ ce b c \<Longrightarrow> g_conv_aux env type_vars local_vars \<Gamma> \<Longrightarrow> [] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c" and       
        "g_conv_aux env type_vars local_vars \<Gamma> \<Longrightarrow> [] ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma> " 
  proof(induct arbitrary: \<Gamma> and \<Gamma> and \<Gamma> and \<Gamma> rule: ce_conv_c_conv_t_conv_raw_g_conv_aux.inducts)
case (g_conv_nilI uu uv)
  then show ?case sorry
next
  case (g_conv_consI env type_vars gs G xa xx typp ba ca)
  then show ?case sorry
next
  case (ce_conv_sumI env ne1 ca1 ne2 ca2 uw)
  then show ?case sorry
next
  case (ce_conj_constI env ii ux)
  then show ?case sorry
next
  case (ce_conj_kidI ce env k uy)
then show ?case sorry
next
  case (t_conv_raw_unitI env ce)
  then show ?case sorry
next
  case (t_conv_raw_trueI env ve vf vg vh ce)
  then show ?case sorry
next
  case (t_conv_raw_false env vi vj vk vl ce)
  then show ?case sorry
next
  case (t_conv_raw_atomI env nexp ce2 vm vn vo ce)
  then show ?case sorry
next
  case (t_conv_raw_rangeI env nexp1 ce1 nexp2 ce2 vp vq vr vs ce)
  then show ?case sorry
next
  case (t_conv_raw_tuple_singleI env t1 ce ba1 ca1 vt)
  then show ?case sorry
next
  case (t_conv_raw_tuple_pairI env t1 ce ba1 ca1 t2 ba2 ca2 vu)
  then show ?case sorry
qed

lemma ce_conv_wfCE:
  fixes  ce::ce
  assumes "type_vars \<turnstile> nexp \<leadsto> ce" and "g_conv env type_vars \<Gamma>" 
  shows "[] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ce : B_int"
  using assms proof(induct rule: ce_conv.inducts)
  case (ce_conv_sumI env ne1 ca1 ne2 ca2 uu)
  then show ?case using wfCE_plusI by auto
next
  case (ce_conj_constI env ii uv)
  moreover have "[] ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>" sorry
  ultimately show ?case using wfCE_valI wfV_litI base_for_lit.simps by metis
qed

lemma c_conv_wfC:
  fixes  c::c
  assumes "env \<turnstile> nc \<leadsto> c" and "g_conv env \<Gamma>" 
  shows "[] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c"
using assms proof(induct rule: c_conv.inducts)
  case (1 G cep1 cea1 cep2 cea2 uu)
  then show ?case using ce_conv_wfCE wfC_eqI by metis
next
  case (2 G uv)
  moreover have "[] ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>" sorry
  ultimately show ?case using  wfC_trueI by auto
next
  case (3 G uw)
  moreover have "[] ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>" sorry
  ultimately show ?case using  wfC_falseI by auto
next
  case (4 G cp1 ca1 cp2 ca2 ux)
  then show ?case using wfC_conjI by auto
next
  case (5 G cp1 ca1 cp2 ca2 uy)
  then show ?case using wfC_disjI by auto
qed



lemma t_conv_wfT:
  fixes  ta::\<tau>
  assumes "env \<turnstile> typ \<leadsto> ta" and "g_conv env \<Gamma>"
  shows "[] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ta"
using assms proof(induct rule: t_conv.inducts)
  case (1 env t ba ca)
  then show ?case proof(induct rule: t_conv_raw.inducts)
    case (t_conv_raw_unitI env)
    then show ?case sorry
next
  case (t_conv_raw_trueI env uu uv uw ux)
  then show ?case sorry
next
  case (t_conv_raw_false env uy uz va vb)
  then show ?case sorry
next
  case (t_conv_raw_numI env vc num vd ve vf)
  then show ?case sorry
next
  case (t_conv_raw_pairI env t1 ba1 ca1 t2 ba2 ca2 vg)
  then show ?case sorry
qed
qed


(* the variable part of this is true by construction of G from E - types only reference kid variables
   and these are all at the back of the list (with true constraint).
   We need however to check that constraints are well-based  *)
lemma conv_g_wfG:
  fixes \<Gamma>::\<Gamma>
  assumes "g_conv_aux env (locals env) \<Gamma>"
  shows "[] ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
using assms proof(induct rule: g_conv_aux.induct)
  case g_conv_nilI
  then show ?case using wfG_nilI wfTh_emptyI by auto
next
  case (g_conv_consI env gs \<Gamma>' xa x typp ba ca)
  show ?case proof(cases "ca[mk_x 0::=[ xa ]\<^sup>v]\<^sub>c\<^sub>v \<in> {TRUE, FALSE}")
    case True
    then show ?thesis proof(rule wfG_cons2I)
      show \<open> [] ; {||}  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<close> using g_conv_consI by auto
      show \<open>atom xa \<sharp> \<Gamma>'\<close> using g_conv_consI sorry
      show \<open> [] ; {||}  \<turnstile>\<^sub>w\<^sub>f ba\<close> sorry
    qed
  next
    case False
    then show ?thesis proof(rule wfG_cons1I)
      show \<open> [] ; {||}  \<turnstile>\<^sub>w\<^sub>f \<Gamma>' \<close> using g_conv_consI by auto
      show \<open>atom xa \<sharp> \<Gamma>'\<close> using g_conv_consI sorry
      show "[] ; {||} ; (xa, ba, TRUE) # \<Gamma>'   \<turnstile>\<^sub>w\<^sub>f ca[mk_x 0::=[ xa ]\<^sup>v]\<^sub>c\<^sub>v "  sorry
      show "[] ; {||}  \<turnstile>\<^sub>w\<^sub>f ba " sorry
    qed
  qed
qed
(*
lemma v_conv_wfV:
  fixes e::exp and v::v
  assumes "check_s e" and "env \<turnstile> e \<leadsto> v" and "g_conv env \<Gamma> " and "t_conv env t ta" and "Some t = getTypeE e" and "Some env = getEnvE e"
  shows "[] ; {||} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f v : b_of ta"
using assms proof(induct rule: v_conv.induct)
  case (v_conv_litI l la G uu)
  hence "[] ; {||}  \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using conv_g_wfG g_conv.simps by auto
  moreover have "b_of ta = base_for_lit la" sorry
  ultimately show ?case using wfV_litI by auto
next
  case (v_conv_varI xa env idd uv tan)
  then show ?case sorry
next
  case (v_conv_pairI env vp1 v1 vp2 v2 uw)
  then show ?case sorry
qed 
*)



section \<open>Soundness\<close>

lemma infer_l_sound:
  shows "check_lit env l typp \<Longrightarrow> lit_conv l lit \<Longrightarrow> t_conv G typp \<tau> \<Longrightarrow>  \<turnstile> lit \<Rightarrow> \<tau> " 
proof(induct rule: check_lit.induct)
  case (check_lit_unitI env uu uv uw)
  then have "lit = Syntax.L_unit" using lit_conv_elims by metis
  moreover have "\<tau> = \<lbrace> mk_x 0 : B_unit | [ [ mk_x 0 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ Syntax.L_unit ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" using t_conv_elims check_lit_unitI  sorry
  ultimately show ?case using infer_l.intros by simp
next
  case (check_lit_numI env num ux uy uz va vb)
  then obtain n where "lit = Syntax.L_num n" using lit_conv_elims by metis                                     
  moreover have "\<tau> = \<lbrace> mk_x 0 : B_int | [ [ mk_x 0 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ Syntax.L_num n]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" 
    using t_conv_elims(1)[OF check_lit_numI(2)] 
      by (metis check_lit_numI.prems(1) lit_conv_elims(4)) (* 0.0 ms *)
  ultimately show ?case using infer_l.intros by simp
next
  case (check_lit_trueI env vc vd ve vf vg)
  then have "lit = Syntax.L_true" using lit_conv_elims by metis                                     
  moreover have "\<tau> = \<lbrace> mk_x 0 : B_bool | [ [ mk_x 0 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ Syntax.L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" 
    using t_conv_elims(2)[OF check_lit_trueI(2)] sorry
(*    by (metis n_constraint_aux.distinct(155) typ_aux.distinct(23) typp.inject unit_typ_def)*)
  ultimately show ?case using infer_l.intros by simp
next
  case (check_lit_falseI env vh vi vj vk vl)
  then have "lit = Syntax.L_false" using lit_conv_elims by metis                                     
  moreover have "\<tau> = \<lbrace> mk_x 0 : B_bool | [ [ mk_x 0 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ Syntax.L_false ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" 
    using t_conv_elims(2)[OF check_lit_falseI(2)] 
(*    by (metis n_constraint_aux.distinct typ_aux.distinct typp.inject unit_typ_def)*) sorry
  ultimately show ?case using infer_l.intros by simp
qed

(*
lemma 
  assumes " g_conv_aux gs G G''" and "Some (G', xa) = add_var_g G'' x"
  shows "atom xa \<notin> (atom ` fst ` setG G)"
using assms proof(induct arbitrary: xa rule: g_conv_aux.induct)
  case g_conv_nilI
  then show ?case by auto
next
 case (g_conv_consI gs G G'' G' xa' x typp ta)
  then show ?case sorry
qed
*)


(* FIXME FIXME - the ta from the v_conv is actually generated from va; doesnt use the type in e 
 
   v_conv must actually be type free.
   perhaps the second ta needs to be subtype of the one from et_conv ?

*)

lemma infer_v_sound:
  fixes e::"tannot Ast.exp"
  shows   "check_exp e \<Longrightarrow> v_conv env  e va \<Longrightarrow> et_conv e ta \<Gamma> \<Longrightarrow> \<exists>ta'. [] ; {||} ; \<Gamma> \<turnstile> va \<Rightarrow> ta' \<and> [] ; {||} ; \<Gamma> \<turnstile> ta' \<lesssim> ta" and
          "check_letbind lb g \<Longrightarrow> True" and
          "check_pexp pexp \<Longrightarrow> True" and
          "check_pexps pexp_list \<Longrightarrow> True"
proof(induct arbitrary: va ta rule: check_exp_check_letbind_check_pexp_check_pexps.inducts)
  case (check_litI env tan t lit uu)
  then obtain la where la:"va = V_lit la \<and>  lit_conv lit la" using v_conv_elims by metis
  obtain t4 env4 G4 where *:"Some t4 = getType tan \<and> Some env4 = getEnv tan \<and> g_conv env \<Gamma>  \<and> t_conv G4 t4 ta"
    using   et_conv_elims(1)[OF check_litI(5)]  by (metis check_litI.hyps option.inject)
  hence "t4 = t \<and> env4 = env" using check_litI 
    by (metis option.inject)
  hence "\<turnstile> la \<Rightarrow> ta" using check_litI infer_l_sound * la by auto
  moreover have "[] ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using conv_g_wfG g_conv.simps * sorry
  ultimately show ?case using  infer_v_litI la sorry
next
  case (check_idI t1 tan x t2 env uv)
  then show ?case sorry
next
  case (check_pairI exp1 exp2 env tan "typ" t1 t2 loc uw)
  then obtain va1 va2  where va:"va = Syntax.V_pair va1 va2 \<and> v_conv env exp1 va1  \<and> v_conv env exp2 va2" using v_conv_elims sorry
  obtain ta1 and ta2 where "et_conv exp1 ta1 \<Gamma> \<and> et_conv exp2 ta2 \<Gamma>" using et_conv_elims(2) t_conv_elims(3) check_pairI sorry
  then obtain ta1' and ta2' where "[] ; {||} ; \<Gamma> \<turnstile> va1 \<Rightarrow>ta1' \<and> [] ; {||} ; \<Gamma> \<turnstile> va2 \<Rightarrow> ta2'" using va check_pairI sorry
   
  have " [] ; {||} ; \<Gamma> \<turnstile> [ va1 , va2 ]\<^sup>v \<Rightarrow> \<lbrace> mk_x 0 : [ b_of ta1' , b_of ta2' ]\<^sup>b  | [ [ mk_x 0 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ va1 , va2 ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" 
  proof
    show "atom (mk_x 0) \<sharp> (va1, va2)" sorry
    show "atom (mk_x 0) \<sharp> \<Gamma>"  sorry
    show "[] ; {||} ; \<Gamma> \<turnstile> va1 \<Rightarrow> \<lbrace>mk_x 0 : b_of ta1'  | c_of ta1' (mk_x 0) \<rbrace>" using check_pairI  sorry (* ok - we have a lemma that type is ta1' *)
    show "[] ; {||} ; \<Gamma> \<turnstile> va2 \<Rightarrow> \<lbrace>mk_x 0 : b_of ta2'  | c_of ta2' (mk_x 0) \<rbrace>" using check_pairI  sorry
  qed 
  moreover have "[] ; {||} ; \<Gamma>  \<turnstile>  \<lbrace> mk_x 0 : [ b_of ta1' , b_of ta2' ]\<^sup>b  | [ [ mk_x 0 ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ va1 , va2 ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace> \<lesssim> ta" 
    sorry (* base of ta is the same and lhs is most specific of type for va *)
  ultimately show  ?case using va by metis
next
  case (check_fstI exp ux uy tan)
  then show ?case using v_conv.simps by blast
next
  case (check_sndI exp uz va tan)
  then show ?case using v_conv.simps by blast
next
  case (check_letI lb exp env t1 t2 tan vb)
  then show ?case using v_conv.simps by blast
next
  case (check_ifI exp1 exp2 exp3 env tan vc nc vd ve env2 env3 t t2 t3 vf)
  then show ?case using v_conv.simps by blast
next
  case (check_varI exp1 exp2 te env tan "typ" mvar vg vh)
  then show ?case using v_conv.simps by blast
next
  case (check_assignI exp t tan mvar te env vi vj)
  then show ?case using v_conv.simps by blast
next
  case (check_caseI exp pexps vk tan)
  then show ?case using v_conv.simps by blast
next
  case check_pexps_nilI
  then show ?case using v_conv.simps by blast
next
  case (check_pexps_conI pexp pexps)
  then show ?case  by blast
next
  case (check_block_nilI vl tan)
  then show ?case using v_conv.simps by blast
next
  case (check_block_consI exp exps tan vm)
  then show ?case using v_conv.simps by blast
next
  case (check_letbindI pat exp vn tan)
  then show ?case using v_conv.simps by blast
next
  case (check_pexpI pat exp vo tan)
  then show ?case using v_conv.simps by blast
qed (blast+)


lemma infer_e_sound:
  fixes e::"tannot Ast.exp"
  shows   
    "check_exp e \<Longrightarrow> e_conv env e ea \<Longrightarrow>  et_conv e ta \<Gamma> \<Longrightarrow> [] ; [] ; {||} ; \<Gamma> ; DNil \<turnstile> ea \<Rightarrow> ta' \<and>  [] ; {||} ; \<Gamma> \<turnstile> ta' \<lesssim> ta" and
    "check_letbind lb g \<Longrightarrow> True" and
    "check_pexp pexp \<Longrightarrow> True" and
    "check_pexps pexp_list \<Longrightarrow> True"
proof(induct arbitrary: ea ta ta' rule: check_exp_check_letbind_check_pexp_check_pexps.inducts)
  case (check_litI env tan t lit uu)
  then show ?case using e_conv.simps sorry
next
  case (check_idI t1 tan x t2 env uv)
  then show ?case sorry
next
  case (check_pairI exp1 exp2 env tan "typ" t1 t2 loc uw)
  then show ?case using e_conv.simps sorry
next
  case (check_fstI exp ux uy tan)
  then show ?case sorry
next
  case (check_sndI exp uz va tan)
  then show ?case sorry
next
  case (check_letI lb exp env t1 t2 tan vb)
  then show ?case using e_conv.simps v_conv.simps sorry
next
  case (check_ifI exp1 exp2 exp3 env tan vc nc vd ve env2 env3 t t2 t3 vf)
  then show ?case using e_conv.simps sorry
next
  case (check_varI exp1 exp2 te env tan "typ" mvar vg vh)
  then show ?case using e_conv.simps sorry
next
  case (check_assignI exp t tan mvar te env vi vj)
  then show ?case using e_conv.simps sorry
next
  case (check_caseI exp pexps vk tan)
  then show ?case using e_conv.simps sorry
next
  case check_pexps_nilI
  then show ?case using e_conv.simps by auto
next
  case (check_pexps_conI pexp pexps)
  then show ?case sorry
next
  case (check_block_nilI vl tan)
  then show ?case using e_conv.simps sorry
next
  case (check_block_consI exp exps tan vm)
  then show ?case using e_conv.simps sorry
next
  case (check_letbindI pat exp vn tan)
  then show ?case using e_conv.simps by auto
next
  case (check_pexpI pat exp vo tan)
  then show ?case using e_conv.simps by auto
qed

inductive_cases s_conv_elims:
  "s_conv G (E_aux (E_let lb exp) (vb, tan)) sa"

thm s_conv_elims


lemma 
  shows "s_conv [] (E_aux (E_let lb exp) (vb, tan)) sa \<Longrightarrow> \<exists>G2 xa2 ea2 sa2. sa = LET xa2 = ea2 IN sa2 \<and> lb_conv [] lb G2 xa2 ea2 \<and> s_conv G2 exp sa2" and
       "lb_conv G lb G' xa ea \<Longrightarrow> True" and "pexp_conv G pexp br \<Longrightarrow> True" and "pexp_list_conv G pexp_list bs \<Longrightarrow> True"
  proof(induct  "(E_aux (E_let lb exp) (vb, tan))" sa rule:s_conv_lb_conv_pexp_conv_pexp_list_conv.inducts)
case (lb_convI G ep1 ea G' xa x uu uv)
  then show ?case by auto
next
  case (s_conv_letI G G' xa ea sa)
  then show ?case by metis
next
  case s_conv_ifI
  then show ?case by auto
next
  case (s_conv_valI G va)
  then show ?case using v_conv.cases[OF s_conv_valI] by auto
qed

lemma check_s_sound:
  fixes e::"tannot Ast.exp"
  shows "check_exp e \<Longrightarrow> s_conv G e sa \<Longrightarrow> et_conv e ta \<Gamma> \<Longrightarrow>[] ; [] ; {||} ; \<Gamma> ; DNil \<turnstile> sa \<Leftarrow> ta" and
        "check_letbind lb g \<Longrightarrow> lb_conv G lb G' xa ea \<Longrightarrow> \<exists>ta. [] ; [] ; {||} ; \<Gamma> ; DNil \<turnstile> ea \<Rightarrow> ta"   and
        "check_pexp pexp \<Longrightarrow> pexp_conv G pexp br \<Longrightarrow> check_branch_s Nil Nil  {||} \<Gamma>  DNil  tyid  ctor  \<tau> v br  ta" and
        "check_pexps pexp_list \<Longrightarrow> pexp_list_conv G pexp_list branch_list \<Longrightarrow> check_branch_list Nil Nil  {||} \<Gamma>  DNil  tyid  dclist v branch_list  ta" 
proof(induct arbitrary: sa ta G \<Gamma>  and ea xa G' G \<Gamma> rule: check_exp_check_letbind_check_pexp_check_pexps.inducts)
case (check_litI env tan t lit uu)
  then show ?case sorry
next
  case (check_idI t1 tan x t2 env uv)
  then show ?case sorry
next
  case (check_pairI exp1 exp2 env tan "typ" t1 t2 loc uw)
  then show ?case sorry
next
  case (check_fstI exp ux uy tan)
  then show ?case sorry
next
  case (check_sndI exp uz va tan)
  then show ?case sorry
next
    case (check_letI lb bindings env exp t1 t2 tan vb)
  thm s_conv_lb_conv_pexp_conv_pexp_list_conv.inducts

  obtain G2 xa2 ea2 sa2 where *:"sa = LET xa2 = ea2 IN sa2 \<and> lb_conv G lb G2 xa2 ea2 \<and> s_conv G2 exp sa2" 
  proof(rule s_conv_elims(1)[OF check_letI(10)],goal_cases)
    case (1 G' xa ea sa)
    then show ?case by auto
  next
    case (2 va)
    then show ?case using v_conv.cases by auto
  qed

  obtain ta2 where ta2: "[] ; [] ; {||} ; \<Gamma> ; []  \<turnstile> ea2 \<Rightarrow> ta2" using check_letI(2)[of _ G2 xa2 ea2] * by auto

  let ?\<Gamma> = " (xa2, b_of ta2, (c_of ta2 (mk_x 0))[mk_x 0::=[ xa2 ]\<^sup>v]\<^sub>v) # \<Gamma>"

  have **:"et_conv exp ta ?\<Gamma>" using check_letI sorry (* needs thought *)

  have "[] ; [] ; {||} ; \<Gamma> ; []  \<turnstile> LET xa2 = ea2 IN sa2 \<Leftarrow> ta"
  proof
    show "atom xa2 \<sharp> (Nil, Nil, {||}, \<Gamma>, DNil, ea2, ta)" sorry (* okish *)
    show "atom (mk_x 0) \<sharp> (xa2, Nil, Nil, {||}, \<Gamma>, DNil, ea2, ta, sa2)" sorry  (* okish *)
    show "[] ; [] ; {||} ; \<Gamma> ; []  \<turnstile> ea2 \<Rightarrow> \<lbrace> mk_x 0 : b_of ta2  | c_of ta2 (mk_x 0) \<rbrace>" using ta2 sorry  (* ok *)
    show "[] ; [] ; {||} ; ?\<Gamma> ; []  \<turnstile> sa2 \<Leftarrow> ta" using check_letI(5)[of G2 sa2 ta] * ** by auto
  qed
  then show ?case using * by auto

next
  case (check_ifI exp1 exp2 exp3 env tan vc nc vd ve env2 env3 t t2 t3 vf)
  then show ?case sorry
next
  case (check_varI exp1 exp2 te env tan "typ" mvar vg vh)
  then show ?case sorry
next
  case (check_assignI exp t tan mvar te env vi vj)
  then show ?case sorry
next
  case (check_caseI exp pexps vk tan)
  then show ?case sorry
next
  case check_pexps_nilI
  then show ?case sorry
next
  case (check_pexps_conI pexp pexps)
  then show ?case sorry
next
  case (check_block_nilI vl tan)
  then show ?case sorry
next
  case (check_block_consI exp exps tan vm)
  then show ?case sorry
next
  case (check_letbindI pat exp vn tan)
  then show ?case sorry
next
case (check_pexpI pat exp vo tan)
  then show ?case sorry
qed

end
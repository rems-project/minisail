theory SailToMsDirect
imports Validator Utils SailEnv SailASTUtils ShowAST "../Safety/Syntax"   "HOL-Library.Debug" "../Safety/Typing"
begin


chapter\<open>Convert from Sail to MiniSail directly and with proofs\<close>

text \<open>Here we convert Sail that is already in MiniSail directly to MiniSail. We build this up 
with proofs from the start\<close>


type_synonym xa=x
type_synonym ea=e
type_synonym va=v
type_synonym sa=s
type_synonym la=l
type_synonym ba=b
type_synonym ca=c

type_synonym exp  = "tannot exp"

section \<open>Types\<close>

inductive b_of_typ :: "typ \<Rightarrow> b \<Rightarrow> bool" where
"b_of_typ  unit_typ  B_unit"
| "b_of_typ ( (Typ_app ( (SailAST.id (STR ''atom_bool'')) ) _)  )  B_bool" 
| "b_of_typ  ( (Typ_app ( (SailAST.id (STR ''atom'')) ) _ ) ) B_int"
| "b_of_typ  ( (Typ_app ( (SailAST.id (STR ''bitvector'')) ) _ ) ) B_bitvec"
| "b_of_typ  ( (Typ_id ( (SailAST.id (STR ''unit'')) )  ) ) B_unit"
| "\<lbrakk>  
   b_of_typ  t1 b1;
   b_of_typ  t2 b2
\<rbrakk> \<Longrightarrow> b_of_typ ( (Typ_tup [t1,t2]) ) (B_pair b1 b2)"
| "b_of_typ (Typ_id (SailAST.id tyid)) (B_id (String.explode tyid))"


inductive t_conv :: "typ \<Rightarrow> \<tau> \<Rightarrow> bool" where
  "t_conv  ( (Typ_id ( (SailAST.id (STR ''unit'')) )  ) ) \<lbrace> z : B_unit | [[z]\<^sup>v]\<^sup>c\<^sup>e == [[L_unit]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>"

inductive_cases t_conv_elims[elim!]:
  "t_conv typ ta"

thm t_conv.intros

section \<open>Literals\<close>

inductive lit_conv :: "lit \<Rightarrow> la \<Rightarrow> bool"  ( "\<turnstile> _ \<leadsto> _") where
lit_conv_unitI:   "\<turnstile> ( SailAST.L_unit  ) \<leadsto> L_unit"
 | lit_conv_trueI:  "\<turnstile>  ( SailAST.L_true ) \<leadsto>  L_true"
 | lit_conv_falseI:  "\<turnstile> ( SailAST.L_false ) \<leadsto> L_false"
 | lit_conv_bvec_bit: "\<turnstile> (SailAST.L_bin bs) \<leadsto> L_bitvec (List.map (\<lambda>b. if b = CHR ''1'' then BitOne else BitZero) (String.explode bs))"
 | lit_conv_bvec_hex: "\<turnstile> (SailAST.L_hex bs) \<leadsto> L_bitvec []"
 | lit_conv_num:  "lit_conv (SailAST.L_num ii)  (L_num (int_of_integer ii))"

hide_const id
inductive_cases check_lit_elims[elim!]:
  "check_lit env SailAST.L_unit typ"

thm check_lit_elims

(* Could make this check_l ?. Might need to as bitvec we make precise in MS but not in Sail *)
lemma sound_lit:
  assumes  "lit_conv l la" and "check_lit env l typ" and "t_conv typ ta"
  shows "infer_l la ta"
using assms proof(induct)
  case lit_conv_unitI
  hence  t:"typ = Typ_id (id STR ''unit'')" using check_lit_elims by auto
  hence bof: "b_of_typ typ B_unit" using b_of_typ.intros by simp 
  then obtain z where "ta = \<lbrace> z : B_unit |  [[z]\<^sup>v]\<^sup>c\<^sup>e == [[L_unit]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>" using t_conv_elims[OF lit_conv_unitI(2)] bof t by metis
  then show ?case using infer_l.intros by simp
next
  case lit_conv_trueI
  then show ?case sorry
next
  case lit_conv_falseI
  then show ?case sorry
next
  case (lit_conv_bvec_bit bs)
  then show ?case sorry
next
  case (lit_conv_bvec_hex bs)
  then show ?case sorry
next
  case (lit_conv_num ii)
  then show ?case sorry
qed

section \<open>Values\<close>


type_synonym xmap = "(SailAST.id * xa ) list"

inductive v_conv :: "env \<Rightarrow> xmap \<Rightarrow> exp \<Rightarrow> \<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> va  \<Rightarrow> bool" ( "_ ; _ \<turnstile> _ \<leadsto> _ ; _ ; _ ") where
 v_conv_litI:  "\<lbrakk>
   trace ''v_conv_litI'';
   \<turnstile> l \<leadsto> la 
\<rbrakk> \<Longrightarrow> E ; _ \<turnstile> ( (SailAST.E_lit _ l) ) \<leadsto> [] ; GNil ; (V_lit la )"

| v_conv_varI:"\<lbrakk> 
   trace ''v_conv_varI'';
   Some xa = SailEnv.lookup xm idd;
   Some t = lookup_local_id_env env idd;
   b_of_typ t ba;
   trace (''v_conv_varI end'' @ (cf ba))
\<rbrakk> \<Longrightarrow> 
  env ; xm \<turnstile>   ( (SailAST.E_id _ idd)) \<leadsto> [] ; (xa,ba,C_true) #\<^sub>\<Gamma> GNil ; (V_var xa) "


(* FIXME Better merging of m1 and m2 is needed *)
| v_conv_pairI: "\<lbrakk> 
   trace ''v_conv_pairI'';
   env ; m \<turnstile> vp1 \<leadsto> T1 ; G1; v1 ; 
   env ; m \<turnstile> vp2 \<leadsto> T2 ; G2; v2  
\<rbrakk> \<Longrightarrow> 
   env ; m \<turnstile> ( (SailAST.E_tuple _ [vp1, vp2])  ) \<leadsto> T1 @ T2 ; G1 @ G2 ; (V_pair v1 v2)" 

lemma v_conv_wf:
  fixes \<Theta>::\<Theta> and \<Gamma>::\<Gamma>
  assumes  "v_conv env xm exp \<Theta> \<Gamma> va"
  shows "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
using assms proof(induct)
  case (v_conv_litI l la E uu uv)
  then show ?case using wfG_nilI wfTh_emptyI by simp
next
  case (v_conv_varI xa xm idd t env ba cf uw)
  then show ?case sorry
next
  case (v_conv_pairI env m vp1 T1 G1 v1 vp2 T2 G2 v2 ux)
  then show ?case sorry
qed



lemma sound_v:
  assumes  "v_conv env xm exp \<Theta> \<Gamma> va" and "check_exp env exp typ" and "t_conv typ ta"
  shows "infer_v \<Theta> {||} \<Gamma> la ta"
using assms proof(induct)
  case (v_conv_litI l la E uu uv)
  moreover have "\<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f \<Gamma>" sorry
  ultimately  show ?case using sound_lit infer_v_litI sorry
next
  case (v_conv_varI xa xm idd t env ba cf uw)
  then show ?case sorry
next
  case (v_conv_pairI env m vp1 T1 G1 v1 vp2 T2 G2 v2 ux)
  then show ?case sorry
qed
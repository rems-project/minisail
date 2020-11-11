(*<*)
theory TypingDBI
  imports  WellformedDBI IVSubstDBI BTVSubstDBI
begin
(*>*)

chapter \<open>Type System\<close>

section \<open>Typing Judgements\<close>

subsection \<open>Subtyping\<close>

(* Work will be needed to get code gen to work with this. See https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2017-February/msg00060.html *)
(*
locale smt_valid  =
  fixes valid :: "\<Theta> \<Rightarrow>  \<B>  \<Rightarrow> \<Gamma> \<Rightarrow> c \<Rightarrow> bool" ("_ ; _ ; _  \<Turnstile> _ " [50, 50] 50)
begin

end

context smt_valid
begin
*)
text {* Subtyping is defined on top of SMT logic. A subtyping check is converted into an SMT validity check. *}


(*
; 
                    x = mk_fresh_x  \<Gamma> ;
            \<Theta> ; \<B> ; (x,b,open_x c x 0 )#\<Gamma> \<Turnstile> (open_x c' x 0)
*)
inductive subtype :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> bool"  ("_ ; _ ; _  \<turnstile> _ \<lesssim> _" [50, 50, 50] 50) where
  subtype_baseI: "\<lbrakk> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> : b | c \<rbrace>;  
                    \<Theta> ; \<B>  ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace>  : b | c' \<rbrace>
                   
\<rbrakk> \<Longrightarrow>  
                    \<Theta> ; \<B> ; \<Gamma> \<turnstile>  \<lbrace> : b | c \<rbrace>  \<lesssim> \<lbrace>  : b | c' \<rbrace>"

code_pred (modes: 
       subtype: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool  ) [show_steps,  show_mode_inference,  show_invalid_clauses] subtype .

inductive_cases subtype_elims: 
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> \<lbrace> : b | c \<rbrace> \<lesssim>  \<lbrace>  : b | c' \<rbrace>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> \<tau>\<^sub>1 \<lesssim>  \<tau>\<^sub>2"




subsection \<open>Literals\<close>

text {* The type synthesised has the constraint that z equates to the literal *}
inductive infer_l  :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> l \<Rightarrow> \<tau> \<Rightarrow> bool" ("_  ; _ ; _ \<turnstile> _ \<Rightarrow> _" [50, 50, 50] 50) where
  infer_trueI:  "\<lbrakk> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile> L_true \<Rightarrow> \<lbrace>  : B_bool | (C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit (L_true))))\<rbrace>"
| infer_falseI: "\<lbrakk> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile> L_false \<Rightarrow> \<lbrace>  : B_bool | (C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit (L_false))))\<rbrace>"
| infer_natI:   "\<lbrakk> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile> L_num n \<Rightarrow> \<lbrace>  : B_int  | (C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit (L_num n))))\<rbrace>"
| infer_unitI:  "\<lbrakk> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile> L_unit \<Rightarrow> \<lbrace>  : B_unit | (C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit (L_unit)))) \<rbrace>"
| infer_bitvecI:  "\<lbrakk> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile> L_bitvec bv \<Rightarrow> \<lbrace>  : B_bitvec | (C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit (L_bitvec bv)))) \<rbrace>"


inductive_cases infer_l_elims[elim!]:
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> L_true \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> L_false \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> L_num n \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> L_unit \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> L_bitvec x \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> l \<Rightarrow> \<tau>"


lemma infer_l_form2[simp]:
  fixes \<Gamma>::\<Gamma>
  assumes "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> "   
  shows "\<Theta> ; \<B> ; \<Gamma> \<turnstile> l \<Rightarrow> (\<lbrace> : base_for_lit l | C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit l)) \<rbrace>)"
  using assms
proof (induct l)
  case (L_num x)
  then show ?case using infer_l.intros base_for_lit.simps  by metis
next
  case L_true
then show ?case using infer_l.intros base_for_lit.simps  by metis
next
case L_false
  then show ?case using infer_l.intros base_for_lit.simps  by metis
next
  case L_unit
  then show ?case using infer_l.intros base_for_lit.simps  by metis
next
case (L_bitvec x)
  then show ?case using infer_l.intros base_for_lit.simps by metis
qed

subsection \<open>Values\<close>

inductive infer_v :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> v \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ; _ ; _ \<turnstile> _ \<Rightarrow> _" [50, 50, 50] 50) where

infer_v_varI: "\<lbrakk>
      \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; 
      Some (b,c) = lookup \<Gamma> (XBVar k) \<rbrakk> \<Longrightarrow> 
      \<Theta> ; \<B> ; \<Gamma>    \<turnstile> V_var (XBVar k) \<Rightarrow> \<lbrace> : b | C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_var (XBVar (k+1)))) \<rbrace>"

| infer_v_litI: "\<lbrakk>
      \<Theta> ; \<B> ; \<Gamma> \<turnstile> l \<Rightarrow> \<tau> \<rbrakk> \<Longrightarrow> 
      \<Theta> ; \<B> ; \<Gamma> \<turnstile> V_lit l \<Rightarrow> \<tau>"

| infer_v_pairI: "\<lbrakk> 
     
      \<Theta> ; \<B> ; \<Gamma> \<turnstile> v1 \<Rightarrow> (\<lbrace>  : b1 | c1 \<rbrace>) ; 
      \<Theta>  ; \<B> ;  \<Gamma> \<turnstile> v2 \<Rightarrow> (\<lbrace> : b2 | c2 \<rbrace>)  \<rbrakk> \<Longrightarrow> 
      \<Theta> ;  \<B> ; \<Gamma>  \<turnstile> V_pair v1 v2 \<Rightarrow> (\<lbrace> : B_pair b1  b2 |  C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_pair (lift_x v1 0 1) (lift_x v2 0 1))) \<rbrace>) "

| infer_v_consI: "\<lbrakk> 
      Some (AF_typedef s dclist) = lookup_td \<Theta> s;
      Some (dc, \<lbrace> : b  | c \<rbrace>) = lookup_dc dclist dc; 
      \<Theta> ;  \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> (\<lbrace>   : b | c' \<rbrace>) ; 
      \<Theta> ; \<B> ; \<Gamma> \<turnstile> \<lbrace>  : b | c' \<rbrace> \<lesssim> \<lbrace> : b | c \<rbrace> 
   \<rbrakk> \<Longrightarrow> 
      \<Theta> ;  \<B> ; \<Gamma>  \<turnstile> V_cons s dc v \<Rightarrow> (\<lbrace> : B_id s |  C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_cons s dc (lift_x v 0 1))) \<rbrace>)"

code_pred (modes: 
       infer_v: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool  ) [show_steps,  show_mode_inference,  show_invalid_clauses] infer_v .

values "{ t . infer_v [] {} GNil (V_pair (V_lit L_true) (V_lit L_unit)) t }"

inductive_cases infer_v_elims[elim!]:
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> V_var x \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> V_lit l \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> V_pair v1 v2 \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> V_cons s dc v \<Rightarrow> \<tau>"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> V_pair v1 v2 \<Rightarrow> (\<lbrace>  : b |  c  \<rbrace>) "
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile> V_pair v1 v2 \<Rightarrow> (\<lbrace>  : B_pair b1  b2 |  C_eq (CE_val (V_var zz)) (CE_val (V_pair v1 v1)) \<rbrace>) "

subsection \<open>Introductions\<close>

(*
lemma infer_vI:
  fixes v::v
  assumes  "[] ;  \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b" 
  shows "[] ;  \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace>  : b | C_eq (CE_val (V_var (XBVar 0))) (CE_val v) \<rbrace>"
using assms proof(induct v arbitrary: b )
  case (V_lit x)
  then show ?case using infer_l_form2 infer_v_litI  wbV_elims(2) by metis
next
  case (V_var x)
  thus ?case using  infer_v.intros wbV_elims(1) V_var by metis
next
  case (V_pair v1 v2)

  obtain b1 and b2 where b1b2: "b = B_pair b1 b2 \<and> [] ;  \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b1  \<and> [] ;  \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : b2" using wbV_elims(3) using V_pair by metis
  have z1:"[] ; \<B> ; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace> : b1  | CE_val (V_var zz)  ==  CE_val v1  \<rbrace> " using b1b2 V_pair by metis
  have z2:"[]; \<B> ; \<Gamma> \<turnstile> v2 \<Rightarrow> \<lbrace> : b2  | CE_val (V_var zz)  ==  CE_val v2  \<rbrace> " using b1b2 V_pair by metis
  then show ?case using infer_v_pairI[of  "Nil"  \<B>  \<Gamma> v1 b1 _ v2]
       V_pair  b1b2  z1 z2   by blast
next
  case (V_cons tyid dc v)
  thus ?case using wbV_elims by fastforce
qed

lemma infer_v2I:
  fixes v::v
  assumes  "[] ;  \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b"
  shows "[] ;  \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> : b | C_eq (CE_val (V_var zz)) (CE_val v) \<rbrace>"
proof -
  have "[] ;  \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace>  : b | C_eq (CE_val (V_var zz)) (CE_val v) \<rbrace>"
    using assms infer_vI by metis
  moreover hence "\<lbrace> : b | C_eq (CE_val (V_var zz)) (CE_val v) \<rbrace> = \<lbrace>  : b | C_eq (CE_val (V_var zz)) (CE_val v) \<rbrace>" using assms by simp
  ultimately show ?thesis by metis
qed
*)

inductive check_v :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> v \<Rightarrow> \<tau> \<Rightarrow> bool"  ("_ ; _ ; _  \<turnstile> _ \<Leftarrow> _" [50, 50, 50] 50) where
check_v_subtypeI:  "\<lbrakk>  \<Theta> ; \<B> ; \<Gamma> \<turnstile> \<tau>1 \<lesssim> \<tau>2; \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>1 \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ;  \<Gamma> \<turnstile>  v \<Leftarrow> \<tau>2"


code_pred (modes: 
       check_v: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool  ) [show_steps,  show_mode_inference,  show_invalid_clauses] check_v .

inductive_cases check_v_elims[elim!]:
  "\<Theta>; \<B> ; \<Gamma> \<turnstile> v \<Leftarrow> \<tau>"


subsection \<open>Expressions\<close>
definition zz where "zz \<equiv> XBVar 0"


text {* Type synthesis for expressions *}
inductive infer_e :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> e \<Rightarrow> \<tau> \<Rightarrow> bool"  ("_ ; _ ; _ ; _ ; _  \<turnstile> _ \<Rightarrow> _" [50, 50, 50,50] 50) where

infer_e_valI:  "\<lbrakk>
         (\<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>) ; 
         (\<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>)) ; 
         (\<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>) \<rbrakk> \<Longrightarrow> 
         \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_val v) \<Rightarrow> \<tau>"

| infer_e_plusI: "\<lbrakk> 
        \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace>  : B_int | c1 \<rbrace> ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile>  v2 \<Rightarrow> \<lbrace>  : B_int | c2 \<rbrace> \<rbrakk> \<Longrightarrow> 
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_op Plus v1 v2 \<Rightarrow> \<lbrace> : B_int | C_eq (CE_val (V_var zz)) (CE_op Plus v1 v2) \<rbrace>"

| infer_e_leqI: "\<lbrakk> 
        \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace>  : B_int | c1 \<rbrace> ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v2 \<Rightarrow> \<lbrace>  : B_int | c2 \<rbrace> \<rbrakk> \<Longrightarrow> 
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_op LEq v1 v2 \<Rightarrow>  \<lbrace>  : B_bool | C_eq (CE_val (V_var zz)) (CE_op LEq v1 v2) \<rbrace>"
(*
| infer_e_appI: "\<lbrakk> 
        \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ b c \<tau>' s'))) = lookup_fun \<Phi> f;        
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace>  : b | c \<rbrace>
\<rbrakk> \<Longrightarrow>
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_app f v \<Rightarrow> \<tau>[(XBVar 0)::=v]\<^sub>\<tau>\<^sub>v"
*)
(* FIXME 
| infer_e_appPI: "\<lbrakk> 
        \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f b' ; 
        Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ b c \<tau>' s'))) = lookup_fun \<Phi> f;              
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace>  : b[bv::=b']\<^sub>b\<^sub>b | c \<rbrace>; atom x \<sharp> \<Gamma>;
        (\<tau>'[bv::=b']\<^sub>\<tau>\<^sub>b[x::=v]\<^sub>\<tau>\<^sub>v) = \<tau> ;
        atom bv \<sharp> \<B>
        \<rbrakk> \<Longrightarrow>
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_appP f b' v \<Rightarrow> \<tau>"
*)
| infer_e_fstI:  "\<lbrakk> 
         \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> : B_pair b1 b2 | c \<rbrace> \<rbrakk> \<Longrightarrow> 
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_fst v \<Rightarrow> \<lbrace>  : b1 | (CE_val (V_var zz)) == ((CE_fst v)) \<rbrace>"

| infer_e_sndI: "\<lbrakk> 
        \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace>  : B_pair b1 b2 | c \<rbrace> \<rbrakk> \<Longrightarrow>  
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_snd v \<Rightarrow> \<lbrace>  : b2 | (CE_val (V_var zz)) == ((CE_snd v))  \<rbrace>"

| infer_e_lenI: "\<lbrakk> 
        \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace>  : B_bitvec | c \<rbrace>
\<rbrakk> \<Longrightarrow>  
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_len v \<Rightarrow> \<lbrace>  : B_int | (CE_val (V_var zz)) == ((CE_len v))  \<rbrace>"
(*
| infer_e_mvarI: "\<lbrakk>  
        \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; 
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>;
        Some \<tau> = lookup_d \<Delta> u \<rbrakk> \<Longrightarrow> 
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>  AE_mvar u \<Rightarrow> \<tau>"
*)
| infer_e_concatI: "\<lbrakk> 
        \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace>  : B_bitvec | c1 \<rbrace> ; 
        \<Theta> ; \<B> ; \<Gamma> \<turnstile>  v2 \<Rightarrow> \<lbrace>  : B_bitvec | c2 \<rbrace> \<rbrakk> \<Longrightarrow> 
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_concat  v1 v2 \<Rightarrow> \<lbrace> : B_bitvec | C_eq (CE_val (V_var zz)) (CE_concat v1 v2) \<rbrace>"



inductive_cases infer_e_elims[elim!]:
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op Plus v1 v2) \<Rightarrow> \<lbrace> : B_int | C_eq (CE_val (V_var zz)) (CE_op Plus v1 v2) \<rbrace>"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op LEq v1 v2) \<Rightarrow> \<lbrace>  : B_bool | C_eq (CE_val (V_var zz)) (CE_op LEq v1 v2) \<rbrace>"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op Plus v1 v2) \<Rightarrow> \<lbrace>  : B_int | c \<rbrace>" 
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op Plus v1 v2) \<Rightarrow> \<lbrace>  : b | c \<rbrace>" 
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op LEq v1 v2) \<Rightarrow> \<lbrace>  : b | c \<rbrace>" 
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_app f v ) \<Rightarrow> \<tau>"     
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_val v) \<Rightarrow> \<tau>"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_fst v) \<Rightarrow> \<tau>"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_snd v) \<Rightarrow> \<tau>"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_mvar u) \<Rightarrow> \<tau>"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op Plus v1 v2) \<Rightarrow> \<tau>" 
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op LEq v1 v2) \<Rightarrow> \<tau>" 
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op LEq v1 v2) \<Rightarrow> \<lbrace>  : B_bool | c \<rbrace>" 
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_app f v )  \<Rightarrow> \<tau>[x::=v]\<^sub>\<tau>\<^sub>v"  
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_op opp v1 v2) \<Rightarrow>  \<tau>" 
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_len v) \<Rightarrow> \<tau>"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_len v) \<Rightarrow> \<lbrace> : B_int | (CE_val (V_var zz)) == ((CE_len v))\<rbrace> "
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_concat v1 v2 \<Rightarrow> \<tau>"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_concat v1 v2 \<Rightarrow> (\<lbrace>  : b |  c  \<rbrace>) "
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AE_concat v1 v2 \<Rightarrow> (\<lbrace> : B_bitvec |  C_eq (CE_val (V_var zz)) (CE_concat v1 v1) \<rbrace>) "
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AE_appP f b v )  \<Rightarrow> \<tau>"

code_pred (modes: 
       infer_e: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool  ) [show_steps,  show_mode_inference,  show_invalid_clauses] infer_e .

values "{ t . infer_e [] [] {} GNil DNil (AE_fst (V_pair (V_lit L_true) (V_lit L_unit))) t }"


inductive check_e :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> e \<Rightarrow> \<tau> \<Rightarrow> bool"  (" _ ; _ ; _ ; _ ; _  \<turnstile> _ \<Leftarrow> _" [50, 50, 50] 50) where
check_e_subtypeI: "\<lbrakk> infer_e T P B G D e \<tau>' ; subtype T B G \<tau>' \<tau> \<rbrakk> \<Longrightarrow> check_e T P B G D e \<tau>"
(*equivariance check_e
inductive check_e  .*)

inductive_cases check_e_elims[elim!]:
  "check_e F D B G \<Theta> (AE_val v) \<tau>"
  "check_e F D B G \<Theta> e \<tau>"

subsection \<open>Statements\<close>



inductive check_s ::  "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> s \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _  \<turnstile> _ \<Leftarrow> _" [50, 50, 50,50,50] 50) and
           check_case_s ::  "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta>  \<Rightarrow> tyid \<Rightarrow> string \<Rightarrow> \<tau> \<Rightarrow> branch_s \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ;  _ ; _ ; _ ; _ ; _ ; _ ; _ \<turnstile> _ \<Leftarrow> _") and
     check_case_ss ::  "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta>  \<Rightarrow> tyid \<Rightarrow> (string * \<tau>) list \<Rightarrow> branch_list \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ;  _ ; _ ; _ ; _ ; _ ; _ \<turnstile> _ \<Leftarrow> _" [50, 50, 50,50,50] 50) where 

check_valI:  "\<lbrakk> 
       \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;   
       \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
       \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>'; 
       \<Theta> ; \<B> ; \<Gamma> \<turnstile> \<tau>' \<lesssim> \<tau> \<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AS_val v) \<Leftarrow> \<tau>"

| check_letI: "\<lbrakk>
     
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> e \<Rightarrow> \<lbrace>  : b | c \<rbrace> ; 
       \<Theta> ; \<Phi> ; \<B> ; (GCons (b,c) \<Gamma>) ; \<Delta> \<turnstile> (lift_x s 0 1) \<Leftarrow> \<tau> \<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AS_let e s) \<Leftarrow> \<tau>"

|check_case_s_finalI: "\<lbrakk> 
       \<Theta> ; \<Phi> ;  \<B> ;  \<Gamma> ; \<Delta> ; tid ; dc ; t  \<turnstile> cs \<Leftarrow> \<tau>  \<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta> ; tid ; [(dc,t)] \<turnstile> (AS_final cs) \<Leftarrow> \<tau>"

|check_case_s_consI: "\<lbrakk> 
       \<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta>; tid ; dc ; t  \<turnstile> cs \<Leftarrow> \<tau> ; 
       \<Theta> ; \<Phi> ;  \<B> ;  \<Gamma> ; \<Delta>; tid ; dclist \<turnstile> css \<Leftarrow> \<tau> 
\<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta> ; tid ; (dc,t)#dclist \<turnstile> AS_cons cs css \<Leftarrow> \<tau>"

| check_ifI: "\<lbrakk>      
       (\<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Leftarrow> (\<lbrace>  : B_bool | TRUE \<rbrace>)) ; 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> s1 \<Leftarrow> (\<lbrace> : b | C_imp (C_eq (CE_val v) (CE_val (V_lit L_true))) (c) \<rbrace>) ;
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> s2 \<Leftarrow> (\<lbrace>  : b | C_imp (C_eq (CE_val v) (CE_val (V_lit L_false))) (c) \<rbrace>) \<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AS_if v s1 s2) \<Leftarrow> \<lbrace>  : b | c \<rbrace>"

| check_let2I: "\<lbrakk>
     
       \<Theta> ; \<Phi> ; \<B> ; G; \<Delta> \<turnstile> s1 \<Leftarrow> (\<lbrace>  : b | c \<rbrace>) ; 
       \<Theta> ; \<Phi> ; \<B> ; ((b,c)#G) ; \<Delta> \<turnstile> (lift_x s2 0 1) \<Leftarrow> \<tau> \<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ; \<B> ; G ; \<Delta> \<turnstile> (AS_let2  (\<lbrace> : b | c \<rbrace>)  s1 s2) \<Leftarrow> \<tau>"

| check_varI: "\<lbrakk> 
   
       \<Theta> ; \<B> ; \<Gamma> \<turnstile>  v \<Leftarrow> \<tau>'; 
       \<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; ((\<tau>')#\<Delta>)  \<turnstile> (lift_u s 0 1) \<Leftarrow> \<tau> \<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AS_var \<tau>' v s) \<Leftarrow> \<tau>"
(*
| check_assignI: "\<lbrakk> 
       \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
       \<Theta> ; \<B> ;\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
       Some (u,\<tau>) = lookup_d \<Delta> u ; 
       \<Theta> ; \<B> ; \<Gamma> \<turnstile>  v \<Leftarrow> \<tau>;
       \<Theta> ; \<B> ; \<Gamma> \<turnstile> (\<lbrace> : B_unit | TRUE \<rbrace>) \<lesssim> \<tau>'  \<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>  (AS_assign u v) \<Leftarrow> \<tau>'" 
*)

| check_whileI: "\<lbrakk> 
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> s1 \<Leftarrow> \<lbrace>  : B_bool | TRUE \<rbrace>; 
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> s2 \<Leftarrow> \<lbrace>  : B_unit | TRUE \<rbrace>;
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> (\<lbrace>  : B_unit | TRUE \<rbrace>) \<lesssim> \<tau>' \<rbrakk> \<Longrightarrow>  
        \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AS_while s1 s2) \<Leftarrow> \<tau>'"

| check_seqI: "\<lbrakk> 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> s1 \<Leftarrow> \<lbrace> : B_unit | TRUE \<rbrace>; 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> s2 \<Leftarrow> \<tau> \<rbrakk> \<Longrightarrow> 
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> (AS_seq s1 s2) \<Leftarrow> \<tau>"

| check_caseI: "\<lbrakk> 
      \<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta>; tid ; dclist \<turnstile>  cs \<Leftarrow> \<tau> ;  
       Some (AF_typedef tid dclist ) = lookup_td \<Theta> tid ;                 
       \<Theta> ; \<B> ; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace>  : B_id tid | c \<rbrace>;
       \<turnstile>\<^sub>w\<^sub>f \<Theta>  \<rbrakk> \<Longrightarrow>
      \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_match v cs \<Leftarrow> \<tau>"



inductive_cases check_s_elims[elim!]:
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_val v \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_let  e s \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_if v s1 s2 \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_let2  t s1 s2 \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_while s1 s2 \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_var  t v s \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_seq s1 s2 \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_assign u v \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile> AS_match v cs \<Leftarrow> \<tau>"

inductive_cases check_case_s_elims[elim!]:
   "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta>; tid ; dclist \<turnstile> (AS_final cs) \<Leftarrow> \<tau>"
   "\<Theta> ; \<Phi> ;  \<B> ; \<Gamma> ; \<Delta>; tid ; dclist \<turnstile> (AS_cons cs css) \<Leftarrow> \<tau>"

code_pred (modes:        
  check_s: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
  check_case_s:  i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
  check_case_ss: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool 
 ) [show_steps,  show_mode_inference,  show_invalid_clauses] check_s .

values "{ t . check_s [] [] {} GNil DNil (AS_val (V_lit L_true)) \<lbrace> : B_bool | C_true \<rbrace> }"

subsection \<open>Programs\<close>

inductive check_fundef :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> fun_def \<Rightarrow> bool" where
 "\<lbrakk> x = mk_fresh_x GNil; 
   \<Theta> ; \<Phi> ;  {} ; ((b, c)#GNil) ; [] \<turnstile> (lift_x s 0 1) \<Leftarrow> (lift_x \<tau> x 0) \<rbrakk>
  \<Longrightarrow> check_fundef \<Theta> \<Phi> ((AF_fundef f (AF_fun_typ_none (AF_fun_typ b c \<tau> s))))" 


inductive_cases check_fundef_elims[elim!]:
  "check_fundef \<Theta> \<Phi> ((AF_fundef f (AF_fun_typ_none (AF_fun_typ  b c \<tau> s))))"
  "check_fundef \<Theta> \<Phi> fd"






end
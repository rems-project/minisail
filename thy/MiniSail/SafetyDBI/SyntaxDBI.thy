(*<*)
theory SyntaxDBI
  imports Main "HOL-Library.FSet"  
begin
(*>*)

sledgehammer_params[debug=true, timeout=600, provers= cvc4 spass e vampire z3,isar_proofs=true,smt_proofs=false]   

chapter \<open>Introduction\<close>

text \<open>Syntax and Semantics of MiniSail. This is a kernel language for Sail, an instruction set architecture specification language. 
The idea behind this language is to capture the key and novel features of Sail in terms of their syntax, typing rules and operational semantics
and to confirm that they work together by proving progress and preservation lemmas. We use locally nameless to handle binding.
\<close>

chapter \<open>Syntax\<close>

section \<open>Syntax\<close>

subsection \<open>Datatypes\<close>
type_synonym num_nat = nat

(*
atom_decl  xf
*)

(*
datatype xf = XFVar nat
datatype bvf = BFVar nat
datatype uf = UFVar nat
*)

datatype xb = XBVar nat

type_synonym x = "xb"    (* Immutable variables*)


datatype ub = UBVar nat
type_synonym u = "ub"  (* Mutable variables *)

datatype bvb = BVBVar nat
type_synonym  bv = "bvb"   (* Base-type variables *)
       
type_synonym f = string  (* Function name *)
type_synonym dc = string (* Data constructor *)
type_synonym tyid = string

(* Would things be easier we if include the base type of the constructor argument *)
text \<open> Base types \<close>
datatype "b" =  
   B_int  
 | B_bool  
 | B_id tyid 
 | B_pair b b
 | B_unit
 | B_bitvec
 | B_var bv
 | B_app tyid b

datatype bit = BitOne | BitZero

text  \<open> Literals \<close>
datatype "l" = 
   L_num "nat"
 | L_true
 | L_false
 | L_unit 
 | L_bitvec "bit list"

text  \<open> Values \<close>
datatype "v" = 
    V_lit "l"
  | V_var "x"
  | V_pair "v" "v"  
  | V_cons tyid dc "v" (* Including tyid makes typing and well-formedness checking easier - can be done locally. If required can be added during elaboration  *)
  | V_consp tyid dc b v

text \<open> Binary Operations \<close>
datatype "opp" = Plus | LEq 

text \<open> Expressions \<close>
datatype "e" = 
   AE_val "v"           ( "[ _ ]\<^sup>e"       )
 | AE_app "f" "v"       ( "[ _ ( _ ) ]\<^sup>e" )
 | AE_appP  "f" "b" "v" ( "[_ [ _ ] ( _ )]\<^sup>e" )
 | AE_op "opp" "v" "v"  ( "[ _ _ _ ]\<^sup>e"  )
 | AE_concat v v        ( "[ _ @@ _ ]\<^sup>e" )
 | AE_fst "v"           ( "[#1_ ]\<^sup>e"    )
 | AE_snd "v"           ( "[#2_ ]\<^sup>e"     )
 | AE_mvar "u"          ( "[ _ ]\<^sup>e"      )
 | AE_len "v"           ( "[| _ |]\<^sup>e"    )


text \<open> Expressions for Constraints\<close>
datatype "ce" = 
   CE_val "v"           ( "[ _ ]\<^sup>c\<^sup>e"      )
 | CE_op "opp" "v" "v"  ( "[ _ _ _ ]\<^sup>c\<^sup>e"  )
 | CE_concat v v        ( "[ _ @@ _ ]\<^sup>c\<^sup>e" )
 | CE_fst "v"           ( "[#1_]\<^sup>c\<^sup>e"      )
 | CE_snd "v"           ( "[#2_]\<^sup>c\<^sup>e"      )
 | CE_len "v"           ( "[| _ |]\<^sup>c\<^sup>e"    )
text  \<open> Constraints \<close>
datatype "c" = 
   C_true          ( "TRUE" [] 50 )
 | C_false         ( "FALSE" [] 50 )
 | C_conj "c" "c"  ("_  AND  _ " [50, 50] 50) 
 | C_disj "c" "c"  ("_ OR _ " [50,50] 50)
 | C_not "c"       ( "\<not> _ " [] 50 )
 | C_imp "c" "c"   ("_  IMP  _ " [50, 50] 50) 
 | C_eq "ce" "ce"    ("_  ==  _ " [50, 50] 50) 
   
text  \<open> Refined type \<close>
datatype "\<tau>" = 
   T_refined_type   b c     ("\<lbrace>  : _  | _ \<rbrace>" [50, 50] 1000)

text \<open> Statements \<close>

datatype s = 
  AS_val "v" 
| AS_let   "e" s 
| AS_let2  \<tau>  "s" s
| AS_if "v" "s" "s"  
| AS_var \<tau> v s
| AS_assign u  v
| AS_match "v" branch_list 
| AS_while s s
| AS_seq s s
and branch_s = 
  AS_branch  dc s
and branch_list = 
  AS_final branch_s
| AS_cons branch_s branch_list


text \<open> Function and union type definitions \<close>

datatype "fun_typ"  =
     AF_fun_typ "b" c \<tau> s

datatype "fun_typ_q" = 
     AF_fun_typ_some fun_typ
   | AF_fun_typ_none fun_typ

datatype "fun_def" = 
     AF_fundef f fun_typ_q 

datatype "type_def" = 
    AF_typedef string "(string * \<tau>) list"
    |  AF_typedef_poly string  "(string * \<tau>) list"  

text  \<open> Programs \<close> 
datatype "p" = 
  AP_prog "type_def list" "fun_def list" "s"
 


datatype \<Gamma> = 
  GNil
  | GCons "b*c" \<Gamma>  (infixr "#" 65)

lemma \<Gamma>_induct [case_names GNil GCons] : "P GNil \<Longrightarrow> (\<And>b c \<Gamma>'. P \<Gamma>' \<Longrightarrow> P ((b,c) # \<Gamma>')) \<Longrightarrow> P \<Gamma>"
proof(induct \<Gamma> rule:\<Gamma>.induct)
case GNil
  then show ?case by auto 
next
  case (GCons x1 x2)
  then obtain b and c where "x1=(b,c)"   using surjective_pairing by blast
  then show ?case using GCons by presburger
qed

datatype \<Delta> = 
  DNil  ("[]")
  | DCons "\<tau>" \<Delta>  (infixr "#" 65)


type_synonym \<B> = "bv set"

lemma \<Delta>_induct [case_names DNil DCons] : "P DNil \<Longrightarrow> (\<And>t \<Delta>'. P \<Delta>' \<Longrightarrow> P ((t) # \<Delta>')) \<Longrightarrow> P \<Delta>"
proof(induct \<Delta> rule: \<Delta>.induct)
case DNil
  then show ?case by auto 
next
  case (DCons x1 x2)
  then obtain t  where "x1=(t)"  by fastforce
  then show ?case using DCons by presburger
qed

section \<open>Extras\<close>

fun toList :: "\<Gamma> \<Rightarrow> (b*c) list" where
  "toList GNil = []"
| "toList (GCons xbc G) = xbc#(toList G)"


fun setG :: "\<Gamma> \<Rightarrow> (b*c) set" where
  "setG GNil = {}"
| "setG (GCons xbc G) = { xbc } \<union> (setG G)"

fun setD :: "\<Delta> \<Rightarrow> (\<tau>) set" where
  "setD DNil = {}"
| "setD (DCons xbc G) = { xbc } \<union> (setD G)"

fun append_g :: "\<Gamma> \<Rightarrow> \<Gamma> \<Rightarrow> \<Gamma>" (infixr "@" 65) where
  "append_g GNil g = g"
| "append_g (xbc#g1) g2 = (xbc#(g1@g2))"


lemma append_GNil[simp]:
  "GNil @ G = G"
using append_g.simps by auto

lemma append_g_setGU [simp]: "setG (G1@G2) = setG G1 \<union> setG G2"
  by(induct G1, auto+)
(*
lemma setG_split[simp]:
  "(x',b',c') \<in> setG (\<Gamma>' @ (x, b, c) # \<Gamma>) \<longleftrightarrow> (x',b',c') \<in> setG \<Gamma>' \<or> (x',b',c') = (x, b, c) \<or> (x',b',c') \<in> setG \<Gamma>"
  using append_g_setGU setG.simps by auto

lemma setG_splitU[simp]:
  "(x',b',c') \<in> setG (\<Gamma>' @ (x, b, c) # \<Gamma>) \<longleftrightarrow> (x',b',c') \<in> (setG \<Gamma>' \<union> { (x, b, c) } \<union> setG \<Gamma>)"
  using append_g_setGU setG.simps by auto

lemma setG_splitP[simp]:
 "(\<forall> (x', b', c') \<in> setG (\<Gamma>' @ (x, b, c) # \<Gamma>). P x' b' c') \<longleftrightarrow> (\<forall> (x', b', c') \<in> setG \<Gamma>'. P x' b' c') \<and> P x b c \<and> (\<forall> (x', b', c') \<in> setG \<Gamma>. P x' b' c')"  (is "?A \<longleftrightarrow> ?B")
  using setG_splitU by force

fun domG  ::  "\<Gamma> \<Rightarrow> xf set"  where
  "domG GNil = {}"
| "domG (GCons (x,b,c) G) = {x } \<union> (domG G)"

lemma domG[simp]:
  "domG G = (fst`setG G)"
proof(induct G rule:\<Gamma>_induct)
case GNil
then show ?case by auto
next
case (GCons x b c \<Gamma>')
  then show ?case using setG.simps by auto
qed
  
*)


end
theory MiniSailAST
imports Main "HOL-Library.FSet"
begin

section \<open>MiniSail AST\<close>

type_synonym num_nat = nat

datatype sort = Sort string "string list"

datatype x = Atom sort nat  (* Immutable variables*)
datatype u =  Atom sort nat (* Mutable variables *)
datatype bv  =  Atom sort nat(* Base-type variables *)
       
type_synonym f = string  (* Function name *)
type_synonym dc = string (* Data constructor *)
type_synonym tyid = string

(* Would things be easier we if include the base type of the constructor argument *)
text \<open> Base types \<close>
datatype "b" =  
   B_int  
 | B_bool  
 | B_id tyid 
 | B_pair b b  ("[ _ , _ ]\<^sup>b")
 | B_unit
 | B_bitvec
 | B_var bv
 | B_app tyid b  (* Base type application *)

datatype bit = BitOne | BitZero

text  \<open> Literals \<close>
datatype "l" = 
   L_num "int"
 | L_true
 | L_false
 | L_unit 
 | L_bitvec "bit list"

text  \<open> Values \<close>
datatype "v" = 
    V_lit "l"        ( "[ _ ]\<^sup>v")
  | V_var "x"        ( "[ _ ]\<^sup>v")
  | V_pair "v" "v"   ( "[ _ , _ ]\<^sup>v")
  | V_cons tyid dc "v" (* Including tyid makes typing and well-formedness checking easier - can be done locally. If required can be added during elaboration  *)
  | V_consp tyid dc b "v" (* Including tyid makes typing and well-formedness checking easier - can be done locally. If required can be added during elaboration  *)


text \<open> Binary Operations \<close>
datatype "opp" = Plus ( "plus") | LEq ("leq")

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
 | AE_split "v" "v"  


text \<open> Expressions for Constraints\<close>
datatype "ce" = 
   CE_val "v"           ( "[ _ ]\<^sup>c\<^sup>e"      )
 | CE_op "opp" "ce" "ce"  ( "[ _ _ _ ]\<^sup>c\<^sup>e"  )
 | CE_concat ce ce        ( "[ _ @@ _ ]\<^sup>c\<^sup>e" )
 | CE_fst "ce"           ( "[#1_]\<^sup>c\<^sup>e"      )
 | CE_snd "ce"           ( "[#2_]\<^sup>c\<^sup>e"      )
 | CE_len "ce"           ( "[| _ |]\<^sup>c\<^sup>e"    )

text  \<open> Constraints \<close>
datatype "c" = 
   C_true          ( "TRUE" [] 50 )
 | C_false         ( "FALSE" [] 50 )
 | C_conj "c" "c"  ("_  AND  _ " [50, 50] 50) 
 | C_disj "c" "c"  ("_ OR _ " [50,50] 50)
 | C_not "c"       ( "\<not> _ " [] 50 )
 | C_imp "c" "c"   ("_  IMP  _ " [50, 50] 50) 
 | C_eq "ce" "ce"  ("_  ==  _ " [50, 50] 50) 
   
text  \<open> Refined type \<close>
datatype "\<tau>" = 
   T_refined_type  x b c    ("\<lbrace> _ : _  | _ \<rbrace>" [50, 50] 1000)



text \<open> Statements \<close>

datatype 
 s = 
  AS_val v                             ( "[_]\<^sup>s")                  
| AS_let x  e s     ( "(LET _ = _ IN _)")
| AS_let2 x \<tau>  s s ( "(LET _ : _ = _ IN _)")
| AS_if v s s                          ( "(IF _ THEN _ ELSE _)" [0, 61, 0] 61)
| AS_var u \<tau> v s   ( "(VAR _ : _ = _ IN _)")
| AS_assign u  v                       ( "(_ ::= _)")
| AS_match v branch_list               ( "(MATCH _ WITH { _ })")
| AS_while s s                         ( "(WHILE _ DO { _ } )" [0, 0] 61)     
| AS_seq s s                           ( "( _ ;; _ )"  [1000, 61] 61)
| AS_assert c s                        ( "(ASSERT _ IN _ )" )
and branch_s = 
  AS_branch dc x  s  ( "( _ _ \<Rightarrow> _ )")   
and branch_list = 
  AS_final  branch_s                   ( "{ _ }" )
| AS_cons  branch_s branch_list        ( "( _ | _  )")

term "LET x = [plus [x]\<^sup>v [x]\<^sup>v]\<^sup>e IN [[x]\<^sup>v]\<^sup>s"

text \<open> Function and union type definitions \<close>

datatype "fun_typ"  =
     AF_fun_typ x "b" c \<tau> s

datatype "fun_typ_q" = 
     AF_fun_typ_some bv fun_typ 
   | AF_fun_typ_none fun_typ

datatype "fun_def" = 
     AF_fundef f fun_typ_q 

datatype "type_def" = 
    AF_typedef string "(string * \<tau>) list"
    |  AF_typedef_poly string bv "(string * \<tau>) list"  



datatype "var_def" = 
    AV_def u \<tau> v

text  \<open> Programs \<close> 
datatype "p" = 
  AP_prog "type_def list" "fun_def list" "var_def list" "s"

section\<open>Contexts\<close>

type_synonym \<Phi> = "fun_def list"
type_synonym \<Theta> = "type_def list"
type_synonym \<B> = "bv fset"

datatype \<Delta> = 
  DNil  ("[]\<^sub>\<Delta>")
  | DCons "u*\<tau>" \<Delta>  (infixr "#\<^sub>\<Delta>" 65)

datatype \<Gamma> = 
  GNil
  | GCons "x*b*c" \<Gamma>  (infixr "#\<^sub>\<Gamma>" 65)

fun append_g :: "\<Gamma> \<Rightarrow> \<Gamma> \<Rightarrow> \<Gamma>" (infixr "@" 65) where
  "append_g GNil g = g"
| "append_g (xbc #\<^sub>\<Gamma> g1) g2 = (xbc #\<^sub>\<Gamma> (g1@g2))"

end
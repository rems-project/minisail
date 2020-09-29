theory SailToMs
imports Utils SailEnv SailASTUtils ShowAST MiniSailAST   "HOL-Library.Debug" 
begin


chapter\<open>Convert from Sail to MiniSail\<close>


type_synonym xa=x
type_synonym ea=e
type_synonym va=v
type_synonym sa=s
type_synonym la=MiniSailAST.l
type_synonym ba=b
type_synonym ca=MiniSailAST.c


fun trace :: "char list \<Rightarrow> bool" where
  "trace s = (let _ = Debug.trace (String.implode s) in True)"

section \<open>Variables\<close>

fun string_to_int :: "string \<Rightarrow> int" where
"string_to_int s = (foldr (\<lambda>x y. y*256 + of_char x) (String.explode s)) 0"


fun string_to_nat :: "string \<Rightarrow> nat" where
"string_to_nat s = nat (string_to_int s)"
(*(foldr (\<lambda>x y. y*256 + of_char x) (String.explode s)) 0"*)

value "String.explode (STR ''xyz'')"

value "string_to_int (STR ''xyxxa'')"

(*
fun mk_atom_x :: "nat \<Rightarrow> atom" where
  "mk_atom_x n = (Atom (Sort ''MiniSailAST.x'' []) n)"

fun mk_atom_u :: "nat \<Rightarrow> atom" where
  "mk_atom_u n = (Atom (Sort ''MiniSailAST.u'' []) n)"

lift_definition mk_x :: "nat \<Rightarrow> x" is mk_atom_x using mk_atom_x.simps by auto

lift_definition mk_u :: "nat \<Rightarrow> u" is mk_atom_u using mk_atom_u.simps by auto
*)

fun mk_x :: "nat \<Rightarrow> x" where
  "mk_x n = x.Atom (Sort ''x'' []) n"

fun mk_u :: "nat \<Rightarrow> u" where
  "mk_u n = u.Atom (Sort ''u'' []) n"
 

(* Reserve even indexed atoms starting from 2 for fresh variables *)
fun mk_fresh_x :: "nat \<Rightarrow> nat * xa" where
"mk_fresh_x ii = (ii+1, mk_x ((ii+1)*2))"



fun index_for :: "('a*'b) list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "index_for [] _  = None"
| "index_for ((x,_)#xs) y = (if x = y then Some (length xs + 1) else index_for xs  y)"
 

(* Reserve odd indexed atoms start from 3 for program variables. These will be based on the index of the
variable in the Sail environment *)

fun mk_prog_x :: "env \<Rightarrow> id \<Rightarrow> x option" where
 "mk_prog_x env ( (id x) ) = Option.bind (index_for  (locals env)  ( (id x) )) (Some \<circ> (\<lambda>ii .  mk_x ((ii+1)*2+1)))"



abbreviation "mk_z \<equiv> mk_x 0"

abbreviation "mk_farg \<equiv> mk_x 1"

type_synonym exp  = "tannot exp"


section \<open>Literals and Values\<close>

(* FIXME - hex strings *)

inductive lit_conv :: "lit \<Rightarrow> la \<Rightarrow> bool"  ( "\<turnstile> _ \<leadsto> _") where
lit_conv_unitI:   "\<turnstile> ( SailAST.L_unit  ) \<leadsto> MiniSailAST.L_unit"
 | lit_conv_trueI:  "\<turnstile>  ( SailAST.L_true ) \<leadsto>  MiniSailAST.L_true"
 | lit_conv_falseI:  "\<turnstile> ( SailAST.L_false ) \<leadsto> MiniSailAST.L_false"
 | lit_conv_bvec_bit: "\<turnstile> (SailAST.L_bin bs) \<leadsto> (MiniSailAST.L_bitvec (List.map (\<lambda>b. if b = CHR ''1'' then BitOne else BitZero) (String.explode bs)))"
 | lit_conv_bvec_hex: "\<turnstile> (SailAST.L_hex bs) \<leadsto> (MiniSailAST.L_bitvec [])"
 | lit_conv_num:  "lit_conv (SailAST.L_num ii)  (MiniSailAST.L_num (int_of_integer ii))"

code_pred lit_conv .

values "{ x. lit_conv  (SailAST.L_bin (STR ''0101'')) x }"

inductive b_of_typ :: "typ \<Rightarrow> b \<Rightarrow> bool" where
"b_of_typ  unit_typ  B_unit"
| "b_of_typ ( (Typ_app ( (id STR ''atom_bool'') ) _)  )  B_bool" 
| "b_of_typ  ( (Typ_app ( (id STR ''atom'') ) _ ) ) B_int"
| "b_of_typ  ( (Typ_app ( (id STR ''bitvector'') ) _ ) ) B_bitvec"
| "\<lbrakk>  
   b_of_typ  t1 b1;
   b_of_typ  t2 b2
\<rbrakk> \<Longrightarrow> b_of_typ ( (Typ_tup [t1,t2]) ) (B_pair b1 b2)"
| "b_of_typ (Typ_id (id tyid)) (B_id (String.explode tyid))"

(* Use this to force an ordering on the trace calls. *)
definition cf :: "'a \<Rightarrow> char list"
  where "cf \<equiv> (\<lambda>_.  '''')"


type_synonym xmap = "(SailAST.id * xa ) list"

inductive v_conv :: "env \<Rightarrow> xmap \<Rightarrow> exp \<Rightarrow> \<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> va  \<Rightarrow> bool" ( "_ ; _ \<turnstile> _ \<leadsto> _ ; _ ; _ ") where
 v_conv_litI:  "\<lbrakk>
   trace ''v_conv_litI'';
   \<turnstile> l \<leadsto> la 
\<rbrakk> \<Longrightarrow> E ; _ \<turnstile> ( (SailAST.E_lit _ l) ) \<leadsto> [] ; GNil ; (MiniSailAST.V_lit la )"

| v_conv_varI:"\<lbrakk> 
   trace ''v_conv_varI'';
   Some xa = SailEnv.lookup xm idd;
   Some t = lookup_local_id_env env idd;
   b_of_typ t ba;
   trace (''v_conv_varI end'' @ (cf ba))
\<rbrakk> \<Longrightarrow> 
  env ; xm \<turnstile>   ( (SailAST.E_id _ idd)) \<leadsto> [] ; (xa,ba,C_true) #\<^sub>\<Gamma> GNil ; (V_var xa) "


| v_conv_enumI:"\<lbrakk> 
   trace ''v_conv_enumI'';
   Some (Typ_id (id enum_id))  = lookup_enum_env env (id enum)
\<rbrakk> \<Longrightarrow> 
  env ; _ \<turnstile>   ( (SailAST.E_id _ (id enum))) \<leadsto> [] ; GNil ; (V_cons (String.explode enum_id) (String.explode enum) (V_lit L_unit)) "

(* FIXME Better merging of m1 and m2 is needed *)
| v_conv_pairI: "\<lbrakk> 
   trace ''v_conv_pairI'';
   env ; m \<turnstile> vp1 \<leadsto> T1 ; G1; v1 ; 
   env ; m \<turnstile> vp2 \<leadsto> T2 ; G2; v2  
\<rbrakk> \<Longrightarrow> 
   env ; m \<turnstile> ( (SailAST.E_tuple _ [vp1, vp2])  ) \<leadsto> T1 @ T2 ; G1 @ G2 ; (MiniSailAST.V_pair v1 v2)" 


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] v_conv .

section \<open>Constraints\<close>

(* We need this mapping as we sometimes want to convert kid to a general constraint-expression when handling
   type level variables for functions *)
type_synonym type_vars =  "(kid * kind * ce) list"

fun lookup_kid :: "type_vars \<Rightarrow> kid \<Rightarrow> ce option" where
 "lookup_kid  [] _ = None"
| "lookup_kid ((( k1 ) , _ ,ce) # tvs) ( k2 ) = (if k1 = k2 then Some ce else lookup_kid tvs ( k2 ))"

fun mk_type_vars :: "(kid * kind ) list \<Rightarrow> ce \<Rightarrow> type_vars" where
"mk_type_vars [] _ = []"
| "mk_type_vars [(kid,kind)] ce = [(kid,kind,ce)]"
| "mk_type_vars ((kid,kind)#(k#kv)) ce = (kid,kind,CE_fst ce) # (mk_type_vars (k#kv) (CE_snd ce))"


value "mk_type_vars [ ( (var (STR ''k'')) , K_int ) ,( (var (STR ''n'')) , K_int ) ,  ( (var (STR ''m'')) , K_int ) ] 
       (CE_fst (CE_val (V_var (mk_x 1))))"

(* FIXME. This is the same as b_of_typ ? *)
inductive 
  b_conv :: "typ \<Rightarrow> b \<Rightarrow> bool"
  where
"b_conv ( (Typ_id ( (id (STR ''unit'')) ))  ) MiniSailAST.B_unit"


(* FIXME - Get Ott to generate this *)
fun fvs_x_typ :: "typ => id set" where
  "fvs_x_typ _  = {}"


fun fvs_x_gs :: "(id*mut*typ) list => id set" where
  "fvs_x_gs [] = {}"
| "fvs_x_gs ((x,_,typ)#gs) = {x} \<union> fvs_x_typ typ \<union> fvs_x_gs gs"


(* Making these mutually recursive I think helps prove MiniSail predicates that are mutually recursive *)
inductive 
  ce_conv :: "type_vars \<Rightarrow> nexp \<Rightarrow> \<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> ce \<Rightarrow> bool" ( " _ \<turnstile> _ \<leadsto> _ ; _ ; _") and
  c_conv :: "type_vars \<Rightarrow> n_constraint \<Rightarrow> \<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> c \<Rightarrow> bool"  ( " _ \<turnstile> _ \<leadsto> _ ; _ ; _") and
  t_conv_raw  :: "type_vars \<Rightarrow> typ \<Rightarrow> ce \<Rightarrow> \<Theta> \<Rightarrow> \<Gamma> \<Rightarrow>  ba \<Rightarrow> ca \<Rightarrow> bool" and 
  g_conv_aux :: "env \<Rightarrow> type_vars \<Rightarrow> (id*mut*typ) list  \<Rightarrow> \<Theta> \<Rightarrow> MiniSailAST.\<Gamma>  \<Rightarrow> bool" and
  c_bool_conv :: "type_vars \<Rightarrow> n_constraint \<Rightarrow> ce \<Rightarrow> \<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> c \<Rightarrow> bool"
  where

g_conv_nilI:"g_conv_aux _ _ [] [] GNil"
|g_conv_cons1I: "\<lbrakk>
   g_conv_aux env type_vars gs T1 G1 ;
   Some xa = mk_prog_x env x;
   x \<notin> fvs_x_gs gs;
   t_conv_raw type_vars typ (CE_val [xa]\<^sup>v) T2 G2  ba ca
\<rbrakk> \<Longrightarrow>
   g_conv_aux env type_vars  ((x,Immutable,typ) # gs) (T1@T2) (((xa, ba, ca) #\<^sub>\<Gamma> G2) @ G1) "

|g_conv_cons2I: "\<lbrakk>
   g_conv_aux env type_vars gs T1 G1 
\<rbrakk> \<Longrightarrow>
   g_conv_aux env type_vars  ((x,Mutable,typ) # gs) T1 G1 "

| ce_conv_sumI:
  "\<lbrakk> 
   ce_conv env ne1 T1 G1 ca1 ; ce_conv env ne2 T2 G2 ca2 
\<rbrakk> \<Longrightarrow> ce_conv env ( (Nexp_sum ne1 ne2)  ) (T1@T2) (G1@G2) (MiniSailAST.CE_op Plus ca1 ca2)"

| ce_conj_constI: " ce_conv env ( (Nexp_constant ii)  )  [] GNil (MiniSailAST.CE_val (V_lit (L_num (int_of_integer ii))))"

|ce_conj_kidI: (* FIXME. Add k to Gamma *)
"Some ce = lookup_kid env k \<Longrightarrow> ce_conv env ( (Nexp_var k) ) [] GNil ce"

(* Converting n_constraint *)
| "\<lbrakk> ce_conv G cep1 T1 G1 cea1 ; ce_conv G cep2 T2 G2 cea2 
\<rbrakk> \<Longrightarrow> c_conv G ( (NC_equal cep1 cep2) ) (T1@T2) (G1@G2) (MiniSailAST.C_eq cea1 cea2)"
| "\<lbrakk> ce_conv G cep1 T1 G1 cea1 ; ce_conv G cep2 T2 G2 cea2 
\<rbrakk> \<Longrightarrow> c_conv G ( (NC_bounded_ge cep1 cep2) ) (T1@T2) (G1@G2) (MiniSailAST.C_eq (CE_op LEq cea2 cea1) (CE_val (V_lit L_true)))"
| "\<lbrakk> ce_conv G cep1 T1 G1 cea1 ; ce_conv G cep2 T2 G2 cea2 
\<rbrakk> \<Longrightarrow> c_conv G ( (NC_bounded_le cep1 cep2) ) (T1@T2) (G1@G2) (MiniSailAST.C_eq (CE_op LEq cea1 cea2) (CE_val (V_lit L_true)))"

| "c_conv  G ( NC_true ) [] GNil MiniSailAST.C_true"
| "c_conv  G ( NC_false ) [] GNil MiniSailAST.C_false"

| "\<lbrakk> c_conv G cp1 T1 G1 ca1 ; c_conv G cp2 T2 G2 ca2 \<rbrakk> \<Longrightarrow> c_conv G ( (NC_and  cp1 cp2) ) (T1@T2) (G1@G2) (MiniSailAST.C_conj ca1 ca2)"
| "\<lbrakk> c_conv G cp1 T1 G1 ca1 ; c_conv G cp2 T2 G2 ca2 \<rbrakk> \<Longrightarrow> c_conv G ( (NC_or  cp1 cp2) ) (T1@T2) (G1@G2)  (MiniSailAST.C_disj ca1 ca2)"  

(* Converting bool args *)
| c_bool_conv_trueI: "c_bool_conv env NC_true ce [] GNil (ce  == [[MiniSailAST.L_true]\<^sup>v]\<^sup>c\<^sup>e )"
| "c_bool_conv env NC_false ce [] GNil (ce  == [[MiniSailAST.L_false]\<^sup>v]\<^sup>c\<^sup>e )"
| "Some ce' = lookup_kid env k \<Longrightarrow> c_bool_conv env ( NC_var k ) ce [] GNil    ( ce == ce' )"

| c_conv_raw_not: "\<lbrakk> 
   Some ce' = lookup_kid env k
\<rbrakk> \<Longrightarrow>   c_bool_conv  env ( NC_app (id (STR ''not'')) [ A_bool (NC_var k) ] )  ce [] GNil (C_not ( ce == ce') )"

| c_conv_raw_andI: "\<lbrakk> 
  Some ce1 = lookup_kid env k1;
  Some ce2 = lookup_kid env k2
\<rbrakk>  \<Longrightarrow> c_bool_conv env  (NC_and (NC_var  k1) (NC_var  k2) ) ce  [] GNil   (C_conj ( ce == ce1) (ce == ce2 ))"

| c_conv_raw_eqI: "\<lbrakk> 
  Some ce1 = lookup_kid env k1;
  Some ce2 = lookup_kid env k2
\<rbrakk>  \<Longrightarrow> c_bool_conv env  (NC_equal (Nexp_var  k1) (Nexp_var  k2) ) ce  [] GNil 
        (C_disj (C_conj (ce == [[MiniSailAST.L_true]\<^sup>v]\<^sup>c\<^sup>e) (C_eq ce1 ce2))
                (C_conj (ce == [[MiniSailAST.L_false]\<^sup>v]\<^sup>c\<^sup>e) (C_not (C_eq ce1 ce2))))"

| c_conv_raw_gtI: "\<lbrakk> 
  Some ce1 = lookup_kid env k1;
  Some ce2 = lookup_kid env k2
\<rbrakk>  \<Longrightarrow> c_bool_conv env  (NC_bounded_gt (Nexp_var  k1) (Nexp_var  k2) ) ce  [] GNil   (C_not (ce == (CE_op LEq ce1 ce2 )))"

| c_conv_raw_ltI: "\<lbrakk> 
  Some ce1 = lookup_kid env k1;
  Some ce2 = lookup_kid env k2
\<rbrakk>  \<Longrightarrow> c_bool_conv env  (NC_bounded_lt (Nexp_var  k1) (Nexp_var  k2) ) ce  [] GNil   (ce == (CE_op LEq ce2 ce1 ))"

(* Converting typ *)
|  t_conv_raw_unitI: "t_conv_raw env unit_typ     ce [] GNil  B_unit   ( ce  == [[MiniSailAST.L_unit]\<^sup>v]\<^sup>c\<^sup>e )"
|  t_conv_raw_intI: "t_conv_raw env int_typ       ce [] GNil  B_int   ( C_true )"
|  t_conv_raw_boolI: "t_conv_raw env bool_all_typ  ce [] GNil  B_bool   ( C_true )"

| t_conv_atom_boolI: "c_bool_conv env nc ce T G ca \<Longrightarrow> 
      t_conv_raw env (Typ_app (id ( STR ''atom_bool'')) [ A_bool nc ]) ce T G B_bool ca"

| t_conv_raw_atomI: "ce_conv env nexp T G ce2 \<Longrightarrow> t_conv_raw env ( (Typ_app ( (id STR ''atom'') )
             [ (A_nexp nexp) ]) ) ce T G  B_int  ( ce  == ce2)"

| t_conv_raw_bitvectorI: "ce_conv env nexp T G ce2 \<Longrightarrow> t_conv_raw env (Typ_app (id STR ''bitvector'')
             [ A_nexp nexp , _ ]  ) ce T G  B_bitvec  ( CE_len ce  == ce2)"

| t_conv_raw_rangeI: "\<lbrakk>
  ce_conv env nexp1 T1 G1 ce1;
  ce_conv env nexp2 T2 G2 ce2
\<rbrakk> \<Longrightarrow> t_conv_raw env ( (Typ_app ( (id STR ''range'') )
             [ (A_nexp nexp1)  ,  (A_nexp nexp2)  ]) ) ce (T1@T2) (G1@G2)  B_bool  
           (( C_eq (CE_op LEq ce1 ce) (CE_val (V_lit L_true))) AND  (C_eq (CE_val (V_lit L_true)) (CE_op LEq ce ce2)))"

| t_conv_raw_tuple_singleI:  "\<lbrakk>
   t_conv_raw env t1 ce T G  ba1 ca1
\<rbrakk> \<Longrightarrow> t_conv_raw env ( (Typ_tup [t1]) ) ce T G  ba1 ca1" (* FIXME. Need to handle c_of ta1 *)

| t_conv_raw_tuple_pairI: "\<lbrakk>
   t_conv_raw env t1 (CE_fst ce) T1 G1  ba1 ca1;
   t_conv_raw env (Typ_tup (t2#ts)) (CE_snd ce) T2 G2  ba2 ca2
\<rbrakk> \<Longrightarrow> t_conv_raw env  (Typ_tup (t1#t2#ts) ) ce (T1@T2) (G1@G2)  (B_pair ba1 ba2) C_true" (* FIXME. Need to handle c_of ta1 *)

| "t_conv_raw env (Typ_id (id tyid)) ce [] GNil (B_id (String.explode tyid)) C_true"

(* FIXME - Taking a guess that we only implicit nexps or types *)

| t_conv_raw_tuple_implicit_nexpI:  "\<lbrakk>
   trace (''t_conv_raw_tuple_implicit_nexpI'' @ (show tfn));
   tfn =  (SailAST.id STR ''implicit'');
   t_conv_raw env (Typ_app (SailAST.id STR ''atom'') [A_nexp ne])  ce T G  ba1 ca1
\<rbrakk> \<Longrightarrow> t_conv_raw env ( (Typ_app tfn [A_nexp ne]) ) ce T G  ba1 ca1" 

(*
| t_conv_raw_tuple_implicit_typeI:  "\<lbrakk>
   t_conv_raw env t  ce T G  ba1 ca1
\<rbrakk> \<Longrightarrow> t_conv_raw env ( (Typ_app (id STR ''implicit'') [A_typ t]) ) ce T G  ba1 ca1" 
*)

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] ce_conv .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] c_conv .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] c_bool_conv .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] t_conv_raw .
code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] g_conv_aux .


section \<open>Types\<close>

value "mk_x 0"

values "{ (ba,ca,T,G). t_conv_raw [] (Typ_tup []) (CE_val (V_var (mk_x 0))) T G ba ca }"
values "{ (ba,ca,T,G). t_conv_raw [] (Typ_tup [unit_typ]) (CE_val (V_var (mk_x 0))) T G ba ca }"
values "{ (ba,ca,T,G). t_conv_raw [] (Typ_tup [unit_typ,unit_typ]) (CE_val (V_var (mk_x 0))) T G ba ca }"
values "{ (ba,ca,T,G). t_conv_raw [] (Typ_tup [unit_typ,unit_typ,unit_typ]) (CE_val (V_var (mk_x 0))) T G ba ca }"

values "{ (ba,ca,T,G). t_conv_raw [] (Typ_app (id STR ''implicit'') [ A_nexp (Nexp_constant 1) ]) (CE_val (V_var (mk_x 0))) T G ba ca }"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] t_conv_raw .

inductive 
  t_conv  :: "type_vars \<Rightarrow> typ \<Rightarrow> \<tau> \<Rightarrow> bool" ( " _ \<turnstile> _ \<leadsto> _") where
"t_conv_raw env t (CE_val (V_var mk_z)) G T  ba ca \<Longrightarrow> t_conv env t (MiniSailAST.T_refined_type (mk_z) ba ca)"

| "\<lbrakk> 
    t_conv_raw ((var k, K_int, (CE_val (V_var mk_z)))#env) typ (CE_val (V_var mk_z)) G T  ba ca;
    c_conv  ((var k, K_int, (CE_val (V_var mk_z)))#env) nc T' G' ca'
\<rbrakk> \<Longrightarrow> t_conv env (Typ_exist [KOpt_kind K_int (var k)] nc typ )  (MiniSailAST.T_refined_type (mk_z) ba (C_conj ca' ca))"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] t_conv .

section \<open>Environment to Context\<close>


inductive g_conv :: "env \<Rightarrow> type_vars \<Rightarrow> MiniSailAST.\<Gamma> \<Rightarrow> bool" where
"\<lbrakk>  
   g_conv_aux env type_vars (locals env) T \<Gamma>
\<rbrakk>  \<Longrightarrow> g_conv env type_vars \<Gamma>"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] g_conv.

inductive et_conv :: "type_vars \<Rightarrow> exp \<Rightarrow> \<tau> \<Rightarrow> \<Gamma> \<Rightarrow> bool" where
"\<lbrakk> Some t = get_type tan; Some env = get_env tan ;
   g_conv env type_vars \<Gamma>;
   t_conv type_vars t ta; 
   tan = annot_e exp
\<rbrakk> \<Longrightarrow> 
et_conv type_vars exp  ta \<Gamma>"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] et_conv .


inductive d_conv :: "type_vars \<Rightarrow> (id*mut*typ) list \<Rightarrow> \<Delta> \<Rightarrow> bool" where

d_conv_nilI:"d_conv _ [] DNil"

| d_conv_mutI: "\<lbrakk>
   t_conv type_vars typ t;
   u = mk_u 0;
   d_conv type_vars locs D
\<rbrakk> \<Longrightarrow> d_conv type_vars ((x,Mutable,typ)#locs) ((u,t)#\<^sub>\<Delta>D)"

| d_conv_immutI: "\<lbrakk>
   d_conv type_vars locs D
\<rbrakk> \<Longrightarrow> d_conv type_vars ((x,Immutable,typ)#locs) D"


inductive env_conv :: "env \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta>  \<Rightarrow> bool" where
"\<lbrakk>
   g_conv env [] G;
   d_conv [] (locals env) D
\<rbrakk> \<Longrightarrow> env_conv env G D"


section \<open>Let context\<close>

datatype  lctx = 
    L_hole  ("\<box>" 1000)  
 |  L_continue   (* Continue with other branches *)
 |  L_val va
 |  L_let xa ea lctx 
 |  L_if1 va lctx sa
 |  L_if2 va sa lctx
 |  L_if3 va lctx lctx
 |  L_final1 dc xa lctx
 |  L_final2 dc xa sa
 |  L_match va dc xa lctx   (* One branch is an lctx, the others are not *)
 |  L_compose lctx lctx  ("_ \<circ> _ " 1000)  

fun lctx_apply :: "lctx \<Rightarrow> sa \<Rightarrow> sa" ( "_ [ _ ]\<^sub>L " ) where

  "\<box> [ s ]\<^sub>L = s"
| "L_continue [ s ]\<^sub>L = s"
| "(L_val va) [ _ ]\<^sub>L = (AS_val va)"
| "(L_let xa ea L) [ s ]\<^sub>L = (AS_let xa ea (  L [ s ]\<^sub>L  ))"
| "(L_if1 va L sa ) [ s ]\<^sub>L = (AS_if va (  L [ s ]\<^sub>L ) sa)"
| "(L_if2 va sa L) [ s ]\<^sub>L = (AS_if va sa (  L [ s ]\<^sub>L  ))"
| "(L_if3 va L1 L2) [ s ]\<^sub>L = (AS_if va (L1 [ s ]\<^sub>L) (L2 [ s ]\<^sub>L))"
| "(L_match va dc xa L) [ s ]\<^sub>L = AS_match va (AS_cons (AS_branch dc xa (L [ s ]\<^sub>L)) (AS_final (AS_branch dc xa (AS_val (V_lit L_unit)))))"
| "(L1 \<circ> L2 )[ s ]\<^sub>L = L1 [ L2 [ s ]\<^sub>L ]\<^sub>L"


fun apply_hole_continue :: "lctx \<Rightarrow> sa \<Rightarrow> sa \<Rightarrow> sa"  ( "_ [ _ , _ ] " ) where 
  "\<box> [ s1 , s2 ] = s1"
| "L_continue [ s1 , s2 ] = s2"
| "(L_val va) [ s1 , s2 ] = AS_val va"
| "(L_let xa ea L) [ s1 , s2 ] = (AS_let xa ea (  L [ s1 , s2 ]  ))"
| "(L_if1 va L sa ) [ s1 , s2 ] = (AS_if va (  L [ s1 , s2 ] ) sa)"
| "(L_if2 va sa L) [ s1 , s2 ] = (AS_if va sa (  L [ s1 , s2 ]  ))"
| "(L_if3 va L1 L2) [ s1 , s2 ] = (AS_if va (L1 [ s1 , s2 ]) (L2 [ s1 , s2 ]))"
| "(L1 \<circ> L2 )[ s1 , s2 ] = L1 [ L2 [ s1 , s2 ] ]\<^sub>L"



section \<open>Patterns\<close>

(* Pattern matrix

         (pat,xp) ... (pat,xp)   ep
            :            :       :
         (pat,xp) ... (pat,xp)   ep

Associated to this is a list of types, one type for each column.

We start with a single column and a single type.
    
conv_pattern_matrix works on a matrix as above.
We switch on the type at the head of the type list.


ep are the arms
xp represents the subject of the pattern match - the thing we are matchning against

The xp are for the variable representing the pattern 
*)

type_synonym local_vars = "(id * xa) list"

type_synonym \<Sigma> = "type_vars*local_vars"


type_synonym pat_list = "(tannot pat)  list"
type_synonym pm_row = "pat_list  * sa"
type_synonym pm = "pm_row list"


fun mapi :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "mapi f xs = List.map (\<lambda>(i,x). f i x) (zip [0..<(List.length xs)] xs)"

fun zipi :: "'a list \<Rightarrow> (nat * 'a) list" where
  "zipi xs = mapi (\<lambda>i x. (i,x)) xs"
(* 
   Split first entry of each row into a tuple pattern. 
   Function is full as patterns will have type checked and be compatible with a tuple.
   In the case of wild and id, the row terminates at the branch and all patterns after it are removed.
*) 

subsection \<open>Expand Literals\<close>

fun fresh_vars_list :: "nat \<Rightarrow> nat \<Rightarrow> (nat * (xa list))" where
"fresh_vars_list i 0 = (i,[])"
| "fresh_vars_list i k = (let (i2,xalist) = fresh_vars_list (i+1) (k-1) in
                                 (i2, (mk_x i ) # xalist))"

   
fun add_to_pmlit_aux :: "(pm* (la option)) list \<Rightarrow> la option \<Rightarrow> pm_row \<Rightarrow> (pm* (la option)) list" where
  "add_to_pmlit_aux [] la pm_row = [ ([pm_row] , la) ]"
| "add_to_pmlit_aux (( pm, la' ) # pmlit) la pm_row = (if la' = la then 
                                                       (pm_row#pm,la) # pmlit 
                                                   else
                                                        (pm, la') # (add_to_pmlit_aux pmlit la pm_row))"

fun add_to_pmlit :: "(pm* (la option)) list \<Rightarrow> la option \<Rightarrow> pm_row \<Rightarrow> (pm* (la option)) list" where
  "add_to_pmlit pmlit la pm_row = (if List.member (List.map snd pmlit) la then  add_to_pmlit_aux pmlit la pm_row else
                                   (( [pm_row],la) # pmlit))"
 
fun is_literal_base :: "typ \<Rightarrow> bool" where
  "is_literal_base ( (Typ_id ( (id tyid) )) ) = (tyid \<in> {STR ''bool'', STR ''int'' , STR ''unit''})"
| "is_literal_base ( (Typ_app ( (id tyid) ) _ ) ) = (tyid \<in> {STR ''bool'', STR ''int'', STR ''atom_bool'', STR ''atom'', STR ''vector'', STR ''bitvector'' })"
| "is_literal_base _ = False"          

fun split :: "((la option) * sa) list \<Rightarrow> ( (la*sa) list) * (sa option)" where
  "split [] = ([], None)"
| "split ( x # xs ) = (let (litsa, sa ) = split xs in
                       case fst x of
                                       Some la \<Rightarrow> ( (la,snd x) # litsa , sa )
                                     | None \<Rightarrow>  (litsa , Some (snd x)))"   

inductive get_len :: "typ \<Rightarrow> v \<Rightarrow> bool" where
  "get_len (Typ_app (id STR ''bitvector'') [ A_nexp (Nexp_constant i), _ ]) (V_lit (L_num (int_of_integer i)))"

code_pred (modes : i \<Rightarrow> o \<Rightarrow> bool) get_len .

(* Args:
       pm - Pattern matrix we are processing the first column of
       xa - Variable representing value of first column
       (pm * ( (ltx * xa) option) ) list - list of child pattern matrices index by a let-context + variable
                                           the xa is the variable that will be bool and is true if the guard applies
      (id*xa) list - ??
*)

(* Expand concatenation of vector patterns into a let-context that invokes split function

   xa1 is variable for incoming bitvector, xa2 is the result so far of any boolean tests for
   literals, xa3 is result of boolean tests outgoing
   expand_vector_concat 0 xa1 xa2 [ pat_lit lit1 , pat_id x , pat_lit lit2 ] xa3

   L_let xa4 = (split xa1 len1) in
   L_let xa5 = fst xa4 in let xa6 = snd xa4 in
   L_let xa5 = xa2 \<and> xa4 = lit1 in 
   L_let xa7 = split xa6 len2 in
   L_let xa8 = fst xa7 in let xa9 in snd xa7 in
   L_let x = xa8 in 
   L_let xa10 = split xa9 len3 in 
   L_let xa11 = fst xa10 in xa12 = snd xa10 in
   L_Let xa12 = xa5 \<and> xa11 = lit2 in ...
*)

fun get_len_lit :: "lit \<Rightarrow> v" where
  "get_len_lit (L_hex bs) =  V_lit (L_num (int (length (String.explode bs))*4))"
|  "get_len_lit (L_bin bs) =  V_lit (L_num (int (length (String.explode bs))))"

inductive expand_vector_concat :: "nat \<Rightarrow> xa \<Rightarrow> xa \<Rightarrow> (tannot pat) list \<Rightarrow> lctx \<Rightarrow> xa \<Rightarrow> nat \<Rightarrow> bool" where


expand_vc_empty:
  "\<lbrakk>
  trace ''expand_vc_empty''
\<rbrakk> \<Longrightarrow> expand_vector_concat i1 _  xb [] L_hole xb i1"

| expand_vc_litI: "\<lbrakk>
     trace ''expand_vc_lit'';
     (i2,xb1) = mk_fresh_x i1;
     (i3,xa') = mk_fresh_x i2;
     (i4,xa1) = mk_fresh_x i3;
     (i5,xa2) = mk_fresh_x i4;
     lit_conv lit la;
     len = get_len_lit lit;
     L1 = L_let xa' (AE_split (V_var xa) len ) (
          L_let xa1 (AE_fst (V_var xa')) (L_let xa2 (AE_snd (V_var xa')) L_hole));
     L2 = L_let xb1  (AE_app ''eqand'' (V_pair (V_var xb) (V_pair (V_var xa1) (V_lit la)))) L_hole;
     trace (''expand_vc_litI i5='' @ (show i5));
     expand_vector_concat i5 xa2 xb1 ps L3 xb2 i6;
     trace (''expand_vc_litI i6='' @ (show i6))
\<rbrakk> \<Longrightarrow> expand_vector_concat i1 xa xb ((P_lit _ lit) # ps) (L_compose (L_compose L1 L2) L3) xb2 i6"


| expand_vc_varI: "\<lbrakk>   
     trace (''expand_vc_varI typ='' @ (show typ));
     (i2,xb1) = mk_fresh_x i1;
     (i3,xa') = mk_fresh_x i2;
     (i4,xa1) = mk_fresh_x i3;
     (i5,xa2) = mk_fresh_x i4;
     (i6,xa_id) = mk_fresh_x i5;   
     get_len typ len;
     L1 = L_let xa' (AE_split (V_var xa) len ) (
          L_let xa1 (AE_fst (V_var xa')) (L_let xa2 (AE_snd (V_var xa')) L_hole));
     L2 = L_let xa_id  (AE_val (V_var xa1)) L_hole;
     expand_vector_concat i6 xa2 xb ps L3 xb2 i7;
     trace (''expand_vc_varI i7='' @ (show i7))
\<rbrakk> \<Longrightarrow> expand_vector_concat i1 xa xb ((P_typ _ typ (P_id _  idd)) # ps) (L_compose (L_compose L1 L2) L3) xb2 i7"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] 
      expand_vector_concat .


values "{ (x,y,z) . expand_vector_concat 2 (mk_x 0) (mk_x 1) [ pat_lit_bv (STR ''0011'') ] x y z }"



(* Take first column of matrix and creates a list of literal annotated child matricies + some housekeeping bits
   The annotation is a let-context and variable that guards the matrix. The variable is a boolean that is the result of the guard  *)
inductive expand_lit :: "nat \<Rightarrow> env \<Rightarrow> xmap \<Rightarrow> pm \<Rightarrow> xa \<Rightarrow> (pm * (lctx*xa) option) list \<Rightarrow> (id*xa) list \<Rightarrow> nat \<Rightarrow> bool" where
expand_lit_litI: "\<lbrakk> 
  trace ''expand_lit_litI'';
  expand_lit i1 env xmap pm xp pmlit ms i2;
  trace (''expand_lit_litI i2 = '' @ (show i2));
  lit_conv lit la;
  (i3,xb) = mk_fresh_x i2;
  L = L_let xb (AE_app (''eq'') (V_pair (V_var xp) (V_lit la))) L_hole ;
  trace (''expand_lit_litI i3 = '' @ (show i3))
\<rbrakk> \<Longrightarrow> 
  expand_lit i1 env xmap (  (  ( ( (P_lit _ lit) )) # pm_pat , sa ) # pm) xp (( [(pm_pat,sa)] , Some (L,xb)) # pmlit) ms i3"

| expand_lit_wildI: "\<lbrakk>
  trace ''expand_lit_wildI''
\<rbrakk> \<Longrightarrow>  expand_lit i1 env xmap (  (  ( ( P_wild _) ) # pm_pat , sa ) # pm) xp [ ([(pm_pat,sa)], None)] [] i1"

(*   (i2,xa) = mk_fresh_x i1   *)
| expand_lit_varI: "\<lbrakk> 
  trace ''expand_lit_varI'' ;
  Some xa = SailEnv.lookup xmap idd 
\<rbrakk> \<Longrightarrow>
  expand_lit i1 env xmap (  (  (( (P_id _ idd) ) ) # pm_pat , sa ) # pm) xp [ ( [(pm_pat, AS_let xa (AE_val (V_var xp)) sa)],None)] [(idd,xa)] i1"

| expand_lit_typI: "\<lbrakk>
   trace ''expand_lit_typI'';
   expand_lit i1 env xmap ((pat # pm_pat , sa ) #pm) xp pm' ids i2
\<rbrakk> \<Longrightarrow> 
   expand_lit i1 env xmap ((((P_typ _ _ pat) # pm_pat) , sa ) #pm ) xp pm' ids i2"

(* FIXME Replace mk_x 0 with something sensible *)
| expand_lit_emptyI: "\<lbrakk>
  trace ''expand_lit_emptyI''
\<rbrakk> \<Longrightarrow> expand_lit i1 env xmap [] xp [] [] i1"

(* FIXME - This is missing the use of the types to do the split *)
| expand_lit_concatI: "\<lbrakk>
   trace ''expand_lit_concatI'';
   (i2,xb) = mk_fresh_x i1;
   trace (''expand_lit_concatI i2='' @ (show i2));
   expand_vector_concat i2 xp xb pats L xb2 i3;
   trace (''expand_lit_concatI i3='' @ (show i3));
   expand_lit i3 env xmap pm xp pmlist ms i4;
   trace (''expand_lit_concatI i3='' @ (show i4))
\<rbrakk>  \<Longrightarrow> expand_lit i1 env xmap (  (  ( ( (P_vector_concat _ pats) )) # pm_pat , sa ) # pm) xp (( [ (pm_pat,sa) ] , Some (L,xb2)) # pmlist) ms i4"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] expand_lit .
(*,
            ( [ ( Pat_exp unk (pat_lit_bv  (STR ''0100'')), mk_x 0) ], AS_val (V_lit L_false))*)

definition pm1 :: pm where
   "pm1 = [ ( [ ( (pat_lit_bv  (STR ''0101''))) ], AS_val (V_lit L_true)),
            ( [ ( (pat_lit_bv  (STR ''0100''))) ], AS_val (V_lit L_false)) ]"

values "{ (x2,x3,x4). expand_lit 0 emptyEnv [] pm1 (mk_x 0) x2 x3 x4 }" 

subsection \<open>Expand Constructor\<close>

(* 
 Args 
   List of pattern matrices indexed by (dc,xa)
   (dc,xa)
   pattern matrix row
 Result:
   New list with new pm added
*)
fun add_to_pmctor :: "(pm* ((dc*xa) option)) list \<Rightarrow> (dc*xa) option \<Rightarrow> pm_row \<Rightarrow> (pm* ((dc*xa) option)) list" where
  "add_to_pmctor [] la pm_row = [ ([pm_row] , la) ]"
| "add_to_pmctor (( pm, la' ) # pmlit) la pm_row = (if la' = la then 
                                                       (pm_row#pm,la) # pmlit 
                                                   else
                                                        (pm, la') # (add_to_pmctor pmlit la pm_row))"

(* Take first column of matrix and creates a list of construct/variable annotated child matricies + some housekeeping bits *)
inductive expand_ctor :: "nat \<Rightarrow> env \<Rightarrow> pm \<Rightarrow> id \<Rightarrow> xa \<Rightarrow> (pm * ((dc * xa) option)) list \<Rightarrow>  (id*xa) list \<Rightarrow> nat \<Rightarrow> bool" where


(* FIXME - arg to ctor could be wild as well or anything else *)
expand_ctorI:
"\<lbrakk>  trace ''expand_ctorI'';
   expand_ctor n1 env pm tyid xa pmctor ms n2;
   trace (''expand_ctorI i2='' @ (show n2));
   ( (id dc)) = ctor
 \<rbrakk> \<Longrightarrow>
expand_ctor  n1  env ((( (P_app _ ctor pats) )#pm_pat, sa ) # pm) tyid xa 
                       (add_to_pmctor pmctor (Some (String.explode dc,mk_x 0)) (pats @ pm_pat,sa)) ms n2"

| expand_ctor_wildI:
"expand_ctor n1 env ((( P_wild _)#pm_pat, sa ) # pm) tyid xa [ ([(pm_pat,sa)],None) ] [] n1"

(* FIXME - This could also be the constructor for an enumerator - so need the environment *)
| expand_ctor_varI:
"\<lbrakk> 
   trace ''expand_ctor_varI'';
   None = lookup_enum_env env idd
 \<rbrakk> \<Longrightarrow> expand_ctor n1 env ((( (P_id _ idd))#pm_pat, sa ) # pm) tyid xa [ ([(pm_pat,sa)],None) ] [] n1"

| expand_ctor_enumI:
"\<lbrakk>
    Some _ = lookup_enum_env env (id dc);
    trace ''expand_ctor_enumI'';
   expand_ctor n1 env pm tyid xa pmctor ms n2;
   trace (''expand_enumI i2='' @ (show n2))
 
\<rbrakk> \<Longrightarrow> expand_ctor n1 env ((( (P_id _ (id dc)))#pm_pat, sa ) # pm) tyid xa (add_to_pmctor pmctor (Some (String.explode dc,mk_x 0)) 
                       ( (P_lit unk SailAST.L_unit)# pm_pat,sa)) ms n2"

| expand_ctor_emptyI:
 "expand_ctor n1 env [] tyid xa [] [] n1"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] expand_ctor .

subsection \<open>Expand Tuple\<close>

(* FIXME - The xa list is not needed *)
inductive expand_tuple :: "nat \<Rightarrow> pm \<Rightarrow> nat \<Rightarrow> xa \<Rightarrow> pm \<Rightarrow> xa list \<Rightarrow> nat \<Rightarrow> bool" where

expand_tuple_emptyI: 
"trace ''expand_tuple_emptyI'' \<Longrightarrow> expand_tuple i1 (  [] ) num_ele xa ([])  [] i1"

|expand_tuple_tupI: "\<lbrakk> 
   trace (''expand_tuple_tupI pats='');
   (i2,xalist) = fresh_vars_list i1 num_ele ;
   trace (''expand_tuple_tupI i2='' @ (show i2));
   expand_tuple i2 pm num_ele xa pm' xalist' i3;
   trace (''expand_tuple_tupI i3='' @ (show i3))
\<rbrakk> \<Longrightarrow> 
   expand_tuple i1 (Cons (  ( Cons ((   (P_tup _ pats) ))  pm_pat) , sa )  pm ) num_ele xa (Cons ((pats)@pm_pat,sa) pm')  xalist' i3"

| expand_tuple_wildI:"\<lbrakk> 
   (i2,xalist) = fresh_vars_list i1 num_ele 
\<rbrakk> \<Longrightarrow> 
   expand_tuple i1 (  (  ( P_wild  lc ) # pm_pat , sa ) # pm) num_ele xa 
       (((List.map (\<lambda>xa. ( P_wild  lc)) xalist)@pm_pat,sa)#[])  xalist i1"

(* 
   FIXME Need to do something with the idd - pass in env from the expression part of the pexp? Will be a per branch basis, next to sa
       change sa to something like AS_let idd xa sa 
   we need to have with the sa something that maps Sail identifiers to MiniSail ones.
*)
| expand_tuple_varI: "\<lbrakk> 
  trace ''expand_tuple_varI'';
   (i1,xalist) = fresh_vars_list i1 num_ele
\<rbrakk> \<Longrightarrow> 
   expand_tuple i1 (  (  (( (P_id lc idd) )) # pm_pat , sa ) # pm) num_ele xa (((List.map (\<lambda>xa. ( P_wild lc)) xalist)@pm_pat,sa)#[])  xalist i1"



code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] expand_tuple .


abbreviation "s_unit \<equiv> AS_val (V_lit L_unit)"



inductive as_unpack :: "nat \<Rightarrow> xa \<Rightarrow>  xa list \<Rightarrow> sa  \<Rightarrow> sa \<Rightarrow> nat \<Rightarrow> bool" where
   "as_unpack i xa [] sa sa i"
 |  "\<lbrakk>
          (i2,xa) = mk_fresh_x i1;
          as_unpack i2 xa xas sa sa' i3
\<rbrakk> \<Longrightarrow> as_unpack i1 xa1 (xa2#xas) sa                                    
             (AS_let xa2 (AE_fst (V_var xa1)) (AS_let xa (AE_snd (V_var xa1)) sa')) i3" 
                                          
code_pred   (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool ) [show_steps,  show_mode_inference,  show_invalid_clauses] as_unpack .

values "{ (sa,i) . as_unpack 3 (mk_x 0) [ mk_x 1, mk_x 2] s_unit sa i}"

subsection \<open>Convert Pattern Matrix\<close>

(* Using the same variable xa all the way down the chain is ok *)
(* Second arg has same size as third. Last element of first arg has None for snd; this is the final else *)
(* We assume existance of an eq function. We don't have an eq operator native in MiniSail but we can construct a function with 
   a return type that reflects equality has we do have eq in the constraint language *)
fun mk_switch2 :: "xa \<Rightarrow> (pm * (la option) ) list \<Rightarrow> sa list \<Rightarrow> sa" where
  "mk_switch2 xa [ ( _ , _ ) ] [sa] = sa"
| "mk_switch2 xa  (( _ , Some la)#ps) (sa#sas) = LET xa = (AE_app (''eq'') (V_pair (V_var xa) (V_lit la))) IN IF (V_var xa)  THEN sa ELSE (mk_switch2 xa ps sas)"
(* Leave these partial as hitting the non-domain indicates a problem elsewhere which would otherwise be hidden *)

(* FIXME - Need an abort or something *)
fun mk_switch :: "xa \<Rightarrow> (pm * ( (lctx * xa) option) ) list \<Rightarrow> sa list \<Rightarrow> sa" where
  "mk_switch xa  (( _ , Some (L,xb))#[]) [sa] =  L [ IF (V_var xb)  THEN sa ELSE s_unit ]\<^sub>L"
| "mk_switch xa   (( _ , None)#[]) [sa] =  sa"
| "mk_switch xa  (( _ , Some (L,xb))#ps) (sa#sas) = L [ IF (V_var xb)  THEN sa ELSE (mk_switch xa ps sas) ]\<^sub>L"


fun mk_match_aux :: "(pm * (dc * xa) option) list \<Rightarrow> sa list \<Rightarrow> branch_list " where
  "mk_match_aux [ (_ , Some (dc,xa)) ] [sa] = AS_final (AS_branch dc xa sa)"
| "mk_match_aux ((_ , Some (dc,xa))#bs) (sa#sas) = AS_cons (AS_branch dc xa sa) (mk_match_aux bs sas)"


fun mk_match :: "xa \<Rightarrow> (pm * (dc * xa) option) list \<Rightarrow> sa list  \<Rightarrow> sa" where
 "mk_match xa  [ (_ , None) ] [sa] = sa"
| "mk_match xa bs sa  = AS_match (V_var xa) (mk_match_aux bs sa) "


fun mk_fresh_many :: "nat \<Rightarrow> nat \<Rightarrow> (nat * (xa list))" where
  "mk_fresh_many i1 0 = (i1,[])"
| "mk_fresh_many i1 n = (let (i2,xa) = mk_fresh_x i1 in
                         let (i3,xas) = mk_fresh_many i2 (n-1) in
                          (i3,xa#xas))"

definition mk_pm_list :: "env \<Rightarrow> SailAST.id \<Rightarrow> (pm * ((dc * xa) option)) list \<Rightarrow>(typ*xa) list \<Rightarrow> (pm* (typ*xa) list) list" where
 "mk_pm_list env tyid pmctor bss = List.map (\<lambda>(pm,xx). case xx of
                                   Some (dc,xa) \<Rightarrow> (case lookup_variant_env env tyid (id (String.implode dc)) of
                                                        (Some typ) \<Rightarrow>(pm, (typ,xa)#bss)
                                                      | None \<Rightarrow> (case lookup_enum_env  env (id (String.implode dc)) of
                                                          Some _ \<Rightarrow> (pm , (unit_typ, xa) # bss))   

)
                                | None \<Rightarrow> (pm,bss)) pmctor"

inductive conv_pattern_matrix :: "nat \<Rightarrow> env \<Rightarrow> xmap \<Rightarrow> pm \<Rightarrow> (typ*xa) list \<Rightarrow> sa \<Rightarrow> nat \<Rightarrow> bool" and
          conv_pattern_matrix_list ::"nat \<Rightarrow> env \<Rightarrow> xmap \<Rightarrow> (pm* (typ*xa) list) list \<Rightarrow> sa list \<Rightarrow> nat \<Rightarrow> bool" 
          where

(* conv_pattern_matrix_list *)
conv_pm_list_nilI: "\<lbrakk>
  trace ''conv_pm_list_nilI''
\<rbrakk> \<Longrightarrow> conv_pattern_matrix_list i _ _ [] [] i"

| conv_pm_list_consI:"\<lbrakk>
  trace ''conv_pm_list_consI'';
  conv_pattern_matrix i1 env xmap pm bss sa i2;
  trace (''conv_pm_consI i2=''@string_of_nat i2);
  conv_pattern_matrix_list i2 env xmap pmlist salist i3;
  trace (''conv_pm_consI i3=''@string_of_nat i3)
\<rbrakk> \<Longrightarrow>
  conv_pattern_matrix_list i1 env xmap ((pm,bss)#pmlist)  (sa#salist) i3"

(* FIXME - Do something with sa *)
|conv_tupleI: "\<lbrakk> 
   trace ''conv_pm_tupleI'';
   (i2,xas) = mk_fresh_many i1 (List.length bs);
   trace (''conv_pm_tupleI i2='' @ (show i2));
   expand_tuple i2 pm (List.length bs) xa  pm' xalist i3 ;
   trace (''conv_pm_tupleI i3='' @ (show i3) @ (show bs));
   conv_pattern_matrix i3 env xmap pm' ( (List.zip bs xas) @ bss) sa i4;
   trace (''conv_pm_tupleI i4='' @ (show i4) @ (show (List.length xalist)));
   as_unpack i4 xa xas sa sa' i5
\<rbrakk> \<Longrightarrow> 
   conv_pattern_matrix i1 env xmap pm ( ( ( (Typ_tup bs, xa) ) # bss)) sa' i5"

(* We don't mean the pattern is a lit but that its domain is a base type - int, bool, bit etc
   processing a literal gives us a list of pattern matrices - these are the children of thus node
 *)

(* FIXME do something with ms *)
| conv_litI: "\<lbrakk>
   trace (''conv_pm_litI b='' @ (show b));
   is_literal_base b;
   trace (''conv_pm_litI i1=''@string_of_nat i1);
   expand_lit i1 env xmap pm xa pmlits ms i3 ;
   trace (''conv_pm_litI i3=''@string_of_nat i3);
   conv_pattern_matrix_list i3 env xmap (map (\<lambda>pm. (pm,bss)) (map fst pmlits)) salist i4;
   trace (''conv_pm_litI i4=''@string_of_nat i4)
\<rbrakk> \<Longrightarrow> 
   conv_pattern_matrix i1 env xmap pm (Cons (b,xa)  bss) (mk_switch xa pmlits salist)  i4" 


| conv_ctorI: "\<lbrakk>
  trace ''conv_pm_ctorI'';
  \<not> (is_literal_base (Typ_id tyid));
  expand_ctor i1 env pm tyid xa pmctor ms i2;
  trace (''conv_pm_ctorI i2'' @ (show i2));
  pmlist = mk_pm_list env tyid  pmctor bss;
  conv_pattern_matrix_list i2 env xmap pmlist salist i3 ;
  trace (''conv_pm_ctorI i3'' @ (show i3))
\<rbrakk> \<Longrightarrow>  conv_pattern_matrix i1 env xmap pm (Cons ( (Typ_id tyid,xa)  )  bss) (mk_match xa pmctor salist )  i3" 

| conv_emptyI:  "\<lbrakk> 
   trace ''conv_pm_emptyI''
\<rbrakk> \<Longrightarrow>   conv_pattern_matrix i1 env xmap (( ( [], sa )  ) # pm) [] sa i1"




code_pred   (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool ) [show_steps,  show_mode_inference,  show_invalid_clauses] conv_pattern_matrix .

values "{ (pm',xalist,i). expand_tuple 0 ( [(  [ ( P_wild (None) )] , s_unit) ] ) 2 (mk_x 0)  pm' xalist i}"

values "{ (sa,i). conv_pattern_matrix 0 emptyEnv [] ( [(  [] , s_unit )] ) ([])  sa i}"

values "{ (sa,i,ms). expand_lit 0 emptyEnv [] ( [(  [ ( P_wild unk )] , s_unit )] ) (mk_x 0) sa ms  i}"

values "{ (sa,i,ms). expand_lit 0 emptyEnv [] ( [(  [ (( (P_lit unk ( SailAST.L_true ) ) ) )] , s_unit )] ) (mk_x 0) sa ms i}"

values "{(x,y). conv_pattern_matrix 0 emptyEnv [] [([], s_unit)] [] x y }"

value "nc_true"

value "is_literal_base (bool_typ True )"

values "{(x,y). conv_pattern_matrix 0 emptyEnv [] ( [(  [ (( (P_lit unk ( SailAST.L_true ) ) )  )] , s_unit ),
                                         (  [ (( (P_lit unk ( SailAST.L_false ) ) )  )] , s_unit )
] )  [ (bool_typ True,(mk_x 0)) ] x y }"

definition ctor_typ :: "char list \<Rightarrow> typ" where
  "ctor_typ s = Typ_id (id (String.implode s))"

values "{(x,y). conv_pattern_matrix 0 emptyEnv [] [ ([  ( (P_lit unk ( SailAST.L_true ) ) )], s_unit)] [(bool_typ True,(mk_x 0)) ] x y }"

(*values "{(x,y). conv_pattern_matrix 0 emptyEnv [ ([  ( P_app unk (id STR ''C'') [ P_id unk (id STR ''x'') ] )], s_unit)] [(ctor_typ ''foo'',(mk_x 0)) ] x y }"*)

values "{(x,y). conv_pattern_matrix 0 emptyEnv [(id STR ''x'', mk_x 1)] [ ( [  (  P_id unk (id STR ''x'')) ] , s_unit)] [(ctor_typ ''foo'',(mk_x 0)) ] x y }"

values "{(x,y). conv_pattern_matrix 0 emptyEnv [(id STR ''x'', mk_x 1)] [ ( [  (  P_id unk (id STR ''x'')) ] , s_unit)] [(ctor_typ ''foo'',(mk_x 0)) ] x y }"

definition env3 :: env where
  "env3 = emptyEnv \<lparr> variants := [ (id STR ''foo'', TypQ_no_forall , [
          (Tu_ty_id unit_typ (id STR ''R'') ) ] ) ] \<rparr>"

values "{(x,y). conv_pattern_matrix 0 env3 [(id STR ''x'', mk_x 1)] [ ( [  
   (  P_app unk (id STR ''R'') [ P_id unk (id STR ''x'') ]) ] , s_unit)] [(ctor_typ ''foo'',(mk_x 0)) ] x y }"

value "\<not> (is_literal_base (ctor_typ ''foo''))"

section \<open>Statements\<close>

type_synonym pexp = "tannot pexp"
type_synonym pat = "tannot pat"

inductive pat_conv :: "env \<Rightarrow> pat \<Rightarrow> string \<Rightarrow> xa \<Rightarrow> bool" where
"Some xa = mk_xa G x \<Longrightarrow> pat_conv G ( (P_app _ ( (id ctor) ) [  (P_id _ x) ]) ) ctor xa " 


fun mk_str' :: "'a \<Rightarrow> string" where
"mk_str' s = STR ''''"

fun mk_str :: "'a \<Rightarrow> char list" where
"mk_str t = String.explode (mk_str' t)"

code_printing
 constant mk_str' \<rightharpoonup> (Eval) "(@{make'_string} _)" \<comment> \<open>note indirection via antiquotation\<close>

value "trace (mk_str [True,False])"

(* FIXME - Not sure if I should also be returning a gamma and a MS type? *)

(* Type annotated Sail expression to MiniSail expression/statement with contexts and type *)
inductive 
   e_conv :: "nat \<Rightarrow> xmap \<Rightarrow> tannot SailAST.exp \<Rightarrow> xa \<Rightarrow> \<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> lctx \<Rightarrow>  nat \<Rightarrow> bool" ( " _  ; _ \<turnstile> _ ; _ \<leadsto> _ ; _ ; _ ; _ ; _ ; _ ; _"  ) and
   e_conv_list :: "nat \<Rightarrow> xmap \<Rightarrow> tannot SailAST.exp list \<Rightarrow> xa \<Rightarrow> \<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> lctx \<Rightarrow>  nat \<Rightarrow> bool"  and
   s_conv :: "nat \<Rightarrow> xmap \<Rightarrow> tannot SailAST.exp \<Rightarrow> \<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> s \<Rightarrow> nat \<Rightarrow> bool" ( " _ \<turnstile> _ \<leadsto> _") and
   pexp_list_conv :: "nat \<Rightarrow> env \<Rightarrow> xmap \<Rightarrow> pexp list \<Rightarrow> xa \<Rightarrow> pm \<Rightarrow> nat \<Rightarrow> bool" 
(*   lb_conv :: "env \<Rightarrow> tannot SailAST.letbind \<Rightarrow> x \<Rightarrow> e  \<Rightarrow> bool"  ( " _ \<turnstile> _ \<leadsto> _ ; _") and
   pexp_conv :: "env \<Rightarrow> pexp \<Rightarrow> branch_s \<Rightarrow> bool" ( " _ \<turnstile>\<^sub>p _ \<leadsto> _" )and 
   pexp_list_conv :: "env \<Rightarrow> pexp list \<Rightarrow> branch_list \<Rightarrow> bool" ( " _ \<turnstile> _ \<leadsto> _" ) *)
where

(* EXPRESSIONS *)
e_conv_valI: "\<lbrakk>
   Some E = get_env_exp e;
   trace (''e_conv_valI n='' @ show n) ;
   E ; xm \<turnstile> e \<leadsto> T ; G ; va;
   trace (''e_conv_valI len='' @ (show (List.length T))) 
\<rbrakk>  \<Longrightarrow>  n ; xm \<turnstile> e ; xa \<leadsto> T ; [] ; {||} ; G ; DNil ; L_let xa (AE_val va)  L_hole ; n"

| e_conv_regI: "\<lbrakk>
   trace (''e_conv_regI n='' @ show n) ;
   Some env = get_env tan;
   Some regi = lookup_register_index_env env reg;
   Some typ = lookup_register_env env reg;
   t_conv [] typ ta;
   trace (''e_conv_regI n='' @ (show regi))   
\<rbrakk>  \<Longrightarrow>  n ; xm \<turnstile> (E_id tan reg) ; xa \<leadsto> [] ; [] ; {||} ; GNil ; ((mk_u regi, ta)#\<^sub>\<Delta>DNil) ; L_let xa (AE_mvar (mk_u regi))  L_hole ; n"

| e_conv_appI: "\<lbrakk>
 trace ''e_conv_appI'';
 (n2,xa') = mk_fresh_x n1;
 e_conv_list n2 xm es  xa'  T  P  B  G  D  L  n3
\<rbrakk>  \<Longrightarrow>  n1 ; xm \<turnstile> (E_app tan (id fid) es) ; xa \<leadsto> T ; P ; B ; G ; D ; L \<circ> ( L_let xa (AE_app (String.explode fid) (V_var xa')) L_hole ) ; n3"

| e_conv_tupleI: "\<lbrakk> 
 trace ''e_conv_tupleI'';
  e_conv_list n1 xm es  xa  T  P  B  G  D  L  n2
\<rbrakk> \<Longrightarrow> n1 ; xm \<turnstile> (E_tuple  tan es) ; xa \<leadsto> T ; P ; B ; G ; D ; L  ; n2"

| e_conv_list_singleI: "\<lbrakk> 
   trace (''e_conv_list_singleI n1='' @ (show n1));
   e_conv n1 xm e xa T P B G D L n2;
   trace (''e_conv_list_singleI n2='' @ (show n2))
\<rbrakk> \<Longrightarrow> e_conv_list n1 xm [e] xa T P B G D L n2"

| e_conv_list_consI: "\<lbrakk> 
   trace (''e_conv_list_consI n1='' @ (show n1));
   (n2,xa') = mk_fresh_x n1;
   e_conv n2 xm e xa' T' P' B' G' D' L1 n3;
   trace (''e_conv_list_consI n3='' @ (show n3));
  (n4,xa'') = mk_fresh_x n3;
   e_conv_list n4 xm (es) xa'' T P B G D L2 n5;
   trace (''e_conv_list_consI n5='' @ (show n5))
\<rbrakk> \<Longrightarrow> e_conv_list n1 xm (e#es) xa T P B G D (L_compose L1 (L_compose L2  (L_let xa  (AE_val (V_pair (V_var xa') (V_var xa''))) L_hole))) n5"

(* STATEMENTS *)

| s_conv_expI: "\<lbrakk> 
 trace (''s_conv_expI n1='' @ (show n1));
 (n2,xa) = mk_fresh_x n1;
  n2 ; xm \<turnstile> e ; xa \<leadsto> T ; P ; B ; G ; D ; L ; n3;
  trace (''s_conv_expI n3='' @ (show n3))
\<rbrakk> \<Longrightarrow> s_conv n1  xm e  T P B G D (L [ AS_val (V_var xa) ]\<^sub>L)  n3"

| s_conv_block_single: "\<lbrakk>
  trace (''s_conv_blockI n1='' @ (show n1));
  s_conv n1 xm  e T P B G D L n2;
  trace (''s_conv_blockI n2='' @ (show n2))
\<rbrakk> \<Longrightarrow> s_conv n1 xm  (E_block _ [e]) T P B G D L n2"

(*E_assign(LEXP_aux(LEXP_id(Id_aux(Id("R1"),)),),E_aux(E_id(Id_aux(Id("v"),)),)
*)
| s_conv_assignI: "\<lbrakk>
  (n2,xa) = mk_fresh_x n1;
  e_conv n2 xm e xa T P B G D L n3;
  Some env = get_env tan;
  Some regi = lookup_register_index_env env regid
\<rbrakk> \<Longrightarrow> s_conv n1 xm (E_assign tan (LEXP_id _ regid) e) T P B G D L[ AS_assign (mk_u regi) (V_var xa)]\<^sub>L n3"

| s_conv_ifI: "\<lbrakk> 
   (n2,xa) = mk_fresh_x n1;
   e_conv n2 xm e1 xa T1 P1 B1 G1 D1 L n3;
   s_conv n3 xm e2 T2 P2 B2 G2 D2 sa2 n4;
   s_conv n4 xm e3 T3 P3 B3 G3 D3 sa3 n5
\<rbrakk> \<Longrightarrow> 
   s_conv n1 xm ( (E_if _ e1 e2 e3) ) T3 P3 B3 G3 D3 (L [ AS_if [xa]\<^sup>v sa2 sa3 ]\<^sub>L) n4 "

| s_conv_letI: "\<lbrakk> 
   trace ''letI'';
   (i2,xa) = mk_fresh_x i1;
   e_conv i2 xm e1 xa T1 P1 B1 G1 D1 L i3;
   Some t = type_of_exp e1;
   trace (''t='' @ (show t));
   Some env = get_env tan;
   pexp_list_conv i3 env xm  [  (Pat_exp None pat e2)  ] xa pm i4;
   trace (''done pexp list conv'' @ (mk_str pm) @ (string_of_nat i4));
   conv_pattern_matrix i4 env xm pm [(t, xa)] sa i5;
   trace (''elab i5='' @  (string_of_nat i5))
\<rbrakk> \<Longrightarrow>
   s_conv i1 xm  ( (E_let tan ( (LB_val lc pat e1 ) ) e2)) T1 P1 B1 G1 D1 (L [ sa ]\<^sub>L) i5"


(* FIXME when we convert each sa in the pm we will get a map of Sail to MS variables;
         we will need to use this to map pattern identifiers to MiniSail ones
   Perhaps put it alongside each sa in the pattern matrix ?
*)

| ep_s_elab_matchI: "\<lbrakk>
  trace (''ep_s_elab_matchI i1='' @ (show i1));
  Some env = get_env tan;
  (i2, xa) = mk_fresh_x i1;
  e_conv i2 xm ep xa T P B G D L i3;
  trace (''ep_s_elab_matchI i3='' @ (show i3));
  pexp_list_conv i3 env xm pexps xa pm i4;
  trace (''ep_s_elab_matchI i4='' @ (show i4));
  conv_pattern_matrix i4 env xm pm [(t,xa)] sa i5;
  trace (''ep_s_elab_matchI i5='' @ (show i5));
  Some t = type_of_exp ep  
\<rbrakk> \<Longrightarrow> 
  s_conv i1 xm ( (E_case tan ep pexps) ) T P B G D (L [ sa ]\<^sub>L) i5"


|  ep_s_elab_pexp_singletonI: "\<lbrakk>
  trace (''ep_s_elab_pexp_singletonI i1='' @ (show i1));
  s_conv i1 xm ep T P B G D sa i2;
  trace (''ep_s_elab_pexp_singletonI i2='' @ (show i2))
\<rbrakk> \<Longrightarrow> 
  pexp_list_conv i1  env xm [ ( (Pat_exp _ patp ep)  ) ] xa [ ([ (patp ) ], sa)] i2"


|  ep_s_elab_pexp_consI: "\<lbrakk>
  trace ''ep_s_elab_pexp_consI'';
  s_conv i1 xm ep T P B G D sa i2;
  pexp_list_conv i2  env xm (pexp#pexps) xa pm i3
\<rbrakk> \<Longrightarrow> 
  pexp_list_conv i1 env xm (( (Pat_exp  _ patp ep)) # pexp # pexps) xa (([ (patp ) ], sa)#pm) i3"



code_pred (modes: 
    e_conv : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool and
    e_conv_list : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool and
    s_conv : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool and
    pexp_list_conv : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool )  [show_steps,  show_mode_inference,  show_invalid_clauses] s_conv .


values "{ (T,P,B,G,D,sa,n) . s_conv 0 [] ( (E_if (set_type None unit_typ)
                     ( (E_lit (set_type None (bool_typ True)) ( SailAST.L_true )) )
                           ( (E_lit (set_type None unit_typ) ( SailAST.L_unit )) )
                           ( (E_lit (set_type None unit_typ) ( SailAST.L_unit )) )
                     )) T P B G D sa n}"

values "{ (T,P,B,G,D,sa,n) . s_conv 0 [] ( (E_let (set_type None unit_typ)
              ( (LB_val None ( (P_id (set_type None (bool_typ True)) ( (id (STR ''x'')) )) )
                      ( (E_lit (set_type None (bool_typ True))) ( SailAST.L_true ))       ))
                      ( (E_lit (set_type None unit_typ) ( SailAST.L_unit ))) 
                                         )) T P B G D sa n}"


values  "{ (T,P,B,G,D,sa,n) . s_conv 0 [] (e_let e_unit unit_typ) T P B G D sa n}"
  


values "{ (T,P,B,G,D,sa,n) . s_conv 0  [] ( (E_let (set_type None unit_typ)
              ( (LB_val None ( (P_id (set_type None (bool_typ True)) ( (id (STR ''x'')) )) )
                      ( (E_lit (set_type None (bool_typ True))) ( SailAST.L_true ))       ))
                      ( (E_lit (set_type None unit_typ) ( SailAST.L_unit ))) 
                                         )) T P B G D sa n}"

value " ( (LB_val None (pat_id (STR ''x'')) (e_unit)))"

values "{ (T,P,B,G,D,sa,n) . s_conv 0  [] ( (E_let (set_type None unit_typ)
              ( (LB_val None (pat_unit) (e_unit))) e_unit                    
                                         )) T P B G D sa n}"


values "{ (T,P,B,G,D,sa,n) . s_conv 0 [] ( (E_let (set_type None unit_typ)
              ( (LB_val None (pat_id (STR ''x'')) (e_unit))) e_unit                    
                                         )) T P B G D sa n}"

values "{ (T,P,B,G,D,sa,n) . s_conv 0 [] ( (E_let (set_type None unit_typ)
              ( (LB_val None (pat_pair) (e_pair))) e_unit
                    
                                         )) T P B G D sa n}"


values "{ (x,y) . pexp_list_conv 0 emptyEnv [] [] (mk_x 0) x y }"

values "{ (x,y) . pexp_list_conv 0 emptyEnv [] [
                ( Pat_exp  (set_type None (bool_typ True))
                   ( (P_id  (set_type None (bool_typ True))) ( (id (STR ''x'')) ))
                          ( (E_lit (set_type None unit_typ)) ( SailAST.L_unit ))) ] (mk_x 0) x y }"

 

value "(bool_typ True)"



(* Note: We build into this that x does not occur in the rest of gs - this will give us that 
         xa is fresh in G OR should we impose this condition on Gamma? Is supp constructive for our use of nominal? *)
(* FIXME - The [] in t_conv_raw *)


section \<open>Definitions\<close>


primrec option_map :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"option_map f [] = []"
| "option_map f (x#xs) = (case f x of Some y \<Rightarrow> y # option_map f xs | _ \<Rightarrow> option_map f xs)"

fun mk_xxx :: "quant_item list \<Rightarrow> (kid*kind) list" where
"mk_xxx qi_list =  (option_map (\<lambda>qi. case qi of ( (QI_id ( (KOpt_kind kind kid) ))  ) \<Rightarrow> Some (kid,kind) | _ \<Rightarrow> None) qi_list) "

fun mk_tq_map :: "typquant \<Rightarrow> type_vars" where
"mk_tq_map ( TypQ_no_forall ) = []"
| "mk_tq_map ( (TypQ_tq qi_list) ) = mk_type_vars (mk_xxx qi_list)
    (CE_fst (CE_val (V_var (mk_x 1))))"


inductive mk_tq_c_aux :: "type_vars \<Rightarrow> quant_item list \<Rightarrow> c \<Rightarrow> bool" where
 "mk_tq_c_aux _ [] (C_true)"
| "mk_tq_c_aux m qis c \<Longrightarrow> mk_tq_c_aux m ((QI_id _)#qis) c"
| "\<lbrakk> c_conv m nc T G c1; mk_tq_c_aux m qis c2 \<rbrakk> \<Longrightarrow> mk_tq_c_aux m ((QI_constraint nc)#qis) (c1 AND c2)"


inductive mk_tq_c :: "type_vars \<Rightarrow> typquant \<Rightarrow> c \<Rightarrow> bool" where
   "mk_tq_c _  ( TypQ_no_forall ) C_true"
|  "mk_tq_c_aux m qi_list c  \<Longrightarrow> mk_tq_c m ( (TypQ_tq qi_list) ) c "


code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool ) 
    [show_steps,  show_mode_inference,  show_invalid_clauses]
       mk_tq_c .

inductive def_funtyp :: "typquant \<Rightarrow> typ \<Rightarrow> ba \<Rightarrow> ca \<Rightarrow> \<tau> \<Rightarrow> bool" where
"\<lbrakk> tv_map = mk_tq_map tyq ; 
   k_typ = List.map (\<lambda>(_,k,_). case k of 
                                  K_int \<Rightarrow> int_typ | K_bool \<Rightarrow> bool_all_typ) tv_map;
   k_typ' = (if length k_typ = 0 then unit_typ else 
            (if length k_typ = 1 then hd k_typ else
            Typ_tup k_typ));
   mk_tq_c tv_map tyq ca;
   t_conv tv_map out_typ ta ; 
   trace (''def_funtyp out_typ='' @ (show out_typ) @ (show in_typs));  
   t_conv_raw tv_map  k_typ' (CE_fst (CE_val (V_var (mk_x 1)))) T1 G1 ba1 ca1;
   t_conv_raw tv_map  (Typ_tup in_typs) (CE_snd (CE_val (V_var (mk_x 1)))) T2 G2 ba2 ca2
\<rbrakk> \<Longrightarrow> def_funtyp tyq ( (Typ_fn in_typs out_typ _) ) (B_pair ba1 ba2) (C_conj ca (C_conj ca1 ca2)) ta"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] def_funtyp .

values "{(ba,ca,ta) . def_funtyp ( TypQ_no_forall ) ( (Typ_fn [unit_typ] unit_typ ( (Effect_set Nil)  )) ) ba ca ta}"

(*
definition collect_ids_pexps :: "pexp list \<Rightarrow> id list" where
   "collect_ids_pexps pexps = concat (map (collect_pexp (\<lambda>p. case p of (P_id _ i) \<Rightarrow> [i] | _ \<Rightarrow> []) (\<lambda>p. case p of (E_id _ i) \<Rightarrow> [i] | _ \<Rightarrow> [])) pexps)" 
*)
fun mk_id_map :: "pexp list \<Rightarrow> (id * xa) list" where
  "mk_id_map ps = mapi (\<lambda>n i. (i,mk_x (2*n+1))) (concat (map collect_pexp ps))"

inductive funcl_conv :: "env \<Rightarrow> type_vars \<Rightarrow> (tannot pexp_funcl) list \<Rightarrow> s \<Rightarrow> bool" where
"\<lbrakk>
  trace (''funcl_conv'' @ (show t));
  (i1,xa) = mk_fresh_x 0;
  pexps = List.map (\<lambda>fcls. case fcls of  (PEXP_funcl pexp) \<Rightarrow> pexp) funcls;

  xm = mk_id_map pexps;

  pexp_list_conv i1 env xm pexps xa pm i4;
  trace (''funcl_conv i4=''@string_of_nat i4);
  conv_pattern_matrix i4 env xm pm [(t,xa)] sa i5;
  trace (''funcl_conv i5=''@string_of_nat i5);
  Some t = type_of_pexp (hd pexps   )

\<rbrakk> \<Longrightarrow> funcl_conv env tvars funcls (AS_let xa (AE_snd (V_var (mk_farg))) sa)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] funcl_conv .

inductive variant_conv :: "env \<Rightarrow> type_union list \<Rightarrow> (char list  * \<tau>) list \<Rightarrow> bool" where

"variant_conv _ Nil Nil"

| "\<lbrakk> 
   trace (''variant_convI'' @ (show typ));
   t_conv Nil typ ta; 
   variant_conv env tu_list dclist
\<rbrakk> \<Longrightarrow> variant_conv env (( (Tu_ty_id typ ( (id ctor) )) ) # tu_list) ((String.explode ctor, ta) # dclist)"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] variant_conv .



fun lookup_fun_typ :: "env \<Rightarrow> string \<Rightarrow> (typquant * typ) option" where
  "lookup_fun_typ env f = get_val_spec_env env (SailAST.id f)"

datatype ms_def = 
  MS_type_def MiniSailAST.type_def 
  | MS_fun_def MiniSailAST.fun_def
  | MS_val_spec f x b c \<tau>
  | MS_register u \<tau> v

definition extract_pexp :: "(tannot funcl) list \<Rightarrow> (tannot pexp_funcl) list" where
  "extract_pexp fcls =  List.map (\<lambda>pe. case pe of (FCL_Funcl _ _ pe) \<Rightarrow> pe) fcls"

fun extract_tan ::  "tannot \<Rightarrow> (tannot funcl) list \<Rightarrow> tannot" where
 "extract_tan tan [] = tan"
| "extract_tan tan ((FCL_Funcl tan' _ _ )#fcls) = extract_tan tan' fcls"

(* Turn let binds into functions with unit argument ? *)
inductive def_conv :: "env \<Rightarrow> tannot def \<Rightarrow> ms_def option \<Rightarrow> bool" where

(* Where there is a type annotation on the function, the typ on the annot is actually just
   the return type.
   The input type is to be found on the patterns
*)
(*
"\<lbrakk>    
   trace ''def_conv_annot_some'';
   (PEXP_funcl  (Pat_exp _ (P_typ _ in_typ _) _)) = pexp_funcl;
   def_funtyp tyq (Typ_fn  [in_typ] out_typ (Effect_set [])) ba ca ta;
   type_vars = mk_tq_map tyq;
   funcl_conv env type_vars pexp_funcl sa \<rbrakk>
\<Longrightarrow> def_conv env (DEF_fundef  ( (FD_function _ rec_opt ( (Typ_annot_opt_some tyq out_typ)) effect_opt
          [ (FCL_Funcl _ ( (id f ) ) pexp_funcl) ])  )) 
          (Some (MS_fun_def (AF_fundef (String.explode f) (MiniSailAST.AF_fun_typ_none (AF_fun_typ (mk_x 1) ba ca  ta (sa))))))"
*)
(* We have to get tan/env from the *last* funcl. 
 pexp_funcls = List.map (\<lambda>pe. case pe of (FCL_Funcl _ _ pe) \<Rightarrow> pe) []; *)
"\<lbrakk>    
   tan' = extract_tan tan fcls;
   Some env = get_env tan';
   trace (''def_conv_annot_none env='' @ (show_env env));
   Some (tyq,fntyp) = lookup_fun_typ env f ;
   trace (''def_conv_annot_none typ='' @ (show fntyp));
   def_funtyp tyq fntyp ba ca ta;
   type_vars = mk_tq_map tyq;
   pexp_funcls = extract_pexp fcls;
   funcl_conv env type_vars (pexp_funcl#pexp_funcls) sa \<rbrakk>
\<Longrightarrow> def_conv _ (DEF_fundef  ( (FD_function _ rec_opt ( ( _)) effect_opt
          ((FCL_Funcl tan ( (id f ) ) pexp_funcl)#fcls))  )) 
          (Some (MS_fun_def (AF_fundef (String.explode f) (MiniSailAST.AF_fun_typ_none (AF_fun_typ (mk_x 1) ba ca  ta (sa))))))"

(* FIXME - tq list *)
| "variant_conv env tu_list dclist \<Longrightarrow> def_conv env  
    (DEF_type (TD_aux (TD_variant  (SailAST.id tyid)   _ tu_list _ ) ) )
    (Some (MS_type_def (AF_typedef (String.explode tyid) dclist)))"

| "\<lbrakk>
    tu_list = List.map (\<lambda>i. Tu_ty_id unit_typ i) id_list;
    variant_conv env tu_list dclist
\<rbrakk> \<Longrightarrow> def_conv env  
    (DEF_type (TD_aux (TD_enum  (SailAST.id tyid)  id_list _ ) ) )
    (Some (MS_type_def (AF_typedef (String.explode tyid) dclist)))"

| "\<lbrakk>
    def_funtyp tyq typ ba ca ta
\<rbrakk> \<Longrightarrow> def_conv env (DEF_spec (VS_aux ((TypSchm_ts tyq typ) ,id f, _, _))) 
(Some (MS_val_spec (String.explode f) (mk_x 0) ba ca ta))"

(* FIXME. Make u unique and make a proper v *)
| "\<lbrakk> 
     t_conv [] typ t;
     u = mk_u 0     ;
     v = V_lit (L_bitvec []) 
\<rbrakk> \<Longrightarrow> def_conv env ((DEF_reg_dec ( (DEC_reg _ _ _ typ rid) ))) 
               (Some (MS_register u t v))"

| "def_conv env (DEF_overload _ _ ) None"
| "def_conv env (DEF_default _ ) None"
| "def_conv env (DEF_type (TD_aux (TD_abbrev _ _ _  ))) None"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] def_conv .

values "{ dc . def_conv emptyEnv (DEF_type (TD_aux (TD_variant (id (STR ''ast''))
             TypQ_no_forall [(Tu_ty_id (bool_all_typ ) (id (STR ''bob'')))] False))) dc }"

values "{ dc . def_conv emptyEnv (DEF_type (TD_aux (TD_variant (id (STR ''ast''))
             TypQ_no_forall [(Tu_ty_id (bv_typ2 2 ) (id (STR ''bob'')))] False))) dc }"

values "{ dc . def_conv emptyEnv (DEF_type (TD_aux (TD_variant (id (STR ''ast''))
             TypQ_no_forall [
                  (Tu_ty_id (Typ_tup [unit_typ,unit_typ,unit_typ] ) (id (STR ''bob''))),
                  (Tu_ty_id (Typ_tup [unit_typ,unit_typ,unit_typ] ) (id (STR ''bill'')))

] False))) dc }"
(*
Defs([(DEF_spec(VS_val_spec(cast_false,Id_aux(Id("foo"),),[],TypSchm_aux(TypSchm_ts(TypQ_aux(TypQ_tq([(QI_aux
(QI_id(KOpt_aux(KOpt_kind(K_aux(K_int,),Kid_aux(Var("'n"),)),)),))]),),
Typ_aux(Typ_fn([(Typ_aux(Typ_app(Id_aux(Id("atom"),),[(A_aux(A_nexp(Nexp_aux(Nexp_var(Kid_aux(Var("'n"),)),)),))]),))],Typ_aux(Typ_id(Id_aux(Id("int"),)),),Effect_aux(Effect_set([]),)),)),))))
])markw@mark-vb:~/github/research/minisail/tests/duopod$ 
*)

values "{ dc. def_conv emptyEnv (DEF_spec (VS_aux ( 
     (TypSchm_ts (TypQ_tq [
             (QI_id (KOpt_kind K_int  (var (STR ''n'')))),
             (QI_constraint (NC_bounded_ge (Nexp_var (var (STR ''n''))) (Nexp_constant 0)))
        ])
          (Typ_fn [ Typ_app (id (STR ''atom'')) [ A_nexp (Nexp_var (var (STR ''n'')))]] int_typ
          (Effect_set []))
     ),
     (id (STR ''foo'')), (\<lambda>_. None), False))     
     ) dc }"


definition tq1 where
  "tq1 =  (TypQ_tq [(QI_id (KOpt_kind K_int  (var (STR ''n'')))),
                            (QI_constraint (NC_bounded_ge (Nexp_var (var (STR ''n''))) (Nexp_constant 0))) ])"

value "mk_tq_map tq1"

values "{ (T,G,c) . c_conv (mk_tq_map tq1)  (NC_bounded_ge (Nexp_constant 0) (Nexp_constant 0)) T G c }"

values "{ (T,G,c) . ce_conv (mk_tq_map tq1)  (Nexp_var (var  (STR ''n''))) T G c }"

values "{ (T,G,c) . c_conv (mk_tq_map tq1)  (NC_bounded_ge (Nexp_var (var (STR ''n''))) (Nexp_constant 0)) T G c }"

values "{ c . mk_tq_c (mk_tq_map tq1) tq1 c }"



values "{ta. t_conv [] unit_typ ta }"

values "{(t,g,ba,ca). t_conv_raw Nil ( (Typ_tup [unit_typ]) ) (CE_val (V_var (mk_x 1))) t g ba ca }"

abbreviation 
  "env1 \<equiv> emptyEnv \<lparr> locals := [  (( (id (STR ''x'')) ),Immutable, (bool_typ True)) ] , typ_vars := [( (var STR ''n'') , 
                    K_int  )] \<rparr>"

abbreviation "tan1 \<equiv> ( add_local (set_type None unit_typ)  ( (id (STR ''x'')) ) (unit_typ)  )"

abbreviation "tan2 \<equiv> ( add_local (set_type None int_typ)  ( (id (STR ''x'')) ) (unit_typ)  )"

abbreviation "pexp1 \<equiv> ( (Pat_exp unk ( (P_id (set_type None unit_typ) ( (id (STR ''x''))) )) ( (E_id tan1 ( (id (STR ''x'')) )) 
  )))"

abbreviation "pexp2 \<equiv> ( (Pat_exp unk ( (P_typ (set_type None unit_typ) unit_typ  
            (P_id (set_type None unit_typ) ( (id (STR ''x''))) ))) 
      ( E_block tan1  [(E_lit tan1 (SailAST.L_unit)  )] )))"

abbreviation "pexp3 \<equiv> ( (Pat_exp unk ( (P_typ (set_type None unit_typ) unit_typ  
            (P_id (set_type None unit_typ) ( (id (STR ''x''))) ))) 
      ( E_block tan2  [(E_lit tan1 (SailAST.L_num 42)  )] )))"

abbreviation "funcl1 \<equiv> (FCL_Funcl unk ( (id (STR ''f'')) ) (PEXP_funcl pexp1))  "

abbreviation "funcl2 \<equiv> (FCL_Funcl unk ( (id (STR ''f'')) ) (PEXP_funcl pexp2))  "

abbreviation "funcl3 \<equiv> (FCL_Funcl unk ( (id (STR ''f'')) ) (PEXP_funcl pexp3))  "

values "{ (va,t,g) . v_conv env1 [] ( (E_id tan1 ( (id (STR ''x'')) )) ) t g va }"

values "{ (t,p,b,g,d,sa,i) . s_conv 0 [] ( (E_id tan1 ( (id (STR ''x'')) )) ) t p b g d sa i }"

values "{ (pm,i) . pexp_list_conv 0 emptyEnv  [] [pexp1] (mk_x 1) pm i }"

values "{ sa . funcl_conv emptyEnv [] [(PEXP_funcl pexp1)] sa }"

(* These no longer work as you don't process types in function - needs to be val first *)
values "{ fa . def_conv emptyEnv (DEF_fundef ( (FD_function unk Rec_nonrec  ( (Typ_annot_opt_some 
   ( (TypQ_tq [ (QI_id ( (KOpt_kind ( K_int ) ( (var (STR ''x'')) )) ))   ]) )
  ( (Typ_fn [unit_typ] unit_typ ( (Effect_set Nil)  )) )  ) ) ( Effect_opt_none ) [funcl1]) )) fa }"

values "{ fa . def_conv emptyEnv (DEF_fundef ( (FD_function unk Rec_nonrec  
  (Typ_annot_opt_some TypQ_no_forall unit_typ) Effect_opt_none
     [funcl2]) )) fa }"

values "{ fa . def_conv emptyEnv (DEF_fundef ( (FD_function unk Rec_nonrec  
  (Typ_annot_opt_some TypQ_no_forall int_typ) Effect_opt_none
     [funcl3]) )) fa }"

abbreviation "pexp4 \<equiv> ( (Pat_exp unk 
         (P_tup (set_type None (Typ_tup [int_typ,int_typ]))
              [ P_id (set_type None int_typ) ( (id (STR ''x''))),
                P_id (set_type None int_typ) ( (id (STR ''y'')))])
 
      ( E_block tan2  [(E_if tan1 (E_lit tan1 SailAST.L_true) 
           (E_lit tan1 (SailAST.L_num 42)) (E_lit tan1 (SailAST.L_num 42))
                              )] )))"



abbreviation "env4 \<equiv> emptyEnv \<lparr> top_val_specs := 
                         [ (id (STR ''f''), TypQ_no_forall ,                             
                   ( (Typ_fn [int_typ,int_typ] int_typ ( (Effect_set Nil)))))  ] \<rparr>"

abbreviation "tan4 \<equiv>  \<lparr> tannot_env = env4 ,   tannot_typ = int_typ, 
          tannot_effect = ( (Effect_set [])), tannot_expected = None, tannot_instantiations = None  \<rparr>"

abbreviation "funcl4 \<equiv> (FCL_Funcl (Some tan4) ( (id (STR ''f'')) ) (PEXP_funcl pexp4))  "

value "collect_ids funcl4"

(* There are 16 derivations here! *)
values "{ fa . def_conv env4 (DEF_fundef ( (FD_function unk Rec_nonrec  
  (Typ_annot_opt_none) Effect_opt_none
     [funcl4]) )) fa }"

value "mk_fresh_many 0 2"

value int_typ 
value unit_typ

values "{ fa . def_conv emptyEnv (DEF_fundef ( (FD_function unk Rec_nonrec  ( (Typ_annot_opt_some 
   TypQ_no_forall
  ( (Typ_fn [int_typ] int_typ ( (Effect_set Nil)  )) )  ) ) ( Effect_opt_none ) [funcl1]) )) fa }"

(*"fun_typ_conv 
"def_conv env (DEF_fundef (FD_aux (FD_function rec_opt Typ_annot_opt_none effect_top [funcl]) _))  *)

section \<open>Programs\<close>

(* Go through defns
         function def - convert add to Phi
         variant def - add to Theta
         register - Add to Delta. 

  
*)
(*
inductive defs_conv :: "tannot def list \<Rightarrow> \<Theta> \<Rightarrow> \<Phi> \<Rightarrow> var_def \<Rightarrow> bool" where
defs_conv_nilI:  "defs_conv [] T P V T P V"

| defs_conv_consI: "\<lbrakk>
   def_conv def T1 P1 V1 T2 P2 V2
  defs_conv defs T2 T2 V2 T3 P3 V3
\<rbrakk> \<Longrightarrow> defs_conv (def#defs) T1 P1 V1 T3 P3 D3"

(*
| defs_conv_variantI: "\<lbrakk>
     defs_conv defs T P D;
     def_conv emptyEnv def (Some (MS_type_def td))
\<rbrakk> \<Longrightarrow> defs_conv (def#defs) (td#T) P D"

| defs_conv_fundefI: "\<lbrakk>
     defs_conv defs T P D;
     def_conv emptyEnv def (Some (MS_fun_def fd))
\<rbrakk> \<Longrightarrow> defs_conv (def#defs) T (fd#P) D"

(* FIXME. Need to calculate u correctly *)
| defs_conv_registerI: "\<lbrakk> 
     defs_conv defs T P D;
     t_conv [] typ t;
     u = mk_u 0
\<rbrakk> \<Longrightarrow> defs_conv ((DEF_reg_dec ( (DEC_reg _ _ _ typ rid) ))#defs) T P ((u,t)#\<^sub>\<Delta>D)"

| "defs_conv defs T P D \<Longrightarrow> defs_conv ((DEF_overload _ _ )#defs) T P D"
| "defs_conv defs T P D \<Longrightarrow> defs_conv ((DEF_default _ )#defs) T P D"
*)


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] defs_conv .
*)



section \<open>Examples\<close>



values "{ G. g_conv env1 []  G }" 

values "{ (sa,T,P,B,G,D,i) . s_conv 0  [( id STR ''x'', mk_x 1)]         
            (E_id 
            (add_local (set_type None (bool_typ True)) ( (id (STR ''x'')))  (bool_typ True)  )
            (id (STR ''x'')) ) 
            T P B G D sa i}"

(* Expected to fail as xx not in env *)
values "{  (sa,T,P,B,G,D,i) . s_conv 0  [( id STR ''x'', mk_x 1)]     
                ( (E_id 
                     (add_local (set_type None (bool_typ True)) ( (id (STR ''x'')))  (bool_typ True)  )
                    ( (id (STR ''xx'')) )))
     T P B G D sa i }"



values "{ (sa,T,P,B,G,D,i) . s_conv 0  [( id STR ''x'', mk_x 1)]     
             ( E_case  (set_type None (bool_typ True))  e_unit [ Pat_exp unk (pat_id (STR ''x'')) e_true ])
             T P B G D sa i }"



values  "{ (sa,T,P,B,G,D,i) . s_conv 0 []  (e_let (bv_lit (STR ''0101'')) (bv_typ 4)) T P B G D sa i }"

values "{ (sa,T,P,B,G,D,i) . s_conv 0 []
             (bv_lit  (STR ''0101''))
             T P B G D sa i }"

(* Target is for a match statements with bit vectors *)



definition match1 where
  "match1 = E_case int_tannot (bv_lit  (STR ''0101'')) [ 
            Pat_exp unk (pat_lit_bv  (STR ''0101'')) e_true,
            Pat_exp unk (pat_lit_bv  (STR ''0100'')) e_false ]"

values "{ (sa,T,P,B,G,D,i) . s_conv 0 [] match1 T P B G D sa i }"



value "x_pp (mk_x 0)"

(*
lemma
  shows "{ (T ,P, B, G, D, sa, i).  s_conv 0 
             ( E_lit (set_type None (bv_typ 4)) (SailAST.L_bin (STR ''0101'')))
             T P B G D sa i } \<noteq> {}"
  by eval
*)
end
theory Validator
imports SailEnv Native_Word.Uint32 SailASTUtils ShowAST  "HOL-Library.Debug"
begin

chapter \<open>Sail Validator\<close>

(* We use the nesting for aux params; different from MS+. Any preference? *)

(* First limit to small subset of Sail that is equivalent, modulo type syntax, to MiniSail *)

(* Debugging with traces - the order that the Isabelle code generator puts the premises is
not the same textual order in the theory file 

In the Sail implementation, the function check_exp annotates the expression with the type being checked against and infer_exp 
annotates the expression with the type inferred.
Thus when checking the annotated expression, we do we subtype check between the 'lower' type (which is for example the type of a function return if we 
are at an E_app node and type on the ast)
*)

section \<open>Wellformedness\<close>

text \<open>Use mutual recursion to make this align with MiniSail's equivalent\<close>

inductive wfNE :: "env \<Rightarrow> nexp \<Rightarrow> kind \<Rightarrow> bool" and 
          wfNC :: "env \<Rightarrow> n_constraint \<Rightarrow> bool" and 
          wfTyp :: "env \<Rightarrow> typ \<Rightarrow> bool" and 
          wfLocals :: "env \<Rightarrow> (id*mut*typ) list \<Rightarrow> bool" and 
          wfE :: "env \<Rightarrow> bool"
where

wfNE_constI: "wfNE env ( (Nexp_constant n ) )  K_int"

| wfNE_timesI:"\<lbrakk>
  wfNE env nexp1 ( K_int);
  wfNE env nexp2 ( K_int)
\<rbrakk> \<Longrightarrow> wfNE env ( (Nexp_times nexp1 nexp2 ) ) ( K_int)"

| wfNE_sumI:"\<lbrakk>
  wfNE env nexp1 ( K_int );
  wfNE env nexp2 ( K_int )
\<rbrakk> \<Longrightarrow> wfNE env ( (Nexp_sum nexp1 nexp2 ) ) ( K_int )"

| wfNE_minusI:"\<lbrakk>
  wfNE env nexp1 ( K_int );
  wfNE env nexp2 ( K_int )
\<rbrakk> \<Longrightarrow> wfNE env ( (Nexp_minus nexp1 nexp2 ) ) ( K_int )"

| wfNE_kid: "\<lbrakk> Some ( kind ) = lookup (typ_vars env) kid 
\<rbrakk> \<Longrightarrow> wfNE env ( (Nexp_var kid) ) kind"

| wfNC_eqI: "\<lbrakk> wfNE env nexp1 k1 ; wfNE env nexp2 k2 \<rbrakk> \<Longrightarrow>  wfNC env ( (NC_equal nexp1 nexp2) )" 

| wfTyp_idI: "Some kd = lookup (typ_vars env) x \<Longrightarrow> wfTyp env ( ( Typ_var x)  )"
| wfTyp_fnI: "wfTyp env ( (Typ_fn typs_in  typ_ret _ )   )"   
| wfTyp_bidirI: "wfTyp env ( (Typ_bidir t1 t2 _ )  )"
| wfTyp_tup: "wfTyp env ( (Typ_tup typs)  )"  
| wfTyp_app: "wfTyp env ( (Typ_app x args  )  )"
| wfTyp_exist: "wfTyp env ( (Typ_exist kids nc t  )  )"

| wfLocals_nilI: "wfLocals env []"
| wfLocals_consI: "\<lbrakk>
  wfTyp env typ;
  wfLocals env locs
\<rbrakk> \<Longrightarrow> wfLocals env ((x,(mut,typ))#locs)"

| wfEI: "wfLocals env (locals env) \<Longrightarrow> wfE env"

(* Processing this doesn't terminate but it isn't complicated ?? *)
code_pred (modes: 
            wfNE:  i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
            wfNC: i \<Rightarrow> i \<Rightarrow> bool and
            wfTyp : i \<Rightarrow> i \<Rightarrow> bool and
            wfLocals : i \<Rightarrow> i \<Rightarrow> bool and
            wfE : i \<Rightarrow> bool )  [show_steps,  show_mode_inference,  show_invalid_clauses] wfNC .

section \<open>Subtyping\<close>


hide_const id

fun  env_of :: "tannot exp \<Rightarrow> env option" where
  "env_of exp  = get_env (annot_e exp)"

fun  type_of_exp_lb :: "tannot letbind \<Rightarrow> typ option" where
  "type_of_exp_lb lb = get_type (annot_letbind lb)"

(*fun get_e :: "tannot exp \<Rightarrow> (env*typ) option" where
  "get_e ( _ tan) = get tan"
*)
fun env_of_lb :: "tannot letbind \<Rightarrow> env option" where
  "env_of_lb lb = get_env (annot_letbind lb)"

(* FIXME NEed to compare x and y \<Or> *)
inductive eq_id :: "id \<Rightarrow> id \<Rightarrow> bool" where
"x = y \<Longrightarrow> eq_id ( (id x) ) ( (id y) )"

code_pred (modes: 
       eq_id  : i \<Rightarrow> i \<Rightarrow> bool ) eq_id .

value "eq_id (id (STR ''int'')) (id (STR ''unit''))"

(* Smart constructors. These are borrowed from sail/src/type_check.ml *)

inductive eq_kid :: "kid \<Rightarrow> kid \<Rightarrow> bool" where
"x = y \<Longrightarrow> eq_kid ( (var x) ) ( (var y) )"

definition nc_and :: "n_constraint \<Rightarrow> n_constraint \<Rightarrow> n_constraint" where
 "nc_and nc1 nc2 \<equiv>  (NC_and nc1 nc2) "

definition nc_or :: "n_constraint \<Rightarrow> n_constraint \<Rightarrow> n_constraint" where
 "nc_or nc1 nc2 \<equiv>  (NC_or nc1 nc2) "

definition mk_id where  "mk_id x =  (id (String.implode x))"

definition arg_bool where "arg_bool nc =  (A_bool nc)"

definition nc_not :: "n_constraint \<Rightarrow> n_constraint" where
 "nc_not nc \<equiv>  (NC_app (mk_id ''not'') [ arg_bool nc ] ) "

definition nc_between :: "nexp \<Rightarrow> nexp \<Rightarrow> nexp \<Rightarrow> n_constraint" where
 "nc_between n1 n n2 = nc_and ( (NC_bounded_le n1 n) ) ( (NC_bounded_ge n n1) )"

definition nc_ge_zero :: "nexp \<Rightarrow> n_constraint" where
 "nc_ge_zero  n  =  ( (NC_bounded_ge n (Nexp_constant 0) ))"

definition nc_bool_equiv :: "n_constraint \<Rightarrow> n_constraint \<Rightarrow> n_constraint" where
 "nc_bool_equiv nc1 nc2 = (nc_or (nc_and nc1 nc2) (nc_and (nc_not nc1) (nc_not nc2)))"


inductive 
match :: "typ \<Rightarrow> typ \<Rightarrow> n_constraint list  \<Rightarrow> bool" and
match_list :: "typ list \<Rightarrow> typ list \<Rightarrow> n_constraint list  \<Rightarrow> bool" and
match_arg :: "typ_arg \<Rightarrow> typ_arg \<Rightarrow> n_constraint list  \<Rightarrow> bool" and
match_arg_list :: "typ_arg list \<Rightarrow> typ_arg list \<Rightarrow> n_constraint list  \<Rightarrow> bool" and
match_nc :: "n_constraint \<Rightarrow> n_constraint  \<Rightarrow> n_constraint list  \<Rightarrow> bool" and
match_nexp :: "nexp \<Rightarrow> nexp  \<Rightarrow> n_constraint list  \<Rightarrow> bool"
where

(* match_arg *)
match_arg_typ: "match t1 t2 ms \<Longrightarrow> match_arg ( (A_typ t1) ) ( (A_typ t2) ) ms"

| match_arg_nexpI: "match_nexp ne1 ne2 ms \<Longrightarrow> match_arg ( (A_nexp ne1) ) ( (A_nexp ne2) ) ms" 

| match_arg_ncI: "match_nc nc1 nc2 ms \<Longrightarrow> match_arg ( (A_bool nc1) ) ( (A_bool nc2) ) ms" 

| match_arg_orderI: "match_arg ( (A_order ord)) ( (A_order ord)) []"

(* match arg list *)
| match_arg_list_nilI: "match_arg_list [] [] []"

| match_arg_list_consI:
  "\<lbrakk> 
      match_arg a1 a2  ms1;
      match_arg_list as1 as2 ms2
\<rbrakk> \<Longrightarrow> match_arg_list (a1#as1) (a2#as2) ((ms1@ms2))"

(* match *)

| match_appI: "\<lbrakk> match_arg_list args1 args2 ms ;  eq_id id1 id2 
\<rbrakk> \<Longrightarrow> match ( (Typ_app id1 args1)  ) ( (Typ_app id2 args2) ) ms"

(* In the example with ast we some times get Ty_id ast and sometimes Ty_app ast [] *)
| match_app1I: "\<lbrakk> eq_id id1 id2 
\<rbrakk> \<Longrightarrow> match ( (Typ_id id1 )  ) ( (Typ_app id2 []) ) []"

| match_app2I: "\<lbrakk>  eq_id id1 id2 
\<rbrakk> \<Longrightarrow> match ( (Typ_app id1 [])  ) ( (Typ_id id2) ) []"

| match_idI: "\<lbrakk>  eq_id id1 id2 
\<rbrakk> \<Longrightarrow> match ( (Typ_id id1)  ) ( (Typ_id id2) ) []"

(* FIXME allow for unification / where one side is concrete type *)
| match_varI: "\<lbrakk>  eq_kid kid1 kid2 
\<rbrakk> \<Longrightarrow> match ( (Typ_var kid1) ) ( (Typ_var kid2) ) []"

| match_var_leftI: " match ( (Typ_var kid1) ) _ []"

| match_var_rightI: " match _ ( (Typ_var kid2) ) []"

| match_tupleI: "\<lbrakk> match_list ts1 ts2 bs
\<rbrakk> \<Longrightarrow> match ( (Typ_tup ts1)) ( (Typ_tup ts2)) bs"

(* FIXME - Need a smarter way of doing this *)
| match_intI: "
  match ( (Typ_id ( (id (STR ''int'')) )) ) ( (Typ_app ( (id (STR ''atom'')) ) _ ) ) []" (* What goes here? *)

| match_intI2: "
  match  ( (Typ_app ( (id (STR ''atom'')) ) _) ) 
                  ( (Typ_id ( (id (STR ''int'')) )) ) [ (NC_true) ]"    

| match_nat_intI: "
  match  ( (Typ_id ( (id (STR ''nat'')) ) ) ) 
                  ( (Typ_id ( (id (STR ''int'')) )) ) [ (NC_true) ]"     

| match_nat1I: "
  match ( (Typ_app ( (id (STR ''atom'')) ) [ (A_nexp nexp )] )) ( (Typ_id ( (id (STR ''nat'')) )) )  [ nc_pos nexp ]" 

| match_nat2I: "
  match (Typ_id ( (id (STR ''nat'')) ))  (Typ_app ( (id (STR ''atom'')) )[ A_nexp nexp ] ) []" (* What goes here? ne \<ge> 0 ?? *)

| match_nat_range: "
  match 
         ( (Typ_app ( (id (STR ''range'')) ) [( (A_nexp ne1) ),( (A_nexp ne2) )]) ) 
         (Typ_id ( (id (STR ''nat'')) ))  
         [ nc_ge_zero ne1, nc_ge_zero ne2 ]"

(* FIXME. Wrong *)
| match_range1I: "
  match  ( (Typ_app ( (id (STR ''atom'')) ) [( (A_nexp ne) ) ]) )  
         ( (Typ_app ( (id (STR ''range'')) ) [( (A_nexp ne1) ),( (A_nexp ne2) )]) )  [ nc_between ne1 ne ne2 ]"

| match_range2I: "
  match 
         ( (Typ_app ( (id (STR ''range'')) ) [( (A_nexp ne1) ),( (A_nexp ne2) )]) ) 
         ( (Typ_app ( (id (STR ''atom'')) ) [( (A_nexp ne) ) ]) )  
         [ nc_between ne1 ne ne2 ]"

| match_range3I: "
  match 
         ( (Typ_app ( (id (STR ''range'')) ) [( (A_nexp ne1) ),( (A_nexp ne2) )]) ) 
         ( (Typ_id ( (id (STR ''int'')) ) ) )  
         [  NC_true ]"

| match_boolI1: "
  match  ( (Typ_app ( (id (STR ''atom_bool'')) ) _ ) ) ( (Typ_id ( (id (STR ''bool'')) )) ) [ (NC_true) ]"

| match_bool21: "
  match   ( (Typ_id ( (id (STR ''bool'')) )) ) ( (Typ_app ( (id (STR ''atom_bool'')) ) [ (A_bool nc) ])) [nc ]"

(* match list *)
| match_list_nilI: "match_list [] [] []"

| match_list_consI: "\<lbrakk>
  match t1 t2 b;
  match_list ts1 ts2 bs
\<rbrakk> \<Longrightarrow> match_list (t1#ts1) (t2#ts2) (b@bs)"

(* match nexp *)

| match_nexp: "match_nexp ne1 ne2 [  (NC_equal ne1 ne2) ]"

(* match nc *)

| match_ncI: "match_nc nc1 nc2 [(nc_bool_equiv nc1 nc2)]"

(*
| "\<lbrakk> eq_kid kid1 kid2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_var kid1) ) ( (NC_var kid2) ) ([])"
| "\<lbrakk> match_nexp ne1 ne1' ms1 ; match_nexp ne2 ne2' ms2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_equal ne1 ne2) ) ( (NC_equal ne1' ne2') ) (ms1@ms2)"
| "\<lbrakk> match_nexp ne1 ne1' ms1 ; match_nexp ne2 ne2' ms2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_bounded_ge ne1 ne2) ) ( (NC_bounded_ge ne1' ne2') ) (ms1@ms2)"
| "\<lbrakk> match_nexp ne1 ne1' ms1 ; match_nexp ne2 ne2' ms2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_bounded_gt ne1 ne2)) ( (NC_bounded_gt ne1' ne2') ) (ms1@ms2)"
| "\<lbrakk> match_nexp ne1 ne1' ms1 ; match_nexp ne2 ne2' ms2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_bounded_le ne1 ne2) ) ( (NC_bounded_le ne1' ne2') )  (ms1@ms2)"
| "\<lbrakk> match_nexp ne1 ne1' ms1 ; match_nexp ne2 ne2' ms2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_bounded_lt ne1 ne2)) ( (NC_bounded_lt ne1' ne2') ) (ms1@ms2)"
| "\<lbrakk> match_nexp ne1 ne1' ms1 ; match_nexp ne2 ne2' ms2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_not_equal ne1 ne2) ) ( (NC_not_equal ne1' ne2') ) (ms1@ms2)"
| "\<lbrakk> match_nc nc1 nc1' ms1 ; match_nc nc2 nc2' ms2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_or nc1 nc2) ) ( (NC_or nc1' nc2') ) (ms1@ms2)"
| "\<lbrakk> match_nc nc1 nc1' ms1 ; match_nc nc2 nc2' ms2 \<rbrakk> \<Longrightarrow> match_nc  ( (NC_and nc1 nc2) ) ( (NC_and nc1' nc2')) (ms1@ms2)"
| "match_nc ( NC_true) ( NC_true) []"
| "match_nc ( NC_false) ( NC_false) []"
*)
(*
| match_nexp_consI: "match_nexp ( (Nexp_constant c) _) ( (Nexp_constant c) _) []"
| match_nexp_varI: "eq_kid kid1 kid2 \<Longrightarrow> match_nexp  ( (Nexp_var kid1) _) ( (Nexp_var kid2) _) []"
| match_nexp_sumI: "\<lbrakk> match_nexp ne1 ne1' ms1; match_nexp ne2 ne2' ms2 \<rbrakk> \<Longrightarrow> match_nexp ( (Nexp_sum ne1 ne2 ) _) ( (Nexp_sum ne1' ne2') _) (ms1@ms2)"
*)

(* FIXME. This is a bit hacky. Need to be clear on what we are normalising and why *)
inductive normalise :: "env \<Rightarrow> typ \<Rightarrow> typ \<Rightarrow> bool" and
         normalise_list :: "env \<Rightarrow> typ list \<Rightarrow> typ list \<Rightarrow> bool" where
"normalise env ( ( Typ_exist x y z)) (Typ_exist x y z)"
| "normalise env ( ( Typ_id i)) (Typ_exist [] ( NC_true) ( (Typ_id i)))"
| "normalise env ( ( Typ_var k)) (Typ_exist [] ( NC_true) ( (Typ_var k )))"
| "normalise env ( ( Typ_tup ts1)) (Typ_exist [] ( NC_true) ( (Typ_tup ts1)))"
| "normalise env ( ( Typ_app idd tas)) (Typ_exist [] ( NC_true) ( (Typ_app idd tas)))"
(*| "normalise env t1 t2 \<Longrightarrow> normalise env ( Typ_app (id (STR ''implicit'')) [ A_typ t1 ] ) t2"*)
| "normalise_list env [] []"
| "\<lbrakk> normalise env t1 t2 ; normalise_list env ts1 ts2 \<rbrakk> \<Longrightarrow> normalise_list env (t1#ts1) (t2#ts2)"

section \<open>Printing\<close>

fun trace :: "char list \<Rightarrow> bool" where
  "trace s = (let _ = Debug.trace (String.implode s) in True)"

fun nc_and_list :: "n_constraint list \<Rightarrow> n_constraint" where
"nc_and_list ncs = List.fold nc_and ncs ( NC_true)"


(*
fun pp_typ :: "typ \<Rightarrow> string" where
"pp_typ ( (Typ_exist _ _ _ )) = STR ''Typ_exist''"
| "pp_typ ( (Typ_app ( (id x)) _ )) = STR ''Typ_app'' + x"
| "pp_typ _ = STR ''typ''"
*)

(* FIXME - Should add 'call out' to SMT solver *)
inductive subtype :: "env \<Rightarrow> typ \<Rightarrow> typ \<Rightarrow> bool" where
"\<lbrakk> 
  normalise env t1 (Typ_exist k1 nc1 t1');
  normalise env t2 (Typ_exist k2 nc2 t2');
  trace (''t1='' @ show t1 @ '' t2='' @ show t2);
  trace (''t1'='' @ show t1' @ '' t2'='' @ show t2');
  match t1' t2' bs;
  trace (''ncs='' @ (List.concat (List.map show bs))) ;
  prove env (nc_and_list bs)
\<rbrakk> \<Longrightarrow> subtype env t1 t2"


inductive subtype_exp :: "tannot exp \<Rightarrow> typ \<Rightarrow> bool" where
"\<lbrakk>
    Some env = get_env_exp exp;
    Some typ1 = type_of_exp exp;
    subtype env typ1 typ2
\<rbrakk> \<Longrightarrow> subtype_exp exp typ2"

code_pred (modes: 
       subtype : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       subtype_exp : i \<Rightarrow> i \<Rightarrow> bool and
       match : i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
       match_list : i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
       match_nc : i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
       match_arg : i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
       match_arg_list : i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool

)  [show_steps,  show_mode_inference,  show_invalid_clauses] subtype .

value "bool_typ True"


values "{ms . match unit_typ unit_typ ms}"

values "{ms . match (bool_typ True) (bool_typ True) ms}"

values "{ms . match_nexp ( (Nexp_constant 10)) ( (Nexp_constant 10)) ms }"

values "{ms . match_arg_list [ ( (A_nexp ( (Nexp_constant 10))))] [ ( (A_nexp ( (Nexp_constant 10))))] ms }"

values "{ms . match ( (Typ_app ( (id (STR ''atom''))) [ (A_nexp ( (Nexp_constant 10)))]))
                    ( (Typ_app ( (id (STR ''atom''))) [ (A_nexp ( (Nexp_constant 11)))])) ms }"

values "{ms . match ( (Typ_app ( (id (STR ''atom_bool''))) [arg_bool ( NC_true) ]))
                    ( (Typ_app ( (id (STR ''atom_bool''))) [arg_bool ( NC_false)])) ms }"

section \<open>Checking\<close>

subsection \<open>Literals\<close>

fun integer_of_int2 :: "int \<Rightarrow> integer" where
  "integer_of_int2 x = integer_of_int x"

inductive check_lit :: "env \<Rightarrow> lit \<Rightarrow> typ \<Rightarrow> bool" where
check_lit_unitI: "check_lit env ( L_unit ) ( (Typ_id ( (id (STR ''unit'')) ) ) )" 

| check_lit_realI: "check_lit env ( L_real _  ) ( (Typ_id ( (id (STR ''real'')) ) ) )" 

(* FIXME Should check typ is mono? *)
| check_lit_undefI: "check_lit env  L_undef typ " 

| check_lit_numI: "check_lit env ( (L_num num)  ) ( (Typ_app ( (id (STR ''atom''))  ) 
     [( (A_nexp ( (Nexp_constant num)  ))  ) ] )  )"

| check_lit_trueI: "check_lit env ( L_true  ) ( (Typ_app ( (id (STR ''atom_bool''))  ) 
     [( (A_bool ( NC_true  ))  ) ] )  )"

| check_lit_falseI: "check_lit env ( L_false  ) ( (Typ_app ( (id (STR ''atom_bool''))  ) 
     [( (A_bool ( NC_false  ))  ) ] )  )"

(* FIXME - Sail doesn't do a precise type for this *)
| check_lit_bitoneI: "check_lit env ( L_one ) ( (Typ_id ( (id (STR ''bit''))  ) ))"
| check_lit_bitzeroI: "check_lit env ( L_zero ) ( (Typ_id ( (id (STR ''bit''))  ) ))"

(* FIXME check order matches the one set in the environment? *)
| check_lit_binI: "check_lit env ( (L_bin s)  ) ( (Typ_app ( (id (STR ''bitvector'')) ) 
     [( (A_nexp ( (Nexp_constant (integer_of_int2 ( (int (length (String.explode s)))))) )) ) ,  (A_order ( _ ))    ])  )"

(* Why do I have to flip integer_of_int to int ? integer_of_int for when using SailAST session *)
| check_lit_hexI: "check_lit env ( (L_hex s)  ) ( (Typ_app ( (id (STR ''bitvector''))  ) 
     [( (A_nexp ( (Nexp_constant (4*( (integer_of_int2 (int (length (String.explode s))))))) )) ) ,  (A_order ( _ ))    ])  )"

| check_lit_stringI: "check_lit env ( (L_string _)) ( (Typ_id ( (id (STR ''string'')))))"


code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool) check_lit .

values [expected "{()}"] "{ True. check_lit emptyEnv ( L_unit )  unit_typ  }"

values [expected "{()}"] "{ True. check_lit emptyEnv ( (L_num 43) )  (num_typ 43)  }"



(* cf type_checker.subtyp. Call type_checker.subtype_check or need to capture what subtyp does? *)
(*inductive subtype :: "env \<Rightarrow> typ \<Rightarrow> typ \<Rightarrow> bool" where
"subtype env t1 t2"*)


fun print_type :: "typ \<Rightarrow> bool" where
  "print_type _ = True"

code_printing
  constant subtype \<rightharpoonup>  (OCaml) "Type'_check.subtype'_check" 

code_printing
  constant print_type \<rightharpoonup>  (OCaml) "Utils2.print'_type" 

type_synonym bindings = "(id*mut*typ) list"

fun locals_in :: "env \<Rightarrow> bindings \<Rightarrow> bool" where
  "locals_in _ [] = True"
| "locals_in env ((x,mut,typ)#gs)  = (case  lookup_local_id_env env x of
                                       Some t \<Rightarrow> locals_in env gs  | None \<Rightarrow> False)"

subsection \<open>Patterns\<close>

inductive 
  check_pat :: "env \<Rightarrow> tannot pat \<Rightarrow> typ \<Rightarrow> bindings \<Rightarrow> bool" ( "_ \<turnstile> _ : _ \<leadsto> _" ) and
  check_pat_s ::  "env \<Rightarrow> tannot pat \<Rightarrow> typ \<Rightarrow> bindings \<Rightarrow> bool" ( "_ |~ _ : _ \<leadsto> _" ) and
  check_pat_list :: "tannot pat list \<Rightarrow> bindings \<Rightarrow> bool"
  where

check_pat_sI: "\<lbrakk>
  trace (''check_pat_sI t='' @ show t @ '' t' = '' @ show t');
  Some (env',t') = env_type_of_pat pat;
  subtype env t' t;
  check_pat env' pat t' bs
\<rbrakk> \<Longrightarrow> check_pat_s env pat t bs"

| check_pat_litI: "\<lbrakk> 
   trace (''check_pat_litI t='' @ (show t));
   check_lit env lit t \<rbrakk> \<Longrightarrow> check_pat env ( (P_lit tan lit)) t []"

| check_pat_wildI: "check_pat env ( P_wild _ ) t []"

| check_pat_orI: "\<lbrakk>
   check_pat_s env p1 t bs1;
   check_pat_s env p2 t bs2
\<rbrakk> \<Longrightarrow> check_pat env ( (P_or _ p1 p2) ) t (bs1@bs2)"

| check_pat_notI: "\<lbrakk>
   check_pat env p1 t bs1
\<rbrakk> \<Longrightarrow> check_pat env ( (P_not _ p1)  ) t (bs1)"

| check_pat_asI:"check_pat env pat t bindings \<Longrightarrow> check_pat env ( (P_as  _ pat _)  ) t bindings" (* FIXME *)

| check_pat_typI:"check_pat env pat t bindings  \<Longrightarrow> check_pat env ( (P_typ _ _ pat)  ) t bindings"

| check_pat_idI: "\<lbrakk>      
      trace ''check_pat_idI'';
      None = lookup_enum_env env x
 \<rbrakk> \<Longrightarrow> check_pat env ( (P_id tan x)  ) t [(x,Immutable,t)] "

| check_pat_enumI: "\<lbrakk> 
      Some t2 = lookup_enum_env env x ;      
      subtype env t2 t1
\<rbrakk> \<Longrightarrow> check_pat env ( (P_id tan x)  ) t1 [] "

(* FIXME check typ pat *)
| check_pat_varI:"\<lbrakk>
   check_pat env pat t bindings
\<rbrakk> \<Longrightarrow> check_pat env ( (P_var _ pat _ )  ) t bindings"

(* FIXME Need to get and check type for ctor*)
| check_pat_appI:"\<lbrakk>
   check_pat env parg t bindings
\<rbrakk> \<Longrightarrow> check_pat env ( (P_app _ ctor [ parg ])  ) t bindings"

| check_pat_vectorI: "\<lbrakk>
   check_pat_list pats bs
\<rbrakk> \<Longrightarrow> check_pat env ( (P_vector _ pats) ) t bs"

| check_pat_vector_concatI: "\<lbrakk>
   check_pat_list pats bs
\<rbrakk> \<Longrightarrow> check_pat env ( (P_vector_concat _ pats) ) t bs"

| check_pat_tupI: "\<lbrakk>
   check_pat_list pat_list bindings
\<rbrakk> \<Longrightarrow> check_pat env ( (P_tup _ pat_list) ) t bindings"

| check_pat_listI: "\<lbrakk>
   check_pat_list pat_list bindings
\<rbrakk> \<Longrightarrow> check_pat env ( (P_list _ pat_list) ) t bindings"

| check_pat_consI: "\<lbrakk>
   check_pat env p1 t bs1;
   check_pat env p2 t bs2
\<rbrakk> \<Longrightarrow> check_pat env (  (P_cons _ p1 p2)  ) t (bs1@bs2)"

| check_pat_string_appendI: "\<lbrakk>
   check_pat_list pat_list bindings
\<rbrakk> \<Longrightarrow> check_pat env ( (P_string_append _ pat_list) ) t bindings"

| check_pat_list_nilI: "check_pat_list [] []"
| check_pat_list_consI: "\<lbrakk>
   Some (env,t) = env_type_of_pat pat;
   check_pat env pat t bindings1;
   check_pat_list pats bindings2
\<rbrakk> \<Longrightarrow> check_pat_list (pat#pats) (bindings1@bindings2)"


code_pred (modes: check_pat: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
                   check_pat_s: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool) [show_steps,  show_mode_inference,  show_invalid_clauses] check_pat .

values "{ x . check_pat emptyEnv (P_lit (set_type None unit_typ) L_unit) unit_typ x }"

text \<open>The type we get from the type annotation on a node is a subtype of the supplied type \<close>
inductive subtype_tan :: "typ \<Rightarrow> tannot \<Rightarrow> bool" where
"\<lbrakk> Some env = get_env tan ; Some t' = get_type tan ; subtype env  t t' \<rbrakk> \<Longrightarrow> subtype_tan t tan"

subsection \<open>L-values\<close>


subsection \<open>Expressions\<close>

inductive  check_lexp_vector_list :: "(tannot lexp) list \<Rightarrow> order \<Rightarrow> typ \<Rightarrow> bool" where

check_lexp_vector_list_nilI: "check_lexp_vector_list [] _ _ "

| check_lexp_vector_list_consI: "\<lbrakk>
Some t = type_of_lexp lexp;
Some (_, order, typ) = deconstruct_vector_type t;
check_lexp_vector_list lexps order typ
\<rbrakk> \<Longrightarrow> check_lexp_vector_list (lexp#lexps) order typ"

inductive check_local_binds :: "(tannot exp) list \<Rightarrow>  bindings  \<Rightarrow> bool" where
"check_local_binds [] _ "

| "\<lbrakk> Some env = get_env_exp exp;
     locals_in env bindings;
     check_local_binds exps bindings
\<rbrakk> \<Longrightarrow> check_local_binds (exp#exps) bindings"

(*
fun deconstruct_assign :: "tannot exp \<Rightarrow> (tannot lexp * tannot exp) option" where
 "deconstruct_assign ( (E_assign lexp exp) _) = Some (lexp,exp)"
| "deconstruct_assign _ = None"

fun not_assign  :: "tannot exp \<Rightarrow> bool" where
 "not_assign ( (E_assign lexp exp) _) = False"
| "not_assign _ = True"
*)

fun add_locals :: "env \<Rightarrow> bindings \<Rightarrow> env" where
  "add_locals env _ = env"

text \<open>Second environment contains at the least the bindings that the first does and the constraints FIXME\<close>
inductive subenv :: "env \<Rightarrow> env \<Rightarrow> bool" where

"subenv e1 e2"

definition exception_typ where
  "exception_typ =  ( (Typ_id ( (id (STR ''exception'')))))"

(* Should I make this more like the Ott definition? *)
inductive check_exp :: "env \<Rightarrow> tannot exp \<Rightarrow> typ \<Rightarrow> bool" ( "_ \<turnstile> _ :  _") and
          check_exp_s :: "env \<Rightarrow> tannot exp \<Rightarrow> typ \<Rightarrow> bool" ( "_ |~ _ :  _") and
          check_exp_list :: "(tannot exp) list \<Rightarrow> typ list \<Rightarrow> bool" and 
         
          check_pexp :: "env \<Rightarrow> tannot pexp \<Rightarrow> typ \<Rightarrow> typ \<Rightarrow> bool" ( " _ \<turnstile> _ : _  / _") and
          check_pexp_s :: "env \<Rightarrow> tannot pexp \<Rightarrow> typ \<Rightarrow> bool" ( "_ |~  _ : _") and
          check_pexps :: "env \<Rightarrow> tannot pexp list \<Rightarrow> typ \<Rightarrow> typ \<Rightarrow> bool" ( "_ \<turnstile> _ : _ / _")  and
         
          check_letbind :: "tannot letbind \<Rightarrow> bindings \<Rightarrow> bool" ( "\<turnstile> _ \<leadsto> _") and 
          check_fexp :: "tannot fexp \<Rightarrow> typ \<Rightarrow> bool" ( "\<turnstile> _ <: _ ") and
          check_fexp_list :: "tannot fexp list \<Rightarrow> typ \<Rightarrow> bool" and 
        
      
          check_lexp :: "env \<Rightarrow> tannot lexp \<Rightarrow> typ \<Rightarrow> bindings \<Rightarrow> bool"  ( " _ \<turnstile> _ : _ \<leadsto> _") and
          check_lexp_list :: "(tannot lexp) list \<Rightarrow> bindings \<Rightarrow> bool" and
          check_exp_bindings :: "tannot exp \<Rightarrow> bindings \<Rightarrow> bool" 
where

(* FIXME NEed to check env *)
check_exp_sI: "\<lbrakk>
     trace ''check_exp_sI'';
     Some (e,t) = env_type_of_exp exp;
     trace (''check_exp_sI t='' @ (show t));
     subtype e t t';
     e \<turnstile> exp : t
\<rbrakk> \<Longrightarrow> e' |~ exp : t'"

(* CHECK LEXP *)
| check_lexp_id_notbI:"\<lbrakk>   
   trace ''check_lexp_id_notbI'';  
   None = lookup_mutable E x
\<rbrakk> \<Longrightarrow> E \<turnstile> ( (LEXP_id tan x) ) : t \<leadsto> [ (x,Mutable,t) ]" 

| check_lexp_id_bI:"\<lbrakk>   
   trace ''check_lexp_id_bI'';
   Some t2 = lookup_mutable env x;
   trace (''check_lexp_id_bI found mut'' @ show t2);
   subtype env t1 t2;
   trace (''check_lexp_id_bI subtype ok'')
\<rbrakk> \<Longrightarrow> env \<turnstile> ( (LEXP_id tan x)  ) : t1 \<leadsto> []" 

(* 
   We need the following to work: 
            y : nat = 10 : range(0,10)
            y : range(1,100) = 100
   The type on the annot is the type of rhs, this needs to be the lowest type.
   If y is already registered as a mutable, then it is the highest type, otherwise its the cast.

  *)
| check_lexp_cast_notbI:"\<lbrakk>  
   None = lookup_mutable env x;
   subtype env t' t
\<rbrakk> \<Longrightarrow> env \<turnstile> ( (LEXP_cast tan t x)  ) : t' \<leadsto> [ (x,Mutable,t) ]" 


| check_lexp_cast_bI:"\<lbrakk> 
   Some t'' = lookup_mutable env x;  
   subtype env t' t;
   subtype env t t''
\<rbrakk> \<Longrightarrow> env \<turnstile> ( (LEXP_cast tan t x)  ) : t' \<leadsto>  []" 

| check_lexp_derefI: "\<lbrakk>    
    Some (e,t) = env_type_of_exp exp;
    e \<turnstile> exp : t;    
    Some t1 = deconstruct_register_type t;  
    subtype e  t2 t1
\<rbrakk> \<Longrightarrow> env \<turnstile> (LEXP_deref tan exp) : t2 \<leadsto>  []"

| check_lexp_list_nilI: "\<lbrakk>
   trace ''check_lexp_list_nilI''
\<rbrakk> \<Longrightarrow>
   check_lexp_list [] [] "

| check_lexp_list_consI: "\<lbrakk>
    trace ''check_lexp_list_consI'';
    Some (env,typ) = env_type_of_lexp lexp;
    env \<turnstile> lexp : typ \<leadsto> binding;  
    check_lexp_list lexps bindings
\<rbrakk> \<Longrightarrow>   check_lexp_list (lexp#lexps) (binding@bindings)"


| check_lexp_tupI: "\<lbrakk>
    trace ''check_lexp_tupI'';  
    check_lexp_list lexps bindings;
    Some ts1 = those (List.map (\<lambda>l. type_of_lexp l) lexps);
    trace (''check_lexp_tupI types='' @ show ts1);
    subtype_tan ( (Typ_tup ts1) ) tan
\<rbrakk> \<Longrightarrow> env \<turnstile> (LEXP_tup tan lexps) : t2 \<leadsto>  bindings"

(*
| check_lexp_tupI: "\<lbrakk>
    trace ''check_lexp_tupI'';
    Some env = get_env tan;
    check_lexp_list lexps bindings
\<rbrakk> \<Longrightarrow> check_lexp ( (LEXP_tup lexps) tan) bindings"
*)
| check_lexp_vector_concatI: "\<lbrakk>
    trace ''check_lexp_vector_concatI'';  
    Some (nexp, order, typ) = is_vector_type tan;
    check_lexp_list lexps bindings;
    check_lexp_vector_list lexps order typ
\<rbrakk> \<Longrightarrow> env \<turnstile> (LEXP_vector_concat tan lexps) : t \<leadsto> bindings"


| check_lexp_vectorI: "\<lbrakk>
   trace ''check_lexp_vectorI'';  
   Some (env2,t) = env_type_of_lexp lexp;
   env \<turnstile> lexp : t \<leadsto> bindings;
   trace ''check_lexp_vectorI 2''; 
   trace (''check_lexp_vectorI vectype='' @ show t);
   Some (nexp', order, typ) = deconstruct_vector_type t;
   trace (''check_lexp_vectorI typ='' @ show typ);
   Some (ee,te) = env_type_of_exp exp;
   ee \<turnstile> exp : te;
   subtype ee te int_typ
\<rbrakk> \<Longrightarrow> env \<turnstile> (LEXP_vector tan lexp exp) : typ \<leadsto> bindings"

| check_lexp_vector_rangeI: "\<lbrakk>   
    env |~  exp1 : int_typ;
    env |~  exp2 : int_typ;
    Some (env1,t1) = env_type_of_lexp lexp;  
    env1 \<turnstile> lexp : typ \<leadsto> bindings ;
    Some (nexp', order, typ) = deconstruct_vector_type t1;
    Some (nexp , order, typ) = deconstruct_vector_type t2
\<rbrakk> \<Longrightarrow> env \<turnstile> ( (LEXP_vector_range tan lexp exp1 exp2) ) : t2 \<leadsto> []"

(* Get type of field x from typ and environment, check exp is a subtype *)
(* The fexp doesn't have an evironment, the exp inside does *)
| check_fexpI: "\<lbrakk>
  Some recid = deconstruct_record_type rtyp;
  Some env = get_env_exp exp;
  Some t2 = lookup_record_field_env env recid x;
  env |~ exp : t2
\<rbrakk> \<Longrightarrow> check_fexp ( (FE_Fexp tan x exp)) rtyp"


(* CHECK FEXP LIST *)

| check_fexp_list_nillI: "check_fexp_list [] _"

| check_fexp_list_consI: "\<lbrakk>
   check_fexp fexp typ;
   check_fexp_list fexp_list typ
\<rbrakk> \<Longrightarrow> check_fexp_list (fexp#fexp_list) typ"

(* FIXME *)
| check_lexp_fieldI: "\<lbrakk>
   Some (env,typ) = env_type_of_lexp lexp;
   env \<turnstile> lexp : typ \<leadsto> bindings
\<rbrakk> \<Longrightarrow>  env' \<turnstile> ( (LEXP_field tan lexp fid ) ) : typ' \<leadsto> []"

(* CHECK EXP *)

(* Value like things *)
| check_litI: "\<lbrakk>
   check_lit env lit t
\<rbrakk>  \<Longrightarrow> env \<turnstile> ( (E_lit tan lit) ) : t"

| check_idI: "\<lbrakk> 
   trace ''check_idI'';
   Some t1 = lookup_id env x;
   subtype env t1 t2
\<rbrakk> \<Longrightarrow> env \<turnstile> ( (E_id tan x)  ) : t2"

(*  subtype env ( (Typ_tup [t1,t2]) ) typ *)
(* Or do we check_exp the components of the tuple and do as line LEXP_vector? *)
| check_tupleI: "\<lbrakk>   
    ( (Typ_tup typs)) = t;
    check_exp_list exps typs      
\<rbrakk> \<Longrightarrow> e  \<turnstile> ( (E_tuple tan exps)   ) : t"

| check_castI: "\<lbrakk>
   E |~ exp : t;
   subtype E t t'
\<rbrakk> \<Longrightarrow>  E \<turnstile> E_cast tan t exp : t'"

(*
| check_exp_env_typI: 
  "\<lbrakk>  \<turnstile> exp \<leadsto> bs;
     Some (e,t) = get_e exp;    
     subtype env t typ;
     subenv env e
\<rbrakk> \<Longrightarrow> check_exp_typ_env env exp typ"

| check_exp_typI: 
  "\<lbrakk>  \<turnstile> exp \<leadsto> bs;    
     subtype_exp  exp typ
\<rbrakk> \<Longrightarrow> check_exp_typ exp typ"
*)
| check_exp_list_nilI: "check_exp_list  [] []"

| check_exp_list_consI: "\<lbrakk>
   Some E = env_of_exp exp;
   E |~  exp : typ;
   check_exp_list  exps typs
\<rbrakk> \<Longrightarrow> check_exp_list (exp#exps) (typ#typs)"

(* \<open>Check the actual arguments against function arguments and check return type,
   with substutition of instantiations, against 'tan' type\<close>
*)
| check_appI: "\<lbrakk>   
    Some (in_typs,rett_typ ) = lookup_fun tan fid;
    trace (''E_app '' @ (show_tannot tan));    
    Some in_typs2 = subst_inst_list tan in_typs;
    trace ''E_app after subst_inst in args'';
    check_exp_list exps in_typs2;
    Some ret_typ2 = subst_inst tan rett_typ;  
    trace ''E_app after subst_inst ret'';  
    trace (''E_app subtype'' @ ''t1='' @ show ret_typ2 @ ''t2='' @ show t);
    subtype_tan ret_typ2 tan
\<rbrakk> \<Longrightarrow> env \<turnstile> E_app tan fid exps : t"



| check_recordI: "\<lbrakk>
   check_fexp_list fexp_list typ   
\<rbrakk> \<Longrightarrow> env \<turnstile> E_record tan fexp_list : typ"

| check_record_updateI: "\<lbrakk>
  E \<turnstile> exp : typ ;
  check_fexp_list fexp_list typ 
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_record_update tan exp fexp_list) : typ"

| check_fieldI: "\<lbrakk> 
   env |~ exp : rtype;
   Some rtype = type_of_exp exp;
   Some recid = deconstruct_record_type rtype;
   Some t2 = lookup_record_field_env env recid fid;
   subtype env t1 t2
\<rbrakk> \<Longrightarrow> env \<turnstile> (E_field tan exp fid) : t1 "

(* Don't need this as it's sugar
| check_sizeofI:
"check_exp ( (E_sizeof nexp) tan )"
*)

(* Type of return stmt can be anything; exp must be return type of function *)
| check_returnI: "\<lbrakk>
   Some r_typ = ret_type tan;
   E |~ exp : r_typ
\<rbrakk> \<Longrightarrow> E \<turnstile> E_return tan exp : t"

(* Type of exit can be anything; exp must be unit *)
| check_exitI: "\<lbrakk> 
   E |~ exp :  unit_typ
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_exit tan exp) : typ"

| check_throwI: "\<lbrakk>
   E |~ exp : exception_typ
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_throw tan exp) : exception_typ"

| check_tryI: "\<lbrakk> 
   E |~ exp : exception_typ;
   check_pexps E pexps unit_typ exception_typ
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_try tan exp pexps) : unit_typ"

| check_refI: "\<lbrakk> 
    Some t1 = lookup_register tan x;
    subtype_tan t1 tan
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_ref tan x) : typ"

| check_vectorI: "\<lbrakk>  
    Some (len,ord,typ) = deconstruct_vector_type vec_typ;
    check_exp_list exps (replicate (length exps) typ);
    prove env (nc_eq (nint (integer_of_int2 (int (length exps)))) (len))
\<rbrakk> \<Longrightarrow> env \<turnstile> (E_vector tan exps) : vec_typ"

(* These are sugar 
| check_vector_accessI:
"check_exp ( (E_vector_access exp1 exp2) tan )"

| check_vector_subrangeI:
"check_exp ( (E_vector_access exp1 exp2) tan )"

| check_vector_updateI:
"check_exp ( (E_vector_access exp1 exp2) tan )"

| check_vector_update_subrangeI:
"check_exp ( (E_vector_update_subrange exp1 exp2 exp3 exp4) tan )"

| check_vector_appendI:
"check_exp ( (E_vector_append exp1 exp2) tan )"
*)

| check_listI: "\<lbrakk> 
  Some elem_typ = is_list_type tan;
  check_exp_list exps (replicate (length exps) elem_typ)
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_list tan exps) : typ"

| check_list_consI: "\<lbrakk>   
  Some elem_typ = is_list_type tan;
  check_exp_list [exp1] [elem_typ];
  E |~ exp2 : t
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_cons tan exp1 exp2)   : t "
 
(* Statement like things - subtype checks *)

| check_letI: "\<lbrakk> 
     trace ''check_letI'';              
     check_letbind lb bindings;
     (add_locals env bindings) |~ exp : t1       
\<rbrakk> \<Longrightarrow> env \<turnstile> (E_let tan lb exp)  : t1"


| check_ifI: "\<lbrakk>   
     env |~ exp1 : bool_all_typ;
     Some t_exp1 = type_of_exp exp1 ;
     Some nc = deconstruct_bool_type t_exp1;
     (add_constraint nc env) |~ exp2 : t;
     (add_constraint (nc_not nc ) env) |~ exp3 : t
\<rbrakk> \<Longrightarrow> env \<turnstile> E_if tan exp1 exp2 exp3 : t"

(* We don't have any information about guard so no flow typing *)
(*
| check_ifI2: "\<lbrakk> 
     check_exp exp1;
     check_exp exp2;
     check_exp exp3;
     Some env = get_env tan;
     Some ( ( (Typ_id ( (id (STR ''bool'')) ) ) )) = type_of_exp exp1
\<rbrakk> \<Longrightarrow> check_exp ( (E_if exp1 exp2 exp3) tan)"
*)

(* FIXME add mvar to E *)
| check_var_castI: "\<lbrakk>     
     trace ''check_var_castI'';
     E |~ exp1 : typ ;
     E |~ exp2 : t2
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_var tan ( (LEXP_cast _ typ mvar)) exp1 exp2) : t2"

| check_var_idI: "\<lbrakk> 
     trace ''check_var_idI'';
     Some (E1,t1) = env_type_of_exp exp1;    
     E1 \<turnstile> exp1 : t1 ;
     E |~ exp2 : t2
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_var tan (LEXP_id _ mvar) exp1 exp2) : t2"

(* FIXME Surely has to be some check of the bindings of lexp in the environment ? *)
| check_assignI:"\<lbrakk>   
     trace ''check_assignI'';
     trace (''check_assignI type_exp='' @ (show t1) @ '' type_lexp ='' @ (show typ));
     Some (e1,t1) = env_type_of_exp exp;
     e1 \<turnstile> exp : t1;
     Some (env,typ) = env_type_of_lexp lexp;      
     env \<turnstile> lexp : typ \<leadsto> b
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_assign tan lexp exp ) : unit_typ"


| check_caseI:"\<lbrakk>
    trace ''check_caseI'';
    Some typ = type_of_exp exp;
    trace (''check_caseI typ='' @ (show typ));
    E |~ exp : typ;
    Some (ep,tp) = get tan;
    trace (''check_caseI tp='' @ (show tp));
    check_pexps E pexps typ tp
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_case tan exp pexps)  : t "


(* FIXME. See while_0.sail test case *)
| check_loop1I: "\<lbrakk>   
   E |~ exp1 : bool_all_typ; 
   Some t1 = type_of_exp exp1 ;   
   Some nc = deconstruct_bool_type t1;
   add_constraint nc E |~ exp2 : unit_typ
\<rbrakk> \<Longrightarrow> E \<turnstile> (E_loop tan lp lm exp1 exp2)  : t "

(*
| check_loop12: "\<lbrakk>
   Some env = get_env tan;
   check_exp exp1;
   check_exp exp2;
   Some ( ( (Typ_id ( (id (STR ''bool''))  )  )  )) = type_of_exp exp1 ;
   Some t2 = type_of_exp exp2; 
   subtype env t2 unit_typ
\<rbrakk> \<Longrightarrow> check_exp ( (E_loop lp  lm exp1 exp2) tan )"
*)

(* basically
      check/deconstruct exp1 and exp2 as numerics.
      check exp3 as numeric
      check exp4 as unit_typ with constraint that x is between exp1 exp2 (for up, reversed for down) using new type-level variable for x
 Do we have to deconstruct or just proof something knowing the loop inv *)
(* FIXME *)
| check_forI: "\<lbrakk>
    E |~ exp1 : int_typ;
    E |~ exp2 : int_typ;
    E |~ exp3 : int_typ;
    E |~ exp4 : unit_typ
\<rbrakk> \<Longrightarrow> E \<turnstile> E_for tan x exp1 exp2 exp3 ord exp4 : unit_typ"

| check_pexps_nilI: "check_pexps _ [] _ _"
| check_pexps_conI: "\<lbrakk> 
   trace ''check_pexps_conI'';
   check_pexp E pexp t1 t2; 
   check_pexps E pexps t1 t2
\<rbrakk> \<Longrightarrow> check_pexps E (pexp#pexps) t1 t2"

| check_block_singleI: "\<lbrakk>
   E |~ exp : t ;   
   trace (''block single t='' @ show t)
\<rbrakk> \<Longrightarrow> E \<turnstile> ( (E_block tan [exp]) ) : t "

(*
| check_block_cons_assignI:"\<lbrakk>                                    
     Some (lexp , exp) = deconstruct_assign exp1;
     check_exp exp;
     check_lexp lexp bindings;
     check_local_binds (exp2#exps) bindings;
     check_exp ( (E_block (exp2#exps)) ( tan))
\<rbrakk> \<Longrightarrow> check_exp ( (E_block ( exp1#exp2#exps)) tan)"
*)
| check_block_consI:"\<lbrakk> 
     E \<turnstile> exp1 : unit_typ ;    
     E \<turnstile> E_block tan (exp2#exps) : t
\<rbrakk> \<Longrightarrow> E \<turnstile> E_block tan (exp1#exp2#exps) : t"

(* FIXME need to check constraint is in env *)
| check_assertI: "\<lbrakk>
   E |~ assert_exp : t;
   Some t = type_of_exp assert_exp
\<rbrakk> \<Longrightarrow> E \<turnstile> E_assert tan assert_exp msg_exp : _"

(*   (case get_env_exp exp of None \<Rightarrow> trace ''No tan'' | Some env \<Rightarrow> trace (''letbindI '' @ (show_env env))); *)
| check_letbindI:"\<lbrakk>      
     Some (e',t') = env_type_of_pat pat;
     check_pat_s e' pat t' bindings;  
     Some (E,t) = env_type_of_exp exp;
     E |~ exp : t 
\<rbrakk> \<Longrightarrow> 
     check_letbind ( (LB_val tan pat exp) ) bindings "

(* FIXME - Add subtype check; add bindings to E *)

| check_pexpI:"\<lbrakk>   
     trace (''check_pexpI typ_pat='' @ (show typ_pat) @ '' typ_e='' @  (show typ_e)); 
     check_pat_s E pat typ_pat bindings;
     Some env = env_of exp;   
     locals_in env bindings;  
     env |~ exp : typ_e
\<rbrakk> \<Longrightarrow> check_pexp E (Pat_exp tan pat exp)  typ_pat  typ_e "

(*
| check_pexpI:"\<lbrakk>   
     trace (''check_pexpI typ_pat='' @ (show typ_pat) @ '' typ_e='' @  (show typ_e)); 
     check_pat E pat typ_pat bindings
\<rbrakk> \<Longrightarrow> check_pexp E (Pat_exp tan pat exp)  typ_pat  typ_e "
*)

(* FIXME expg needs to be bool *)
| check_pexp_whenI:"\<lbrakk>   
     Some env = env_of exp;    
     check_pat_s E pat typ_pat bindings;
     locals_in env bindings;   
     env |~ exp : typ_e;
     locals_in envg bindings;
     Some envg = env_of expg;
     envg |~ expg : bool_all_typ 
\<rbrakk> \<Longrightarrow> check_pexp E (Pat_when tan pat expg exp) typ_pat typ_e"



code_pred (modes: 
       check_exp: i \<Rightarrow>  i \<Rightarrow> i  \<Rightarrow> bool and
       check_letbind: i \<Rightarrow> o \<Rightarrow> bool and
       check_pexp : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       check_pexps : i \<Rightarrow>i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       check_fexp : i \<Rightarrow> i  \<Rightarrow> bool and
       check_fexp_list : i \<Rightarrow> i \<Rightarrow> bool and
       check_exp_list : i \<Rightarrow> i \<Rightarrow> bool and
       check_lexp : i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
       check_lexp_list : i \<Rightarrow> o \<Rightarrow> bool 
    
)  [show_steps,  show_mode_inference,  show_invalid_clauses] check_exp .

(* FIXME - NEed to expand synonyms in the above *)

values [expected "{()}"] "{ x. check_exp emptyEnv  (E_lit (set_type None unit_typ) L_unit) unit_typ }"
value "True"

values "{x . match unit_typ unit_typ x } "

values [expected "{()}"] "{x . subtype emptyEnv unit_typ unit_typ }"

values [expected "{()}"] "{ x . check_lit emptyEnv  L_unit  unit_typ }"

values [expected "{}"] "{ x . check_lit emptyEnv  L_unit  int_typ }"



definition tan0 where 
  "tan0 = (set_type None (bool_typ True))"

definition tan1 where 
  "tan1 = add_local (set_type None (bool_typ True))
                                 ( (id (STR ''x'')) ) (bool_typ True)"

definition env11 where
  "env11 = add_local_env emptyEnv (id (STR ''x'')) (bool_typ True)"

values [expected "{()}"] "{ x . check_exp env11  (E_id tan1 ( (id (STR ''x'')) )) (bool_typ True) }"

values [expected "{()}"] "{ x . check_exp emptyEnv
              (E_let tan1 (LB_val tan1 (P_id tan0 (id (STR ''x''))) 
                                  (E_lit tan0 L_true ))
                          (E_id tan1 ( (id (STR ''x'')) )))
                                 (bool_typ True) }"


values [expected "{}"] "{ x . check_exp emptyEnv
               (E_if  (set_type None unit_typ) ( (E_lit (set_type None (bool_typ True)) ( L_true )) )
                           ( (E_lit (set_type None unit_typ) ( L_unit )) )
                           ( (E_lit (set_type None unit_typ) ( L_unit )) )
                    ) (bool_typ True) }"

values [expected "{()}"] "{ x . check_exp emptyEnv
               (E_if  (set_type None unit_typ) ( (E_lit (set_type None (bool_typ True)) ( L_true )) )
                           ( (E_lit (set_type None unit_typ) ( L_unit )) )
                           ( (E_lit (set_type None unit_typ) ( L_unit )) )
                    ) unit_typ }"

values [expected "{()}"] "{ x . check_exp emptyEnv
              ( (E_if  (set_type None int_typ))
                   ( (E_lit (set_type None (bool_typ True)) ( L_true ))) 
                           ( (E_lit (set_type None (num_typ 1)) ( (L_num 1) )) )
                           ( (E_lit (set_type None (num_typ 2)) ( (L_num 2) )))
                    ) int_typ }"

values  [expected "{()}"] "{ x . check_exp emptyEnv
              ( (E_if  (set_type None int_typ))
                   ( (E_lit (set_type None (bool_typ True)) ( L_true ))) 
                           ( (E_lit (set_type None (num_typ 1)) ( (L_num 1) )) )
                           ( (E_lit (set_type None (num_typ 2)) ( (L_num 2) )))
                    ) (num_or 1 2) }"




(* Need an example with true let binding
   let x = 1 in
        let y = x + 1 in y

   let x = true in 
         if x then 1 else 2
*)

(*
values "{ bs. check_letbind ( (LB_val ( P_wild (,None)) 
              ( (E_lit ( L_unit )) (,set_type None unit_typ))) (,None)) bs }"
*)

inductive check_funcls :: "tannot funcl list \<Rightarrow> tannot_opt \<Rightarrow> bool" where
check_funcls_emptyI: " trace ''check_funcls_emptyI'' \<Longrightarrow> check_funcls [] _"


| check_funcls_consI: "\<lbrakk>
    Some (e,Typ_fn typ_in typ_out _) = get tan;
    trace ''check_funcls_consI'';
    check_funcls fs to;
    
    trace (''check_funcl t='' @ show typ_out) ;
    typ_in' = (case typ_in of
                [t] \<Rightarrow> t | ts \<Rightarrow> Typ_tup ts);
    check_pexp e pexp typ_in' typ_out
\<rbrakk> \<Longrightarrow> check_funcls (( (FCL_Funcl tan fid ((PEXP_funcl pexp)  ))  )#fs) to"

subsection \<open>Definitions\<close>

(* Don't need these
inductive check_sd :: "env \<Rightarrow> tannot scattered_def \<Rightarrow> bool" where
"check_sd env ( (SD_function ro to eo fid) tan)" 
| "\<lbrakk>
    Some (e,t) = env_type_of_pexp pexp;
    check_pexp e pexp t
\<rbrakk> \<Longrightarrow> check_sd env ( (SD_funcl tan ((FCL_Funcl ftan fid (PEXP_funcl pexp)) )) )"

| "check_sd env ( (SD_variant tan tyid tq) )"
| "check_sd env ( (SD_unioncl tan tyid tu) )"
(* FIXME. Leave these out as don't expect to encounter them in typed AST. Need to fixup where I tap into Sail pipeline *)
| "check_sd env ( (SD_mapping tan mapid to) )"
| "check_sd env ( (SD_mapcl tan mapid mapcl) )"  

| "check_sd env ( (SD_end tan tid) )"

code_pred (modes: i \<Rightarrow> i \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] check_sd .
*)
inductive check_def :: "env \<Rightarrow> tannot def \<Rightarrow> bool" ( " _ \<turnstile> _ " ) where

check_fundefI:
 "\<lbrakk> trace ''check_fundefI'' ; check_funcls funcls tannot_opt \<rbrakk> \<Longrightarrow> check_def e (DEF_fundef (  (FD_function _ rec_opt tannot_opt effect_top funcls )  ))"

(* FIXME Addings bindings to E to be available later *)
| check_letbindI:
  "\<lbrakk>   
    check_letbind  letbind bindings
\<rbrakk> \<Longrightarrow> check_def e (DEF_val letbind)"

(* FIXME Check wellformedness? *)
| check_typedefI: "check_def env (DEF_type tdef)"
| check_valspecI:  "check_def env (DEF_spec _)"

(* Pass these. These have already been handled by Sail type checker or are sugar *)
| check_fixityI:  "check_def env (DEF_fixity _ _ _)"
| check_overloadI:  "check_def env (DEF_overload _ _)"
| check_set_orderI:  "check_def env (DEF_default ( _ ))"
| check_measureI:  "check_def env (DEF_measure _ _ _)"
| check_loop_measureI:  "check_def env (DEF_loop_measures _ _ )"
| check_reg_decI:  "check_def env (DEF_reg_dec _)"
| check_internal_mutrecI:  "check_def env (DEF_internal_mutrec _)"
| check_pragmaI:  "check_def env (DEF_pragma _ _)"

(* FIXME. Don't expect these *)
(*|check_mapdefI: "check_def env (DEF_mapdef md )"
| check_sdI: "check_sd env sd \<Longrightarrow> check_def env (DEF_scattered sd )"*)

code_pred (modes: i \<Rightarrow> i \<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] check_def .

(*values "{True. check_def *)

(*
values "{ xx . check_def (DEF_fundef((FD_function (Rec_aux (Rec_nonrec) _) 
                                ( Typ_annot_opt_aux (Typ_annot_opt_some (TypQ_aux (TypQ_no_forall) _)) _)
                                ( (Typ_id((Id (STR ''int''))_)) _ )
                                (Effect_opt_aux (Effect_opt_none, _))
        [ (FC (FCL_Funcl ( (Id(STR ''main'') _)) ) 
             (Pat_exp ( (P_typ ( (Typ_id ( (Id (STR ''int'')) _)) _ )
                                           ( (P_id ( (Id (STR ''z'')) _)) _))) 
,)),(  E { locals = ;  ; typ_vars =  (Var("'_z"),)=K_int,(Var("'_z#0"),)=K_int; C = }(Typ_app((Id("atom"),),[((A_nexp((Nexp_var((Var("'_z"),)),)),))]),)))),(  E { locals = ;  ; typ_vars =  (Var("'_z"),)=K_int; C = }
(Typ_id((Id("int"),)),)))
*)

definition "env2 \<equiv> add_local  (set_type None unit_typ) ( (id (STR ''z'')) ) unit_typ"

value "eq_id (id (STR ''int'')) (id (STR ''unit''))"

values [expected "{}"] "{ x . match int_typ unit_typ x }"

values  [expected "{}"] "{ x . subtype emptyEnv int_typ unit_typ }"

values  [expected "{()}"] "{ x . subtype emptyEnv unit_typ unit_typ }"

values  [expected "{()}"] "{ x . subtype emptyEnv int_typ int_typ }"

values  [expected "{}"] "{ x .  emptyEnv |~ ( E_lit (set_type None unit_typ) L_unit ) :  int_typ }"

values [expected "{}"] "{ x .  emptyEnv \<turnstile> ( E_lit (set_type None unit_typ) L_unit ) :  int_typ }" 

values [expected "{}"] "{ x . check_exp emptyEnv
   (  (E_block (  set_type None unit_typ) ( [ (  (E_lit (  set_type None unit_typ) ( L_unit )) )  ]))) int_typ }"

values [expected "{()}"] "{ x . check_exp emptyEnv
   (  (E_block (  set_type None unit_typ) ( [ (  (E_lit (  set_type None unit_typ) ( L_unit )) )  ]))) unit_typ }"



definition real_typ where
  "real_typ \<equiv> ( (Typ_id  ( (id  (STR ''real'')) )) )"

values "{x . subtype emptyEnv real_typ real_typ }"

values "{x . subtype emptyEnv unit_typ (Typ_var (var (STR ''a''))) }"

values "{b . match  unit_typ (Typ_var (var (STR ''a''))) b }"

code_printing
  constant Debug.trace \<rightharpoonup> (OCaml) "Utils2.trace _"



section \<open>Examples\<close>

(* let.sail 

let _ = let x = 1 in x

Defs([(DEF_val
    ((LB_val((P_wild,(  E { locals = ;  ; typ_vars =  ; C = }(Typ_app((Id("atom"),),
           [((A_nexp((Nexp_constant(1),)),))]),))),
       (E_let((LB_val((P_id((Id("x"),)),(  E { locals = ;  ; typ_vars =  ; C = }
                     (Typ_app((Id("atom"),),[((A_nexp((Nexp_constant(1),)),))]),))),
             (E_lit((L_num(1),)),(  E { locals = ;  ; typ_vars =  ; C = }
                 (Typ_app((Id("atom"),),[((A_nexp((Nexp_constant(1),)),))]),)))),None),
         (E_id((Id("x"),)),(  E { locals = (Id("x"),) : (Typ_app((Id("atom"),),[((A_nexp((Nexp_constant(1),)),))]),);  ; typ_vars =  ; C = }(Typ_app((Id("atom"),),[((A_nexp((Nexp_constant(1),)),))]),)))
),(  E { locals = ;  ; typ_vars =  ; C = }(Typ_app((Id("atom"),),[((A_nexp((Nexp_constant(1),)),))]),)))
),None)))
])

if.sail
let x : bool(true) = true
let _ : int(1) = if x then 1 else 3

Defs([(DEF_val((LB_val((P_typ((Typ_id((Id("bool"),)),),(P_id((Id("x"),)),(  
E { locals = ;  ; typ_vars =  (Var("'ex1#"),)=K_bool,(Var("'ex2#"),)=K_bool; C = }
(Typ_app((Id("atom_bool"),),[((A_bool((NC_var((Var("'ex2#"),)),)),))]),)))),(  
E { locals = ;  ; typ_vars =  (Var("'ex1#"),)=K_bool; C = }(Typ_id((Id("bool"),)),))),
(E_lit((L_true,)),(  E { locals = ;  ; typ_vars =  ; C = }(Typ_app((Id("atom_bool"),),[((A_bool((NC_true,)),))]),)))
),None)))

;(DEF_val((LB_val((P_wild,(  E { locals = (Id("x"),) : (Typ_app((Id("atom_bool"),),[((A_bool((NC_var((Var("'ex2#"),)),)),))]),);  ; typ_vars =  (Var("'ex1#"),)=K_bool,(Var("'ex2#"),)=K_bool,(Var("'ex4#"),)=K_int; C = (NC_or((NC_equal((Nexp_var((Var("'ex4#"),)),),(Nexp_constant(1),)),),(NC_equal((Nexp_var((Var("'ex4#"),)),),(Nexp_constant(3),)),)),)}(Typ_app((Id("atom"),),[((A_nexp((Nexp_var((Var("'ex4#"),)),)),))]),))),(E_if((E_id((Id("x"),)),(  E { locals = (Id("x"),) : (Typ_app((Id("atom_bool"),),[((A_bool((NC_var((Var("'ex2#"),)),)),))]),);  ; typ_vars =  (Var("'ex1#"),)=K_bool,(Var("'ex2#"),)=K_bool; C = }(Typ_app((Id("atom_bool"),),[((A_bool((NC_var((Var("'ex2#"),)),)),))]),)))
,(E_lit((L_num(1),)),(  E { locals = (Id("x"),) : (Typ_app((Id("atom_bool"),),[((A_bool((NC_var((Var("'ex2#"),)),)),))]),);  ; typ_vars =  (Var("'ex1#"),)=K_bool,(Var("'ex2#"),)=K_bool; C = (NC_var((Var("'ex2#"),)),)}(Typ_app((Id("atom"),),[((A_nexp((Nexp_constant(1),)),))]),)))
,(E_lit((L_num(3),)),(  E { locals = (Id("x"),) : (Typ_app((Id("atom_bool"),),[((A_bool((NC_var((Var("'ex2#"),)),)),))]),);  ; typ_vars =  (Var("'ex1#"),)=K_bool,(Var("'ex2#"),)=K_bool; C = (NC_app((Id("not"),),[((A_bool((NC_var((Var("'ex2#"),)),)),))]),)}(Typ_app((Id("atom"),),[((A_nexp((Nexp_constant(3),)),))]),)))
),(  E { locals = (Id("x"),) : (Typ_app((Id("atom_bool"),),[((A_bool((NC_var((Var("'ex2#"),)),)),))]),);  ; typ_vars =  (Var("'ex1#"),)=K_bool,(Var("'ex2#"),)=K_bool; C = }(Typ_exist([(KOpt_aux(KOpt_kind((K_int,),(Var("'ex3#"),)),))],(NC_or((NC_equal((Nexp_var((Var("'ex3#"),)),),(Nexp_constant(1),)),),(NC_equal((Nexp_var((Var("'ex3#"),)),),(Nexp_constant(3),)),)),),(Typ_app((Id("atom"),),[((A_nexp((Nexp_var((Var("'ex3#"),)),)),))]),)),)))
),None)))
])

function   int  main ( int ) z -> { z }

;(DEF_fundef((FD_function(Rec_aux(Rec_nonrec,),Typ_annot_opt_aux(Typ_annot_opt_some(TypQ_aux(TypQ_no_forall,),(Typ_id((Id("int"),)),)),),Effect_opt_aux(Effect_opt_none,),[(FC(FCL_Funcl((Id("main"),),(Pat_exp((P_typ((Typ_id((Id("int"),)),),(P_id((Id("z"),)),(  E { locals = ;  ; typ_vars =  (Var("'_z"),)=K_int,(Var("'_z#0"),)=K_int; C = }(Typ_app((Id("atom"),),[((A_nexp((Nexp_var((Var("'_z"),)),)),))]),)))),(  E { locals = ;  ; typ_vars =  (Var("'_z"),)=K_int; C = }(Typ_id((Id("int"),)),))),(E_block([((E_id((Id("z"),)),(  E { locals = (Id("z"),) : (Typ_app((Id("atom"),),[((A_nexp((Nexp_var((Var("'_z"),)),)),))]),);  ; typ_vars =  (Var("'_z"),)=K_int,(Var("'_z#0"),)=K_int; C = }(Typ_app((Id("atom"),),[((A_nexp((Nexp_var((Var("'_z"),)),)),))]),)))
)]),(  E { locals = (Id("z"),) : (Typ_app((Id("atom"),),[((A_nexp((Nexp_var((Var("'_z"),)),)),))]),);  ; typ_vars =  (Var("'_z"),)=K_int,(Var("'_z#0"),)=K_int; C = }(Typ_id((Id("int"),)),)))
),None)),(  E { locals = ;  ; typ_vars =  ; C = }(Typ_fn([((Typ_id((Id("int"),)),))],(Typ_id((Id("int"),)),),Effect_aux(Effect_set([]),)),))))]),None)))

*)

end
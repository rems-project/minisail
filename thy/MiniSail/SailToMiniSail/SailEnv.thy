theory SailEnv
  imports SailASTUtils
begin

section \<open>Sail Environment\<close>

(* From sail/src/type_check.ml
type env =
  { top_val_specs : (typquant * typ) Bindings.t;
    defined_val_specs : IdSet.t;
    locals : (mut * typ) Bindings.t;
    top_letbinds : IdSet.t;
    union_ids : (typquant * typ) Bindings.t;
    registers : (effect * effect * typ) Bindings.t;
    variants : (typquant * type_union list) Bindings.t;
    scattered_variant_envs : env Bindings.t;
    mappings : (typquant * typ * typ) Bindings.t;
    typ_vars : (Ast.l * kind_aux) KBindings.t;
    shadow_vars : int KBindings.t;
    typ_synonyms : (typquant * typ_arg) Bindings.t;
    overloads : (id list) Bindings.t;
    enums : IdSet.t Bindings.t;
    records : (typquant * (typ * id) list) Bindings.t;
    accessors : (typquant * typ) Bindings.t;
    externs : (string * string) list Bindings.t;
    casts : id list;
    allow_casts : bool;
    allow_bindings : bool;
    constraints : n_constraint list;
    default_order : order option;
    ret_typ : typ option;
    poly_undefineds : bool;
    prove : (env -> n_constraint -> bool) option;
    allow_unknowns : bool;
    bitfields : (Big_int.num * Big_int.num) Bindings.t Bindings.t;
  }
*)

datatype mut = Mutable | Immutable

record env = 
          top_val_specs :: "(id  * (typquant * typ)) list"
          typ_vars :: "(kid * kind) list"
          locals :: "(id * (mut * typ)) list"
          records :: "(id * ( typquant * (( id * typ) list) )) list"
          variants :: "(id * (typquant * (type_union list))) list"
          constraints :: "n_constraint list"
          default_order :: "order option"
          ret_typ :: "typ option"
          registers :: "(id * typ) list"
          typ_synonyms :: "(id * (typquant * typ_arg)) list"
          enums :: "(id * (id list)) list"
          prover :: "((n_constraint list) \<Rightarrow> n_constraint \<Rightarrow> bool) option"

definition emptyEnv :: env where
  "emptyEnv = \<lparr> top_val_specs = [],  typ_vars = [] , locals = [], records=[],variants=[],constraints=[],default_order=None, ret_typ=None, 
     registers=[], typ_synonyms=[] , enums=[], prover = None\<rparr>"


record tannot' =
   tannot_env :: env
   tannot_typ :: "typ"
   tannot_effect :: effect
   tannot_expected :: "typ option"
   tannot_instantiations :: "((kid*typ_arg) list) option"

type_synonym tannot = "tannot' option"


definition bind' where
  "bind' f t = Option.bind t (Some \<circ> f)"

section \<open>Unpacking tannot\<close>
definition get_type :: "tannot \<Rightarrow> typ option"  where
  "get_type  = bind' tannot_typ"

definition get_env :: "tannot \<Rightarrow> env option" where
  "get_env  = bind' tannot_env"

primrec get :: "tannot \<Rightarrow> (env*typ) option" where
   "get None = None"
 | "get (Some tan) = Some (tannot_env tan, tannot_typ tan)"

fun get_e :: "tannot exp \<Rightarrow> (env*typ) option" where
  "get_e exp  = get (annot_e exp)"

fun get_tan_e :: "tannot exp \<Rightarrow> tannot" where
  "get_tan_e exp = annot_e exp"

fun get_tan_pat :: "tannot pat \<Rightarrow> tannot" where
  "get_tan_pat exp = annot_pat exp"

fun get_tan_pexp :: "tannot pexp \<Rightarrow> tannot" where
  "get_tan_pexp pexp  = annot_pexp pexp"


fun get_tan_lexp :: "tannot lexp \<Rightarrow> tannot" where
  "get_tan_lexp lexp = annot_lexp lexp"

fun get_tan_letbind :: "tannot letbind \<Rightarrow> tannot" where
  "get_tan_letbind lexp = annot_letbind lexp"

fun type_of_exp :: "tannot exp \<Rightarrow> typ option" where
  "type_of_exp exp = get_type (get_tan_e exp)"

fun env_type_of_exp :: "tannot exp \<Rightarrow> (env*typ) option" where
   "env_type_of_exp exp = (case get_type (get_tan_e exp) of
                            None \<Rightarrow> None | Some t \<Rightarrow> (case get_env (get_tan_e exp) of
                                                         None \<Rightarrow> None | Some e \<Rightarrow> Some (e,t)))"

fun env_type_of_pexp :: "tannot pexp \<Rightarrow> (env*typ) option" where
   "env_type_of_pexp exp = (case get_type (get_tan_pexp exp) of
                            None \<Rightarrow> None | Some t \<Rightarrow> (case get_env (get_tan_pexp exp) of
                                                         None \<Rightarrow> None | Some e \<Rightarrow> Some (e,t)))"

fun type_of_pat :: "tannot pat \<Rightarrow> typ option" where
  "type_of_pat pat  = get_type (get_tan_pat pat)"

fun type_of_pexp :: "tannot pexp \<Rightarrow> typ option" where
  "type_of_pexp (Pat_exp _ pat exp) = type_of_pat pat"
| "type_of_pexp (Pat_when _ pat _ exp) = type_of_pat pat"

fun get_env_exp :: "tannot exp \<Rightarrow> env option" where
  "get_env_exp exp = get_env (get_tan_e exp)"

fun get_env_letbind :: "tannot letbind \<Rightarrow> env option" where
  "get_env_letbind lexp  = get_env (get_tan_letbind lexp)"

definition ret_type :: "tannot \<Rightarrow> typ option" where
  "ret_type t = Option.bind (Option.bind t (Some \<circ> tannot_env) ) ret_typ"

primrec set_type :: "tannot \<Rightarrow> typ \<Rightarrow> tannot" where
  "set_type (Some t) typ = Some (t \<lparr> tannot_typ := typ \<rparr>)"
| "set_type None typ = Some \<lparr> tannot_env = emptyEnv ,   tannot_typ = typ, tannot_effect = ( (Effect_set [])), tannot_expected = None, tannot_instantiations = None  \<rparr>"


fun type_of_lexp :: "tannot lexp \<Rightarrow> typ option" where
  "type_of_lexp lexp = get_type (get_tan_lexp lexp)"

fun env_of_lexp :: "tannot lexp \<Rightarrow> env option" where
  "env_of_lexp lexp = get_env (get_tan_lexp lexp)"

fun get_tan_exp :: "tannot exp \<Rightarrow> tannot" where
  "get_tan_exp exp = annot_e exp"

fun env_of_exp :: "tannot exp \<Rightarrow> env option" where
  "env_of_exp lexp = get_env (get_tan_exp lexp)"

section \<open>Generic Lookup\<close>
fun lookup :: "('a*'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lookup [] _ = None"
| "lookup ((x,t)#xs) y = (if x = y then Some t else lookup xs y)"

section \<open>Enumerations\<close>
fun lookup_enum_env :: "env \<Rightarrow> id \<Rightarrow> typ option" where
"lookup_enum_env env x = (case find (\<lambda>(_,es). List.member es x ) (enums env) of
                                 None \<Rightarrow> None | Some (tyid,_) \<Rightarrow> Some ( (Typ_id tyid)))"



primrec lookup_enum :: "tannot \<Rightarrow> id \<Rightarrow> typ option" where
  "lookup_enum (Some tan) x = lookup_enum_env (tannot_env tan) x"
| "lookup_enum None _ = None"


section \<open>Constraints\<close>

fun add_constraint :: "n_constraint \<Rightarrow> env \<Rightarrow> env" where
  "add_constraint nc env = env \<lparr> constraints := nc # (constraints env) \<rparr>"


section \<open>Records\<close>
fun lookup_record_field_env :: "env \<Rightarrow> id \<Rightarrow> id \<Rightarrow> typ option" where
  "lookup_record_field_env env recc_id field_id = (case lookup (records env) recc_id of
                                                       Some (_, fieldds) \<Rightarrow> lookup fieldds field_id | None \<Rightarrow> None)"

fun lookup_record_field :: "tannot \<Rightarrow> id \<Rightarrow> id \<Rightarrow> typ option" where
"lookup_record_field (Some tan) x y = lookup_record_field_env (tannot_env tan) x y"
| "lookup_record_field None x y = None"


fun deconstruct_record_type :: "typ \<Rightarrow> id option" where
  "deconstruct_record_type ( (Typ_id recid) ) = Some recid"
| "deconstruct_record_type ( (Typ_app recid _ ) ) = Some recid"
| "deconstruct_record_type _ = None"


section \<open>Variants\<close>

fun lookup_tud :: "type_union list \<Rightarrow> id \<Rightarrow> typ option" where 
  "lookup_tud [] _ = None"
| "lookup_tud (( (Tu_ty_id typ ( (id x) ))) # tus) ( (id y)  ) = (if x = y then Some typ else lookup_tud tus ( (id y) ))"
| "lookup_tud ( _ # tus ) _ = None"

fun lookup_variant_env :: "env \<Rightarrow> id \<Rightarrow> id \<Rightarrow> typ option" where
"lookup_variant_env env tid vid = (case lookup (variants env) tid of
                                     Some (_ , tus) \<Rightarrow> lookup_tud tus vid | None \<Rightarrow> None)"

fun lookup_variant :: "tannot \<Rightarrow> id \<Rightarrow> id \<Rightarrow> typ option" where
 "lookup_variant (Some tan) x y = lookup_variant_env (tannot_env tan) x y"
| "lookup_variant None _ _ = None"

section \<open>Val Specs\<close>
fun get_val_spec_env :: "env \<Rightarrow> id \<Rightarrow> (typquant * typ) option" where
  "get_val_spec_env env x = lookup (top_val_specs env) x"

fun get_val_spec :: "tannot \<Rightarrow> id \<Rightarrow> (typquant * typ) option" where
 "get_val_spec (Some tan) x = get_val_spec_env (tannot_env tan) x"
| "get_val_spec None _ = None"

fun lookup_fun :: "tannot \<Rightarrow> id \<Rightarrow> (typ list * typ) option" where
"lookup_fun (Some tan) fid = (case get_val_spec_env (tannot_env tan) fid of 
                                 Some (_ ,  (Typ_fn in_typs rett_typ _ )  ) \<Rightarrow> Some (in_typs, rett_typ)
                               | _ \<Rightarrow> None)"
| "lookup_fun None _ = None"


section \<open>Registers\<close>

fun lookup_register_env :: "env \<Rightarrow> id \<Rightarrow> typ option" where
"lookup_register_env env x =  (case lookup (registers env) x of
                                 Some t \<Rightarrow> Some t | None \<Rightarrow> None)"

fun lookup_index :: "(id * 'a) list \<Rightarrow> id \<Rightarrow> nat option" where
  "lookup_index [] _ = None"
| "lookup_index (x#xs) y = (if fst x = y then Some (List.length xs) 
                           else lookup_index xs y)"

fun lookup_register_index_env :: "env \<Rightarrow> id \<Rightarrow> nat option" where
  "lookup_register_index_env env x = (case lookup_index (registers env) x of
                                 Some t \<Rightarrow> Some t | None \<Rightarrow> None)"

fun lookup_register :: "tannot \<Rightarrow> id \<Rightarrow> typ option" where
"lookup_register (Some tan) x = lookup_register_env (tannot_env tan) x"
| "lookup_register None _ = None"

section \<open>Local Identifiers\<close>
fun lookup_local_id_env :: "env \<Rightarrow> id \<Rightarrow> typ option" where
  "lookup_local_id_env env x = (case (lookup (locals env) x) of
                                     Some (_,t) \<Rightarrow> Some t | None \<Rightarrow> lookup_enum_env env x)"

primrec lookup_local_id :: "tannot \<Rightarrow> id  \<Rightarrow> typ option" where
  "lookup_local_id (Some tan) x = lookup_local_id_env (tannot_env tan) x"
| "lookup_local_id None x = None"

fun lookup_mutable_env :: "env \<Rightarrow> id \<Rightarrow> typ option" where
  "lookup_mutable_env env x = (case (lookup (locals env) x) of
                                     Some (Mutable,t) \<Rightarrow> Some t | None \<Rightarrow> lookup_register_env env x)"

fun lookup_mutable :: "tannot \<Rightarrow> id \<Rightarrow> typ option" where
  "lookup_mutable (Some tan) x = lookup_mutable_env (tannot_env tan) x"
| "lookup_mutable None x = None"

fun add_local_env :: "env \<Rightarrow> id \<Rightarrow> typ \<Rightarrow> env" where
  "add_local_env env x typ = env \<lparr> locals := (x,(Immutable,typ)) # (locals env) \<rparr>"

fun add_local :: "tannot \<Rightarrow> id \<Rightarrow> typ \<Rightarrow> tannot" where
  "add_local (Some tan) x typ = Some (tan  \<lparr> tannot_env := add_local_env (tannot_env tan) x typ \<rparr>)" 
| "add_local None _ _ = None"
(*|  "add_local None x typ =  Some \<lparr> tannot_env = add_local_env (tannot_env tan) x typ , tannot_typ = tannot_typ tan \<rparr>" *)


fun lookup_id :: "tannot \<Rightarrow> id \<Rightarrow> typ option" where
 "lookup_id t x = (case lookup_local_id t x of 
                      Some typ \<Rightarrow> Some typ 
                    | None \<Rightarrow> lookup_register t x)"


fun deconstruct_register_type :: "typ \<Rightarrow> typ option" where
"deconstruct_register_type t = (case  t of
                                 ( (Typ_app ( (id ( app_id ))) [ ( (A_typ typ )) ])) \<Rightarrow> 
                                     (if app_id = STR ''register'' then Some typ else None) | _ \<Rightarrow> None)"

section \<open>Vectors\<close>
fun deconstruct_bitvector_type ::  "typ \<Rightarrow> (nexp *order*typ) option" where
"deconstruct_bitvector_type t = (case  t of
                                 ( (Typ_app ( (id ( app_id ))) [ ( (A_nexp len)),  (A_order ord) ])) \<Rightarrow> 
                                     (if app_id = STR ''bitvector'' then Some (len,ord, (Typ_id ( (id (STR ''bit''))))) else None) | _ \<Rightarrow> None)"

fun is_bitvector_type :: "tannot \<Rightarrow> (nexp *order*typ) option" where
  "is_bitvector_type None = None"
| "is_bitvector_type (Some t) =  deconstruct_bitvector_type (tannot_typ t)"

fun deconstruct_vector_type :: "typ \<Rightarrow> (nexp *order*typ) option" where
 "deconstruct_vector_type t = (case t of
                                 ( (Typ_app ( (id ( app_id ))) [ ( (A_nexp len)),  (A_order ord),  (A_typ typ) ])) \<Rightarrow> 
                                     (if app_id = STR ''vector'' then Some (len,ord,typ) else None) | _ \<Rightarrow> deconstruct_bitvector_type t)"

fun is_vector_type :: "tannot \<Rightarrow> (nexp *order*typ) option" where
  "is_vector_type None = None"
| "is_vector_type (Some t) =  deconstruct_vector_type (tannot_typ t)"

(* Some (len,ord,typ) = is_vector_type tan;*)



fun is_list_type :: "tannot \<Rightarrow> typ option" where
  "is_list_type None = None"
| "is_list_type (Some t) = (case tannot_typ t of
                                 ( (Typ_app ( (id ( app_id ))) [ ( (A_typ typ)) ])) \<Rightarrow> (if app_id = STR ''list'' then Some typ else None) | _ \<Rightarrow> None)"

fun deconstruct_list_type :: "typ \<Rightarrow> typ option" where
  "deconstruct_list_type (Typ_app ( (id ( app_id ))) [ ( (A_typ typ)) ]) = (if app_id = STR ''list'' then Some typ else None)"
| "deconstruct_list_type _ = None"


(* FIXME. Is this complete? *)
fun deconstruct_bool_type :: "typ \<Rightarrow> n_constraint option" where
  "deconstruct_bool_type ( (Typ_id ( (id b)))) = (if b = STR ''bool'' then Some nc_true else None)"
|   "deconstruct_bool_type ( (Typ_app ( (id b)) [ (A_bool nc )])) = (if b = STR ''atom_bool'' then Some nc  else None)"
| "deconstruct_bool_type ( (Typ_exist kids nc typ)) = deconstruct_bool_type typ"
| "deconstruct_bool_type Typ_internal_unknown = None"
| "deconstruct_bool_type (Typ_id (operator va)) = None"
| "deconstruct_bool_type (Typ_var v) = None"
| "deconstruct_bool_type (Typ_fn v va vb)  = None"
| " deconstruct_bool_type (Typ_bidir v va vb) = None"
| "deconstruct_bool_type (Typ_tup v) = None"
| "deconstruct_bool_type (Typ_app (operator vb) va) = None"
| "deconstruct_bool_type (Typ_app (id va) _) = None"





fun prove :: "env \<Rightarrow> n_constraint \<Rightarrow> bool" where
"prove env nc = (case (prover env) of
                  Some p \<Rightarrow> p (constraints env) nc | None \<Rightarrow> True)"

section \<open>Substitution in Types\<close>



fun subst_nexp ::  "(kid*typ_arg) \<Rightarrow> nexp \<Rightarrow> nexp" where 

  "subst_nexp ks   (Nexp_id x) = Nexp_id x"
| "subst_nexp (k1,  (A_nexp ( ne))) (Nexp_var k2) = (if k1 = k2 then ne else (Nexp_var k2))"
| "subst_nexp (k1,  (A_bool _)) (Nexp_var k2) = ((Nexp_var k2))"
| "subst_nexp (k1,  (A_typ _ )) (Nexp_var k2) = ((Nexp_var k2))"
| "subst_nexp (k1,  (A_order _ )) (Nexp_var k2) = ((Nexp_var k2))"

 | "subst_nexp ks (Nexp_constant n) = Nexp_constant n"   \<comment> \<open>constant\<close>
 | "subst_nexp ks (Nexp_app x nes) = Nexp_app x (List.map (subst_nexp ks) nes)"   \<comment> \<open>app\<close>
 | "subst_nexp ks (Nexp_times n1 n2) = Nexp_times (subst_nexp ks n1) (subst_nexp ks n1)" 
| "subst_nexp ks (Nexp_sum n1 n2) = Nexp_sum (subst_nexp ks n1) (subst_nexp ks n1)" 
| "subst_nexp ks (Nexp_minus n1 n2) = Nexp_minus (subst_nexp ks n1) (subst_nexp ks n1)" 
| "subst_nexp ks (Nexp_exp n1) = Nexp_exp (subst_nexp ks n1)" 
| "subst_nexp ks (Nexp_neg n1) = Nexp_neg (subst_nexp ks n1)"




fun subst_order ::  "(kid*typ_arg) \<Rightarrow> order \<Rightarrow> order" 
    where

 "subst_order (k1,  (A_order ( ord))) (Ord_var k2) = (if k1 = k2 then ord else (Ord_var k2))"
| "subst_order (k1,  _ ) (Ord_var k2) = (Ord_var k2)"
| "subst_order _ Ord_inc = Ord_inc"
 | "subst_order _ Ord_dec = Ord_dec"


fun subst_typ ::  "(kid*typ_arg) \<Rightarrow> typ \<Rightarrow> typ" and
   
    subst_typ_arg :: " (kid*typ_arg) \<Rightarrow> typ_arg \<Rightarrow> typ_arg" and
    
    subst_nc ::  "(kid*typ_arg) \<Rightarrow> n_constraint \<Rightarrow> n_constraint"  
 
    where


 "subst_nc ks  (NC_equal ne1 ne2) = NC_equal (subst_nexp ks ne1) (subst_nexp ks ne1) "  
| "subst_nc ks  (NC_bounded_ge ne1 ne2) = NC_bounded_ge (subst_nexp ks ne1) (subst_nexp ks ne1) "  
| "subst_nc ks  (NC_bounded_gt ne1 ne2) = NC_bounded_gt (subst_nexp ks ne1) (subst_nexp ks ne1) "  
| "subst_nc ks  (NC_bounded_le ne1 ne2) = NC_bounded_le (subst_nexp ks ne1) (subst_nexp ks ne1) "  
| "subst_nc ks  (NC_bounded_lt ne1 ne2) = NC_bounded_lt (subst_nexp ks ne1) (subst_nexp ks ne1) "  
| "subst_nc ks  (NC_not_equal ne1 ne2) = NC_not_equal (subst_nexp ks ne1) (subst_nexp ks ne1) "  
| "subst_nc ks (NC_set k is) = NC_set k is"  
| "subst_nc ks (NC_or nc1 nc2) = NC_or (subst_nc ks nc1)  (subst_nc ks nc2)"  
| "subst_nc ks (NC_and nc1 nc2) = NC_and (subst_nc ks nc1)  (subst_nc ks nc2)"  
| "subst_nc ks (NC_app tid args) = NC_app tid (List.map (subst_typ_arg ks) args)"
| "subst_nc (k1,  (A_bool ( nc))) (NC_var k2) =  (if k1 = k2 then nc else (NC_var k2))"
| "subst_nc (k1,  (A_nexp _ )) (NC_var k2) =  ((NC_var k2))"
| "subst_nc (k1,  (A_typ _ )) (NC_var k2) =  ((NC_var k2))"
| "subst_nc (k1,  (A_order _ )) (NC_var k2) =  ((NC_var k2))"
| "subst_nc ks NC_true   = NC_true"
| "subst_nc ks  NC_false  = NC_false"



 | "subst_typ _ Typ_internal_unknown   = Typ_internal_unknown"
 | "subst_typ _ (Typ_id tyid)   =   (Typ_id tyid)"
 | "subst_typ (k1, (A_typ ( t))) (Typ_var k2) = (if k1=k2 then t else (Typ_var k2))"
 | "subst_typ (k1, (A_bool _ )) (Typ_var k2) = Typ_var k2"
 | "subst_typ (k1, (A_order _ )) (Typ_var k2) = Typ_var k2"
 | "subst_typ (k1, (A_nexp _ )) (Typ_var k2) = (Typ_var k2)"
 | "subst_typ ks (Typ_fn ts tr e) = Typ_fn (List.map (subst_typ ks) ts) (subst_typ ks tr) e"
 | "subst_typ ks (Typ_bidir t1 t2 e) = Typ_bidir (subst_typ ks t1) (subst_typ ks t2) e"
 | "subst_typ ks (Typ_tup ts) =  Typ_tup (List.map (subst_typ ks) ts)"
 | "subst_typ ks (Typ_app tyid tas) = Typ_app tyid (List.map (subst_typ_arg ks) tas)"
 | "subst_typ ks (Typ_exist kids nc typ) = Typ_exist kids (subst_nc ks nc) (subst_typ ks typ)"  


| "subst_typ_arg ks (A_nexp ne) = A_nexp (subst_nexp ks ne)"
| "subst_typ_arg ks (A_typ ne) = A_typ (subst_typ ks ne)"
| "subst_typ_arg ks (A_order ne) = A_order (subst_order ks ne)"
| "subst_typ_arg ks (A_bool nc) = A_bool (subst_nc ks nc)"


fun subst_inst :: "tannot \<Rightarrow> typ \<Rightarrow> typ option" where
"subst_inst None t = Some t"
| "subst_inst (Some t') t = (case tannot_instantiations t' of 
                  None \<Rightarrow> Some t 
                | Some is \<Rightarrow> Some (List.fold subst_typ  is t ))"



fun subst_inst_list :: "tannot \<Rightarrow> typ list \<Rightarrow> typ list option" where
"subst_inst_list tan typs = those (List.map (subst_inst tan) typs)"

section \<open>Constructors\<close>

definition pat_id where
  "pat_id x = P_id (set_type None unit_typ) (id x)"

definition pat_pair where
  "pat_pair = P_tup (set_type None (Typ_tup [unit_typ,unit_typ])) [ pat_id (STR ''x'') , pat_id (STR ''y'')]"

definition pat_unit where
  "pat_unit  = P_lit (set_type None unit_typ) (SailAST.L_unit)"

definition e_unit where
  "e_unit =  (E_lit (set_type None unit_typ) ( SailAST.L_unit ))"

definition e_let where 
  "e_let e t = (E_let (set_type None unit_typ)
                    ( (LB_val None ( (P_id (set_type None t) ( (id (STR ''x'')) )) ))
                      e)  e_unit )"


definition e_pair where 
  "e_pair = E_tuple  (set_type None (Typ_tup [unit_typ,unit_typ])) [ e_unit, e_unit]"

definition e_true where
  "e_true =   (E_lit (set_type None (bool_typ True)) ( SailAST.L_true ))"

definition bv_typ where
  "bv_typ n = (Typ_app (id (STR ''vector'')) [ A_typ (Typ_id (id (STR ''bit''))) , A_order Ord_dec, A_nexp (Nexp_constant n)])" 

definition bv_typ2 where
  "bv_typ2 n = (Typ_app (id (STR ''bitvector'')) [ A_nexp (Nexp_constant n) , A_order Ord_dec])"

definition bv_lit where
  "bv_lit bs =  ( E_lit (set_type None (bv_typ (integer_of_nat (List.length (String.explode bs))))) (SailAST.L_bin bs))"

definition int_tannot where
  "int_tannot = set_type None int_typ"

definition pat_lit_bv where
  "pat_lit_bv bs = P_lit (set_type None (bv_typ (integer_of_nat (List.length (String.explode bs))))) (SailAST.L_bin bs)"

definition e_false where
  "e_false =   (E_lit (set_type None (bool_typ False)) ( SailAST.L_false ))"


abbreviation "unk \<equiv> (None)"

end
theory Ast
imports Main Native_Word.Uint32
begin

(* This a match for ast.ml in Sail except we omit location information *)

type_synonym string = String.literal

datatype "value" = Val

datatype "loop" = While | Until

type_synonym 'a annot = "'a"


type_synonym "x" = "string" \<comment> \<open>identifier\<close>
type_synonym "ix" = "string" \<comment> \<open>infix identifier\<close>
datatype base_effect_aux =  \<comment> \<open>effect\<close>
   BE_rreg   \<comment> \<open>read register\<close>
 | BE_wreg   \<comment> \<open>write register\<close>
 | BE_rmem   \<comment> \<open>read memory\<close>
 | BE_rmemt   \<comment> \<open>read memory and tag\<close>
 | BE_wmem   \<comment> \<open>write memory\<close>
 | BE_eamem   \<comment> \<open>signal effective address for writing memory\<close>
 | BE_exmem   \<comment> \<open>determine if a store-exclusive (ARM) is going to succeed\<close>
 | BE_wmv   \<comment> \<open>write memory, sending only value\<close>
 | BE_wmvt   \<comment> \<open>write memory, sending only value and tag\<close>
 | BE_barr   \<comment> \<open>memory barrier\<close>
 | BE_depend   \<comment> \<open>dynamic footprint\<close>
 | BE_undef   \<comment> \<open>undefined-instruction exception\<close>
 | BE_unspec   \<comment> \<open>unspecified values\<close>
 | BE_nondet   \<comment> \<open>nondeterminism, from $nondet$\<close>
 | BE_escape   \<comment> \<open>potential exception\<close>
 | BE_config   \<comment> \<open>configuration option\<close>

datatype kid_aux =  \<comment> \<open>kinded IDs: Type, Int, and Order variables\<close>
   var "x"  

datatype kind_aux =  \<comment> \<open>base kind\<close>
   K_type   \<comment> \<open>kind of types\<close>
 | K_int   \<comment> \<open>kind of natural number size expressions\<close>
 | K_order   \<comment> \<open>kind of vector order specifications\<close>
 | K_bool   \<comment> \<open>kind of constraints\<close>

datatype id_aux =  \<comment> \<open>Identifier\<close>
   id "x"  
 | operator "x"   \<comment> \<open>remove infix status\<close>

datatype base_effect = 
   BE_aux "base_effect_aux"  

datatype kid = 
   Kid_aux "kid_aux"  

datatype kind = 
   K_aux "kind_aux"  

datatype id = 
   Id_aux "id_aux"  

datatype effect_aux = 
   Effect_set "base_effect list"   \<comment> \<open>effect set\<close>

datatype order_aux =  \<comment> \<open>vector order specifications, of kind Order\<close>
   Ord_var "kid"   \<comment> \<open>variable\<close>
 | Ord_inc   \<comment> \<open>increasing\<close>
 | Ord_dec   \<comment> \<open>decreasing\<close>

datatype kinded_id_aux =  \<comment> \<open>optionally kind-annotated identifier\<close>
   KOpt_kind "kind" "kid"   \<comment> \<open>kind-annotated variable\<close>

datatype nexp_aux =  \<comment> \<open>numeric expression, of kind Int\<close>
   Nexp_id "id"   \<comment> \<open>abbreviation identifier\<close>
 | Nexp_var "kid"   \<comment> \<open>variable\<close>
 | Nexp_constant "integer"   \<comment> \<open>constant\<close>
 | Nexp_app "id" "nexp list"   \<comment> \<open>app\<close>
 | Nexp_times "nexp" "nexp"   \<comment> \<open>product\<close>
 | Nexp_sum "nexp" "nexp"   \<comment> \<open>sum\<close>
 | Nexp_minus "nexp" "nexp"   \<comment> \<open>subtraction\<close>
 | Nexp_exp "nexp"   \<comment> \<open>exponential\<close>
 | Nexp_neg "nexp"   \<comment> \<open>unary negation\<close>
and nexp = 
   Nexp_aux "nexp_aux"  

datatype effect = 
   Effect_aux "effect_aux"  

datatype order = 
   Ord_aux "order_aux"  

datatype kinded_id = 
   KOpt_aux "kinded_id_aux"  

datatype lit_aux =  \<comment> \<open>literal constant\<close>
   L_unit  
 | L_zero  
 | L_one  
 | L_true  
 | L_false  
 | L_num "integer"   \<comment> \<open>natural number constant\<close>
 | L_hex "string"   \<comment> \<open>bit vector constant, C-style\<close>
 | L_bin "string"   \<comment> \<open>bit vector constant, C-style\<close>
 | L_string "string"   \<comment> \<open>string constant\<close>
 | L_undef   \<comment> \<open>undefined-value constant\<close>
 | L_real "string"  

datatype typ_aux =  \<comment> \<open>type expressions, of kind Type\<close>
   Typ_internal_unknown  
 | Typ_id "id"   \<comment> \<open>defined type\<close>
 | Typ_var "kid"   \<comment> \<open>type variable\<close>
 | Typ_fn "typp list" "typp" "effect"   \<comment> \<open>Function (first-order only)\<close>
 | Typ_bidir "typp" "typp" "effect"   \<comment> \<open>Mapping\<close>
 | Typ_tup "typp list"   \<comment> \<open>Tuple\<close>
 | Typ_app "id" "typ_arg list"   \<comment> \<open>type constructor application\<close>
 | Typ_exist "kinded_id list" "n_constraint" "typp"  
and typp = 
   Typ_aux "typ_aux"  
and typ_arg_aux =  \<comment> \<open>type constructor arguments of all kinds\<close>
   A_nexp "nexp"  
 | A_typp "typp"  
 | A_order "order"  
 | A_bool "n_constraint"  
and typ_arg = 
   A_aux "typ_arg_aux"  
and n_constraint_aux =  \<comment> \<open>constraint over kind Int\<close>
   NC_equal "nexp" "nexp"  
 | NC_bounded_ge "nexp" "nexp"  
 | NC_bounded_gt "nexp" "nexp"  
 | NC_bounded_le "nexp" "nexp"  
 | NC_bounded_lt "nexp" "nexp"  
 | NC_not_equal "nexp" "nexp"  
 | NC_set "kid" "integer list"  
 | NC_or "n_constraint" "n_constraint"  
 | NC_and "n_constraint" "n_constraint"  
 | NC_app "id" "typ_arg list"  
 | NC_var "kid"  
 | NC_true  
 | NC_false  
and n_constraint = 
   NC_aux "n_constraint_aux"  

datatype lit = 
   L_aux "lit_aux"  

datatype typ_pat_aux =  \<comment> \<open>type pattern\<close>
   TP_wild  
 | TP_var "kid"  
 | TP_app "id" "typ_pat list"  
and typ_pat = 
   TP_aux "typ_pat_aux"  

datatype quant_item_aux =  \<comment> \<open>kinded identifier or Int constraint\<close>
   QI_id "kinded_id"   \<comment> \<open>optionally kinded identifier\<close>
 | QI_constraint "n_constraint"   \<comment> \<open>constraint\<close>
 | QI_constant "kinded_id list"  

datatype 'a pat_aux =  \<comment> \<open>pattern\<close>
   P_lit "lit"   \<comment> \<open>literal constant pattern\<close>
 | P_wild   \<comment> \<open>wildcard\<close>
 | P_or "'a pat" "'a pat"   \<comment> \<open>pattern disjunction\<close>
 | P_not "'a pat"   \<comment> \<open>pattern negation\<close>
 | P_as "'a pat" "id"   \<comment> \<open>named pattern\<close>
 | P_typp "typp" "'a pat"   \<comment> \<open>typed pattern\<close>
 | P_id "id"   \<comment> \<open>identifier\<close>
 | P_var "'a pat" "typ_pat"   \<comment> \<open>bind pattern to type variable\<close>
 | P_app "id" "'a pat list"   \<comment> \<open>union constructor pattern\<close>
 | P_vector "'a pat list"   \<comment> \<open>vector pattern\<close>
 | P_vector_concat "'a pat list"   \<comment> \<open>concatenated vector pattern\<close>
 | P_tup "'a pat list"   \<comment> \<open>tuple pattern\<close>
 | P_list "'a pat list"   \<comment> \<open>list pattern\<close>
 | P_cons "'a pat" "'a pat"   \<comment> \<open>Cons patterns\<close>
 | P_string_append "'a pat list"   \<comment> \<open>string append pattern, x ^^ y\<close>
and 'a pat = 
   P_aux "'a pat_aux" "'a annot"  

datatype quant_item = 
   QI_aux "quant_item_aux"  

datatype 'a internal_loop_measure_aux =  \<comment> \<open>internal syntax for an optional termination measure for a loop\<close>
   Measure_none  
 | Measure_some "'a exp"  
and 'a internal_loop_measure = 
   Measure_aux "'a internal_loop_measure_aux"  
and 'a exp_aux =  \<comment> \<open>expression\<close>
   E_block "'a exp list"   \<comment> \<open>sequential block\<close>
 | E_id "id"   \<comment> \<open>identifier\<close>
 | E_lit "lit"   \<comment> \<open>literal constant\<close>
 | E_app "id" "'a exp list"   \<comment> \<open>function application\<close>
 | E_tuple "'a exp list"   \<comment> \<open>tuple\<close>
 

 | E_cast "typp" "'a exp"   \<comment> \<open>cast\<close>

 | E_app_infix "'a exp" "id" "'a exp"   \<comment> \<open>infix function application\<close>

 | E_if "'a exp" "'a exp" "'a exp"   \<comment> \<open>conditional\<close>
 | E_loop "loop" "'a internal_loop_measure" "'a exp" "'a exp"  
 | E_for "id" "'a exp" "'a exp" "'a exp" "order" "'a exp"   \<comment> \<open>for loop\<close>
 | E_vector "'a exp list"   \<comment> \<open>vector (indexed from 0)\<close>
 | E_vector_access "'a exp" "'a exp"   \<comment> \<open>vector access\<close>
 | E_vector_subrange "'a exp" "'a exp" "'a exp"   \<comment> \<open>subvector extraction\<close>
 | E_vector_update "'a exp" "'a exp" "'a exp"   \<comment> \<open>vector functional update\<close>
 | E_vector_update_subrange "'a exp" "'a exp" "'a exp" "'a exp"   \<comment> \<open>vector subrange update, with vector\<close>
 | E_vector_append "'a exp" "'a exp"   \<comment> \<open>vector concatenation\<close>
 | E_list "'a exp list"   \<comment> \<open>list\<close>
 | E_cons "'a exp" "'a exp"   \<comment> \<open>cons\<close>
 | E_record "'a fexp list"   \<comment> \<open>struct\<close>
 | E_record_update "'a exp" "'a fexp list"   \<comment> \<open>functional update of struct\<close>
 | E_field "'a exp" "id"   \<comment> \<open>field projection from struct\<close>
 | E_case "'a exp" "'a pexp list"   \<comment> \<open>pattern matching\<close>
 | E_let "'a letbind" "'a exp"   \<comment> \<open>let expression\<close>
 | E_assign "'a lexp" "'a exp"   \<comment> \<open>imperative assignment\<close>
 | E_sizeof "nexp"   \<comment> \<open>the value of $nexp$ at run time\<close>
 | E_return "'a exp"   \<comment> \<open>return $'a exp$ from current function\<close>
 | E_exit "'a exp"   \<comment> \<open>halt all current execution\<close>
 | E_ref "id"  
 | E_throw "'a exp"  
 | E_try "'a exp" "'a pexp list"  
 | E_assert "'a exp" "'a exp"   \<comment> \<open>halt with error message $'a exp$ when not $'a exp$. exp' is optional.\<close>
 | E_var "'a lexp" "'a exp" "'a exp"   \<comment> \<open>This is an internal node for compilation that demonstrates the scope of a local mutable variable\<close>
 | E_internal_plet "'a pat" "'a exp" "'a exp"   \<comment> \<open>This is an internal node, used to distinguised some introduced lets during processing from original ones\<close>
 | E_internal_return "'a exp"   \<comment> \<open>For internal use to embed into monad definition\<close>
 | E_internal_value "value"   \<comment> \<open>For internal use in interpreter to wrap pre-evaluated values when returning an action\<close>
 | E_constraint "n_constraint" 
and 'a exp = 
   E_aux "'a exp_aux" "'a annot"  
and 'a lexp_aux =  \<comment> \<open>lvalue expression\<close>
   LEXP_id "id"   \<comment> \<open>identifier\<close>
 | LEXP_deref "'a exp"  
 | LEXP_memory "id" "'a exp list"   \<comment> \<open>memory or register write via function call\<close>
 | LEXP_cast "typp" "id"  
 | LEXP_tup "'a lexp list"   \<comment> \<open>multiple (non-memory) assignment\<close>
 | LEXP_vector_concat "'a lexp list"   \<comment> \<open>vector concatenation L-exp\<close>
 | LEXP_vector "'a lexp" "'a exp"   \<comment> \<open>vector element\<close>
 | LEXP_vector_range "'a lexp" "'a exp" "'a exp"   \<comment> \<open>subvector\<close>
 | LEXP_field "'a lexp" "id"   \<comment> \<open>struct field\<close>
and 'a lexp = 
   LEXP_aux "'a lexp_aux" "'a annot"  
and 'a fexp_aux =  \<comment> \<open>field expression\<close>
   FE_Fexp "id" "'a exp"  
and 'a fexp = 
   FE_aux "'a fexp_aux" "'a annot"  
and 'a pexp_aux =  \<comment> \<open>pattern match\<close>
   Pat_exp "'a pat" "'a exp"  
 | Pat_when "'a pat" "'a exp" "'a exp"  
and 'a pexp = 
   Pat_aux "'a pexp_aux" "'a annot"  
and 'a letbind_aux =  \<comment> \<open>let binding\<close>
   LB_val "'a pat" "'a exp"   \<comment> \<open>let, implicit type ($'a pat$ must be total)\<close>
and 'a letbind = 
   LB_aux "'a letbind_aux" "'a annot"  

datatype 'a mpat_aux =  \<comment> \<open>Mapping pattern. Mostly the same as normal patterns but only constructible parts\<close>
   MP_lit "lit"  
 | MP_id "id"  
 | MP_app "id" "'a mpat list"  
 | MP_vector "'a mpat list"  
 | MP_vector_concat "'a mpat list"  
 | MP_tup "'a mpat list"  
 | MP_list "'a mpat list"  
 | MP_cons "'a mpat" "'a mpat"  
 | MP_string_append "'a mpat list"  
 | MP_typp "'a mpat" "typp"  
 | MP_as "'a mpat" "id"  
and 'a mpat = 
   MP_aux "'a mpat_aux" "'a annot"  

datatype typquant_aux =  \<comment> \<open>type quantifiers and constraints\<close>
   TypQ_tq "quant_item list"  
 | TypQ_no_forall   \<comment> \<open>empty\<close>

datatype 'a reg_id_aux = 
   RI_id "id"  

datatype 'a mpexp_aux = 
   MPat_pat "'a mpat"  
 | MPat_when "'a mpat" "'a exp"  

datatype typquant = 
   TypQ_aux "typquant_aux"  

datatype 'a reg_id = 
   RI_aux "'a reg_id_aux" "'a annot"  

datatype  'a pexp_funcl = PEXP_funcl "'a pexp"

datatype 'a mpexp = 
   MPat_aux "'a mpexp_aux" "'a annot"  

datatype typschm_aux =  \<comment> \<open>type scheme\<close>
   TypSchm_ts "typquant" "typp"  

datatype 'a alias_spec_aux =  \<comment> \<open>register alias expression forms\<close>
   AL_subreg "'a reg_id" "id"  
 | AL_bit "'a reg_id" "'a exp"  
 | AL_slice "'a reg_id" "'a exp" "'a exp"  
 | AL_concat "'a reg_id" "'a reg_id"  

datatype tannot_opt_aux =  \<comment> \<open>optional type annotation for functions\<close>
   Typ_annot_opt_none  
 | Typ_annot_opt_some "typquant" "typp"  

datatype 'a funcl_aux =  \<comment> \<open>function clause\<close>
   FCL_Funcl "id" "'a pexp_funcl"  

datatype 'a rec_opt_aux =  \<comment> \<open>optional recursive annotation for functions\<close>
   Rec_nonrec   \<comment> \<open>non-recursive\<close>
 | Rec_rec   \<comment> \<open>recursive without termination measure\<close>
 | Rec_measure "'a pat" "'a exp"   \<comment> \<open>recursive with termination measure\<close>

datatype effect_opt_aux =  \<comment> \<open>optional effect annotation for functions\<close>
   Effect_opt_none   \<comment> \<open>no effect annotation\<close>
 | Effect_opt_effect "effect"  

datatype type_union_aux =  \<comment> \<open>type union constructors\<close>
   Tu_ty_id "typp" "id"  

datatype 'a mapcl_aux =  \<comment> \<open>mapping clause (bidirectional pattern-match)\<close>
   MCL_bidir "'a mpexp" "'a mpexp"  
 | MCL_forwards "'a mpexp" "'a exp"  
 | MCL_backwards "'a mpexp" "'a exp"  

datatype typschm = 
   TypSchm_aux "typschm_aux"  

datatype 'a alias_spec = 
   AL_aux "'a alias_spec_aux" "'a annot"  

datatype tannot_opt = 
   Typ_annot_opt_aux "tannot_opt_aux"  

datatype 'a funcl = 
   FCL_aux "'a funcl_aux" "'a annot"  

datatype 'a rec_opt = 
   Rec_aux "'a rec_opt_aux"  

datatype effect_opt = 
   Effect_opt_aux "effect_opt_aux"  

datatype type_union = 
   Tu_aux "type_union_aux"  

datatype 'a mapcl = 
   MCL_aux "'a mapcl_aux" "'a annot"  

datatype index_range_aux =  \<comment> \<open>index specification, for bitfields in register types\<close>
   BF_single "nexp"   \<comment> \<open>single index\<close>
 | BF_range "nexp" "nexp"   \<comment> \<open>index range\<close>
 | BF_concat "index_range" "index_range"   \<comment> \<open>concatenation of index ranges\<close>
and index_range = 
   BF_aux "index_range_aux"  

datatype default_spec_aux =  \<comment> \<open>default kinding or typing assumption\<close>
   DT_order "order"  

type_synonym "val_spec_aux" = "typschm * id  * (string => string option) * bool"
datatype 'a dec_spec_aux =  \<comment> \<open>register declarations\<close>
   DEC_reg "effect" "effect" "typp" "id"  
 | DEC_config "id" "typp" "'a exp"  
 | DEC_alias "id" "'a alias_spec"  
 | DEC_typ_alias "typp" "id" "'a alias_spec"  

datatype 'a fundef_aux =  \<comment> \<open>function definition\<close>
   FD_function "'a rec_opt" "tannot_opt" "effect_opt" "'a funcl list"  

datatype 'a scattered_def_aux =  \<comment> \<open>scattered function and union type definitions\<close>
   SD_function "'a rec_opt" "tannot_opt" "effect_opt" "id"   \<comment> \<open>scattered function definition header\<close>
 | SD_funcl "'a funcl"   \<comment> \<open>scattered function definition clause\<close>
 | SD_variant "id" "typquant"   \<comment> \<open>scattered union definition header\<close>
 | SD_unioncl "id" "type_union"   \<comment> \<open>scattered union definition member\<close>
 | SD_mapping "id" "tannot_opt"  
 | SD_mapcl "id" "'a mapcl"  
 | SD_end "id"   \<comment> \<open>scattered definition end\<close>

datatype type_def_aux =  \<comment> \<open>type definition body\<close>
   TD_abbrev "id" "typquant" "typ_arg"   \<comment> \<open>type abbreviation\<close>
 | TD_record "id" "typquant" "(typp*id) list" "bool"   \<comment> \<open>struct type definition\<close>
 | TD_variant "id" "typquant" "type_union list" "bool"   \<comment> \<open>tagged union type definition\<close>
 | TD_enum "id" "id list" "bool"   \<comment> \<open>enumeration type definition\<close>
 | TD_bitfield "id" "typp" "(id*index_range) list"   \<comment> \<open>register mutable bitfield type definition\<close>

datatype 'a mapdef_aux =  \<comment> \<open>mapping definition (bidirectional pattern-match function)\<close>
   MD_mapping "id" "tannot_opt" "'a mapcl list"  

datatype default_spec = 
   DT_aux "default_spec_aux"  

datatype val_spec = 
   VS_aux "val_spec_aux"  

datatype prec = 
   Infix  
 | InfixL  
 | InfixR  

datatype 'a dec_spec = 
   DEC_aux "'a dec_spec_aux" "'a annot"  

datatype 'a fundef = 
   FD_aux "'a fundef_aux" "'a annot"  

datatype 'a scattered_def = 
   SD_aux "'a scattered_def_aux" "'a annot"  

datatype 'a loop_measure = 
   Loop "loop" "'a exp"  

datatype type_def = 
   TD_aux "type_def_aux"  "'a annot"

datatype 'a mapdef = 
   MD_aux "'a mapdef_aux" "'a annot"  

datatype 'a opt_default_aux =  \<comment> \<open>optional default value for indexed vector expressions\<close>
   Def_val_empty  
 | Def_val_dec "'a exp"  

datatype 'a def =  \<comment> \<open>top-level definition\<close>
   DEF_type "type_def"   \<comment> \<open>type definition\<close>
 | DEF_fundef "'a fundef"   \<comment> \<open>function definition\<close>
 | DEF_mapdef "'a mapdef"   \<comment> \<open>mapping definition\<close>
 | DEF_val "'a letbind"   \<comment> \<open>value definition\<close>
 | DEF_spec "val_spec"   \<comment> \<open>top-level type constraint\<close>
 | DEF_fixity "prec" "integer" "id"   \<comment> \<open>fixity declaration\<close>
 | DEF_overload "id" "id list"   \<comment> \<open>operator overload specification\<close>
 | DEF_default "default_spec"   \<comment> \<open>default kind and type assumptions\<close>
 | DEF_scattered "'a scattered_def"   \<comment> \<open>scattered function and type definition\<close>
 | DEF_measure "id" "'a pat" "'a exp"   \<comment> \<open>separate termination measure declaration\<close>
 | DEF_loop_measures "id" "'a loop_measure list"   \<comment> \<open>separate termination measure declaration\<close>
 | DEF_reg_dec "'a dec_spec"   \<comment> \<open>register declaration\<close>
 | DEF_internal_mutrec "'a fundef list"   \<comment> \<open>internal representation of mutually recursive functions\<close>
 | DEF_pragma "string" "string"   \<comment> \<open>compiler directive\<close>

datatype 'a opt_default = 
   Def_val_aux "'a opt_default_aux" "'a annot"  

datatype 'a defs =  \<comment> \<open>definition sequence\<close>
   Defs "'a def list"  


end




theory Tests
imports Validator SailToMs

begin

hide_const id


values "{ x . check_exp emptyEnv ( (E_let (set_type None unit_typ)
              ( (LB_val None ( (P_id (set_type None (bool_typ True)) ( (id (STR ''x'')) )) )
                      ( (E_lit (set_type None (bool_typ True))) ( SailAST.L_true ))       ))
                      ( (E_lit (set_type None unit_typ) ( SailAST.L_unit ))) 
                                         )) unit_typ}"
(* function x : unit \<rightarrow> unit = x *)
value funcl1

values "{x . check_pexp emptyEnv pexp1 unit_typ }"

values "{ x . check_def  emptyEnv (DEF_fundef ( (FD_function unk Rec_nonrec  ( (Typ_annot_opt_some 
   ( (TypQ_tq [ (QI_id ( (KOpt_kind ( K_int ) ( (var (STR ''x'')) )) ))   ]) )
  ( (Typ_fn [unit_typ] unit_typ ( (Effect_set Nil)  )) )  ) ) ( Effect_opt_none ) [funcl1]) )) }"

end
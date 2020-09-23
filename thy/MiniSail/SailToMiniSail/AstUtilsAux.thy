theory AstUtils
  imports  SailAST
begin


definition unit_typ where
  "unit_typ \<equiv> (Typ_aux (Typ_id (Id_aux (id (STR ''unit'')) )) )"

definition num_typ where
  "num_typ n \<equiv>  (Typ_aux (Typ_app (Id_aux (id (STR ''atom''))  ) 
     [(A_aux (A_nexp (Nexp_aux (Nexp_constant n)  ))  ) ] )  )"

definition int_typ where 
  "int_typ \<equiv>  (Typ_aux (Typ_id (Id_aux (id (STR ''int'')) )) )"

fun bool_typ where
  "bool_typ b =  (Typ_aux (Typ_app (Id_aux (id (STR ''atom_bool''))  ) 
     [(A_aux (A_bool (NC_aux (if b then NC_true else NC_false)  ))  ) ] )  )"

abbreviation "nc_eq \<equiv> \<lambda>n1 n2. NC_aux (NC_equal n1 n2) "

abbreviation "nint \<equiv> \<lambda>i. Nexp_aux (Nexp_constant i) "

abbreviation "nc_pos \<equiv> \<lambda>ne. NC_aux (NC_bounded_ge ne (nint 0))"

abbreviation "nc_true \<equiv> NC_aux NC_true"


(*
abbreviation "nexp_simp \<equiv> \<lambda>n. n"
*)



abbreviation nexp_var where
  "nexp_var s \<equiv> Nexp_aux (Nexp_var (Kid_aux (var s)))"

abbreviation atom_typ_var where
  "atom_typ_var s \<equiv> Typ_aux (Typ_app (Id_aux (id (STR ''atom''))) [ A_aux (A_nexp  (Nexp_aux (Nexp_var (Kid_aux (var s))))) ] )"

abbreviation nexp_const where
  "nexp_const s \<equiv> Nexp_aux (Nexp_constant s)"

abbreviation num_or where
 "num_or n1 n2 \<equiv> Typ_aux (Typ_exist [] (NC_aux (NC_or (nc_eq (nexp_var (STR ''n'')) (nexp_const 1)) (nc_eq (nexp_var (STR ''n'')) (nexp_const 2)))) (atom_typ_var (STR ''n'') ))"



end

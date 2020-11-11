(*<*)
theory IVSubstDBI
  imports  SyntaxDBI DBIndex
begin
(*>*)

chapter \<open>Immutable Variable Substitution\<close>

section \<open>Class\<close>

class has_subst_v = has_x_vars +
  fixes subst_v :: "'a \<Rightarrow> x \<Rightarrow> v \<Rightarrow> 'a"   ("_[_::=_]\<^sub>v" [1000,50,50] 1000)



section \<open>Values\<close>

fun
   subst_vv :: "v \<Rightarrow> x \<Rightarrow> v \<Rightarrow> v" where
   "subst_vv (V_lit l) x v = V_lit l"
 | "subst_vv (V_var y) x v = (if x = y then v else V_var y)"
 | "subst_vv (V_cons tyid c v') x v  = V_cons tyid c (subst_vv v' x v)"
 | "subst_vv (V_consp tyid c b v') x v  = V_consp tyid c b (subst_vv v' x v)"
 | "subst_vv (V_pair v1 v2) x v = V_pair (subst_vv v1 x v ) (subst_vv v2 x v )"


abbreviation 
  subst_vv_abbrev :: "v \<Rightarrow> x \<Rightarrow> v \<Rightarrow> v" ("_[_::=_]\<^sub>v\<^sub>v" [1000,50,50] 1000)
where 
  "v[x::=v']\<^sub>v\<^sub>v  \<equiv> subst_vv v x v'" 

instantiation v :: has_subst_v
begin

definition 
  "subst_v = subst_vv"

instance proof

qed

end

section \<open>Expressions\<close>

fun subst_ev :: "e \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> e" where
  "subst_ev  ( (AE_val v') ) x v = ( (AE_val (subst_vv v' x v)) )"
| "subst_ev  ( (AE_app f v') ) x v  = ( (AE_app f (subst_vv v' x v )) )"                
| "subst_ev  ( (AE_appP f b v') ) x v = ( (AE_appP f b (subst_vv v' x v )) )"   
| "subst_ev  ( (AE_op opp v1 v2) ) x v  = ( (AE_op opp (subst_vv v1 x v ) (subst_vv v2 x v )) )"
| "subst_ev  [#1 v']\<^sup>e x v = [#1 (subst_vv v' x v )]\<^sup>e"
| "subst_ev  [#2 v']\<^sup>e x v = [#2 (subst_vv v' x v )]\<^sup>e"
| "subst_ev  ( (AE_mvar u)) x v = AE_mvar u"
| "subst_ev  [| v' |]\<^sup>e x v = [| (subst_vv  v' x v ) |]\<^sup>e"
| "subst_ev  ( AE_concat v1 v2) x v = AE_concat (subst_vv v1 x v ) (subst_vv v2 x v )"


abbreviation 
  subst_ev_abbrev :: "e \<Rightarrow> x \<Rightarrow> v \<Rightarrow> e" ("_[_::=_]\<^sub>e\<^sub>v" [1000,50,50] 500)
where 
  "e[x::=v']\<^sub>e\<^sub>v  \<equiv> subst_ev e x v' " 

instantiation e :: has_subst_v
begin

definition 
  "subst_v = subst_ev"

instance proof

qed
end


section \<open>Expressions in Constraints\<close>

fun subst_cev :: "ce \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> ce" where
  "subst_cev ( (CE_val v') ) x v = ( (CE_val (subst_vv  v' x v )) )" 
| "subst_cev ( (CE_op opp v1 v2) ) x v = ( (CE_op opp (subst_vv  v1 x v ) (subst_vv v2 x v )) )"
| "subst_cev ( (CE_fst v')) x v = CE_fst (subst_vv  v' x v )"
| "subst_cev ( (CE_snd v')) x v = CE_snd (subst_vv  v' x v )"
| "subst_cev ( (CE_len v')) x v = CE_len (subst_vv  v' x v )"
| "subst_cev ( CE_concat v1 v2) x v = CE_concat (subst_vv v1 x v ) (subst_vv v2 x v )"



abbreviation 
  subst_cev_abbrev :: "ce \<Rightarrow> x \<Rightarrow> v \<Rightarrow> ce" ("_[_::=_]\<^sub>c\<^sub>e\<^sub>v" [1000,50,50] 500)
where 
  "e[x::=v']\<^sub>c\<^sub>e\<^sub>v  \<equiv> subst_cev  e x v'" 


instantiation ce :: has_subst_v
begin


definition 
  "subst_v = subst_cev"

instance proof

qed

end


section \<open>Constraints\<close>

fun subst_cv :: "c \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> c" where
   "subst_cv (C_true) x v = C_true"
|  "subst_cv (C_false) x v = C_false"
|  "subst_cv (C_conj c1 c2) x v = C_conj (subst_cv c1 x v ) (subst_cv c2 x v )"
|  "subst_cv (C_disj c1 c2) x v = C_disj (subst_cv c1 x v ) (subst_cv c2 x v )"
|  "subst_cv (C_imp c1 c2) x v = C_imp (subst_cv c1 x v ) (subst_cv c2 x v )"
|  "subst_cv (e1 == e2) x v = ((subst_cev e1 x v ) == (subst_cev e2 x v ))"
|  "subst_cv (C_not c) x v = C_not (subst_cv c x v )"


abbreviation 
  subst_cv_abbrev :: "c \<Rightarrow> x \<Rightarrow> v \<Rightarrow> c" ("_[_::=_]\<^sub>c\<^sub>v" [1000,50,50] 1000)
where 
  "c[x::=v']\<^sub>c\<^sub>v  \<equiv> subst_cv c x v'" 


instantiation c :: has_subst_v
begin

definition 
  "subst_v = subst_cv"

instance proof

qed

end


section \<open>Variable Context\<close>

(* The idea of this substitution is to remove x from \<Gamma>. We really want to add the condition that x is fresh in v 
but this causes problems with proofs. So we need to make sure x \<sharp> v each time it is used to ensure wellfoundness of \<Gamma>[x::=v]*)
fun subst_gv_aux :: "nat \<Rightarrow> \<Gamma>  \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> \<Gamma>" where
  "subst_gv_aux _ GNil x v = GNil"
| "subst_gv_aux n ((b,c)#\<Gamma>) (XBVar k) v  = (if n = k then (unlift_x \<Gamma> k 1) else ((b,c[(XBVar k)::=v]\<^sub>c\<^sub>v)# (subst_gv_aux  (n+1) \<Gamma>  (XBVar k) v )))"

definition subst_gv where "subst_gv \<equiv>  subst_gv_aux 0"


abbreviation 
  subst_gv_abbrev :: "\<Gamma> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<Gamma>" ("_[_::=_]\<^sub>\<Gamma>\<^sub>v" [1000,50,50] 1000)
where 
  "g[x::=v]\<^sub>\<Gamma>\<^sub>v  \<equiv> subst_gv g x v" 


section \<open>Types\<close>



fun subst_tv :: "\<tau> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<tau>" where
  "subst_tv  \<lbrace> : b | c \<rbrace> (XBVar k) v  = \<lbrace> : b | c[(XBVar (k+1))::=v]\<^sub>c\<^sub>v \<rbrace>"

abbreviation 
  subst_tv_abbrev :: "\<tau> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<tau>" ("_[_::=_]\<^sub>\<tau>\<^sub>v" [1000,50,50] 1000)
where 
  "t[x::=v]\<^sub>\<tau>\<^sub>v  \<equiv> subst_tv t x v" 


instantiation \<tau> :: has_subst_v
begin

definition 
  "subst_v = subst_tv"

instance ..
end

section \<open>Mutable Variable Context\<close>


fun subst_dv :: "\<Delta> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<Delta>" where
  "subst_dv  DNil x v = DNil"
| "subst_dv ((t)#\<Delta>) x v  = ((t[x::=v]\<^sub>\<tau>\<^sub>v) # (subst_dv \<Delta> x v ))"


abbreviation 
  subst_dv_abbrev :: "\<Delta> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<Delta>" ("_[_::=_]\<^sub>\<Delta>\<^sub>v" [1000,50,50] 1000)
where 
  "\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v  \<equiv> subst_dv \<Delta> x v " 

section \<open>Statements\<close>


fun 
subst_sv :: "s \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> s"
and subst_branchv :: "branch_s \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> branch_s" 
and subst_branchlv :: "branch_list \<Rightarrow> x \<Rightarrow> v \<Rightarrow> branch_list" where
   "subst_sv ( (AS_val v') ) x v = (AS_val (subst_vv v' x v  ))"
 | "subst_sv  (AS_let  e s) (XBVar k) v = (AS_let  (e[(XBVar k)::=v]\<^sub>e\<^sub>v) (subst_sv s (XBVar (k+1)) v ))"  
 | "subst_sv (AS_let2 t s1 s2) (XBVar k) v = (AS_let2 (t[(XBVar k)::=v]\<^sub>\<tau>\<^sub>v) (subst_sv s1 (XBVar k) v ) (subst_sv s2 (XBVar (k+1)) v ))"  
 | "subst_sv (AS_match v'  cs) x v = AS_match  (v'[x::=v]\<^sub>v\<^sub>v)  (subst_branchlv cs x v )"
 | "subst_sv (AS_assign y v') x v = AS_assign y (subst_vv v' x v )"
 | "subst_sv ( (AS_if v' s1 s2) ) x v = (AS_if (subst_vv v' x v ) (subst_sv s1 x v ) (subst_sv s2 x v ) )"  
 | "subst_sv (AS_var \<tau> v' s) x v = AS_var (subst_tv \<tau> x v ) (subst_vv v' x v ) (subst_sv s x v ) "
 | "subst_sv (AS_while s1 s2) x v = AS_while (subst_sv s1 x v ) (subst_sv s2 x v )"
 | "subst_sv (AS_seq s1 s2) x v = AS_seq (subst_sv s1 x v ) (subst_sv s2 x v )" 

 | "subst_branchv (AS_branch dc s1 ) (XBVar k) v  = AS_branch dc (subst_sv s1 (XBVar (k+1)) v )" 

 | "subst_branchlv (AS_final cs) x v = AS_final (subst_branchv  cs x v )"
 | "subst_branchlv (AS_cons cs css) x v = AS_cons (subst_branchv cs x v ) (subst_branchlv css x v )"

abbreviation 
  subst_sv_abbrev :: "s \<Rightarrow> x \<Rightarrow> v \<Rightarrow> s" ("_[_::=_]\<^sub>s\<^sub>v" [1000,50,50] 1000)
where 
  "s[x::=v]\<^sub>s\<^sub>v  \<equiv> subst_sv s x v" 

abbreviation 
  subst_branchv_abbrev :: "branch_s \<Rightarrow> x \<Rightarrow> v \<Rightarrow> branch_s" ("_[_::=_]\<^sub>s\<^sub>v" [1000,50,50] 1000)
where 
  "s[x::=v]\<^sub>s\<^sub>v  \<equiv> subst_branchv s x v" 

instantiation s :: has_subst_v
begin

definition 
  "subst_v = subst_sv"

instance proof
 
qed
end



end
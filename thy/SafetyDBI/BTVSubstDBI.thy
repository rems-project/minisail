(*<*)
theory BTVSubstDBI
  imports DBIndex
begin
(*>*)
chapter \<open>Base Type Variable Substitution\<close>

section \<open>Class\<close>

class has_subst_b = has_b_vars +
  fixes subst_b :: "'a \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> 'a" ("_[_::=_]\<^sub>b" [1000,50,50] 1000)


section \<open>Base Type\<close>

fun subst_bb :: "b \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> b" where
  "subst_bb  (B_var bv2) bv1 b  = (if bv1 = bv2 then b else (B_var bv2))"
 | "subst_bb  B_int bv1 b  = B_int"
 | "subst_bb B_bool bv1 b = B_bool"
 | "subst_bb (B_id s) bv1 b = B_id s "
 | "subst_bb (B_pair b1 b2) bv1 b = B_pair (subst_bb b1 bv1 b) (subst_bb b2 bv1 b)"
 | "subst_bb B_unit bv1 b = B_unit  "
 | "subst_bb B_bitvec bv1 b = B_bitvec "
 | "subst_bb (B_app s b2) bv1 b = B_app s (subst_bb b2 bv1 b)"



abbreviation 
  subst_bb_abbrev :: "b \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> b" ("_[_::=_]\<^sub>b\<^sub>b" [1000,50,50] 1000)
where 
  "b[bv::=b']\<^sub>b\<^sub>b  \<equiv> subst_bb b bv b' " 

instantiation b :: has_subst_b
begin
definition "subst_b = subst_bb"

instance proof

qed
end

section \<open>Value\<close>

fun subst_vb :: "v \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> v" where
   "subst_vb (V_lit l) x v = V_lit l"
 | "subst_vb (V_var y) x v = V_var y"
 | "subst_vb (V_cons tyid c v') x v  = V_cons tyid c (subst_vb v' x v)"
 | "subst_vb (V_consp tyid c b v') x v  = V_consp tyid c (subst_bb b x v) (subst_vb v' x v)"
 | "subst_vb (V_pair v1 v2) x v = V_pair (subst_vb v1 x v ) (subst_vb v2 x v )"

abbreviation 
  subst_vb_abbrev :: "v \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> v" ("_[_::=_]\<^sub>v\<^sub>b" [1000,50,50] 500)
where 
  "e[bv::=b]\<^sub>v\<^sub>b  \<equiv> subst_vb e bv b" 

instantiation v :: has_subst_b
begin
definition "subst_b = subst_vb"



instance proof


qed
end

section \<open>Constraints Expressions\<close>

fun subst_ceb :: "ce \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> ce" where
  "subst_ceb  ( (CE_val v') ) bv b = ( CE_val (subst_vb v' bv b) )"
| "subst_ceb  ( (CE_op opp v1 v2) ) bv b = ( (CE_op opp (subst_vb v1 bv b)(subst_vb v2 bv b)) )"
| "subst_ceb  ( (CE_fst v')) bv b = CE_fst (subst_vb v' bv b)"
| "subst_ceb  ( (CE_snd v')) bv b = CE_snd (subst_vb v' bv b)"
| "subst_ceb  ( (CE_len v')) bv b = CE_len (subst_vb v' bv b)"
| "subst_ceb  ( CE_concat v1 v2) bv b = CE_concat (subst_vb v1 bv b) (subst_vb v2 bv b)"


abbreviation 
  subst_ceb_abbrev :: "ce \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> ce" ("_[_::=_]\<^sub>c\<^sub>e\<^sub>b" [1000,50,50] 500)
where 
  "ce[bv::=b]\<^sub>c\<^sub>e\<^sub>b  \<equiv> subst_ceb ce bv b" 

instantiation ce :: has_subst_b
begin
definition "subst_b = subst_ceb"

instance
proof
qed
end


section \<open>Constraints\<close>

fun subst_cb :: "c \<Rightarrow> bv \<Rightarrow> b  \<Rightarrow> c" where
   "subst_cb (C_true) x v = C_true"
|  "subst_cb (C_false) x v = C_false"
|  "subst_cb (C_conj c1 c2) x v = C_conj (subst_cb c1 x v ) (subst_cb c2 x v )"
|  "subst_cb (C_disj c1 c2) x v = C_disj (subst_cb c1 x v ) (subst_cb c2 x v )"
|  "subst_cb (C_imp c1 c2) x v = C_imp (subst_cb c1 x v ) (subst_cb c2 x v )"
|  "subst_cb (C_eq e1 e2) x v = C_eq (subst_ceb e1 x v ) (subst_ceb e2 x v )"
|  "subst_cb (C_not c) x v = C_not (subst_cb c x v )"


abbreviation 
  subst_cb_abbrev :: "c \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> c" ("_[_::=_]\<^sub>c\<^sub>b" [1000,50,50] 500)
where 
  "c[bv::=b]\<^sub>c\<^sub>b  \<equiv> subst_cb c bv b" 


instantiation c :: has_subst_b
begin
definition "subst_b = subst_cb"

instance proof
 
qed
end


section \<open>Types\<close>


fun subst_tb :: "\<tau> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<tau>" where
  "subst_tb  (\<lbrace>  : b2 | c \<rbrace>) bv1 b1 = \<lbrace> : b2[bv1::=b1]\<^sub>b\<^sub>b | c[bv1::=b1]\<^sub>c\<^sub>b \<rbrace>"



abbreviation 
  subst_tb_abbrev :: "\<tau> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<tau>" ("_[_::=_]\<^sub>\<tau>\<^sub>b" [1000,50,50] 1000)
where 
  "t[bv::=b']\<^sub>\<tau>\<^sub>b  \<equiv> subst_tb t bv b' " 


instantiation \<tau> :: has_subst_b
begin
definition "subst_b = subst_tb"


instance proof

qed
end


section \<open>Expressions\<close>

fun subst_eb :: "e \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> e" where
  "subst_eb ( (AE_val v')) bv b  = ( AE_val (subst_vb v' bv b))"
| "subst_eb ( (AE_app f v') ) bv b = ( (AE_app f (subst_vb v' bv b)) )"                
| "subst_eb ( (AE_appP f b' v') ) bv b = ( (AE_appP f (b'[bv::=b]\<^sub>b\<^sub>b) (subst_vb v' bv b)))"   
| "subst_eb ( (AE_op opp v1 v2) ) bv b = ( (AE_op opp (subst_vb v1 bv b) (subst_vb v2 bv b)) )"
| "subst_eb ( (AE_fst v')) bv b = AE_fst (subst_vb v' bv b)"
| "subst_eb ( (AE_snd v')) bv b = AE_snd (subst_vb v' bv b)"
| "subst_eb ( (AE_mvar u)) bv b = AE_mvar u"
| "subst_eb ( (AE_len v')) bv b = AE_len (subst_vb v' bv b)"
| "subst_eb ( AE_concat v1 v2) bv b = AE_concat (subst_vb v1 bv b) (subst_vb v2 bv b)"


abbreviation 
  subst_eb_abbrev :: "e \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> e" ("_[_::=_]\<^sub>e\<^sub>b" [1000,50,50] 500)
where 
  "e[bv::=b]\<^sub>e\<^sub>b  \<equiv> subst_eb e bv b" 

instantiation e :: has_subst_b
begin
definition "subst_b = subst_eb"

instance proof

qed
end

section \<open>Statements\<close>

fun subst_sb :: "s \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> s"
and subst_branchb :: "branch_s \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> branch_s" 
and subst_branchlb :: "branch_list \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> branch_list"
where
   "subst_sb (AS_val v') bv b        = (AS_val (subst_vb v' bv b))"
 | "subst_sb  (AS_let   e s)  bv b   = (AS_let   (e[bv::=b]\<^sub>e\<^sub>b) (subst_sb s bv b ))"  
 | "subst_sb (AS_let2  t s1 s2) bv b = (AS_let2  (subst_tb t bv b) (subst_sb s1 bv b ) (subst_sb s2 bv b))"  
 | "subst_sb (AS_match v'  cs) bv b   = AS_match  (subst_vb v' bv b)  (subst_branchlb cs bv b)"
 | "subst_sb  (AS_assign y v') bv b   = AS_assign y (subst_vb v' bv b)"
 | "subst_sb  (AS_if v' s1 s2) bv b   = (AS_if (subst_vb v' bv b) (subst_sb s1 bv b ) (subst_sb s2 bv b ) )"  
 | "subst_sb  (AS_var  \<tau> v' s) bv b   = AS_var  (subst_tb  \<tau> bv b)  (subst_vb v' bv b) (subst_sb s bv b )"
 | "subst_sb  (AS_while s1 s2) bv b   = AS_while (subst_sb s1 bv b  ) (subst_sb s2 bv b )"
 | "subst_sb  (AS_seq s1 s2)  bv b    = AS_seq (subst_sb s1 bv b ) (subst_sb s2 bv b )"

| "subst_branchb (AS_branch dc  s') bv b = AS_branch dc  (subst_sb s' bv b)"

| "subst_branchlb  (AS_final sb)  bv b     = AS_final (subst_branchb sb bv b )"
| "subst_branchlb  (AS_cons sb ssb) bv b   = AS_cons (subst_branchb sb bv b) (subst_branchlb ssb bv b)"

abbreviation 
  subst_sb_abbrev :: "s \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> s" ("_[_::=_]\<^sub>s\<^sub>b" [1000,50,50] 1000)
where 
  "b[bv::=b']\<^sub>s\<^sub>b  \<equiv> subst_sb b bv b'" 

instantiation s :: has_subst_b
begin
definition "subst_b = (\<lambda>s bv b. subst_sb s bv b)"

instance proof
 
qed
end

section \<open>Function Type\<close>

fun subst_ft_b :: "fun_typ \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> fun_typ" where
 "subst_ft_b ( AF_fun_typ b c t (s::s)) x v = AF_fun_typ  (subst_bb b x v) (subst_cb c x v) t[x::=v]\<^sub>\<tau>\<^sub>b s[x::=v]\<^sub>s\<^sub>b"



fun subst_ftq_b :: "fun_typ_q \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> fun_typ_q" where
"subst_ftq_b (AF_fun_typ_some ft) (BVBVar k) v = (AF_fun_typ_some (subst_ft_b ft (BVBVar (k+1)) v))" 
|  "subst_ftq_b (AF_fun_typ_none  ft) x v = (AF_fun_typ_none (subst_ft_b ft x v))" 



instantiation fun_typ :: has_subst_b
begin
definition "subst_b = subst_ft_b"



instance proof

qed
end

instantiation fun_typ_q :: has_subst_b
begin
definition "subst_b = subst_ftq_b"

instance proof

qed
end



section \<open>Contexts\<close>

subsection \<open>Immutable Variables\<close>
fun subst_gb :: "\<Gamma> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<Gamma>" where
  "subst_gb GNil _ _  = GNil"
| "subst_gb ((b',c)#\<Gamma>) bv b = ((b'[bv::=b]\<^sub>b\<^sub>b,c[bv::=b]\<^sub>c\<^sub>b)# (subst_gb \<Gamma> bv b))"

abbreviation 
  subst_gb_abbrev :: "\<Gamma> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<Gamma>" ("_[_::=_]\<^sub>\<Gamma>\<^sub>b" [1000,50,50] 1000)
where 
  "g[bv::=b']\<^sub>\<Gamma>\<^sub>b  \<equiv> subst_gb g bv b'" 


instantiation \<Gamma> :: has_subst_b
begin
definition "subst_b = subst_gb"

instance proof

qed
end



subsection \<open>Mutable Variables\<close>

fun subst_db :: "\<Delta> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<Delta>" where
  "subst_db [] _ _  = []"
| "subst_db  ((t)#\<Delta>) bv b = ((t[bv::=b]\<^sub>\<tau>\<^sub>b) # (subst_db \<Delta> bv b))"


abbreviation 
  subst_db_abbrev :: "\<Delta> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<Delta>" ("_[_::=_]\<^sub>\<Delta>\<^sub>b" [1000,50,50] 1000)
where 
  "\<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<equiv> subst_db \<Delta> bv b" 

instantiation \<Delta> :: has_subst_b
begin
definition "subst_b = subst_db"


instance proof

qed
end




end
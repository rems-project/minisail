theory DBIndex
  imports SyntaxDBI
begin

text \<open>Machinery specific to using DBI. 

A reminder of what we are doing.

We have 

let x = e in x  is represented as  LET = e IN (XBVar 0)

the index on a variable represents its distance from binder.

and 

let x = 1 in (let y = x+2 in let z = y + 1 in x + y + z) == LET 1 IN ( LET ((XBVar 0) + 2) IN (LET (XBVar 0 + 1) (XBVar 2) + (XBVar 1) + (XBVar 0)

which we unpactk to be

(int, XBVar 0 = XBVar 1 + 1) # (int, XBVar 1 = (XBVar 2 + 2) # (int, XBVar 2 = 1) |- (XBVar 2) + (XBVar 1) + (XBVar 0)

If if subst y for something 9 in the context then need 
to down x.

(int, XBVar 0 = 1) |- (XBVar 0) + 9

Rule is: Any var > the one being subst is reduced by one in context and term after |-


\<close>

section  \<open>Terms With Immutable Variables\<close>

fun listG :: "\<Gamma> \<Rightarrow> (b*c) list" where
 "listG GNil = []"
 | "listG ((b,c)#G) = (b,c) # (listG G)"



subsection \<open>Class\<close>
class has_x_vars =
  fixes lift_x :: "'a \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> 'a" and
        unlift_x  :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a "   
       


begin

end

abbreviation 
  lift_x_abbrev :: "'a::has_x_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" ("_\<up>\<^sub>_\<^sup>_" [1000,50,50] 1000)
where 
  "t\<up>\<^sub>i\<^sup>j  \<equiv> lift_x t i j"

subsection \<open>Values\<close>

fun lift_x_x :: "x \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> x" where
  "lift_x_x   (XBVar k) i j  = (if k < i then (XBVar k) else XBVar (k+j))"

fun unlift_x_x :: "x \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> x" where
  "unlift_x_x   (XBVar k) i j  = (if k > i then (XBVar (k-j)) else XBVar k)"


fun lift_x_v :: "v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> v" where
   "lift_x_v (V_var x) i j = V_var (lift_x_x x i j)"
 |  "lift_x_v (V_lit l) xf i = V_lit l"
 |  "lift_x_v (V_pair v1 v2) xf i = V_pair (lift_x_v v1 xf i) (lift_x_v v2 xf i)"
 |  "lift_x_v (V_cons x y v) xf i = V_cons x y (lift_x_v v xf i)"

fun unlift_x_v :: "v \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> v" where
   "unlift_x_v (V_var x) i j = V_var (unlift_x_x x i j)"
 |  "unlift_x_v (V_lit l) xf i = V_lit l"
 |  "unlift_x_v (V_pair v1 v2) xf i = V_pair (lift_x_v v1 xf i) (lift_x_v v2 xf i)"
 |  "unlift_x_v (V_cons x y v) xf i = V_cons x y (lift_x_v v xf i)"


fun base_for_lit :: "l \<Rightarrow> b" where
  "base_for_lit (L_true) = B_bool "
| "base_for_lit (L_false) = B_bool "
| "base_for_lit (L_num n) = B_int "
| "base_for_lit (L_unit) = B_unit " 
| "base_for_lit (L_bitvec v) = B_bitvec"



fun type_for_lit :: "l \<Rightarrow> \<tau>" where
  "type_for_lit (L_true) = (\<lbrace> : B_bool | C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit L_true)) \<rbrace>)"
| "type_for_lit (L_false) = (\<lbrace>  : B_bool | C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit L_false)) \<rbrace>)"
| "type_for_lit (L_num n) = (\<lbrace>  : B_int | C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit (L_num n))) \<rbrace>)"
| "type_for_lit (L_unit) = (\<lbrace>  : B_unit | C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit (L_unit ))) \<rbrace>)" (* could have done { z : unit | True } but want the uniformity *)
| "type_for_lit (L_bitvec v) = (\<lbrace>  : B_bitvec | C_eq (CE_val (V_var (XBVar 0))) (CE_val (V_lit (L_bitvec v ))) \<rbrace>)"


(* Defining as functions outside and then using definitions provides the nice/uniform def and simps *)
instantiation v :: has_x_vars
begin
definition "lift_x = lift_x_v" 
definition  "unlift_x = unlift_x_v"
instance by standard

end

subsection \<open>Expressions\<close>

fun lift_x_e :: "e \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> e" where
  "lift_x_e  ( (AE_val v') ) i j = AE_val (lift_x v' i j)"
| "lift_x_e  ( (AE_app f v') ) i j  = AE_app f (lift_x v' i j)"                
| "lift_x_e  ( (AE_appP f b v') ) i j = ( (AE_appP f b ((lift_x v' i j) )) )"   
| "lift_x_e  ( (AE_op opp v1 v2) ) i j  = ( (AE_op opp ((lift_x v1 i j) ) ((lift_x v2 i j))) )"
| "lift_x_e  ( (AE_fst v')) i j = AE_fst (lift_x v' i j )"
| "lift_x_e  ( (AE_snd v')) i j = AE_snd (lift_x v' i j )"
| "lift_x_e  ( (AE_mvar u)) i j = AE_mvar u"
| "lift_x_e  ( (AE_len v')) i j = AE_len (lift_x  v' i j )"
| "lift_x_e  ( AE_concat v1 v2) i j = AE_concat (lift_x v1 i j)  (lift_x v2 i j)"

fun unlift_x_e :: "e \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> e" where
  "unlift_x_e  ( (AE_val v') ) i j = AE_val (unlift_x v' i j)"
| "unlift_x_e  ( (AE_app f v') ) i j  = AE_app f (unlift_x v' i j)"                
| "unlift_x_e  ( (AE_appP f b v') ) i j = ( (AE_appP f b ((unlift_x v' i j) )) )"   
| "unlift_x_e  ( (AE_op opp v1 v2) ) i j  = ( (AE_op opp ((unlift_x v1 i j) ) ((unlift_x v2 i j))) )"
| "unlift_x_e  ( (AE_fst v')) i j = AE_fst (unlift_x v' i j )"
| "unlift_x_e  ( (AE_snd v')) i j = AE_snd (unlift_x v' i j )"
| "unlift_x_e  ( (AE_mvar u)) i j = AE_mvar u"
| "unlift_x_e  ( (AE_len v')) i j = AE_len (unlift_x  v' i j )"
| "unlift_x_e  ( AE_concat v1 v2) i j = AE_concat (unlift_x v1 i j)  (unlift_x v2 i j)"  


instantiation e :: has_x_vars
begin
definition "lift_x = lift_x_e"
definition "unlift_x = unlift_x_e"

instance by standard

end

subsection \<open>Constraint Expressions\<close>

fun lift_x_ce :: "ce \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ce" where
  "lift_x_ce  ( (CE_val v') ) x i = ( (CE_val (lift_x v' x i)) )"  
| "lift_x_ce  ( (CE_op opp v1 v2) ) x i  = ( (CE_op opp (lift_x v1 x i ) (lift_x v2 x i )) )"
| "lift_x_ce  ( (CE_fst v')) x i = CE_fst (lift_x v' x i )"
| "lift_x_ce  ( (CE_snd v')) x i = CE_snd (lift_x v' x i )"
| "lift_x_ce  ( (CE_len v')) x i = CE_len (lift_x  v' x i )"
| "lift_x_ce  ( CE_concat v1 v2) x i = CE_concat (lift_x v1 x i ) (lift_x v2 x i )"

fun unlift_x_ce :: "ce \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ce" where
  "unlift_x_ce  ( (CE_val v') ) x i = ( (CE_val (unlift_x v' x i)) )"  
| "unlift_x_ce  ( (CE_op opp v1 v2) ) x i  = ( (CE_op opp (unlift_x v1 x i ) (unlift_x v2 x i )) )"
| "unlift_x_ce  ( (CE_fst v')) x i = CE_fst (unlift_x v' x i )"
| "unlift_x_ce  ( (CE_snd v')) x i = CE_snd (unlift_x v' x i )"
| "unlift_x_ce  ( (CE_len v')) x i = CE_len (unlift_x  v' x i )"
| "unlift_x_ce  ( CE_concat v1 v2) x i = CE_concat (unlift_x v1 x i ) (unlift_x v2 x i )"

instantiation ce :: has_x_vars
begin
definition "lift_x = lift_x_ce"
definition "unlift_x = unlift_x_ce"

instance by standard

end

subsection \<open>Constraints\<close>

fun lift_x_c :: "c \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> c" where
   "lift_x_c (C_true)  x v = C_true"
|  "lift_x_c (C_false)  x v = C_false"
|  "lift_x_c (C_conj c1 c2)  x v = C_conj (lift_x_c c1  x v ) (lift_x_c c2   x v)"
|  "lift_x_c (C_disj c1 c2)  x v = C_disj (lift_x_c c1 x v  ) (lift_x_c c2  x v )"
|  "lift_x_c (C_imp c1 c2) x v  = C_imp (lift_x_c c1  x v ) (lift_x_c c2  x v )"
|  "lift_x_c (C_eq e1 e2)  x v = C_eq (lift_x e1  x v  ) (lift_x e2  x v )"
|  "lift_x_c (C_not c)   x v= C_not (lift_x_c c   x v)"

fun unlift_x_c :: "c \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> c" where
   "unlift_x_c (C_true)  x v = C_true"
|  "unlift_x_c (C_false)  x v = C_false"
|  "unlift_x_c (C_conj c1 c2)  x v = C_conj (unlift_x_c c1  x v ) (unlift_x_c c2   x v)"
|  "unlift_x_c (C_disj c1 c2)  x v = C_disj (unlift_x_c c1 x v  ) (unlift_x_c c2  x v )"
|  "unlift_x_c (C_imp c1 c2) x v  = C_imp (unlift_x_c c1  x v ) (unlift_x_c c2  x v )"
|  "unlift_x_c (C_eq e1 e2)  x v = C_eq (unlift_x e1  x v  ) (unlift_x e2  x v )"
|  "unlift_x_c (C_not c)   x v= C_not (unlift_x_c c   x v)"

instantiation c :: has_x_vars
begin
definition "lift_x = lift_x_c"
definition "unlift_x = unlift_x_c"
instance by standard

end

subsection \<open>Types\<close>

fun lift_x_t :: "\<tau> \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> \<tau>" where
 "lift_x_t (\<lbrace> : b | c \<rbrace>) i j = (\<lbrace> : b | (lift_x c (i+1)) j \<rbrace>)"

fun unlift_x_t :: "\<tau> \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> \<tau>" where
 "unlift_x_t (\<lbrace> : b | c \<rbrace>) i j = (\<lbrace> : b | (unlift_x c (i-1)) j \<rbrace>)"


instantiation \<tau> :: has_x_vars
begin
definition "lift_x = lift_x_t"
definition "unlift_x = unlift_x_t"
instance by standard
end




subsection \<open>Statements\<close>

fun 
lift_x_s :: "s \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> s"
and lift_x_branch_s :: "branch_s \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> branch_s"
and lift_x_branch_list :: "branch_list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> branch_list" where
   "lift_x_s ( (AS_val v') ) i j = (AS_val (lift_x v' i j ))"
 | "lift_x_s (AS_let  e s) i j  = (AS_let   (lift_x e i j) (lift_x_s s  (i+1) j ))"  
 | "lift_x_s  (AS_let2 t s1 s2) i j  = (AS_let2  (lift_x_t t i j ) (lift_x_s s1 i j ) (lift_x_s s2 (i+1) j ))"  
 | "lift_x_s  (AS_match v'  css) x i  = AS_match  (lift_x v' x i )  (lift_x_branch_list css x i )"
 | "lift_x_s  (AS_assign y v') x i = AS_assign y (lift_x v' x i )"
 | "lift_x_s  ( (AS_if v' s1 s2) ) x i = (AS_if (lift_x v' x i ) (lift_x_s s1 x i ) (lift_x_s s2 x i ) )"  
 | "lift_x_s  (AS_var \<tau> v' s) x i = AS_var (lift_x_t \<tau> x i ) (lift_x v' x i ) (lift_x_s s x i)"
 | "lift_x_s  (AS_while s1 s2) x i = AS_while (lift_x_s s1 x i  ) (lift_x_s  s2 x i )"
 | "lift_x_s  (AS_seq s1 s2) x i = AS_seq (lift_x_s  s1 x i ) (lift_x_s  s2 x i )"

 | "lift_x_branch_list  (AS_final cs) x i  = AS_final (lift_x_branch_s cs x i )"
 | "lift_x_branch_list  (AS_cons cs css) x i  = AS_cons (lift_x_branch_s cs x i ) (lift_x_branch_list css x i )"
 | "lift_x_branch_s  (AS_branch dc s1 ) x i  = AS_branch dc (lift_x_s s1 (x+1) i )"

fun 
unlift_x_s :: "s \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> s"
and unlift_x_branch_s :: "branch_s \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> branch_s"
and unlift_x_branch_list :: "branch_list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> branch_list" where
   "unlift_x_s ( (AS_val v') ) i j = (AS_val (unlift_x v' i j ))"
 | "unlift_x_s (AS_let  e s) i j  = (AS_let   (unlift_x e i j) (unlift_x_s s  (i+1) j ))"  
 | "unlift_x_s  (AS_let2 t s1 s2) i j  = (AS_let2  (unlift_x t i j ) (unlift_x_s s1 i j ) (unlift_x_s s2 (i+1) j ))"  
 | "unlift_x_s  (AS_match v'  css) x i  = AS_match  (unlift_x v' x i )  (unlift_x_branch_list css x i )"
 | "unlift_x_s  (AS_assign y v') x i = AS_assign y (unlift_x v' x i )"
 | "unlift_x_s  ( (AS_if v' s1 s2) ) x i = (AS_if (unlift_x v' x i ) (unlift_x_s s1 x i ) (unlift_x_s s2 x i ) )"  
 | "unlift_x_s  (AS_var \<tau> v' s) x i = AS_var (unlift_x \<tau> x i ) (unlift_x v' x i ) (unlift_x_s s x i)"
 | "unlift_x_s  (AS_while s1 s2) x i = AS_while (unlift_x_s s1 x i  ) (unlift_x_s  s2 x i )"
 | "unlift_x_s  (AS_seq s1 s2) x i = AS_seq (unlift_x_s  s1 x i ) (unlift_x_s  s2 x i )"

 | "unlift_x_branch_list  (AS_final cs) x i  = AS_final (unlift_x_branch_s cs x i )"
 | "unlift_x_branch_list  (AS_cons cs css) x i  = AS_cons (unlift_x_branch_s cs x i ) (unlift_x_branch_list css x i )"
 | "unlift_x_branch_s  (AS_branch dc s1 ) x i  = AS_branch dc (unlift_x_s s1 (x+1) i )"


value "lift_x_s (AS_val (V_var (XBVar 0))) 0 1"

value "unlift_x_x (XBVar 1) 0 1"

value "unlift_x_s (AS_val (V_var (XBVar 1))) 0 1"

instantiation s :: has_x_vars
begin
definition "lift_x = lift_x_s"
definition "unlift_x = unlift_x_s"


instance by standard
end

instantiation branch_s :: has_x_vars
begin
definition "lift_x = lift_x_branch_s"
definition "unlift_x = unlift_x_branch_s"

instance by standard
end

subsection \<open>Function Definition\<close>



instantiation fun_typ :: has_x_vars
begin

instance
  by standard
end



instantiation fun_typ_q :: has_x_vars
begin


instance
  by standard
end




instantiation fun_def :: has_x_vars
begin


instance
  by standard
end


subsection \<open>Type Definition\<close>


instantiation type_def :: has_x_vars

begin

instance by standard
end


subsection \<open>Mutable Variable Context\<close>

fun lift_x_g :: "\<Gamma> \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> \<Gamma>" where
  "lift_x_g GNil _ _ = GNil"
| "lift_x_g ((b,c)#g) i j = ((b,lift_x c i j)#g)"

fun unlift_x_g :: "\<Gamma> \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> \<Gamma>" where
  "unlift_x_g GNil _ _ = GNil"
| "unlift_x_g ((b,c)#g) i j = ((b,unlift_x c i j)#g)"



instantiation \<Gamma> :: has_x_vars
begin
definition "lift_x = lift_x_g"
definition "unlift_x = unlift_x_g"
instance proof
qed
end

subsection \<open>Immutable Variable Context\<close>

fun lift_x_d :: "\<Delta> \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> \<Delta>" where
  "lift_x_d DNil i j = DNil"
| "lift_x_d (DCons t d) i j = DCons (lift_x t i j) (lift_x_d d i j)"

fun unlift_x_d :: "\<Delta> \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> \<Delta>" where
  "unlift_x_d DNil i j = DNil"
| "unlift_x_d (DCons t d) i j = DCons (unlift_x t i j) (unlift_x_d d i j)"


instantiation \<Delta> :: has_x_vars
begin
definition "lift_x = lift_x_d"
definition "unlift_x = unlift_x_d"

instance proof
qed
end

section \<open>Terms With Mutable Variables\<close>


subsection \<open>Class\<close>
class has_u_vars =
  fixes lift_u :: "'a \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> 'a" and
        unlift_u  :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a "     


begin

end

(*
abbreviation 
  lift_u_abbrev :: "'a::has_u_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" ("_\<up>\<^sub>_\<^sup>_" [1000,50,50] 1000)
where 
  "t\<up>\<^sub>i\<^sup>j  \<equiv> lift_u t i j"
*)

fun lift_u_u :: "u \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> u" where
  "lift_u_u   (UBVar k) i j  = (if k < i then (UBVar k) else UBVar (k+j))"

fun unlift_u_u :: "u \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> u" where
  "unlift_u_u   (UBVar k) i j  = (if k > i then (UBVar (k-j)) else UBVar k)"

subsection \<open>Expressions\<close>

fun lift_u_e :: "e \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> e" where
  "lift_u_e  ( (AE_val v') ) i j = AE_val v'"
| "lift_u_e  ( (AE_app f v') ) i j  = AE_app f v' "                
| "lift_u_e  ( (AE_appP f b v') ) i j = ( (AE_appP f b ((v') )) )"   
| "lift_u_e  ( (AE_op opp v1 v2) ) i j  = ( (AE_op opp ((v1) ) ((v2))) )"
| "lift_u_e  ( (AE_fst v')) i j = AE_fst ( v' )"
| "lift_u_e  ( (AE_snd v')) i j = AE_snd ( v' )"
| "lift_u_e  ( (AE_mvar u)) i j = AE_mvar (lift_u_u u i j)"
| "lift_u_e  ( (AE_len v')) i j = AE_len  v'"
| "lift_u_e  ( AE_concat v1 v2) i j = AE_concat v1  v2"

fun unlift_u_e :: "e \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> e" where
  "unlift_u_e  ( (AE_val v') ) i j = AE_val v'"
| "unlift_u_e  ( (AE_app f v') ) i j  = AE_app f v' "                
| "unlift_u_e  ( (AE_appP f b v') ) i j = ( (AE_appP f b ((v') )) )"   
| "unlift_u_e  ( (AE_op opp v1 v2) ) i j  = ( (AE_op opp ((v1) ) ((v2))) )"
| "unlift_u_e  ( (AE_fst v')) i j = AE_fst ( v' )"
| "unlift_u_e  ( (AE_snd v')) i j = AE_snd ( v' )"
| "unlift_u_e  ( (AE_mvar u)) i j = AE_mvar (unlift_u_u u i j)"
| "unlift_u_e  ( (AE_len v')) i j = AE_len  v'"
| "unlift_u_e  ( AE_concat v1 v2) i j = AE_concat v1  v2"  


instantiation e :: has_u_vars
begin
definition "lift_u = lift_u_e"
definition "unlift_u = unlift_u_e"

instance by standard

end

subsection \<open>Statements\<close>

fun 
lift_u_s :: "s \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> s"
and lift_u_branch_s :: "branch_s \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> branch_s"
and lift_u_branch_list :: "branch_list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> branch_list" where
   "lift_u_s ( (AS_val v') ) x i  = (AS_val v' )"
 | "lift_u_s (AS_let  e s) i j  = (AS_let   (lift_u e i j) (lift_u_s s  (i+1) j ))"  
 | "lift_u_s  (AS_let2 t s1 s2) i j  = (AS_let2  t (lift_u_s s1 i j ) (lift_u_s s2 (i+1) j ))"  
 | "lift_u_s  (AS_match v'  css) x i  = AS_match v'  (lift_u_branch_list css x i )"
 | "lift_u_s  (AS_assign y v') x i = AS_assign y v'"
 | "lift_u_s  ( (AS_if v' s1 s2) ) x i = (AS_if v' (lift_u_s s1 x i ) (lift_u_s s2 x i ) )"  
 | "lift_u_s  (AS_var \<tau> v' s) x i = AS_var \<tau>  v'  (lift_u_s s x i)"
 | "lift_u_s  (AS_while s1 s2) x i = AS_while (lift_u_s s1 x i  ) (lift_u_s  s2 x i )"
 | "lift_u_s  (AS_seq s1 s2) x i = AS_seq (lift_u_s  s1 x i ) (lift_u_s  s2 x i )"

 | "lift_u_branch_list  (AS_final cs) x i  = AS_final (lift_u_branch_s cs x i )"
 | "lift_u_branch_list  (AS_cons cs css) x i  = AS_cons (lift_u_branch_s cs x i ) (lift_u_branch_list css x i )"
 | "lift_u_branch_s  (AS_branch dc s1 ) x i  = AS_branch dc (lift_u_s s1 (x+1) i )"

fun 
unlift_u_s :: "s \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> s"
and unlift_u_branch_s :: "branch_s \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> branch_s"
and unlift_u_branch_list :: "branch_list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> branch_list" where
   "unlift_u_s ( (AS_val v') ) x i  = (AS_val v' )"
 | "unlift_u_s (AS_let  e s) i j  = (AS_let   (unlift_u e i j) (unlift_u_s s  (i+1) j ))"  
 | "unlift_u_s  (AS_let2 t s1 s2) i j  = (AS_let2  t (unlift_u_s s1 i j ) (unlift_u_s s2 (i+1) j ))"  
 | "unlift_u_s  (AS_match v'  css) x i  = AS_match v'  (unlift_u_branch_list css x i )"
 | "unlift_u_s  (AS_assign y v') x i = AS_assign y v'"
 | "unlift_u_s  ( (AS_if v' s1 s2) ) x i = (AS_if v' (unlift_u_s s1 x i ) (unlift_u_s s2 x i ) )"  
 | "unlift_u_s  (AS_var \<tau> v' s) x i = AS_var \<tau>  v'  (unlift_u_s s x i)"
 | "unlift_u_s  (AS_while s1 s2) x i = AS_while (unlift_u_s s1 x i  ) (unlift_u_s  s2 x i )"
 | "unlift_u_s  (AS_seq s1 s2) x i = AS_seq (unlift_u_s  s1 x i ) (unlift_u_s  s2 x i )"

 | "unlift_u_branch_list  (AS_final cs) x i  = AS_final (unlift_u_branch_s cs x i )"
 | "unlift_u_branch_list  (AS_cons cs css) x i  = AS_cons (unlift_u_branch_s cs x i ) (unlift_u_branch_list css x i )"
 | "unlift_u_branch_s  (AS_branch dc s1 ) x i  = AS_branch dc (unlift_u_s s1 (x+1) i )"

instantiation s :: has_u_vars
begin
definition "lift_u = lift_u_s"
definition "unlift_u = unlift_u_s"

instance by standard

end


section \<open>Terms With Base Type Variables\<close>


subsection \<open>Class\<close>
class has_b_vars =
  fixes lift_b :: "'a \<Rightarrow> nat \<Rightarrow> nat  \<Rightarrow> 'a" and
        unlift_b  :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a "     


begin

end

(*
abbreviation 
  lift_u_abbrev :: "'a::has_u_vars \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" ("_\<up>\<^sub>_\<^sup>_" [1000,50,50] 1000)
where 
  "t\<up>\<^sub>i\<^sup>j  \<equiv> lift_u t i j"
*)

fun lift_b_b :: "bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv" where
  "lift_b_b   (BVBVar k) i j  = (if k < i then (BVBVar k) else BVBVar (k+j))"

fun unlift_b_b :: "bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv" where
  "unlift_b_b   (BVBVar k) i j  = (if k > i then (BVBVar (k-j)) else BVBVar k)"

subsection \<open>Base Types\<close>

subsection \<open>Values\<close>

subsection \<open>Expressions\<close>

subsection \<open>Constraint Expressions\<close>

subsection \<open>Constraints\<close>

subsection \<open>Types\<close>

subsection \<open>Statements\<close>

end
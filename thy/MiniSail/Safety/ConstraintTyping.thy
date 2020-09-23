theory ConstraintTyping
imports Syntax "HOL-Library.Finite_Map"
begin

section \<open>Base Types\<close>

type_synonym BC = "(bv*b) list"


inductive bcstr_v :: "\<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> BC \<Rightarrow> v \<Rightarrow> bv \<Rightarrow> BC \<Rightarrow> bool" where
  "atom bv \<sharp> BC \<Longrightarrow> bcstr_v T G BC (V_lit l) bv ((bv,base_for_lit l)#BC)"

| "\<lbrakk> 
   atom bv \<sharp> BC;
   Some (b,c) = lookup \<Gamma> x \<rbrakk>
 \<Longrightarrow> 
   bcstr_v T G BC (V_var x) bv ((bv,b)#BC)"

| "\<lbrakk>
   atom bv \<sharp> BC ; 
   bcstr_v T G BC v1 bv1 BC1; 
   bcstr_v T G BC v2 bv2 BC2 
\<rbrakk> \<Longrightarrow> 
   bcstr_v T G BC (V_pair v1 v2) bv ((bv,B_pair (B_var bv1) (B_var bv2))#BC2)"

| "\<lbrakk> 
  atom bv \<sharp> BC ; 
  AF_typedef s dclist \<in> set \<Theta>;
  (dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist ;
  bcstr_v T G BC v1 bv1 BC1 
\<rbrakk> \<Longrightarrow> 
  bcstr_v T G BC (V_cons tyid dc v) bv ((bv,B_id tyid)#((bv1,b')#BC1))"

| "\<lbrakk> 
  atom bv \<sharp> BC ; 
  AF_typedef_poly s bv' dclist \<in> set \<Theta>;
  (dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist ;
  bcstr_v T G BC v1 bv1 BC1 ;
  atom bv' \<sharp> BC  
\<rbrakk> \<Longrightarrow> 
  bcstr_v T G BC (V_consp tyid dc b v) bv ((bv,B_id tyid)#((bv1,b')#(bv',b)#BC1))"

equivariance bcstr_v
nominal_inductive bcstr_v .


inductive bcstr_e :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> BC \<Rightarrow> e \<Rightarrow> bv \<Rightarrow> BC \<Rightarrow> bool" where
   "bcstr_v T G BC v bv BC1 \<Longrightarrow> bcstr_e T P G D BC (AE_val v) bv BC1"

| "\<lbrakk>
   atom bv \<sharp> BC;  
   bcstr_v T G BC v1 bv1 BC1;
   bcstr_v T G BC1 v2 bv2 BC2
\<rbrakk> \<Longrightarrow>
   bcstr_e T P G D BC (AE_op Plus v1 v2) bv ((bv,B_int)#(bv1,B_int)#(bv2,B_int)#BC2)"

| "\<lbrakk>
   atom bv \<sharp> BC;  
   atom bv2 \<sharp> BC;
   bcstr_v T G BC v1 bv1 BC1
\<rbrakk> \<Longrightarrow>
   bcstr_e T P G D BC (AE_fst v1) bv ((bv1,B_pair (B_var bv) (B_var bv2))#BC1)"

| "\<lbrakk>
   atom bv \<sharp> BC;  
   bcstr_v T G BC v1 bv1 BC1;
   Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))) = lookup_fun P f 
\<rbrakk> \<Longrightarrow>
   bcstr_e T P G D  BC (AE_app f v1) bv ((bv, b_of \<tau>)# (bv1, b)#BC1)"

| "\<lbrakk> 
   atom bv \<sharp> BC;
    (u,\<tau>) \<in> setD \<Delta> 
 \<rbrakk> \<Longrightarrow> 
   bcstr_e P T G D BC (AEV_mvar u) bv ((bv,b_of \<tau>)#BC)"

equivariance bcstr_e
nominal_inductive bcstr_e .

inductive bcstr_s :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> BC \<Rightarrow> s \<Rightarrow> bv \<Rightarrow> BC \<Rightarrow> bool" where
 "\<lbrakk>
    bcstr_e T P G D BC e bve BC1;
    bcstr_s T P ((x,B_var bve,C_true)#G) D BC1 s bv BC2
\<rbrakk> \<Longrightarrow> 
   bcstr_s T P G D BC (LET x = e IN S) bv BC2"

equivariance bcstr_s
nominal_inductive bcstr_s .

section \<open>Full Types\<close>

inductive cstr_v :: "\<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> v \<Rightarrow> x \<Rightarrow> \<Gamma> \<Rightarrow> bool" where
  "atom x \<sharp> G \<Longrightarrow> cstr_v T G v x ((x,B_int, ([[x]\<^sup>v]\<^sup>c\<^sup>e == [v]\<^sup>c\<^sup>e))#G)"
equivariance cstr_v
nominal_inductive cstr_v .


type_synonym uxmap = "(u,(x*b)) map"

type_synonym fxmap = "(f,(x*x*b)) map"

inductive cstr_e :: "\<Theta> \<Rightarrow> fxmap \<Rightarrow> \<Gamma> \<Rightarrow> uxmap \<Rightarrow> e \<Rightarrow> x \<Rightarrow> \<Gamma> \<Rightarrow> bool" where
  "cstr_v T  G v x G'  \<Longrightarrow> cstr_e T P G D (AE_val v) x G'"

| "\<lbrakk>
  cstr_v T  G v1 x1 G1 ; 
  cstr_v T  G1 v2 x2 G2 
\<rbrakk> \<Longrightarrow> 
  cstr_e T P G D (AE_op Plus v1 v2) x  ((x,B_int,  ([[x]\<^sup>v]\<^sup>c\<^sup>e == (CE_op Plus [x1]\<^sup>v [x2]\<^sup>v) ))#G2)"

| "Some (ux,b) = uxm u  \<Longrightarrow> cstr_e T fx G uxm (AE_mvar u) x ((x,b, ([[x]\<^sup>v]\<^sup>c\<^sup>e == [[ux]\<^sup>v]\<^sup>c\<^sup>e))#G)"
| "\<lbrakk> 
     cstr_v T G v x_in G1;
     Some (fx_ret, fx_in ,b ) = fx f
\<rbrakk>  \<Longrightarrow>   
     cstr_e T fx G uxm (AE_app f v) x ((x,b,(([[x]\<^sup>v]\<^sup>c\<^sup>e == [[fx_ret]\<^sup>v]\<^sup>c\<^sup>e) AND ([V_var x_in]\<^sup>c\<^sup>e == [ V_var fx_in]\<^sup>c\<^sup>e)))#G)"
equivariance cstr_e
nominal_inductive cstr_e .

inductive cstr_s :: "\<Theta> \<Rightarrow> fxmap \<Rightarrow> \<Gamma> \<Rightarrow> uxmap \<Rightarrow> s \<Rightarrow> x \<Rightarrow> \<Gamma> \<Rightarrow> bool" where

"\<lbrakk> 
   cstr_e T fx G ux e xe G1 ;
   cstr_s T fx G1 ux s xs G2
\<rbrakk> \<Longrightarrow>
   cstr_s T fx G ux (LET x = e IN s) x G2"
equivariance cstr_s
nominal_inductive cstr_s .
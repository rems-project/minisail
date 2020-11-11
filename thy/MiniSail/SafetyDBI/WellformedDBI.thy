theory WellformedDBI
  imports DBIndex SyntaxLemmasDBI
begin
chapter \<open>Wellbased Terms\<close>

text \<open>We require that expressions and values are well-sorted. We identify sort with base. Define a large cluster of mutually recursive
inductive predicates. Some of the proofs are across all of the predicates and although they seemed at first to be daunting they have all
worked out well with only the cases where you think something special needs to be done having some non-uniform part of the proof.\<close>

named_theorems ms_wf "Facts for helping with well-sortedness"


section \<open>Definitions\<close>
(*
nominal_function uniqueness_check :: "\<Theta> \<Rightarrow> string \<Rightarrow> (string * \<tau>) list \<Rightarrow> bool" where
  "uniqueness_check \<Theta> s dclist =  ((s \<notin> name_of_type ` set \<Theta>) \<and>  distinct (map fst dclist) \<and>  (\<forall>dc \<in> fst ` set dclist. new_constructor \<Theta> dc))"
     apply (simp add: eqvt_def uniqueness_check_graph_aux_def,auto)
  done
nominal_termination (eqvt) by lexicographic_order
*)
(* FIXME Argument contexts are the wrong way round *)

fun lengthG :: "\<Gamma> \<Rightarrow> nat" where
  "lengthG GNil = 0"
| "lengthG (x#G) = 1 + lengthG G"

inductive wfV :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> v \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50] 50)  and         
          wfC :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> c \<Rightarrow> bool" (" _ ; _ ; _   \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)  and         
          wfG :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> bool" (" _ ; _  \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50) and
          wfT :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ; _ ; _   \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)  and
          wfTs :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> (string*\<tau>) list \<Rightarrow> bool" (" _ ; _  ; _ \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)  and 
          wfTh :: "\<Theta> \<Rightarrow> bool" ("   \<turnstile>\<^sub>w\<^sub>f _ " [50] 50)  and
          wfB :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> b \<Rightarrow> bool" (" _ ; _  \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50) and       
          wfCE :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> ce \<Rightarrow> b \<Rightarrow> bool" ("  _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50] 50) and
          wfTD :: "\<Theta> \<Rightarrow> type_def \<Rightarrow> bool" (" _ \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50) 
          where
  wfB_intI:  "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f B_int" 
| wfB_boolI:  "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f B_bool" 
| wfB_unitI:  "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f B_unit" 
| wfB_bitvecI:  "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f B_bitvec" 
| wfB_pairI:  "\<lbrakk> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f b1 ; \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f b2 \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f B_pair b1 b2" 
| wfB_consI:  "\<lbrakk> \<turnstile>\<^sub>w\<^sub>f \<Theta>; 
                Some (AF_typedef s dclist) = lookup_td \<Theta> s 
              \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f B_id s"

| wfV_varI: "\<lbrakk> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; Some (b,c) = lookup \<Gamma> x  \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_var x : b"
| wfV_litI: "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_lit l : base_for_lit l"
| wfV_pairI: "\<lbrakk> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1  : b1 ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : b2 \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  (V_pair v1 v2) : B_pair b1 b2"
| wfV_consI: "\<lbrakk>   Some (AF_typedef s dclist) = lookup_td \<Theta> s;
                 Some (dc, \<lbrace> : b'  | c \<rbrace>) = lookup_dc dclist dc ;
                 \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b' \<rbrakk> \<Longrightarrow>
              \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_cons s dc v : B_id s"

| wfCE_valI : "\<lbrakk>                
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : b 
\<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_val v  : b"
| wfCE_plusI: "\<lbrakk>               
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int 
\<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_op Plus v1 v2 : B_int"

| wfCE_leqI:"\<lbrakk>  
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int 
\<rbrakk> \<Longrightarrow>  \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op LEq v1 v2 : B_bool"

| wfCE_fstI: "\<lbrakk>               
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_pair b1 b2  
\<rbrakk> \<Longrightarrow> 
                \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_fst v1 : b1"
| wfCE_sndI: "\<lbrakk>             
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_pair b1 b2  
\<rbrakk> \<Longrightarrow>  \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_snd v1 : b2"

| wfCE_concatI: "\<lbrakk> 
                \<Theta> ;\<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_bitvec 
\<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_concat v1 v2 : B_bitvec"
| wfCE_lenI: "\<lbrakk>                
                 \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec 
                 \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_len v1 : B_int"

| wfTI : "\<lbrakk>   
            
            \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f b;
            \<Theta> ; \<B> ; (b,C_true)#\<Gamma> \<turnstile>\<^sub>w\<^sub>f (lift_x c 0 (lengthG \<Gamma>)) 
\<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> : b | c \<rbrace>"

| wfC_eqI: "\<lbrakk>  
                \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f e1  : b ; 
                 \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f e2  : b  \<rbrakk> \<Longrightarrow> 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_eq e1 e2" 

| wfC_trueI: " \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f C_true "
| wfC_falseI: " \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_false "

| wfC_conjI: "\<lbrakk> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c1 ; \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c2 \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_conj c1 c2"
| wfC_disjI: "\<lbrakk> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c1 ; \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c2 \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_disj c1 c2"
| wfC_notI: "\<lbrakk>  \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c1  \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_not c1"
| wfC_impI: "\<lbrakk>  \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c1 ; 
                \<Theta> ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c2 \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_imp c1 c2"


| wfG_nilI: " \<turnstile>\<^sub>w\<^sub>f \<Theta>  \<Longrightarrow> \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f GNil"
| wfG_cons1I: "\<lbrakk>  c \<notin> { TRUE, FALSE } ; 
                  \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> ;                
                  (\<Theta>  ; \<B> ; (b,C_true)#\<Gamma> \<turnstile>\<^sub>w\<^sub>f c ); 
                 \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f b  
               \<rbrakk> \<Longrightarrow>  \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f ((b,c)#\<Gamma>)" 

(* Use of x in fvs_x not ideal; alternative using freshness leads to some code hurdles *)
| wfG_cons2I: "\<lbrakk>  c \<in> { TRUE, FALSE } ; 
                  \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> ;                   
                  wfB \<Theta> \<B> b   
                \<rbrakk> \<Longrightarrow>  \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f ((b,c)#\<Gamma>)"

| wfTh_emptyI: " \<turnstile>\<^sub>w\<^sub>f []"

| wfTh_consI: "\<lbrakk>      
        (name_of_type tdef) \<notin> name_of_type ` set \<Theta> ;
        \<turnstile>\<^sub>w\<^sub>f \<Theta> ; 
       \<Theta> \<turnstile>\<^sub>w\<^sub>f  tdef \<rbrakk>  \<Longrightarrow>  \<turnstile>\<^sub>w\<^sub>f tdef#\<Theta>"

| wfTD_simpleI: "\<lbrakk>
        \<Theta> ; {} ; GNil \<turnstile>\<^sub>w\<^sub>f lst
      \<rbrakk> \<Longrightarrow> 
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef s lst )"

(*
| wfTD_poly: "\<lbrakk> 
     bv = mk_fresh_bv  {};
        \<Theta> ; {bv} ; GNil \<turnstile>\<^sub>w\<^sub>f List.map (\<lambda>(s,t). (s,open_bv t bv 0)) lst ;
        fvs_bv_ts lst = {}
       \<rbrakk> \<Longrightarrow>
      \<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef_poly s lst)"
*)
| wfTs_nil: "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f []::(string*\<tau>) list"
| wfTs_cons: "\<lbrakk> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau> ; 
                dc \<notin> fst ` set ts;
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ts::(string*\<tau>) list \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ((dc,\<tau>)#ts)"

(*
primrec maxlst :: "nat list \<Rightarrow> nat" where
  "maxlst [] = 0"
| "maxlst (x#xs) = max x (maxlst xs)" 

value "maxlst [1,4,3]"

inductive fresh  :: "nat  \<Rightarrow> nat list \<Rightarrow> bool" where
  "\<lbrakk>  x = (maxlst xs) + 1 \<rbrakk> \<Longrightarrow> fresh x xs"
| "\<lbrakk> x \<notin> set xs \<rbrakk> \<Longrightarrow> fresh x xs"

code_pred  [show_steps,  show_mode_inference,  show_invalid_clauses] fresh .

values "{ True . fresh 4 [2] }"

values "{ x . fresh x [2] }"
*)
(*
code_pred (modes: 
       wfV: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and     
       wfG: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       wfB: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow>  bool and 
       wfCE: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
       wfC: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       wfT: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and     
       wfTs: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool      
    )  [show_steps,  show_mode_inference,  show_invalid_clauses] wfG .
*)

(* Care needed here as we do need some functions with o modes in the base due to CE_fst and CE_snd;
   we don't want to be overly restricted but having no restriction leads to blowup *)
code_pred (modes: 
(*       wfV: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and     
       wfV: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and 
       wfG: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       wfB: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow>  bool and 
       wfCE: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       wfC: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       wfT: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and     
       wfTs: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
       wfTD: i \<Rightarrow> i \<Rightarrow> bool  and
       wfTh: i \<Rightarrow> bool*)
       wfG: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool
    )  [show_steps,  show_mode_inference,  show_invalid_clauses] wfT .

values "{ True . wfV [] {} GNil (V_lit (L_num 10)) B_int }"

values "{ True . wfG [] {} ((B_int , TRUE) # (B_int , FALSE ) # GNil) }"

values "{ True . wfG [] {} ((B_int , TRUE)  # GNil) }"

values "{ b . wfV [] {} ((B_bool , TRUE)  # GNil)  (V_var (XBVar 0)) b }"

values "{ True . wfT [] {} GNil  \<lbrace> : B_int | TRUE \<rbrace> }"

(* fail *)
values "{ True . wfC [] {} ((B_bool, TRUE)#(B_int, TRUE)#GNil)  (CE_val (V_var (XBVar 0)) == CE_val (V_lit (L_num 42))) }"

(* ok *)
values "{ True . wfC [] {} ((B_int, TRUE)#(B_bool, TRUE)#GNil)  (CE_val (V_var (XBVar 0)) == CE_val (V_lit (L_num 42))) }"

values "{ True . wfT [] {} GNil  \<lbrace> : B_int | CE_val (V_var (XBVar 0)) == CE_val (V_lit (L_num 42))\<rbrace> }"

inductive
         wfE :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> e \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50] 50)  and
          wfS :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> s \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50] 50)  and
          wfCS :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow>  tyid \<Rightarrow> string \<Rightarrow> \<tau> \<Rightarrow> branch_s \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _ ; _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50,50,50] 50)  and       
          wfCSS :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow>  tyid \<Rightarrow> (string * \<tau>) list \<Rightarrow> branch_list \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50,50,50] 50)  and       
          wfPhi :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> bool" (" _  \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)  and                 

          wfFTQ :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> fun_typ_q \<Rightarrow> bool"  (" _  ; _ \<turnstile>\<^sub>w\<^sub>f _ " [50] 50) and
          wfFT :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> fun_typ \<Rightarrow> bool"  (" _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ " [50] 50)        and
          wfD :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> bool" (" _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50) 
         
          where
wfE_valI : "\<lbrakk> (\<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>) ; 
                (\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>);
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : b \<rbrakk> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_val v  : b"

| wfE_plusI: "\<lbrakk> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>;
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int \<rbrakk> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_op Plus v1 v2 : B_int"
| wfE_leqI:"\<lbrakk>   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int \<rbrakk> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_op LEq v1 v2 : B_bool"
| wfE_fstI: "\<lbrakk>  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_pair b1 b2  \<rbrakk> \<Longrightarrow> 
                \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_fst v1 : b1"
| wfE_sndI: "\<lbrakk>  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>;
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_pair b1 b2  
\<rbrakk> \<Longrightarrow>  
                \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_snd v1 : b2"
| wfE_concatI: "\<lbrakk>  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
                \<Theta> ;\<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_bitvec \<rbrakk> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_concat v1 v2 : B_bitvec"
| wfE_lenI: "\<lbrakk>  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
                 \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec 
                 \<rbrakk> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_len v1 : B_int"
| wfE_appI:  "\<lbrakk> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
                Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ b c \<tau> s))) = lookup_fun \<Phi> f ;  
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b
        \<rbrakk> \<Longrightarrow>   \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_app f v : b_of \<tau>"
(*
| wfE_appPI:  "\<lbrakk> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
                \<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f b'; 
                bv = mk_fresh_bv \<B>;
                Some (AF_fundef f (AF_fun_typ_some (AF_fun_typ b c \<tau> s))) = lookup_fun \<Phi> f;  
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : (b[bv::=b']\<^sub>b\<^sub>b)
        \<rbrakk> \<Longrightarrow>   \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f (AE_appP f b' v) : ((b_of \<tau>)[bv::=b']\<^sub>b\<^sub>b)"

| wfE_mvarI: "\<lbrakk>  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
                Some u = lookup_d \<Delta> u
                 \<rbrakk> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_mvar u  : b_of \<tau>" 
*)
| wfS_valI: "\<lbrakk> \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;  
              \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b ; 
              \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> \<rbrakk>  \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f (AS_val v) : b"

(*(lift_x s 0 (lengthG \<Gamma>)) : b;*)
| wfS_letI: "\<lbrakk> wfE \<Theta>  \<Phi> \<B> \<Gamma> \<Delta>  e b'  ;
              \<Theta> ; \<Phi> ; \<B> ; (b',C_true)#\<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f (lift_x s 0 (lengthG \<Gamma>)) : b ; 
              \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> 
               \<rbrakk> \<Longrightarrow> 
            \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_let e s : b"

| wfS_let2I: "\<lbrakk> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta>  \<turnstile>\<^sub>w\<^sub>f s1 : b'  ; 
              \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> : b' | c \<rbrace>;
               \<Theta> ; \<Phi> ; \<B> ; (b',C_true)#\<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f (lift_x s2 0 (lengthG \<Gamma>)) : b 
            \<rbrakk> \<Longrightarrow> 
            \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_let2  \<lbrace> : b'|c \<rbrace> s1 s2 : b"

| wfS_ifI: "\<lbrakk>  \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : B_bool; 
                \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : b ; 
                \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b \<rbrakk> \<Longrightarrow>
               \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_if v s1 s2 : b"

| wfS_varI : "\<lbrakk> wfT \<Theta> \<B> \<Gamma>  \<tau> ;  
                \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : b_of \<tau>;                        
                \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  (\<tau>)#\<Delta> \<turnstile>\<^sub>w\<^sub>f (lift_u s 0 1) : b
                \<rbrakk> \<Longrightarrow> 
                 \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_var \<tau> v s : b "

| wfS_assignI: "\<lbrakk> Some \<tau> = lookup_u \<Delta> u ;   
                  \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;  
                  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
                  \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : b_of \<tau> \<rbrakk> \<Longrightarrow>
                   \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_assign u v : B_unit"
(*
| wfS_whileI: "\<lbrakk> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : B_bool ;
                 \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b\<rbrakk> \<Longrightarrow>  
                \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_while s1 s2 : b"

| wfS_seqI: "\<lbrakk>  \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : B_unit ;
   \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b \<rbrakk> \<Longrightarrow> 
               \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_seq s1 s2 : b"

| wfS_matchI: "\<lbrakk> wfV \<Theta>  \<B> \<Gamma>  v  (B_id tid) ;
                 Some (AF_typedef tid dclist ) = lookup_td \<Theta> tid;
                   wfD \<Theta>  \<B> \<Gamma>  \<Delta> ;  
                  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
                   \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f cs : b \<rbrakk> \<Longrightarrow> \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_match v cs : b "

| wfS_finalI: "\<lbrakk>       
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b    
 \<rbrakk> \<Longrightarrow>  
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  \<Delta> ; tid ; [(dc,t)] \<turnstile>\<^sub>w\<^sub>f AS_final cs  : b "

| wfS_cons: "\<lbrakk>           
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b;
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b
 \<rbrakk> \<Longrightarrow>  
       \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  \<Delta> ; tid ; (dc,t)#dclist \<turnstile>\<^sub>w\<^sub>f AS_cons cs css : b "

| wfS_branchI: "\<lbrakk> wfS \<Theta> \<Phi> \<B> (GCons (b_of \<tau>,C_true) \<Gamma>) \<Delta>  (lift_x s 0 (lengthG \<Gamma>)) b ;             
              wfD \<Theta> \<B> \<Gamma> \<Delta>
               \<rbrakk>  \<Longrightarrow> 
              wfCS \<Theta> \<Phi> \<B> \<Gamma> \<Delta> tid dc \<tau> (AS_branch dc s)  b"
*)
| wfPhi_emptyI: " \<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta> \<turnstile>\<^sub>w\<^sub>f []"
| wfPhi_consI: "\<lbrakk> 
        f \<notin> name_of_fun ` set \<Phi>; 
       \<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f ft;
       \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>
   \<rbrakk> \<Longrightarrow>  
        \<Theta>  \<turnstile>\<^sub>w\<^sub>f ((AF_fundef f ft)#\<Phi>)"  
| wfFTNone: " \<Theta> ; \<Phi> ; {} \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>  \<Theta> ; \<Phi> \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_none ft"
(*| wfFTSome: "\<lbrakk> bv = mk_fresh_bv {} ;  \<Theta> ; \<Phi> ; { bv } \<turnstile>\<^sub>w\<^sub>f open_bv ft bv 0; fvs_bv ft = {} \<rbrakk> \<Longrightarrow>  \<Theta> ; \<Phi> \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_some ft" (* need to open ft *)*)

| wfFTI: "\<lbrakk>
        \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f b;
         \<Theta> ; \<Phi> ; B  ; (b,c )#GNil ; [] \<turnstile>\<^sub>w\<^sub>f (lift_x s 0 0) : b_of \<tau> ; 
        \<Theta> ; B ; (b,c )#GNil \<turnstile>\<^sub>w\<^sub>f (lift_x \<tau> 0 1)       
   \<rbrakk> \<Longrightarrow> 
         \<Theta> ; \<Phi> ; B \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ b c \<tau> s)"


| wfD_emptyI: "\<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<Longrightarrow> \<Theta>  ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f ([]::\<Delta>)"
| wfD_cons: "\<lbrakk> \<Theta>  ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta>::\<Delta> ; 
               \<Theta>  ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>
               \<rbrakk> \<Longrightarrow> \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ((\<tau>)#\<Delta>)"

inductive_cases wfC_elims:
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_true"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_false"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_eq e1 e2"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_conj c1 c2"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_disj c1 c2"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_not c1"
  "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_imp c1 c2"

inductive_cases wfV_elims:
 "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_var x : b"
 "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_lit l : b"
 "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_pair v1 v2 : b"
 "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_cons tyid dc v : b"

inductive_cases wfE_elims:
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_val v : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_op Plus v1 v2 : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_op LEq v1 v2 : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_fst v1 : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_snd v1 : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_concat v1 v2 : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_len v1 : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_op opp v1 v2 : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_app f v: b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_appP f b' v: b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_mvar u : b"

inductive_cases wfCE_elims:
 " \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_val v : b"
 " \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op Plus v1 v2 : b"
 " \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op LEq v1 v2 : b"
 " \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_fst v1 : b"
 " \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_snd v1 : b"
 " \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_concat v1 v2 : b"
 " \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_len v1 : b"
 " \<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op opp v1 v2 : b"

inductive_cases wfS_elims:
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_while s1 s2 : b"
 "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_let e s : b"

inductive_cases wfCS_elims:
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dc \<turnstile>\<^sub>w\<^sub>f cs : b"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dc \<turnstile>\<^sub>w\<^sub>f C_final cons s : b"
  "\<Theta> ; \<Phi> ; \<B> ; \<Gamma> ; \<Delta> ; tid ; dc \<turnstile>\<^sub>w\<^sub>f C_branch cons s cs : b"

inductive_cases wfT_elims:
 "\<Pi>; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>::\<tau>"
 "\<Pi>; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace>  : b | c \<rbrace>"

inductive_cases wfG_elims:
  "\<Pi> ; \<B> \<turnstile>\<^sub>w\<^sub>f GNil"
  "\<Pi> ; \<B> \<turnstile>\<^sub>w\<^sub>f (b,c)#\<Gamma>"
  "\<Pi> ; \<B> \<turnstile>\<^sub>w\<^sub>f (b,TRUE)#\<Gamma>"
  "\<Pi> ; \<B> \<turnstile>\<^sub>w\<^sub>f (b,FALSE)#\<Gamma>"

inductive_cases wfTh_elims:
 " \<turnstile>\<^sub>w\<^sub>f []"
 " \<turnstile>\<^sub>w\<^sub>f td#\<Pi>"  

inductive_cases wfTD_elims:
 "\<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef s lst )"  
 "\<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef_poly s lst )" 

inductive_cases wfTs_elims:
  "P ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f ([]::((string*\<tau>) list))"
  "P ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f ((t#ts)::((string*\<tau>) list))"

inductive_cases wfPhi_elims:
 " \<Theta>  \<turnstile>\<^sub>w\<^sub>f []"
 " \<Theta>  \<turnstile>\<^sub>w\<^sub>f ((AF_fundef f ft)#\<Pi>)"  
 " \<Theta>  \<turnstile>\<^sub>w\<^sub>f (fd#\<Phi>::\<Phi>)"  

inductive_cases wfFTQ_elims:
  "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_none ft"
  "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_some ft"
  "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_some (AF_fun_typ b c \<tau> s)"

inductive_cases wfFT_elims:
  "\<Theta> ; \<Phi> ; \<B>  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ b c \<tau> s"

inductive_cases wfB_elims:
 " \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f B_pair b1 b2" 
 " \<Theta> ; \<B> \<turnstile>\<^sub>w\<^sub>f B_id s"

inductive_cases wfD_elims:
  "\<Pi> ; \<B> ; (\<Gamma>::\<Gamma>) \<turnstile>\<^sub>w\<^sub>f []::\<Delta>"
  "\<Pi> ; \<B> ; (\<Gamma>::\<Gamma>) \<turnstile>\<^sub>w\<^sub>f (\<tau>)#\<Delta>::\<Delta>"

(*code_pred (modes: i\<Rightarrow> bool)  [show_steps,  show_mode_inference,  show_invalid_clauses] wfTh .*)


(*
code_pred (modes: 
   wfE: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
   wfS: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
   wfCS: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
   wfCSS: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool and
   wfPhi: i \<Rightarrow> i  \<Rightarrow> bool and
   wfFT: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
   wfFTQ: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow>  bool and     
   wfD: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool                
 )  [show_steps,  show_mode_inference,  show_invalid_clauses] wfE .
*)

code_pred (modes: 
 (*  wfE: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and*)
   wfS: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool 
(*   wfCS: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
   wfCSS: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
   wfPhi: i \<Rightarrow> i  \<Rightarrow> bool and
   wfFT: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool and
   wfFTQ: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow>  bool and     
   wfD: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool                *)
 )  [show_steps,  show_mode_inference,  show_invalid_clauses] wfS .

values "{ b. wfE [] [] {} GNil DNil (AE_val (V_lit L_true)) b }"

values "{ True . wfS [] [] {} ((B_int,C_true)#GNil) DNil (AS_val (V_var (XBVar 0))) B_int }"

(* ok *)
values "{ True . wfS [] [] {} GNil DNil (AS_let (AE_val (V_lit L_true)) (AS_val (V_var (XBVar 0)))) B_bool }"

(* fail *)
values "{ True . wfS [] [] {} GNil DNil (AS_let (AE_val (V_lit L_true)) (AS_val (V_var (XBVar 0)))) B_int }"

values "{ b . wfV [] {} GNil (V_lit (L_num 10)) b }" 

values "{ b . wfS   ([]::\<Theta>)  ([]::\<Phi>) {} GNil (DNil::\<Delta>) (AS_val (V_lit (L_num 10))) B_int }" 

values "{ b . wfS  ([]::\<Theta>) ([]::\<Phi>)  {} GNil (DNil::\<Delta>) (AS_if (V_lit (L_true)) (AS_val (V_lit (L_num 10))) (AS_val (V_lit (L_num 10)))) B_int }" 

(*value "lookup ((mk_fresh_x GNil,B_int, C_true)#GNil) (mk_fresh_x GNil)"*)

values "{ b . wfV   ([]::\<Theta>) {} ((B_int, C_true)#GNil)  (V_var (XBVar 0)) b }" 

values "{ b . wfE  ([]::\<Theta>)  ([]::\<Phi>) {} GNil (DNil::\<Delta>) (AE_val (V_lit (L_num 10))) b }" 

values "{ b . wfE  ([]::\<Theta>)  ([]::\<Phi>) {} GNil (DNil::\<Delta>) (AE_val (V_lit (L_true))) b }" 

values "{ b . wfS   ([]::\<Theta>) ([]::\<Phi>) {} GNil (DNil::\<Delta>) (AS_let  (AE_val (V_lit (L_num 10)))  (AS_let (AE_val (V_lit L_true)) (AS_val (V_var ((XBVar 1)))))) B_bool }" 

end
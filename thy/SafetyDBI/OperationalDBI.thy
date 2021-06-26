(*<*)
theory OperationalDBI
  imports DBIndex SyntaxLemmasDBI IVSubstDBI TypingDBI
begin
(*>*)

chapter \<open>Operational Semantics\<close>

text {* Here we define the operational semantics in terms of a small-step reduction relation. *}

section \<open>Reduction Rules\<close>

text {* The store for mutable variables *}
type_synonym \<delta> = "v list"

fun update_d :: "\<delta> \<Rightarrow> ub  \<Rightarrow> v \<Rightarrow> \<delta>" where
  "update_d [] _ _ = []"
| "update_d ((v')#\<delta>) (UBVar u) v = (if u = 0  then ((v)#\<delta>) else ((v')# (update_d \<delta> (UBVar (u-1)) v)))"


text {* Relates constructor to the branch in the case and binding variable and statement *}
inductive find_branch :: "dc \<Rightarrow> branch_list  \<Rightarrow> branch_s  \<Rightarrow> bool" where
   find_branch_finalI:  "dc' = dc                                  \<Longrightarrow> find_branch dc' (AS_final (AS_branch dc s ))  (AS_branch dc s)"
 | find_branch_branch_eqI: "dc' = dc                               \<Longrightarrow> find_branch dc' (AS_cons  (AS_branch dc s) css)    (AS_branch dc s)"
 | find_branch_branch_neqI:  "\<lbrakk> dc \<noteq> dc'; find_branch dc' css cs \<rbrakk> \<Longrightarrow> find_branch dc' (AS_cons  (AS_branch dc s) css) cs"


inductive_cases find_branch_elims[elim!]:
  "find_branch dc (C_final dc'  s)  s'"
  "find_branch dc (C_branch dc  s cs)  s'"
  "find_branch dc' (C_branch dc  s cs)  s'"



fun lookup_dv :: "(v) list \<Rightarrow> ub   \<Rightarrow> v option" where
   "lookup_dv [] s = None"
|  "lookup_dv ((v)#ts) (UBVar u) = (if (u = 0) then Some v else lookup_dv ts (UBVar (u-1)))"





text {* Reduction rules *}
inductive reduce_stmt :: "\<Phi> \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> bool"  (" _  \<turnstile> \<langle> _ , _ \<rangle> \<longrightarrow> \<langle>  _ , _ \<rangle>" [50, 50, 50] 50)  where
  reduce_if_trueI:  " \<Phi> \<turnstile> \<langle>  \<delta> , AS_if (V_lit L_true) s1 s2 \<rangle> \<longrightarrow> \<langle> \<delta> , s1 \<rangle> "
| reduce_if_falseI: " \<Phi> \<turnstile> \<langle>  \<delta> , AS_if (V_lit L_false) s1 s2 \<rangle> \<longrightarrow> \<langle> \<delta> , s2 \<rangle> "
| reduce_let_valI:  " \<Phi> \<turnstile> \<langle>  \<delta> , AS_let (AE_val v)  s \<rangle> \<longrightarrow> \<langle>  \<delta> , s[(XBVar 0)::=v]\<^sub>s\<^sub>v \<rangle>"  
| reduce_let_plusI: " \<Phi> \<turnstile>  \<langle> \<delta> , AS_let (AE_op Plus ((V_lit (L_num n1))) ((V_lit (L_num n2))))  s \<rangle> \<longrightarrow> 
                           \<langle> \<delta> , AS_let (AE_val (V_lit (L_num ( (( n1)+(n2)))))) s  \<rangle> "  
| reduce_let_leqI:  "b = (if (n1 \<le> n2) then L_true else L_false) \<Longrightarrow> 
             \<Phi>  \<turnstile>  \<langle> \<delta> ,  AS_let ((AE_op LEq (V_lit (L_num n1)) (V_lit (L_num n2)))) s \<rangle> \<longrightarrow> 
                                                          \<langle> \<delta> , AS_let (AE_val (V_lit b)) s \<rangle>"  
| reduce_let_appI:  "\<lbrakk>   
                         Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ b c \<tau> s'))) = lookup_fun \<Phi> f \<rbrakk> \<Longrightarrow>  
             \<Phi>  \<turnstile>  \<langle> \<delta> , AS_let   ((AE_app f v)) s \<rangle> \<longrightarrow> \<langle> \<delta> ,  AS_let2 (\<tau>[(XBVar 0)::=v]\<^sub>v) (s'[(XBVar 0)::=v]\<^sub>v) s \<rangle> "     
(*| reduce_let_appPI:  "\<lbrakk> x = mk_fresh_x GNil ; bv = mk_fresh_bv {}
                       Some (AF_fundef f (AF_fun_typ_some (AF_fun_typ b c \<tau> s'))) = lookup_fun \<Phi> f \<rbrakk> \<Longrightarrow>  
             \<Phi>  \<turnstile>  \<langle> \<delta> , AS_let ((AE_appP f b' v)) s \<rangle> \<longrightarrow> \<langle> \<delta> ,  AS_let2 ((open_t_bv (open_x \<tau> x 0) bv 0)[bv::=b']\<^sub>\<tau>\<^sub>b[x::=v]\<^sub>\<tau>\<^sub>v) 
                                                                            ((open_s_bv (open_x s' x 0) bv 0)[bv::=b']\<^sub>s\<^sub>b[x::=v]\<^sub>s\<^sub>v) s \<rangle> "  *)
| reduce_let_fstI:  "\<Phi> \<turnstile> \<langle>  \<delta> , AS_let (AE_fst (V_pair v1 v2))  s \<rangle> \<longrightarrow> \<langle>  \<delta> , AS_let (AE_val v1)  s \<rangle>"
| reduce_let_sndI:  "\<Phi> \<turnstile> \<langle>  \<delta> , AS_let (AE_snd (V_pair v1 v2))  s \<rangle> \<longrightarrow> \<langle>  \<delta> , AS_let (AE_val v2)  s \<rangle>"
| reduce_let_concatI:  "\<Phi> \<turnstile> \<langle>  \<delta> , AS_let (AE_concat (V_lit (L_bitvec v1))  (V_lit (L_bitvec v2)))  s \<rangle> \<longrightarrow> 
                            \<langle>  \<delta> , AS_let (AE_val (V_lit (L_bitvec (v1@v2))))  s \<rangle>"
| reduce_let_lenI:  "\<Phi> \<turnstile> \<langle>  \<delta> , AS_let (AE_len (V_lit (L_bitvec v)))  s \<rangle> \<longrightarrow> 
                              \<langle>  \<delta> , AS_let (AE_val (V_lit (L_num (List.length v))))  s \<rangle>"
| reduce_let_mvar:  "Some v = lookup_dv \<delta> u \<Longrightarrow>  \<Phi> \<turnstile> \<langle>  \<delta> , AS_let (AE_mvar u)  s \<rangle> \<longrightarrow> \<langle>  \<delta> , AS_let (AE_val v) s  \<rangle>" 
| reduce_varI: "  \<Phi>  \<turnstile>  \<langle>  \<delta> , AS_var \<tau> v s  \<rangle> \<longrightarrow> \<langle> ((v)#\<delta>) , s \<rangle>"
| reduce_assignI: "  \<Phi>  \<turnstile>  \<langle> \<delta> , AS_assign ( u) v  \<rangle> \<longrightarrow> \<langle> update_d \<delta> u v , AS_val (V_lit L_unit) \<rangle>"
| reduce_seq1I: "\<Phi>   \<turnstile>  \<langle> \<delta> , AS_seq (AS_val (V_lit L_unit )) s  \<rangle> \<longrightarrow> \<langle>  \<delta> , s \<rangle>"
(* 16 *) | reduce_seq2I: "\<lbrakk> s_not_v s1 ; \<Phi>  \<turnstile>  \<langle> \<delta> , s1 \<rangle> \<longrightarrow> \<langle>  \<delta>' , s1' \<rangle> \<rbrakk> \<Longrightarrow> 
                          \<Phi>  \<turnstile>  \<langle> \<delta> , AS_seq s1 s2 \<rangle> \<longrightarrow> \<langle>  \<delta>' , AS_seq s1' s2 \<rangle>"
| reduce_let2_valI:  " \<Phi>  \<turnstile>  \<langle>  \<delta> , AS_let2 t (AS_val v) s \<rangle> \<longrightarrow> \<langle>  \<delta> , s[(XBVar 0)::=v]\<^sub>v \<rangle>" 
| reduce_let2I:  " \<Phi>  \<turnstile> \<langle>  \<delta> , s1  \<rangle> \<longrightarrow> \<langle>  \<delta>' , s1' \<rangle> \<Longrightarrow> \<Phi>  \<turnstile> \<langle>  \<delta> , AS_let2 t s1 s2 \<rangle> \<longrightarrow> \<langle>  \<delta>' , AS_let2 t s1' s2 \<rangle>"  

| reduce_caseI:  "\<lbrakk> find_branch dc' cs (AS_branch dc s')  \<rbrakk> \<Longrightarrow>  \<Phi> \<turnstile>  \<langle> \<delta> , AS_match (V_cons tyid dc' v) cs \<rangle>  \<longrightarrow> \<langle> \<delta> , s'[(XBVar 0)::=v]\<^sub>v \<rangle> "
| reduce_whileI: "
                    \<Phi>  \<turnstile>  \<langle> \<delta> , AS_while s1 s2  \<rangle> \<longrightarrow> 
            \<langle> \<delta> , AS_let2 (\<lbrace> : B_bool | TRUE \<rbrace>) s1 (AS_if (V_var ((XBVar 0))) (AS_seq s2 (AS_while s1 s2))  (AS_val (V_lit L_unit)))  \<rangle>"


inductive reduce_stmt_many :: "\<Phi> \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> bool"    ("_ \<turnstile> \<langle> _ , _ \<rangle> \<longrightarrow>\<^sup>* \<langle>  _ , _ \<rangle>" [50, 50, 50] 50)  where  
  reduce_stmt_many_oneI:  "\<Phi> \<turnstile> \<langle> \<delta>  , s \<rangle> \<longrightarrow> \<langle>  \<delta>' , s' \<rangle>  \<Longrightarrow> \<Phi> \<turnstile> \<langle> \<delta>  , s \<rangle> \<longrightarrow>\<^sup>* \<langle>  \<delta>' , s' \<rangle> "
| reduce_stmt_many_manyI:  "\<lbrakk> \<Phi> \<turnstile> \<langle> \<delta>  , s \<rangle> \<longrightarrow>   \<langle>  \<delta>' , s' \<rangle> ; \<Phi> \<turnstile>  \<langle> \<delta>'  , s' \<rangle> \<longrightarrow>\<^sup>* \<langle>  \<delta>'' , s'' \<rangle> \<rbrakk> \<Longrightarrow> \<Phi> \<turnstile>  \<langle> \<delta>  , s \<rangle> \<longrightarrow>\<^sup>* \<langle>  \<delta>'' , s'' \<rangle>"

fun  convert_fds :: "fun_def list \<Rightarrow> (f*fun_def) list" where
  "convert_fds [] = []"
| "convert_fds ((AF_fundef f (AF_fun_typ_none (AF_fun_typ  b c \<tau> s)))#fs) = ((f,AF_fundef f (AF_fun_typ_none (AF_fun_typ  b c \<tau> s)))#convert_fds fs)"
| "convert_fds ((AF_fundef f (AF_fun_typ_some  (AF_fun_typ  b c \<tau> s)))#fs) = ((f,AF_fundef f (AF_fun_typ_some  (AF_fun_typ  b c \<tau> s)))#convert_fds fs)"


fun  convert_tds :: "type_def list \<Rightarrow> (f*type_def) list" where
  "convert_tds [] = []"
| "convert_tds ((AF_typedef s dclist)#fs) = ((s,AF_typedef s dclist)#convert_tds fs)"
| "convert_tds ((AF_typedef_poly s dclist)#fs) = ((s,AF_typedef_poly s  dclist)#convert_tds fs)"


inductive reduce_prog :: "p \<Rightarrow> v \<Rightarrow> bool" where
"\<lbrakk> reduce_stmt_many \<Phi> [] s \<delta> (AS_val v) \<rbrakk> \<Longrightarrow>  reduce_prog (AP_prog \<Theta> \<Phi> s) v"

section \<open>Reduction Typing\<close>

(* FIXME - Can the store contain polymorphic values; for example None with type 'a option? *)
text {* Checks that the store is consistent with @{typ \<Delta>} *}
inductive delta_sim :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<delta> \<Rightarrow> \<Delta> \<Rightarrow> bool" ( "_ ; _ \<turnstile> _ \<sim> _ " [50,50] 50 )  where
  delta_sim_nilI:  "\<Theta> ; \<Phi>  \<turnstile> [] \<sim> [] "
| delta_sim_consI: "\<lbrakk> \<Theta> ; \<Phi>  \<turnstile> \<delta> \<sim> \<Delta> ; check_v \<Theta>  {}  GNil  v  \<tau>  
                        \<rbrakk> \<Longrightarrow> \<Theta> ; \<Phi>  \<turnstile> ((v)#\<delta>) \<sim> (\<tau>#\<Delta>)" 



text {* A typing judgement that combines typing of the statement, the store and the condition that functions are well-formed *}
inductive config_type ::  "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> \<tau> \<Rightarrow> \<Delta> \<Rightarrow>  bool"   ("_ ; _  \<turnstile> \<langle> _ , _ \<rangle> \<Leftarrow> _ ; _ " [50, 50, 50] 50)  where 
config_typeI: "\<lbrakk> \<Theta> ; \<Phi> ; {} ; GNil ; \<Delta> \<turnstile> s \<Leftarrow> \<tau>; 
                (\<forall> fd \<in> set \<Phi>. check_fundef \<Theta> \<Phi> fd) ;
                \<Theta> ; \<Phi>  \<turnstile> \<delta> \<sim> \<Delta> \<rbrakk>
                \<Longrightarrow> \<Theta> ; \<Phi>  \<turnstile> \<langle> \<delta>  , s \<rangle> \<Leftarrow>  \<tau> ; \<Delta>"

end

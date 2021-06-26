(*<*)
theory TypingDBIBroken
  imports Main
begin
(*>*)

datatype c = C_true

datatype s =  
 AS_match  branch_list 
| AS_empty
and branch_s = 
  AS_branch   s
and branch_list = 
  AS_final 
| AS_cons  branch_list

datatype \<tau> = T c

locale smt_valid = fixes valid :: " c \<Rightarrow> bool"  
 assumes "valid C_true"

inductive (in smt_valid) subtype :: "\<tau> \<Rightarrow> \<tau>  \<Rightarrow> bool"   
  where "\<lbrakk> valid   c \<rbrakk> \<Longrightarrow> subtype  t1 t2 "


inductive  (in smt_valid) check_s ::  "s \<Rightarrow> \<tau> \<Rightarrow> bool" ("  \<turnstile> _ \<Leftarrow> _" ) and
           check_case_s ::  "branch_s \<Rightarrow> \<tau> \<Rightarrow> bool" ("   \<turnstile> _ \<Leftarrow> _") and
           check_case_ss ::  "branch_list \<Rightarrow> \<tau> \<Rightarrow> bool" ("  \<turnstile> _ \<Leftarrow> _" ) where 
 "subtype \<tau> \<tau> \<Longrightarrow> \<turnstile> AS_empty \<Leftarrow> \<tau>"
| "\<turnstile> AS_final \<Leftarrow> \<tau>"
| "\<turnstile> AS_cons css \<Leftarrow> \<tau>"
| "\<turnstile> cs \<Leftarrow> \<tau>  \<Longrightarrow> \<turnstile> AS_match cs \<Leftarrow> \<tau>"


global_interpretation smt_valid_i: smt_valid "\<lambda>  _. True" 
  defines smt_valid_i_subtype = "smt_valid_i.subtype"  and        
          smt_valid_i_check_s = "smt_valid_i.check_s"  and
          smt_valid_i_check_case_s = "smt_valid_i.check_case_s" and
          smt_valid_i_check_case_ss = "smt_valid_i.check_case_ss" 
by unfold_locales simp

declare smt_valid_i.subtype.intros[code_pred_intro]
declare smt_valid_i.check_s_check_case_s_check_case_ss.intros[code_pred_intro]

code_pred  (modes: 
       smt_valid_i_subtype:  i \<Rightarrow> i \<Rightarrow> bool and        
       smt_valid_i_check_s:     i \<Rightarrow> i \<Rightarrow> bool and
       smt_valid_i_check_case_ss:   i \<Rightarrow> i \<Rightarrow> bool 
)
[show_steps,  show_mode_inference,  show_invalid_clauses] smt_valid_i_check_s 
  sorry



end
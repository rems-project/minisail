theory CodeGenDBI
imports OperationalDBI
begin

code_pred (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> o \<Rightarrow> bool ) [show_steps,  show_mode_inference,  show_invalid_clauses]  reduce_stmt_many . 

values "{ (d,s) . reduce_stmt_many [] [] (AS_let  (AE_val (V_lit (L_num 10)))  (AS_let (AE_val (V_lit L_true)) (AS_val (V_var ((XBVar 1)))))) d s }"

end
theory SafetyDBI
imports OperationalDBI TypingDBI MiniSail.Operational
begin



lemma  safety:
  fixes \<Phi>::SyntaxLemmasDBI.\<Phi> and s::SyntaxDBI.s and s'::SyntaxDBI.s and v::SyntaxDBI.v
  assumes " \<Phi>   \<turnstile> \<langle> \<delta> , s \<rangle> \<longrightarrow>\<^sup>* \<langle> \<delta>' , s' \<rangle>" and "\<Theta> ; \<Phi>  \<turnstile>  \<langle> \<delta> , s \<rangle> \<Leftarrow> \<tau> ; \<Delta>"
  shows  "(\<exists>v. s' = SyntaxDBI.AS_val v) \<or> (\<exists>\<delta>'' s''. \<Phi>  \<turnstile> \<langle>  \<delta>' , s'  \<rangle> \<longrightarrow> \<langle>  \<delta>'' , s'' \<rangle>)"  
(* convert assms to nominal equivalents.
   invoke safety
   convert back *)
  sorry

end
theory CodeGenNominalSetup
imports MiniSail.Typing  HOL.Code_Numeral
begin

(* Current status is that smart constructors with an arg are not pattern matching in rule
   (and for 'pure quotienting' they don't work in functions. I guess nominal_function is doing something
   special.
  
   free_constructors is the usual way thing to use to register them as true constructors however
   using this requires injectivity which I don't have - ie the constructors are not free?
   (I see free_constructors sort of works by using free_constructors and sorry).

   So maybe this is not going to fly as it can't unpick the n from "L_num" n for example
   so how/why does it work for nominal_functions - probably some other magic going on
  
   See CodeGenQuestion in misc

   Lukas suggested look at some example of another way to do it, requires
   that 'constructors' be invertible. Using code_unfold and some ML code to
   do it. At some point will we need to decide on a canonical representation
    AS_let x e s 

   look at http://isabelle.in.tum.de/repos/isabelle/file/b85a12c2e2bf/src/HOL/Library/Predicate_Compile_Alternative_Defs.thy
    starting at line 64 section \<open>Arithmetic operations\


 Need to understand code generation and quotient types; in particular need
   to get equality to code gen

   See https://lists.cam.ac.uk/pipermail/cl-isabelle-users/2015-July/msg00127.html for help? 

  https://www.isa-afp.org/browser_info/current/AFP/Name_Carrying_Type_Inference/SimplyTyped.html

  These that I think will need looking at the following code generation for:
       Atom_decls
       Nominal_datatypes
       Prescence of binders
       When we need a fresh variable ie let statements
      
*)

section \<open>Basic nominal datatypes and functions - Ok\<close>
(* Doing basic nominal datatypes and functions on them is ok *)

code_datatype BitZero BitOne

code_datatype B_unit B_bitvec B_bool B_int B_pair
code_datatype C_eq C_true C_false C_imp C_conj C_disj C_not
code_datatype AE_val 
code_datatype CE_val
code_datatype V_var V_lit V_pair V_cons
code_datatype T_refined_type



free_constructors case_b for BitOne | BitZero using bit.distinct bit.exhaust by auto
free_constructors case_l for L_true | L_false |L_unit | L_num i | L_bitvec bv using l.distinct l.exhaust by auto+
(*free_constructors case_b for B_unit | B_bitvec | B_bool | B_int | B_pair b1 b2 | B_id s | B_var bv
  using b.exhaust b.distinct this doesn't always work *)

value "L_true = L_false"

setup_lifting type_definition_x
(* And I guess more for those with binders *)

fun mk_atom_x :: "nat \<Rightarrow> atom" where
  "mk_atom_x n = Atom (Sort ''Syntax.x'' []) n"

lift_definition mk_x :: "nat \<Rightarrow> x" is mk_atom_x using mk_atom_x.simps by auto

end
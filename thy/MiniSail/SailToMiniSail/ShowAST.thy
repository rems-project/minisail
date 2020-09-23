theory ShowAST
(* From https://www.isa-afp.org/entries/Show.html *)
imports  Env AstUtils "Show.Show" "Show.Show_Instances"
begin

section \<open>Setup\<close>

subsection \<open>Integer\<close>

definition showsp_integer :: "integer showsp" where
  "showsp_integer p n = showsp_int p (int_of_integer n)"

lemma show_law_integer [show_law_intros]:
  "show_law showsp_integer r"
  by (rule show_lawI) (simp add: showsp_integer_def show_law_simps)

lemma showsp_integer_append [show_law_simps]:
  "showsp_integer p r (x @ y) = showsp_integer p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup {*
  Show_Generator.register_foreign_showsp @{typ integer} @{term "showsp_integer"} @{thm show_law_integer}
*}

subsection \<open>Sting Literal\<close>

definition showsp_literal :: "String.literal showsp" where
  "showsp_literal p n = shows_string (String.explode n)"

lemma show_law_literal [show_law_intros]:
  "show_law showsp_literal r"
  by (rule show_lawI) (simp add: showsp_literal_def show_law_simps)

lemma showsp_literal_append [show_law_simps]:
  "showsp_literal p r (x @ y) = showsp_literal p r x @ y"
  by (intro show_lawD show_law_intros)

local_setup {*
  Show_Generator.register_foreign_showsp @{typ String.literal} @{term "showsp_literal"} @{thm show_law_literal}
*}


derive "show"  id  kid  kind  kinded_id  order loop 


derive "show" nexp

derive "show" base_effect

derive "show" effect

derive "show" n_constraint
derive "show" "typ" typ_arg
derive "show" typ_pat


derive "show"  lit
derive "show"  pat
derive "show" "value"
derive "show"  exp
derive "show"  quant_item  typquant 
derive "show"  type_union index_range
derive "show"  mut


fun show_env :: "env \<Rightarrow> char list" where
"show_env env = ''Locals: '' @ List.concat (List.map (\<lambda>(i,t). show i @ ''::'' @ (show t) @ '' '') (locals env)) @ ''\<newline>'' @
                ''Typvars: '' @ List.concat (List.map (\<lambda>(i,t). show i @ ''::'' @ (show t) @ '' '') (typ_vars env)) @ ''\<newline>'' @
                ''Val specs: '' @ List.concat (List.map (\<lambda>(i,t). show i @ ''::'' @ (show t) @ '' '') (top_val_specs env)) @ ''\<newline>'' @
                ''Variants: '' @ List.concat (List.map (\<lambda>(i,t). show i @ ''::'' @ (show t) @ '' '') (variants env)) @ ''\<newline>'' @
                ''Records: '' @ List.concat (List.map (\<lambda>(i,t). show i @ ''::'' @ (show t) @ '' '') (records env)) @ ''\<newline>'' @
                ''Typsyn: ''  @ List.concat (List.map (\<lambda>(i,(tq,ta)). show i @ ''::'' @ (show tq) @ (show ta) @ '' '') (typ_synonyms env))
"

fun show_tannot :: "tannot \<Rightarrow> char list" where
  "show_tannot None = ''tannot = (None)''"
| "show_tannot (Some t) = ''Inst: '' @ (case tannot_instantiations t of
                                             Some ts \<Rightarrow> List.concat (List.map (\<lambda>(i,t). (show i) @ '' = '' @ (show t) @ '' '') ts)
                                           | None \<Rightarrow> ''(none)'')  @ ''\<newline>'' @
                          ''Typ: '' @ (show (tannot_typ t))
"

(*derive "show" type_def_aux type_def *)

value "show (L_num 10)"

value "show unit_typ"



end
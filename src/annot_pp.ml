open PPrintEngine
open PPrintCombinators
open Sail_pp
open Type_check
open Ast_util

let opt_pp_env = ref true
   
let pp_json_env env = string "{ " ^^
                       string "\"locals\" : [ " ^^ separate (string ",")
                                                     (List.map (fun (s,(_,t)) -> string "{ \"id\" : " ^^
                                                               pp_json_id s ^^ string " , \"typ\" : " ^^ pp_json_typ t ^^ string "}" ) (Bindings.bindings (Env.get_locals env)))  ^^ string " ], \n" ^^

                         string "\"variants\" : [ " ^^ separate (string ",")
                                 (List.map (fun (s,(tq,tus)) -> string "{ \"id\" : " ^^
                                   pp_json_id s ^^ string " , \"tu_list\" : [" ^^ 
                                          separate (string ",") (List.map pp_json_type_union tus) ^^ string "]}")
                         (Bindings.bindings (Env.get_variants env)))  ^^ string " ] \n" ^^
(*          
      string "\"typ_vars\" : [ " ^^  separate (string ",") (List.map (fun (s,k) -> pp_json_kid s ^^ string "=" ^^ pp_raw_kind_aux k) (KBindings.bindings (Env.get_typ_vars env)))  ^^ string "],\n" ^^

        string "\"constraints\" : [ " ^^ separate (string ",") (List.map (fun c -> pp_json_n_constraint c) (Env.get_constraints env)) ^^ string "],\n" ^^

      string "\"records\" : [" ^^ separate (string ",") (List.map (fun (s,(_,fields)) ->
           string "   " ^^ pp_raw_id s ^^ string " = {" ^^
           separate (string ",") (List.map (fun (typ,id) -> pp_raw_id id ^^ string " : " ^^ pp_raw_typ typ) fields ) ^^ string "}\n"
          ) (Bindings.bindings (Env.get_records env))) ^^ string ";\n" ^^
 *)
      string "}\n"

  
let pp_json_annot (_,tannot) = match Type_check.destruct_tannot tannot with
                               None -> string "\"undefined\"" |
                               Some (e,t,_) -> string "{" ^^
                                                 string "\"typ\" :" ^^ pp_json_typ t ^^
                                                   ( if !opt_pp_env then 
                                                       string ",\"env\" : " ^^ pp_json_env e 
                                                     else
                                                       string ""
                                                   )
                                               ^^ string "}"


                       



import tempfile, os, shutil,sys

fn_convert=False

for filename in sys.argv[1:]:

    with tempfile.NamedTemporaryFile(delete=False) as temp_file:
        with open(filename) as infile:
            for line in infile:

                if line.startswith("and pp_raw_loop_default"):
                    line = "and pp_raw_loop _ = string \"<loop>\""

                if line.startswith("and pp_loop_default"):
                    line = "and pp_loop  _ = string \"<loop>\""

                if line.startswith("and pp_json_loop_default"):
                    line = "and pp_json_loop  _ = string \"<loop>\""

                if line.startswith("| L_string("):
                    continue

                line = line.replace("| TD_aux(type_def_aux)", "| TD_aux(type_def_aux,_)")

                line = line.replace("open PPrintCombinators",
                                    "open PPrintCombinators\nopen Ast\nopen Ast_defs\nlet string_of_value _ = string \"<value>\"\nlet string_of_text s = string \"\\\"\" ^^ string s ^^ string \"\\\"\"\n")
                
                if line == "open \n":
                    continue

                if line.startswith("and pp_raw_order x ="):
                    line = "and pp_raw_annot _ = string \"\\\"<annot>\\\"\"\n" + line
                if line.startswith("and pp_json_order x ="):
                    line = "and pp_json_annot _ = string \"\\\"<annot>\\\"\"\n" + line
                if line.startswith("and pp_order x ="):
                    line = "and pp_annot _ = string \"\\\"<annot>\\\"\"\n"  + line

                
                line = line.replace("Big_int.string_of_big_int x" , "string (Nat_big_num.to_string x)")
                
                line = line.replace ("and pp_raw_l_default", "and pp_raw_l _ = string \"\\\"<loc>\\\"\"")
                line = line.replace ("and pp_json_l_default", "and pp_json_l _ = string \"\\\"<loc>\\\"\"")
                line = line.replace ("and pp_l_default", "and pp_l _ = string \"\\\"<loc>\\\"\"")

                line = line.replace ("and pp_raw_semi_opt_default" , "and pp_raw_semi_opt _ = string \"\"")
                line = line.replace ("and pp_json_semi_opt_default" , "and pp_json_semi_opt _ = string \"\"")
                line = line.replace ("and pp_semi_opt_default" , "and pp_semi_opt _ = string \"\"")

                line = line.replace ("and pp_raw_cast_opt x = match x with" , "and pp_raw_cast_opt _ = string \"\"")
                line = line.replace ("and pp_json_cast_opt x = match x with" , "and pp_json_cast_opt _ = string \"\"")
                line = line.replace ("and pp_cast_opt x = match x with" , "and pp_cast_opt _ = string \"\"")

                line = line.replace("and pp_raw_val_spec_aux x = match x with",
                                    "and pp_raw_val_spec_aux x = match x with\n| VS_val_spec (ts,_,_,_) -> pp_raw_typschm ts\n")

                line = line.replace("and pp_json_val_spec_aux x = match x with",
                                    "and pp_json_val_spec_aux x = match x with\n| VS_val_spec (ts,_,_,_) -> pp_json_typschm ts\n")

                line = line.replace("and pp_val_spec_aux x = match x with",
                                    "and pp_val_spec_aux x = match x with\n| VS_val_spec (ts,_,_,_) -> pp_typschm ts\n")

                line = line.replace("Pat_funcl_exp(pat,exp)",
                                    "Pat_aux(Pat_exp(pat,exp),_)") 

                line = line.replace("Pat_funcl_when(pat,exp1,exp)",
                                    "Pat_aux(Pat_when(pat,exp1,exp),_)")

                line = line.replace("VS_aux(val_spec_aux)","VS_aux(val_spec_aux,_)")

                
                if line.startswith("let rec no pp or ocaml hom for n"):
                    continue
                
                temp_file.write(line)

    shutil.move(temp_file.name, filename)

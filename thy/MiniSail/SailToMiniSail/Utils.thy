theory Utils
  imports Main  Native_Word.Uint32
begin

(* Borrowed from AFP library *)
fun string_of_digit :: "nat \<Rightarrow> string"
where
  "string_of_digit n =
    (if n = 0 then ''0''
    else if n = 1 then ''1''
    else if n = 2 then ''2''
    else if n = 3 then ''3''
    else if n = 4 then ''4''
    else if n = 5 then ''5''
    else if n = 6 then ''6''
    else if n = 7 then ''7''
    else if n = 8 then ''8''
    else ''9'')"

(* From https://stackoverflow.com/questions/23864965/string-of-nat-in-isabelle *)
fun string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n = (if n < 10 then string_of_digit n else 
     string_of_nat (n div 10) @ (string_of_digit (n mod 10)))"

fun string_of_literal :: "String.literal \<Rightarrow> string" where
  "string_of_literal s = String.explode s"

fun string_to_literal :: "string \<Rightarrow> String.literal" where
  "string_to_literal s = String.implode s"

fun string_lit_concat :: "String.literal list \<Rightarrow> String.literal" where
 "string_lit_concat s = List.foldr (+) s (STR '''')"

definition string_of_int :: "int \<Rightarrow> string"
where
  "string_of_int i = (if i < 0 then ''-'' @ string_of_nat (nat (- i)) else 
     string_of_nat (nat i))"

definition string_lit_of_int :: "int \<Rightarrow> String.literal"
where
  "string_lit_of_int = String.implode \<circ> string_of_int"


definition string_lit_of_uint32 :: "uint32 \<Rightarrow> String.literal"
where
  "string_lit_of_uint32 = String.implode \<circ> string_of_int \<circ> int_of_uint32"

definition string_lit_of_integer :: "integer \<Rightarrow> String.literal"
where
  "string_lit_of_integer = string_lit_of_int \<circ> int_of_integer"


definition string_lit_of_nat :: "nat \<Rightarrow> String.literal" where
  "string_lit_of_nat = String.implode \<circ> string_of_nat"

fun string_map :: "string \<Rightarrow> ('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string" where
   "string_map delim f [] = ''''"
|  "string_map delim f [x] = f x" 
|  "string_map delim f (x#xs) = f x @ delim @ (string_map delim f xs)"

fun string_lit_map :: "String.literal \<Rightarrow> ('a \<Rightarrow> String.literal) \<Rightarrow> 'a list \<Rightarrow> String.literal" where
   "string_lit_map delim f [] = STR ''''"
|  "string_lit_map delim f [x] = f x" 
|  "string_lit_map delim f (x#xs) = f x + delim + (string_lit_map delim f xs)"

fun unzip3 :: "('a * 'b * 'c) list \<Rightarrow> ('a list * 'b list * 'c list)" where
  "unzip3 [] = ([],[],[])"
| "unzip3 ((x,y,z)#xyz) = (let (xs,ys,zs) = unzip3 xyz in (x#xs, y#ys, z#zs))"

fun unzip :: "('a * 'b ) list \<Rightarrow> ('a list * 'b list )" where
  "unzip [] = ([],[])"
| "unzip ((x,y)#xy) = (let (xs,ys) = unzip xy in (x#xs, y#ys))"

end
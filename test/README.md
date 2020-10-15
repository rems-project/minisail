The following tests from sail/tests/typecheck/pass fail the validator:

existential_ast.sail - need to handle existential in subtype checks
new_bitfields.sail - do something with $option -new_bitfields
nlflow.sail expecting - do something with $option -non_lexical_flow
pow_32_64.sail expecting - do something with $option -smt_linearize
reg_32_64.sail expecting - subtyping between register and bitvector
reg_ref.sail expecting - ??
type_pow_zero.sail expecting - do something with $option -smt_solver cvc4

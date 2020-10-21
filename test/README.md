The following tests from sail/tests/typecheck/pass fail the validator:

existential_ast.sail - need to handle existential in subtype checks
new_bitfields.sail - do something with $option -new_bitfields
nlflow.sail expecting - do something with $option -non_lexical_flow
pow_32_64.sail - do something with $option -smt_linearize
reg_32_64.sail  - subtyping between register and bitvector
reg_ref.sail - ??
type_pow_zero.sail - do something with $option -smt_solver cvc4

removing implicit Typ_app - check calls to fun with implicit args - seems to be ok. Sail tc will attempt to
calculate at value for it.

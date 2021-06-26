# minisail
A core language for Sail.

The ./ott directory contains the following:
* Grammar, typing and operational semantics for MiniSail - minisail_anf
* Rules for Sail type system - sail_decl_rules
* Rules for scheme to convert from Sail to MiniSail - sail_to_anf

PDF files are included here, and commentary on MiniSail can be found in [1] and [2].

The ./thy/MiniSail directory contains the following
* ./Safety - A mechanisation in Isabelle of MiniSail using Nominal2 Isabelle with a safety proof.
* ./SailToMiniSail - Declarative type system for Sail and converter for Sail to MiniSail.
* ./SafetyDBI - A mechanisation of MiniSail using de Bruijn indicies. Partially complete. 

The ./src directory contains a wrapper for code exported from Isabelle for the Sail type validator and converter. 
It invokes the Sail type checker and if that passes can invoke the validator and converter.

# What can be validated?

The validator will validate as correct:

* All of Sail type check tests except one using exisentials.
* ?? of RISCV model.


[1] - 'ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS' https://www.cl.cam.ac.uk/users/pes20/sail/sail-popl2019.pdf

[2] - 'MiniSail - A Core Calculus for Sail'. Supplementary material for the above detailing MiniSail and paper proofs of safety. https://www.cl.cam.ac.uk/~mpew2/papers/minisail_anf.pdf

This work was carried out whilst Mark Wassell was a PhD student at the University of Cambridge and supported by EPSRC award 1789939.

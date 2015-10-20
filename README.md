
### Formalising Parity Complexes

These five files are enough to formalise Ross Street's `Parity Complexes' up to the excision of extremals algorithm (Theorem 4.1).
Strictly speaking, we have formalised sections 1 and 2, Propositions 3.1, 3.2, 3.3, and Theorem 4.1.

The files exhibit dependence in the following order:
 - basic_nat.v 
 - Ensembles_setoids.v 
 - Finite_Ensembles.v 
 - PreparityComplexes.v 
 - ParityComplexes.v 

These files contain the following content:
 - Basic results in logic and for natural numbers that we could not find in the standard library.
 - Setoid rewrite for Ensembles and some extra properties of Ensembles.
 - Modified definitions of Finite and Cardinal that interact well with setoid rewrites. Some basic properties of finite sets.
 - Definition of parity complex without axioms (preparity complex), basic structural results and implementation of Section 2.
 - Implementation of Sections 1, 3 and 4.

Compilation instructions:

1. First, there is already a make file here. One can check it by running 'cat Make'
2. One should then run 'coq_makefile -f Make -o Makefile'.
3. Finally, run 'make' to compile all the code. Warning: the final file might take 5 or 10 minutes to compile.

This has been compiled with coqc version 8.4 (September 2012 with OCaml 3.12.1). We have not checked other releases.

The author is not so experienced with make files and compilation options, any recommendations are welcome at [this address](mailto:mitchell.alan.buckley@gmail.com).
 

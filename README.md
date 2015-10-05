

These five files are enough to formalise Ross Street's `Parity Complexes' up to the excision of extremals algorithm (Theorem 4.1).

Strictly speaking, we have formalised sections 1 and 2, Propositions 3.1, 3.2, 3.3, and Theorem 4.1.

The files exhibit dependence in the following order:
 - basic_nat.v 
    (Basic results in logical and for natural numbers that we could not find in the standard library)
 - Ensembles_setoids.v 
    (Setoid rewrite for Ensembles and some extra properties of Ensembles)
 - Finite_Ensembles.v 
    (Modified definitions of Finite and Cardinal that interact well with setoid rewrites) 
 - PreparityComplexes.v 
    (Definition of parity complex without axioms (preparity complex), and Section 2)
 - ParityComplexes.v 
    (Sections 1, 3, 4)

Compilation instructions:
 First, there is already a make file here. One can check it by running 'cat Make'
 So one should then run 'coq_makefile -f Make -o Makefile' to generate a makefile.
 And finally, run 'make' to compile all the code. Warning: the final file might take 5 or 10 minutes to compile.

 The author is not so experienced with make-files and compilation options, any recommendations are welcome (mitchell.alan.buckley@gmail.com).
 
 We have compiled this with coqc version 8.4 (September 2012 with OCaml 3.12.1). We have not checked compilation with other releases.
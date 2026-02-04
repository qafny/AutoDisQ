From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

Extraction Language OCaml.
Extraction Blacklist String List Nat Bool.


Require Import AUTO.

Extraction "autodisq_2.ml"
  AUTO.auto_disq
  AUTO.auto_disq_search
 AUTO.gen_prog
AUTO.gen_prog_core
AUTO.parallelize_in_membrane.

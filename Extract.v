
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

(* Import the file that defines the algorithm *)
Require Import AUTO.

Extraction Language OCaml.

(* Improve extraction quality *)
Set Extraction AutoInline.


(* Extract top-level executable functions *)
Extraction "autodisq.ml"
  AUTO.auto_disq
  AUTO.auto_disq_search
  AUTO.gen_prog
  AUTO.gen_prog_core
  AUTO.parallelize_in_membrane.








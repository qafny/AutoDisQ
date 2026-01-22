# DisQ

This repo contains the coq definition of DisQ, in which we define the syntax, semantics and type system of it. 

## Overview

Quantum algorithms generally demand a large number of qubits, making implementation on a single quantum computer difficult due to limited resources. To solve this problem, we have developed a new system called DisQ. DisQ is a framework designed to facilitate the rewriting of quantum algorithms into their distributed versions. The core of  DisQ is distributed quantum programming language that integrates concepts from the Chemical Abstract Machine (CHAM) and Markov Decision Processes (MDP) to define the quantum concurrent and distributed behaviors.

## Setup

To compile DisQ, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.13**.

Assuming you have opam installed (following the instructions in the link above), follow the steps below to set up your environment.
```
# environment setup
opam init
eval $(opam env)

# install some version of the OCaml compiler in a switch named "qnp"
opam switch create qnp 4.12.0
eval $(opam env)

# install Coq -- this will take a while!
opam install coq

# install coq-quickchick
opam install coq-quickchick
```

*Notes*:
* Depending on your system, you may need to replace 4.12.0 in the instructions above with something like "ocaml-base-compiler.4.12.0". Any recent version of OCaml should be fine. 
* We require Coq version >= 8.12. We have tested compilation with 8.12.2, 8.13.2, and 8.14.0.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

## Compiling & Running DisQ

Run `make` in the top-level directory to compile our Coq proofs. externals directory contains the coq files from SQIR and QWIRE that support the development of LQafny.

## Directory Contents

* DisQSyntax.v - The DisQ language syntax.
* DisQDef.v - Locus and state syntax and equation rules.
* DisQKind.v - The DisQ Kind system and action level semantics.
* DisQType.v - The DisQ Type system.
* DisQSem.v - The DisQ language semantics.




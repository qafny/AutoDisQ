# AutoDisQ
To compile AutoDisQ, you will need [Coq](https://coq.inria.fr/). We recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.16**.


## Environment Setup
```
# initialize opam
opam init -a  

# create a switch named qblue and import the environment
opam switch create qblue
opam switch import opam-switch.export

# check if the switch and packages are right
opam switch
opam list
```

## Setup

To compile AutoDisQ, you will need [Coq](https://coq.inria.fr/) and [QuickChick](https://github.com/QuickChick/QuickChick). We strongly recommend using [opam](https://opam.ocaml.org/doc/Install.html) to install Coq and `opam switch` to manage Coq versions. We currently support Coq **versions 8.16**.

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
* We require Coq version >= 8.16.
* opam error messages and warnings are typically informative, so if you run into trouble then make sure you read the console output.

# install the QuantumLib library
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quantumlib.1.7.0

# Optional, if you want to compile the proofs in examples/shor
opam install coq-interval
opam pin coq-euler https://github.com/taorunz/euler.git

# install the SQIR library
To install SQIR, run opam pin coq-sqir https://github.com/inQWIRE/SQIR.git

To pull subsequent updates, run opam install coq-sqir.

To import SQIR files, use Require Import SQIR.FILENAME


## Compile & Running AutoDisQ
1. Generate Makefile if it is the first time, run `coq_makefile -f _CoqProject -o Makefile`.

2. Compile, run `make` in the current directory. 


## Directory Contents

* DisQSyntax.v - The AutoDisQ language syntax.
* DisQDef.v - Locus and state syntax and equation rules.
* DisQKind.v - The AutoDisQ Kind system and action level semantics.
* DisQType.v - The AutoDisQ Type system.
* DisQSem.v - The AutoDisQ language semantics.
* AUTO.v - The AutoDisQ supporting theorem.
* AUTO_Correctness.v - The AutoDisQ algorithm well-formedness theorem.
* AUTO_Proof.v - The AutoDisQ algorithm bi-simulation theorem (sim_n_steps) and compiler correctness (compile_config_density_sound_0).



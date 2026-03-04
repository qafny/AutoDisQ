
val negb : bool -> bool

val length : 'a1 list -> int

val mul : int -> int -> int

module Nat :
 sig
  val ltb : int -> int -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

type var = int

type bound =
| BVar of var * int
| BNum of int

type range = (var * bound) * bound

type locus = range list

type aexp =
| BA of var
| Num of int
| APlus of aexp * aexp
| AMult of aexp * aexp

type cbexp =
| CEq of aexp * aexp
| CLt of aexp * aexp

type exp =
| SKIP of var * aexp
| X of var * aexp
| CU of var * aexp * exp
| RZ of int * var * aexp
| RRZ of int * var * aexp
| SR of int * var
| SRR of int * var
| QFT of var * int
| RQFT of var * int
| H of var * aexp
| Addto of var * var
| Seq of exp * exp

type cexp =
| CNew of var * int
| CAppU of locus * exp
| CMeas of var * locus

type cdexp =
| NewCh of var * int
| Send of var * aexp
| Recv of var * var

type process =
| PNil
| AP of cexp * process
| DP of cdexp * process
| PIf of cbexp * process * process

type memb =
| Memb of var * process list
| LockMemb of var * process * process list

type config = memb list

type var0 (* AXIOM TO BE REALIZED *)

type membrane = var0

type membranes = membrane list

val var_eqb : var0 -> var0 -> bool

val vars_of_exp : exp -> var0 list

val place_operation : config -> membrane -> exp -> config

val insert_teleport_sends :
  config -> var0 list -> int -> membrane -> config * int

val insert_teleport_receives :
  config -> var0 list -> int -> membrane -> (var0 -> membrane) ->
  (config * int) * (var0 -> membrane)

val empty_config : config

type op_list = exp list

type op_mem_assign = exp -> membrane

type qubit_mem_assign = var0 -> membrane

type current_qubit_loc = var0 -> membrane

type rank = int

type seq_relation = exp -> rank

type fitness_value = int

type distributed_prog = config

val gen_seq :
  (seq_relation * (op_mem_assign * qubit_mem_assign)) list -> seq_relation

val gen_mem :
  (seq_relation * (op_mem_assign * qubit_mem_assign)) list -> membranes ->
  seq_relation -> op_mem_assign * qubit_mem_assign

val fit : distributed_prog -> fitness_value

val order_by_seq : seq_relation -> op_list -> op_list

val update_loc_for :
  current_qubit_loc -> var0 list -> membrane -> current_qubit_loc

val qubits_to_move : current_qubit_loc -> membrane -> var0 list -> var0 list

val gen_prog_core :
  op_mem_assign -> exp list -> current_qubit_loc -> config -> int ->
  (config * int) * current_qubit_loc

val gen_prog :
  seq_relation -> qubit_mem_assign -> op_mem_assign -> op_list ->
  distributed_prog

type candidate = seq_relation * (op_mem_assign * qubit_mem_assign)

val auto_disq_search :
  op_list -> membranes -> candidate list -> distributed_prog -> fitness_value
  -> int -> distributed_prog

val iNF_SCORE : fitness_value

val fuel_from_ops : op_list -> int

val auto_disq : op_list -> membranes -> distributed_prog

val compute_scc : exp list -> exp list list

val order_ops_in_scc : exp list -> exp list

val parallelize_in_membrane : seq_relation -> exp list -> exp list list

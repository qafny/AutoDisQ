
val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val pow : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val modulo : int -> int -> int
 end

val nth_error : 'a1 list -> int -> 'a1 option

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

type membrane_id = var

type op_list = exp list

type rank = int

type seq_relation = exp -> rank

type op_mem_assign = exp -> membrane_id

type qubit_mem_assign = var -> membrane_id

type fitness_value = int

type distributed_prog = config

type candidate = seq_relation * (op_mem_assign * qubit_mem_assign)

val var_eqb : var -> var -> bool

val vars_of_exp : exp -> var list

val gen_os : op_list -> op_list

val default_mid : membrane_id

val first_mid : config -> membrane_id

val mem_count : config -> int

val nth_mid_default : config -> int -> membrane_id

val exp_tag : exp -> int

val sum_vars : var list -> int

val exp_hash : exp -> int

val gen_seq : candidate list -> seq_relation

val gen_mem :
  candidate list -> config -> seq_relation -> op_mem_assign * qubit_mem_assign

val op_to_process : exp -> process

val place_operation : config -> membrane_id -> exp -> config

val insert_by_seq : seq_relation -> exp -> exp list -> exp list

val sort_by_seq : seq_relation -> exp list -> exp list

val order_by_seq : seq_relation -> op_list -> op_list

val empty_config : config

val gen_prog_core : op_mem_assign -> exp list -> config -> config

val gen_prog : seq_relation -> op_mem_assign -> op_list -> distributed_prog

val count_procs : process list -> int

val fit : distributed_prog -> fitness_value

val iNF_SCORE : fitness_value

val auto_disq_loop :
  int -> op_list -> config -> candidate list -> distributed_prog ->
  fitness_value -> distributed_prog

val auto_disq : int -> op_list -> config -> distributed_prog

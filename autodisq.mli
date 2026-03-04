
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val pow : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

val nth_error : 'a1 list -> int -> 'a1 option

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val firstn : int -> 'a1 list -> 'a1 list

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

type hb_relation = exp -> exp -> bool

type op_list = exp list

type rank = int

type seq_relation = exp -> rank

type op_mem_assign = exp -> membrane_id

type qubit_mem_assign = var -> membrane_id

type fitness_value = int

type distributed_prog = config

val var_eqb : var -> var -> bool

val mem_var : var -> var list -> bool

val uniq : var list -> var list

val intersect : var list -> var list -> var list

val vars_of_exp : exp -> var list

val share_qubit : exp -> exp -> bool

val internal_nat_beq : int -> int -> bool

val internal_nat_beq0 : int -> int -> bool

val internal_aexp_beq : aexp -> aexp -> bool

val exp_beq : exp -> exp -> bool

val exp_eqb : exp -> exp -> bool

val gen_os : op_list -> op_list

val index_of_exp : exp -> exp list -> int

val gen_hp : op_list -> hb_relation

val nth_default : 'a1 -> 'a1 list -> int -> 'a1

val insert_all : exp -> exp list -> exp list list

val permutations : exp list -> exp list list

val respects_hp : hb_relation -> exp list -> bool

val topo_orders_k : hb_relation -> exp list -> int -> exp list list

val seq_from_order : exp list -> seq_relation

val default_mid : membrane_id

val first_mid : config -> membrane_id

val mem_count : config -> int

val nth_mid_default : config -> int -> membrane_id

val exp_tag : exp -> int

val sum_vars : var list -> int

val exp_hash : exp -> int

val subset_vars : var list -> var list -> bool

val overlap_big : var list -> var list -> bool

val insert_by_seq : seq_relation -> exp -> exp list -> exp list

val sort_by_seq : seq_relation -> exp list -> exp list

val order_by_seq : seq_relation -> op_list -> op_list

val build_moO :
  config -> int -> exp list -> (exp * membrane_id) option ->
  (int * membrane_id) list -> (int * membrane_id) list

val lookup_mid : int -> (int * membrane_id) list -> membrane_id

val moO_of_tbl : (int * membrane_id) list -> op_mem_assign

val first_use_mid : exp list -> op_mem_assign -> var -> membrane_id

val gen_mem_seed :
  int -> config -> seq_relation -> op_list -> op_mem_assign * qubit_mem_assign

val mk_reloc : membrane_id -> membrane_id -> exp

val op_to_process : exp -> process

val place_operation : config -> membrane_id -> exp -> config

type qloc_tbl = (var * membrane_id) list

val qloc_lookup : var -> qloc_tbl -> membrane_id -> membrane_id

val qloc_update : var -> membrane_id -> qloc_tbl -> qloc_tbl

val init_qloc : var list -> qubit_mem_assign -> qloc_tbl

val all_qubits : exp list -> var list

val ensure_qubits :
  var list -> membrane_id -> qloc_tbl -> config -> qloc_tbl * config

val gen_prog_core :
  op_mem_assign -> qubit_mem_assign -> exp list -> qloc_tbl -> config ->
  config

val gen_prog :
  seq_relation -> op_mem_assign -> qubit_mem_assign -> op_list ->
  distributed_prog

val is_reloc : exp -> bool

val reloc_pair : exp -> membrane_id * membrane_id

val mem_pair :
  (membrane_id * membrane_id) -> (membrane_id * membrane_id) list -> bool

val uniq_pairs :
  (membrane_id * membrane_id) list -> (membrane_id * membrane_id) list

val extract_exps_from_proc : process -> exp list

val extract_all_exps : config -> exp list

val count_relocs : exp list -> int

val collect_pairs : exp list -> (membrane_id * membrane_id) list

val fit : distributed_prog -> fitness_value

val iNF_SCORE : fitness_value

type case = int * int

val case_eqb : case -> case -> bool

val mem_case : case -> case list -> bool

val range_from : int -> int -> int list

val mk_cases : int -> int -> case list

val filter_fresh : case list -> case list -> case list

val are_still_cases : case list -> case list -> bool

val pick_case : case list -> case list -> case option

val gen_mem_paper :
  config -> seq_relation -> op_list -> case ->
  op_mem_assign * qubit_mem_assign

val auto_disq_loop_paper :
  int -> hb_relation -> op_list -> config -> case list -> case list ->
  distributed_prog -> fitness_value -> int -> distributed_prog

val auto_disq_alg1_paper : int -> int -> op_list -> config -> distributed_prog

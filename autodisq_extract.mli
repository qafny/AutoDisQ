
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val add : int -> int -> int

val tail_add : int -> int -> int

val tail_addmul : int -> int -> int -> int

val tail_mul : int -> int -> int

val of_uint_acc : uint -> int -> int

val of_uint : uint -> int

val of_hex_uint_acc : uint0 -> int -> int

val of_hex_uint : uint0 -> int

val of_num_uint : uint1 -> int

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module Nat :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int
 end

module N :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val ltb : int -> int -> bool

  val to_nat : int -> int

  val of_nat : int -> int
 end

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list

type var = int

type range = var * (int * int)

type locus = range list

type aexp =
| BA of var
| Num of int
| APlus of aexp * aexp
| AMult of aexp * aexp
| AModMult of aexp * aexp * aexp

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
| CNew of range
| CAppU of locus * exp
| CMeas of var * locus
| Send of var * var * int
| Recv of var * var * int

type process =
| PNil
| AP of cexp * process
| PIf of cbexp * process * process

type memb =
| Memb of var * process

type config = memb list

module Sort :
 functor (X:TotalLeBool') ->
 sig
  val merge : X.t list -> X.t list -> X.t list

  val merge_list_to_stack :
    X.t list option list -> X.t list -> X.t list option list

  val merge_stack : X.t list option list -> X.t list

  val iter_merge : X.t list option list -> X.t list -> X.t list

  val sort : X.t list -> X.t list

  val flatten_stack : X.t list option list -> X.t list
 end

type 'a set = 'a list

val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool

val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set

type membrane_id = var

type myOp =
| OpAP of cexp
| OpIf of cbexp * cexp list * cexp list

type op_list = myOp list

type hb_relation = int -> int -> bool

type myOpAux =
| OpNum of int
| OpExp of cexp

type fitness_value = int

type scored_cand = (int * membrane_id) * ((int * int) list * (int * int) list)

type nposi = int * int

module RangeOrder :
 sig
  type t = range

  val leb : range -> range -> bool
 end

module SortRange :
 sig
  val merge : range list -> range list -> range list

  val merge_list_to_stack :
    range list option list -> range list -> range list option list

  val merge_stack : range list option list -> range list

  val iter_merge : range list option list -> range list -> range list

  val sort : range list -> range list

  val flatten_stack : range list option list -> range list
 end

val nat_range_inter : (int * int) -> (int * int) -> bool

val same_name : range -> range -> bool

val intersect' : range -> locus -> bool

val intersect : locus -> locus -> bool

val get_locus : cexp -> locus

val get_loci : cexp list -> locus

val get_vars_cexp : cexp -> var list

val get_vars_aexp : aexp -> var list

val get_vars_bexp : cbexp -> var list

val is_inter : cexp -> cexp -> bool

val inter_vars : var list -> var list -> bool

val gen_hb_single :
  (int * myOp) -> (int * myOp) -> (int -> int -> bool) -> int -> int -> bool

val opListOrder' : op_list -> int -> (int * myOp) list

val opListOrder : op_list -> (int * myOp) list

val gen_hb' : (int * myOp) -> (int * myOp) list -> hb_relation -> hb_relation

val gen_hb_a : (int * myOp) list -> hb_relation -> hb_relation

val trans_closure : int -> int -> hb_relation -> hb_relation

val gen_hb_trans : int -> int -> hb_relation -> hb_relation

val gen_hb : (int * myOp) list -> hb_relation

val sim_exp : exp -> exp -> bool

val sim_cexp : cexp -> cexp -> bool

val insert_op :
  (int * myOp) -> (int * myOp) list list -> (int * myOp) list list

val partition_op' :
  (int * myOp) list -> (int * myOp) list list -> (int * myOp) list list

val partition_op : (int * myOp) list -> (int * myOp) list list

val nposi_eq : nposi -> nposi -> bool

val permutations_one :
  (myOpAux * nposi list) list -> (myOpAux * nposi list) list list

val car_concat' :
  (myOpAux * nposi list) list -> (myOpAux * nposi list) list list ->
  (myOpAux * nposi list) list list

val car_concat :
  (myOpAux * nposi list) list list -> (myOpAux * nposi list) list list ->
  (myOpAux * nposi list) list list

val get_first : (int * myOp) list list -> (int * myOp) list

val in_list_a : (int * myOp) -> (int * myOp) list -> bool

val remove_first :
  (int * myOp) list list -> (int * myOp) list -> (int * myOp) list list

val grab_related' :
  (int * myOp) -> (int * myOp) list -> hb_relation -> (int * myOp) list ->
  (int * myOp) list

val up_qubits : var -> int -> int -> nposi list -> nposi list

val cutToQubits' : range list -> nposi list

val cutToQubits : range list -> nposi list

val get_locus_in_op : (int * myOp) list -> range list

val get_nlocus : (int * myOp) list -> (myOpAux * nposi list) list

val assign_each :
  int -> (int * myOp) list list -> hb_relation -> (myOpAux * nposi list) list
  list -> (myOpAux * nposi list) list list

val gen_seq :
  (int * myOp) list -> hb_relation -> (myOpAux * nposi list)
  list * (myOpAux * nposi list) list list

val count_a :
  (myOpAux * nposi list) list -> membrane_id list -> ((myOpAux * nposi
  list) * membrane_id) list -> ((myOpAux * nposi list) * membrane_id)
  list * (myOpAux * nposi list) list

val gen_mem_new' :
  int -> (myOpAux * nposi list) list -> membrane_id list -> ((myOpAux * nposi
  list) * membrane_id) list -> ((myOpAux * nposi list) * membrane_id) list

val gen_mem_new :
  (myOpAux * nposi list) list -> membrane_id list -> ((myOpAux * nposi
  list) * membrane_id) list

val insert_posis :
  (membrane_id * nposi list) list -> membrane_id -> nposi list ->
  (membrane_id * nposi list) list

val turn_new :
  ((myOpAux * nposi list) * membrane_id) list -> (membrane_id * nposi list)
  list -> (membrane_id * nposi list) list

val posi_set_in : nposi -> nposi list -> bool

val set_inter0 :
  nposi list -> nposi list -> (nposi list * nposi list) -> nposi list * nposi
  list

val dec_mem : (nposi list * membrane_id) list -> nposi -> membrane_id option

val search_mem :
  (membrane_id * nposi list) list -> nposi list -> (membrane_id * (nposi
  list * nposi list)) list -> (membrane_id * (nposi list * nposi list)) list

val all_no_mem : (membrane_id * (nposi list * nposi list)) list -> bool

val is_one_mem : (membrane_id * (nposi list * nposi list)) list -> bool

val gen_comm' :
  membrane_id -> membrane_id -> nposi list -> var -> ((myOpAux * nposi
  list) * membrane_id) list -> ((myOpAux * nposi list) * membrane_id) list

val gen_comm :
  membrane_id -> (membrane_id * (nposi list * nposi list)) list -> var ->
  ((myOpAux * nposi list) * membrane_id) list -> ((myOpAux * nposi
  list) * membrane_id) list -> var * (((myOpAux * nposi list) * membrane_id)
  list * ((myOpAux * nposi list) * membrane_id) list)

val gen_comm_insert :
  membrane_id -> (membrane_id * (nposi list * nposi list)) list -> var ->
  ((myOpAux * nposi list) * membrane_id) list -> ((myOpAux * nposi
  list) * membrane_id) -> var * ((myOpAux * nposi list) * membrane_id) list

val gen_comm_b :
  membrane_id -> (membrane_id * (nposi list * nposi list)) list -> var ->
  ((myOpAux * nposi list) * membrane_id) list -> var * ((myOpAux * nposi
  list) * membrane_id) list

val collect_all_posi :
  (membrane_id * (nposi list * nposi list)) list -> nposi list -> nposi list

val push_to_mem_i :
  membrane_id -> membrane_id -> nposi list -> (membrane_id * (nposi
  list * nposi list)) list -> (membrane_id * nposi list) list ->
  (membrane_id * nposi list) list

val post_dec :
  membrane_id -> (membrane_id * nposi list) list -> (nposi
  list * membrane_id) list -> int -> nposi list -> var ->
  (membrane_id * (nposi list * nposi list)) list -> (membrane_id * (nposi
  list * nposi list)) list -> ((myOpAux * nposi list) * membrane_id) list ->
  var * (((myOpAux * nposi list) * membrane_id) list * (membrane_id * nposi
  list) list) list

val assoc_opt_mem :
  membrane_id -> (membrane_id * nposi list) list -> nposi list option

val mem_qubit_load : (membrane_id * nposi list) list -> membrane_id -> int

val membrane_capacity : int

val op_capacity : int

val mem_has_capacity :
  (membrane_id * nposi list) list -> membrane_id -> nposi list -> bool

val op_load_in_partial :
  ((myOpAux * nposi list) * membrane_id) list -> membrane_id -> int

val overlap_size : nposi list -> nposi list -> int

val import_cost : nposi list -> nposi list -> int

val score_mem_for_op :
  ((myOpAux * nposi list) * membrane_id) list -> nposi list -> membrane_id ->
  nposi list -> int

val over_op_capacity :
  ((myOpAux * nposi list) * membrane_id) list -> membrane_id -> bool

val insert_scored_candidate :
  scored_cand -> scored_cand list -> scored_cand list

val take_scored : int -> scored_cand list -> scored_cand list

val scored_candidates :
  (membrane_id * nposi list) list -> ((myOpAux * nposi list) * membrane_id)
  list -> nposi list -> (membrane_id * (nposi list * nposi list)) list ->
  scored_cand list

val scored_candidates_nocap :
  ((myOpAux * nposi list) * membrane_id) list -> nposi list ->
  (membrane_id * (nposi list * nposi list)) list -> scored_cand list

val build_choices :
  scored_cand list -> (membrane_id * (nposi list * nposi list)) list ->
  (membrane_id * nposi list) list -> (nposi list * membrane_id) list -> int
  -> nposi list -> ((myOpAux * nposi list) * membrane_id) list -> var ->
  (((myOpAux * nposi list) * membrane_id) list * (membrane_id * nposi list)
  list) list -> (((myOpAux * nposi list) * membrane_id)
  list * (membrane_id * nposi list) list) list

val assign_mem_s :
  (membrane_id * nposi list) list -> (nposi list * membrane_id) list ->
  (int * nposi list) -> ((myOpAux * nposi list) * membrane_id) list -> var ->
  var * (((myOpAux * nposi list) * membrane_id) list * (membrane_id * nposi
  list) list) list

val channel : var

val assign_mem' :
  (nposi list * membrane_id) list -> (myOpAux * nposi list) list ->
  (var * (((myOpAux * nposi list) * membrane_id) list * (membrane_id * nposi
  list) list) list) -> var * (((myOpAux * nposi list) * membrane_id)
  list * (membrane_id * nposi list) list) list

val assign_mem_more :
  (membrane_id * nposi list) list -> (nposi list * membrane_id) list ->
  (myOpAux * nposi list) list list -> ((myOpAux * nposi list) * membrane_id)
  list list -> ((myOpAux * nposi list) * membrane_id) list list

val find_empty_new' :
  (membrane_id * nposi list) list -> membrane_id -> membrane_id list ->
  membrane_id list

val find_empy_new :
  (membrane_id * nposi list) list -> membrane_id list -> membrane_id list ->
  membrane_id list

val assign_new_mem :
  (myOpAux * nposi list) list -> membrane_id list -> (nposi
  list * membrane_id) list

val gen_empty_mem : membrane_id list -> (membrane_id * nposi list) list

val take : int -> 'a1 list -> 'a1 list

val fallback_mid : ((myOpAux * nposi list) * membrane_id) list -> membrane_id

val gen_mem :
  (myOpAux * nposi list) list -> (myOpAux * nposi list) list list ->
  membrane_id list -> ((myOpAux * nposi list) * membrane_id) list list

val insert_mem_id :
  membrane_id -> (myOpAux * nposi list) -> (membrane_id * (myOpAux * nposi
  list) list) list -> (membrane_id * (myOpAux * nposi list) list) list

val distribute_op :
  ((myOpAux * nposi list) * membrane_id) list ->
  (membrane_id * (myOpAux * nposi list) list) list ->
  (membrane_id * (myOpAux * nposi list) list) list

val get_op : (int * myOp) list -> int -> myOp option

val turn_cexp_to_proc : cexp list -> process -> process

val turn_op_to_proc : myOp -> process -> process

val to_process :
  (myOpAux * nposi list) list -> (int * myOp) list -> process option

val to_prog :
  (int * (myOpAux * nposi list) list) list -> (int * myOp) list -> memb list

val has_if_ops : (int * myOp) list -> bool

val owner_of_pos : (nposi * membrane_id) list -> nposi -> membrane_id option

val set_owner :
  (nposi * membrane_id) list -> nposi -> membrane_id -> (nposi * membrane_id)
  list

val set_owner_many :
  (nposi * membrane_id) list -> nposi list -> membrane_id ->
  (nposi * membrane_id) list

val append_cexp_to_mem :
  membrane_id -> cexp -> (membrane_id * cexp list) list ->
  (membrane_id * cexp list) list

val add_initial_owners_from_solution :
  ((myOpAux * nposi list) * membrane_id) list -> (int * myOp) list ->
  (nposi * membrane_id) list -> (nposi * membrane_id) list

val ensure_local_qubits_aux :
  membrane_id -> nposi list -> (nposi * membrane_id) list ->
  (membrane_id * cexp list) list -> var -> (var * (nposi * membrane_id)
  list) * (membrane_id * cexp list) list

val ensure_local_qubits :
  membrane_id -> nposi list -> (nposi * membrane_id) list ->
  (membrane_id * cexp list) list -> var -> (var * (nposi * membrane_id)
  list) * (membrane_id * cexp list) list

val to_prog_from_cexps : (membrane_id * cexp list) list -> config

val lower_solution_distributed_go :
  ((myOpAux * nposi list) * membrane_id) list -> (int * myOp) list ->
  (nposi * membrane_id) list -> (membrane_id * cexp list) list -> var ->
  config

val lower_solution_distributed :
  ((myOpAux * nposi list) * membrane_id) list -> (int * myOp) list -> config

val gen_prog :
  ((myOpAux * nposi list) * membrane_id) list list -> (int * myOp) list ->
  config list

val count_send_in_process : process -> int

val count_send_in_memb : memb -> int

val count_comm_ops : config -> int

val process_size : process -> int

val memb_load : memb -> int

val max_load : config -> int

val alpha : int

val fit : config -> fitness_value

val best_prog_aux : config -> int -> config list -> config

val best_prog : config list -> config option

val autodisq_all : op_list -> membrane_id list -> config list

val autodisq_best : op_list -> membrane_id list -> config option

val auto_disq_loop : config option -> config list -> config option

val autodisq_first : (int * myOp) list -> membrane_id list -> config option

val autodisq_best_1 : op_list -> membrane_id list -> config option

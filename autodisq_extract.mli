
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

type reflect =
| ReflectT
| ReflectF

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module Nat :
 sig
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

  val of_succ_nat : int -> int
 end

module N :
 sig
  val add : int -> int -> int

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val ltb : int -> int -> bool

  val of_nat : int -> int
 end

val rev : 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list

val seq : int -> int -> int list

type var = int

type posi = var * int

val posi_eq : posi -> posi -> bool

val posi_eq_reflect : posi -> posi -> reflect

val posi_eq_dec : posi -> posi -> bool

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

val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val aexp_eqb : aexp -> aexp -> bool

val cbexp_eqb : cbexp -> cbexp -> bool

val range_eqb : range -> range -> bool

val locus_eqb : locus -> locus -> bool

val exp_eqb : exp -> exp -> bool

type fitness_value = int

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

val nat_range_sub : (int * int) -> (int * int) -> bool

val range_intersect : range -> range -> bool

val same_name : range -> range -> bool

val intersect' : range -> locus -> bool

val intersect : locus -> locus -> bool

val get_locus : cexp -> range list

val get_loci : cexp list -> range list

val get_vars_cexp : cexp -> var list

val get_vars_aexp : aexp -> var list

val get_vars_bexp : cbexp -> var list

val is_inter : cexp -> cexp -> bool

val inter_vars : var list -> var list -> bool

val gen_hb_single :
  (int * myOp) -> (int * myOp) -> (int -> int -> bool) -> int -> int -> bool

val gen_next :
  int -> (int * myOp) -> (int * myOp) -> (int -> int -> bool) -> int -> int
  -> bool

val opListOrder' : op_list -> int -> (int * myOp) list

val opListOrder : op_list -> (int * myOp) list

val empty_hp : int -> int -> bool

val gen_hb' : int -> (int * myOp) -> (int * myOp) list -> int -> int -> bool

val gen_hb_a :
  int -> (int * myOp) list -> (int -> int -> bool) -> int -> int -> bool

val gen_hb : (int * myOp) list -> int -> int -> bool

val sim_exp : exp -> exp -> bool

val sim_cexp : cexp -> cexp -> bool

val sim_myop : myOp -> myOp -> bool

val insert_op :
  (int * myOp) -> (int * myOp) list list -> (int * myOp) list list

val partition_op' :
  (int * myOp) list -> (int * myOp) list list -> (int * myOp) list list

val partition_op : (int * myOp) list -> (int * myOp) list list

val insert_all :
  (myOpAux * posi list) -> (myOpAux * posi list) list -> (myOpAux * posi
  list) list list

val permutations :
  (myOpAux * posi list) list -> (myOpAux * posi list) list list

val car_concat' :
  (myOpAux * posi list) list -> (myOpAux * posi list) list list ->
  (myOpAux * posi list) list list

val car_concat :
  (myOpAux * posi list) list list -> (myOpAux * posi list) list list ->
  (myOpAux * posi list) list list

val get_first :
  (int * myOp) list list -> ((int * myOp) list * (int * myOp) list list) ->
  (int * myOp) list * (int * myOp) list list

val grab_related' :
  (int * myOp) -> (int * myOp) list -> hb_relation -> (int * myOp) list ->
  (int * myOp) list

val grab_related : (int * myOp) list -> hb_relation -> (int * myOp) list

val grab_nums : (int * myOp) list -> int list

val in_list' : int -> int list -> bool

val in_list : myOpAux -> int list -> bool

val up_qubits : var -> int -> int -> (var * int) list -> (var * int) list

val cutToQubits' : range list -> (var * int) list

val cutToQubits : range list -> (var * int) list

val get_locus_in_op : (int * myOp) list -> range list

val get_nlocus : (int * myOp) list -> (myOpAux * (var * int) list) list

val insert_back :
  (int * myOp) list -> (int * myOp) list list -> int list -> (int * myOp)
  list list

val assign_each :
  int -> (int * myOp) list list -> hb_relation -> (myOpAux * posi list) list
  list -> (myOpAux * posi list) list list

val gen_seq :
  (int * myOp) list -> hb_relation -> (myOpAux * (var * int) list)
  list * (myOpAux * posi list) list list

val count_a :
  int -> (myOpAux * posi list) list -> membrane_id -> ((myOpAux * posi
  list) * membrane_id) list -> ((myOpAux * posi list) * membrane_id)
  list * (myOpAux * posi list) list

val gen_mem_new' :
  int -> (myOpAux * posi list) list -> membrane_id list -> int ->
  ((myOpAux * posi list) * membrane_id) list -> ((myOpAux * posi
  list) * membrane_id) list

val gen_mem_new :
  (myOpAux * posi list) list -> membrane_id list -> ((myOpAux * posi
  list) * membrane_id) list

val sub_locus' : locus -> locus -> bool

val sub_locus : range list -> range list -> bool

val split_nat_range : (int * int) -> (int * int) -> (int * int) list

val assemble_range : (int * int) list -> var -> (var * (int * int)) list

val sublist_posi : posi list -> posi list -> bool

val insert_mem :
  ((posi * membrane_id) * int list) -> ((posi list * membrane_id) * int list)
  list -> ((posi list * membrane_id) * int list) list

val set_inter0 : posi list -> posi list -> posi list

val sub_locus_i : posi -> locus -> bool

val isSend : cexp -> bool

val no_send_check :
  membrane_id -> ((myOpAux * posi list) * membrane_id) list -> bool

val search_hb :
  posi list -> int -> hb_relation -> ((myOpAux * posi list) * membrane_id)
  list -> ((myOpAux * posi list) * membrane_id) list -> (membrane_id * posi
  list) option

val search_mem :
  (membrane_id * (posi * bool) list) list -> posi list -> (membrane_id * posi
  list) list -> (membrane_id * posi list) list

val max_one :
  (membrane_id * posi list) list -> (membrane_id * posi list) -> membrane_id
  list -> membrane_id list

val search_good_mem :
  (membrane_id * (posi * bool) list) list -> posi list -> membrane_id list

val find_least_q' :
  (membrane_id * (posi * bool) list) list -> (membrane_id * (posi * bool)
  list) -> membrane_id * (posi * bool) list

val find_least_q :
  (membrane_id * (posi * bool) list) list -> (membrane_id * (posi * bool)
  list) option

val subtract_aux :
  posi -> (posi * bool) list -> (posi * bool) list -> (posi * bool) list

val subtract_posi :
  posi list -> (posi * bool) list -> (posi * bool) list -> (posi * bool) list

val subtract_all :
  posi list -> (membrane_id * (posi * bool) list) list ->
  (membrane_id * (posi * bool) list) list -> (membrane_id * (posi * bool)
  list) list

val add_posi_true' :
  membrane_id -> (posi * bool) list -> (membrane_id * (posi * bool) list)
  list -> (membrane_id * (posi * bool) list) list

val add_true : posi list -> (posi * bool) list

val add_posi_true :
  membrane_id -> posi list -> (membrane_id * (posi * bool) list) list ->
  (membrane_id * (posi * bool) list) list

val turn_true_aux : posi list -> (posi * bool) list -> (posi * bool) list

val turn_true :
  int -> posi list -> (membrane_id * (posi * bool) list) list ->
  (membrane_id * (posi * bool) list) list

val find_all_in :
  posi list -> (membrane_id * (posi * bool) list) list ->
  (membrane_id * (posi * bool) list) option

val search_all_mem :
  membrane_id -> posi list -> (membrane_id * (posi * bool) list) list ->
  (membrane_id * posi list) list

val gen_comm' :
  membrane_id -> posi list -> var -> ((myOpAux * posi list) * membrane_id)
  list

val gen_comm :
  (membrane_id * posi list) list -> var -> ((myOpAux * posi
  list) * membrane_id) list -> var * ((myOpAux * posi list) * membrane_id)
  list

val assign_mem_s :
  (membrane_id * (posi * bool) list) list -> hb_relation -> (int * posi list)
  -> ((myOpAux * posi list) * membrane_id) list -> var ->
  var * (((myOpAux * posi list) * membrane_id)
  list * (membrane_id * (posi * bool) list) list) list

val channel : int

val assign_mem' :
  hb_relation -> (myOpAux * posi list) list -> (var * (((myOpAux * posi
  list) * membrane_id) list * (membrane_id * (posi * bool) list) list) list)
  -> var * (((myOpAux * posi list) * membrane_id)
  list * (membrane_id * (posi * bool) list) list) list

val assign_mem_more :
  (membrane_id * (posi * bool) list) list -> hb_relation -> (myOpAux * posi
  list) list list -> ((myOpAux * posi list) * membrane_id) list list ->
  ((myOpAux * posi list) * membrane_id) list list

val turn_new :
  ((myOpAux * posi list) * membrane_id) list -> (membrane_id * (posi * bool)
  list) list -> (membrane_id * (posi * bool) list) list

val gen_mem :
  (myOpAux * posi list) list -> (myOpAux * posi list) list list ->
  membrane_id list -> hb_relation -> ((myOpAux * posi list) * membrane_id)
  list list

val insert_mem_id :
  membrane_id -> (myOpAux * posi list) -> (int * (myOpAux * posi list) list)
  list -> (membrane_id * (myOpAux * posi list) list) list

val distribute_op :
  ((myOpAux * posi list) * membrane_id) list -> (int * (myOpAux * posi list)
  list) list -> (int * (myOpAux * posi list) list) list

val get_op : (int * myOp) list -> int -> myOp option

val turn_cexp_to_proc : cexp list -> process -> process

val turn_op_to_proc : myOp -> process -> process

val to_process :
  (myOpAux * posi list) list -> (int * myOp) list -> process option

val to_prog :
  (int * (myOpAux * posi list) list) list -> (int * myOp) list -> memb list

val gen_prog :
  ((myOpAux * posi list) * membrane_id) list list -> (int * myOp) list ->
  memb list list

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

val autodisq_best_1 : op_list -> membrane_id list -> config option

val one_qubit_range : var -> range

val l : locus

val alloc_qubits_from : var list -> op_list

val cnot_from : var -> var list -> op_list

val meas_all_from : var list -> op_list

val ghz8_n : int

val ghz8_qs : var list

val ghz8_outs : var list

val gHZ8_prog : op_list

val ghz16_n : int

val ghz16_qs : var list

val ghz16_outs : var list

val gHZ16_prog : op_list

val apply_H_all_from : var list -> op_list

val controlled_x_chain_from : var list -> var list -> op_list

val shor8_qs : var list

val shor8_ctrls : var list

val shor8_tgts : var list

val shor8_outs : var list

val sHOR8_prog : op_list

val shor16_qs : var list

val shor16_ctrls : var list

val shor16_tgts : var list

val shor16_outs : var list

val sHOR16_prog : op_list

val qft8_n : int

val qft8_q0 : var

val qft8_qubits : var list

val qft8_outs : var list

val qFT8_prog : op_list

val qft16_n : int

val qft16_q0 : var

val qft16_qubits : var list

val qft16_outs : var list

val qFT16_prog : op_list

val qadd8_n : int

val qadd8_q0 : var

val qadd8_qubits : var list

val qadd8_outs : var list

val qadd8_x : var

val qFTAdder8_prog : op_list

val qadd16_n : int

val qadd16_q0 : var

val qadd16_qubits : var list

val qadd16_outs : var list

val qadd16_x : var

val qFTAdder16_prog : op_list

val qft32_n : int

val qft32_q0 : var

val qft32_qubits : var list

val qft32_outs : var list

val qFT32_prog : op_list

val qadd32_n : int

val qadd32_q0 : var

val qadd32_qubits : var list

val qadd32_outs : var list

val qadd32_x : var

val qFTAdder32_prog : op_list

val ghz32_n : int

val ghz32_qs : var list

val ghz32_outs : var list

val gHZ32_prog : op_list

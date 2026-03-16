
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
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val mul : int -> int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int
 end

module N :
 sig
  val zero : int

  val one : int

  val succ_double : int -> int

  val double : int -> int

  val succ : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val pos_div_eucl : int -> int -> int * int

  val div_eucl : int -> int -> int * int

  val div : int -> int -> int

  val to_nat : int -> int

  val of_nat : int -> int
 end

val rev : 'a1 list -> 'a1 list

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

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

val get_locus : cexp -> range list

val get_loci : cexp list -> range list

val get_vars_cexp : cexp -> var list

val get_vars_aexp : aexp -> var list

val get_vars_bexp : cbexp -> var list

val is_inter : cexp -> cexp -> bool

val inter_vars : var list -> var list -> bool

val gen_hb_single :
  (int * myOp) -> (int * myOp) -> (int -> int -> bool) -> int -> int -> bool

val opListOrder' : op_list -> int -> (int * myOp) list

val opListOrder : op_list -> (int * myOp) list

val gen_hb' :
  (int * myOp) -> (int * myOp) list -> (int -> int -> bool) -> int -> int ->
  bool

val gen_hb_a : (int * myOp) list -> (int -> int -> bool) -> int -> int -> bool

val trans_closure : int -> int -> (int -> int -> bool) -> int -> int -> bool

val gen_hb_trans : int -> int -> (int -> int -> bool) -> int -> int -> bool

val gen_hb : (int * myOp) list -> int -> int -> bool

val sim_exp : exp -> exp -> bool

val sim_cexp : cexp -> cexp -> bool

val insert_op :
  (int * myOp) -> (int * myOp) list list -> (int * myOp) list list

val partition_op' :
  (int * myOp) list -> (int * myOp) list list -> (int * myOp) list list

val partition_op : (int * myOp) list -> (int * myOp) list list

type nposi = int * int

val nposi_eq : nposi -> nposi -> bool

val insert_all :
  (myOpAux * nposi list) -> (myOpAux * nposi list) list -> (myOpAux * nposi
  list) list list

val permutations :
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

val up_qubits : var -> int -> int -> (int * int) list -> (int * int) list

val cutToQubits' : range list -> (int * int) list

val cutToQubits : range list -> (int * int) list

val get_locus_in_op : (int * myOp) list -> range list

val get_nlocus : (int * myOp) list -> (myOpAux * (int * int) list) list

val assign_each :
  int -> (int * myOp) list list -> hb_relation -> (myOpAux * nposi list) list
  list -> (myOpAux * nposi list) list list

val gen_seq :
  (int * myOp) list -> hb_relation -> (myOpAux * (int * int) list)
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

val get_one :
  (membrane_id * (nposi list * nposi list)) list -> membrane_id option

val grab_good :
  (membrane_id * (nposi list * nposi list)) list -> (membrane_id * (nposi
  list * nposi list)) list -> (membrane_id * (nposi list * nposi list)) list

val nlength : 'a1 list -> int

val max_one :
  (membrane_id * (nposi list * nposi list)) list -> int ->
  (membrane_id * (nposi list * nposi list)) -> (membrane_id * (nposi
  list * nposi list)) list -> (membrane_id * (nposi list * nposi
  list)) * (membrane_id * (nposi list * nposi list)) list

val max_mem_id :
  (membrane_id * (nposi list * nposi list)) list -> int -> (nposi
  list * nposi list) -> (int * (nposi list * nposi list)) list ->
  (int * (nposi list * nposi list)) * (int * (nposi list * nposi list)) list

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
  int -> int -> nposi list -> (membrane_id * (nposi list * nposi list)) list
  -> (int * nposi list) list -> (int * nposi list) list

val post_dec :
  membrane_id -> (membrane_id * nposi list) list -> (nposi
  list * membrane_id) list -> int -> nposi list -> var ->
  (membrane_id * (nposi list * nposi list)) list -> (membrane_id * (nposi
  list * nposi list)) list -> ((myOpAux * nposi list) * membrane_id) list ->
  var * (((myOpAux * nposi list) * membrane_id) list * (membrane_id * nposi
  list) list) list

val assign_mem_s :
  (membrane_id * nposi list) list -> (nposi list * membrane_id) list ->
  (int * nposi list) -> ((myOpAux * nposi list) * membrane_id) list -> var ->
  var * (((myOpAux * nposi list) * membrane_id) list * (membrane_id * nposi
  list) list) list

val channel : int

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

val gen_mem :
  (myOpAux * nposi list) list -> (myOpAux * nposi list) list list ->
  membrane_id list -> ((myOpAux * nposi list) * membrane_id) list list

val insert_mem_id :
  membrane_id -> (myOpAux * nposi list) -> (int * (myOpAux * nposi list)
  list) list -> (membrane_id * (myOpAux * nposi list) list) list

val distribute_op :
  ((myOpAux * nposi list) * membrane_id) list -> (int * (myOpAux * nposi
  list) list) list -> (int * (myOpAux * nposi list) list) list

val get_op : (int * myOp) list -> int -> myOp option

val turn_cexp_to_proc : cexp list -> process -> process

val turn_op_to_proc : myOp -> process -> process

val to_process :
  (myOpAux * nposi list) list -> (int * myOp) list -> process option

val to_prog :
  (int * (myOpAux * nposi list) list) list -> (int * myOp) list -> memb list

val gen_prog :
  ((myOpAux * nposi list) * membrane_id) list list -> (int * myOp) list ->
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

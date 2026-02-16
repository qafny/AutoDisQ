
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

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

module Nat :
 sig
  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val max : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int
 end

val nth_error : 'a1 list -> int -> 'a1 option

val concat : 'a1 list list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

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

type myOp =
| OpAP of cexp
| OpDP of cdexp
| OpIf of cbexp * process * process

type op_list = myOp list

type hb_relation = myOp -> myOp -> bool

type rank = int

type seq_relation = myOp -> rank

type op_mem_assign = myOp -> membrane_id

val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val aexp_eqb : aexp -> aexp -> bool

val cbexp_eqb : cbexp -> cbexp -> bool

val bound_eqb : bound -> bound -> bool

val range_eqb : range -> range -> bool

val locus_eqb : locus -> locus -> bool

val exp_eqb : exp -> exp -> bool

val cexp_eqb : cexp -> cexp -> bool

val cdexp_eqb : cdexp -> cdexp -> bool

val process_eqb : process -> process -> bool

val myOp_eqb : myOp -> myOp -> bool

type qubit_mem_assign = var -> membrane_id

type fitness_value = int

type distributed_prog = config

val var_eqb : var -> var -> bool

val mem_var : var -> var list -> bool

val uniq : var list -> var list

val intersect : var list -> var list -> var list

val vars_of_exp : exp -> var list

val gen_os : op_list -> op_list

val vars_of_aexp : aexp -> var list

val vars_of_cbexp : cbexp -> var list

val vars_of_myOp : myOp -> var list

val share_qubit_myOp : myOp -> myOp -> bool

val index_of_myOp : myOp -> myOp list -> int

val gen_hp : op_list -> hb_relation

val nth_default : 'a1 -> 'a1 list -> int -> 'a1

val insert_all : myOp -> myOp list -> myOp list list

val permutations : myOp list -> myOp list list

val respects_hp : hb_relation -> myOp list -> bool

val topo_orders_k : hb_relation -> myOp list -> int -> myOp list list

val seq_from_order : myOp list -> seq_relation

val gen_seq_many : int -> int -> hb_relation -> op_list -> seq_relation

val default_mid : membrane_id

val first_mid : config -> membrane_id

val mem_count : config -> int

val sum_vars : var list -> int

val myOp_tag : myOp -> int

val myOp_hash : myOp -> int

val subset_vars : var list -> var list -> bool

val overlap_big : var list -> var list -> bool

val insert_by_seq : seq_relation -> myOp -> myOp list -> myOp list

val sort_by_seq : seq_relation -> myOp list -> myOp list

val order_by_seq : seq_relation -> op_list -> op_list

val build_moO :
  config -> int -> myOp list -> (myOp * membrane_id) option ->
  (int * membrane_id) list -> (int * membrane_id) list

val lookup_mid : int -> (int * membrane_id) list -> membrane_id

val moO_of_tbl : (int * membrane_id) list -> op_mem_assign

val first_use_mid : myOp list -> op_mem_assign -> var -> membrane_id

val gen_mem_seed :
  int -> config -> seq_relation -> op_list -> op_mem_assign * qubit_mem_assign

val mk_reloc : membrane_id -> membrane_id -> exp

val myOp_to_process : myOp -> process

val reloc_process : membrane_id -> membrane_id -> process

val place_operation : config -> membrane_id -> myOp -> config

val place_reloc :
  config -> membrane_id -> membrane_id -> membrane_id -> config

val count_comm_proc : process -> int

val count_comm_cfg : config -> int

val fit : distributed_prog -> fitness_value

val iNF_SCORE : fitness_value

type case = int * int

val case_eqb : case -> case -> bool

val mem_case : case -> case list -> bool

val range_from : int -> int -> int list

val mk_cases : int -> int -> case list

val filter_fresh : case list -> case list -> case list

type candidate = case * (seq_relation * (op_mem_assign * qubit_mem_assign))

val seen_cases : candidate list -> case list

val are_still_cases_cases : case list -> case list -> bool

val pick_case : case list -> case list -> case option

val gen_mem :
  config -> seq_relation -> op_list -> case ->
  op_mem_assign * qubit_mem_assign

type smap = (var * membrane_id) list

val locus_myOp : myOp -> var list

val diff_mem : (var -> membrane_id) -> var list -> membrane_id -> smap

val mem_up_smap :
  (var -> membrane_id) -> smap -> membrane_id -> var -> membrane_id

val insert_send_recv : config -> smap -> membrane_id -> int -> config * int

val gen_prog_loop_alg2 :
  myOp list -> (var -> membrane_id) -> (myOp -> membrane_id) -> config -> int
  -> config

val empty_config : config

val gen_prog_alg2 :
  myOp list -> (var -> membrane_id) -> (myOp -> membrane_id) -> config

val gen_prog_paper :
  seq_relation -> qubit_mem_assign -> op_mem_assign -> op_list ->
  distributed_prog

val auto_disq_loop :
  int -> hb_relation -> op_list -> config -> case list -> candidate list ->
  distributed_prog -> fitness_value -> int -> distributed_prog

val auto_disq_alg1_paper : int -> int -> op_list -> config -> distributed_prog

val mem_op : (myOp -> myOp -> bool) -> myOp -> myOp list -> bool

val uniq_ops : (myOp -> myOp -> bool) -> myOp list -> myOp list

val remove_ops : (myOp -> myOp -> bool) -> myOp list -> myOp list -> myOp list

val opt_hp : hb_relation -> seq_relation -> hb_relation

val succs : hb_relation -> myOp list -> myOp -> myOp list

val reachable_fuel :
  (myOp -> myOp -> bool) -> hb_relation -> myOp list -> int -> myOp list ->
  myOp -> myOp -> bool

val reachable :
  (myOp -> myOp -> bool) -> hb_relation -> myOp list -> myOp -> myOp -> bool

val scc_of :
  (myOp -> myOp -> bool) -> hb_relation -> myOp list -> myOp -> myOp list

val scc_partition_fuel :
  int -> (myOp -> myOp -> bool) -> hb_relation -> myOp list -> myOp list list

val scc_partition :
  (myOp -> myOp -> bool) -> hb_relation -> myOp list -> myOp list list

val gen_ops : seq_relation -> myOp list -> process list

val alg3_loop : seq_relation -> myOp list list -> process list -> process list

val auto_parallelize_alg3 :
  (myOp -> myOp -> bool) -> myOp list -> hb_relation -> seq_relation ->
  process list

val l : locus

val p1_q : var

val p1_x : var

val p_1 : op_list

val p_3_q0 : var

val p_3_q1 : var

val p_3_q2 : var

val p_3_x0 : var

val p_3_x1 : var

val p_3_x2 : var

val cX_01 : exp

val cX_02 : exp

val p_3 : op_list

val p_4_q : var

val p_4_n : int

val p_4_x : var

val p_4 : op_list

val p_5_q0 : var

val p_5_q1 : var

val p_5_x0 : var

val p_5_x1 : var

val theta_pi : int

val oRACLE_01 : exp

val p_5 : op_list

val p_6_qs : var

val p_6_qa : var

val p_6_qb : var

val p_6_m1 : var

val p_6_m2 : var

val cNOT_a_b : exp

val cNOT_s_a : exp

val zcorr_qb : exp

val xcorr_qb : exp

val proc_Xcorr : process

val proc_Zcorr : process

val p_6 : op_list

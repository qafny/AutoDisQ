
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val mul : int -> int -> int **)

let rec mul = ( * )

module Nat =
 struct
  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l0 -> (||) (f a) (existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

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

(** val var_eqb : var0 -> var0 -> bool **)

let var_eqb =
  failwith "AXIOM TO BE REALIZED"

(** val vars_of_exp : exp -> var0 list **)

let vars_of_exp =
  failwith "AXIOM TO BE REALIZED"

(** val place_operation : config -> membrane -> exp -> config **)

let place_operation =
  failwith "AXIOM TO BE REALIZED"

(** val insert_teleport_sends :
    config -> var0 list -> int -> membrane -> config * int **)

let insert_teleport_sends =
  failwith "AXIOM TO BE REALIZED"

(** val insert_teleport_receives :
    config -> var0 list -> int -> membrane -> (var0 -> membrane) ->
    (config * int) * (var0 -> membrane) **)

let insert_teleport_receives =
  failwith "AXIOM TO BE REALIZED"

(** val empty_config : config **)

let empty_config =
  failwith "AXIOM TO BE REALIZED"

type op_list = exp list

type op_mem_assign = exp -> membrane

type qubit_mem_assign = var0 -> membrane

type current_qubit_loc = var0 -> membrane

type rank = int

type seq_relation = exp -> rank

type fitness_value = int

type distributed_prog = config

(** val gen_seq :
    (seq_relation * (op_mem_assign * qubit_mem_assign)) list -> seq_relation **)

let gen_seq =
  failwith "AXIOM TO BE REALIZED"

(** val gen_mem :
    (seq_relation * (op_mem_assign * qubit_mem_assign)) list -> membranes ->
    seq_relation -> op_mem_assign * qubit_mem_assign **)

let gen_mem =
  failwith "AXIOM TO BE REALIZED"

(** val fit : distributed_prog -> fitness_value **)

let fit =
  failwith "AXIOM TO BE REALIZED"

(** val order_by_seq : seq_relation -> op_list -> op_list **)

let order_by_seq =
  failwith "AXIOM TO BE REALIZED"

(** val update_loc_for :
    current_qubit_loc -> var0 list -> membrane -> current_qubit_loc **)

let update_loc_for loc qs target q =
  if existsb (fun x -> var_eqb x q) qs then target else loc q

(** val qubits_to_move :
    current_qubit_loc -> membrane -> var0 list -> var0 list **)

let qubits_to_move loc target_mem qs =
  filter (fun q -> negb (var_eqb (loc q) target_mem)) qs

(** val gen_prog_core :
    op_mem_assign -> exp list -> current_qubit_loc -> config -> int ->
    (config * int) * current_qubit_loc **)

let rec gen_prog_core moO remaining current_loc acc_config fresh_counter =
  match remaining with
  | [] -> ((acc_config, fresh_counter), current_loc)
  | op :: rest ->
    let target_mem = moO op in
    let qs = vars_of_exp op in
    let to_move = qubits_to_move current_loc target_mem qs in
    let (p, loc1) =
      match to_move with
      | [] -> ((acc_config, fresh_counter), current_loc)
      | _ :: _ ->
        let (cfg_s, fresh_s) =
          insert_teleport_sends acc_config to_move fresh_counter target_mem
        in
        let (p, loc_sr) =
          insert_teleport_receives cfg_s to_move fresh_s target_mem
            current_loc
        in
        let loc_fixed = update_loc_for loc_sr to_move target_mem in
        (p, loc_fixed)
    in
    let (acc1, fresh1) = p in
    let acc2 = place_operation acc1 target_mem op in
    gen_prog_core moO rest loc1 acc2 fresh1

(** val gen_prog :
    seq_relation -> qubit_mem_assign -> op_mem_assign -> op_list ->
    distributed_prog **)

let gen_prog seq moQ_init moO ops =
  let ordered = order_by_seq seq ops in
  let (p, _) = gen_prog_core moO ordered moQ_init empty_config 0 in
  let (cfg, _) = p in cfg

type candidate = seq_relation * (op_mem_assign * qubit_mem_assign)

(** val auto_disq_search :
    op_list -> membranes -> candidate list -> distributed_prog ->
    fitness_value -> int -> distributed_prog **)

let rec auto_disq_search ops avail_mem seen best best_score fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> best)
    (fun fuel' ->
    let seq = gen_seq seen in
    let (moO, moQ) = gen_mem seen avail_mem seq in
    let prog = gen_prog seq moQ moO ops in
    let score = fit prog in
    if Nat.ltb score best_score
    then auto_disq_search ops avail_mem ((seq, (moO, moQ)) :: seen) prog
           score fuel'
    else auto_disq_search ops avail_mem ((seq, (moO, moQ)) :: seen) best
           best_score fuel')
    fuel

(** val iNF_SCORE : fitness_value **)

let iNF_SCORE =
  failwith "AXIOM TO BE REALIZED"

(** val fuel_from_ops : op_list -> int **)

let fuel_from_ops ops =
  mul (length ops) (length ops)

(** val auto_disq : op_list -> membranes -> distributed_prog **)

let auto_disq ops avail =
  let fuel = fuel_from_ops ops in
  auto_disq_search ops avail [] empty_config iNF_SCORE fuel

(** val compute_scc : exp list -> exp list list **)

let compute_scc =
  failwith "AXIOM TO BE REALIZED"

(** val order_ops_in_scc : exp list -> exp list **)

let order_ops_in_scc =
  failwith "AXIOM TO BE REALIZED"

(** val parallelize_in_membrane :
    seq_relation -> exp list -> exp list list **)

let parallelize_in_membrane _ ops_in_mem =
  let components = compute_scc ops_in_mem in map order_ops_in_scc components

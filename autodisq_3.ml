
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val mul : int -> int -> int **)

let rec mul = ( * )

module Nat =
 struct
 end

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

type var0 = int

type membrane = var0

type membranes = config

(** val var_eqb : var0 -> var0 -> bool **)

let var_eqb =
  (=)

(** val vars_of_exp : exp -> var0 list **)

let rec vars_of_exp = function
| SKIP (_, _) -> []
| X (x, _) -> x :: []
| CU (x, _, e1) -> x :: (vars_of_exp e1)
| RZ (_, x, _) -> x :: []
| RRZ (_, x, _) -> x :: []
| SR (_, x) -> x :: []
| SRR (_, x) -> x :: []
| QFT (x, _) -> x :: []
| RQFT (x, _) -> x :: []
| H (x, _) -> x :: []
| Addto (x, q) -> x :: (q :: [])
| Seq (e1, e2) -> app (vars_of_exp e1) (vars_of_exp e2)

type op_list = exp list

type op_mem_assign = exp -> membrane

type qubit_mem_assign = var0 -> membrane

type current_qubit_loc = var0 -> membrane

type rank = int

type seq_relation = exp -> rank

type fitness_value = int

type distributed_prog = config

(** val op_to_process : exp -> process **)

let op_to_process op =
  AP ((CAppU ([], op)), PNil)

(** val place_operation : config -> membrane -> exp -> config **)

let rec place_operation cfg m op =
  match cfg with
  | [] -> (Memb (m, ((op_to_process op) :: []))) :: []
  | m0 :: tl ->
    (match m0 with
     | Memb (l, ps) ->
       if (=) l m
       then (Memb (l, (app ps ((op_to_process op) :: [])))) :: tl
       else (Memb (l, ps)) :: (place_operation tl m op)
     | LockMemb (l, r, ps) ->
       (LockMemb (l, r, ps)) :: (place_operation tl m op))

(** val empty_config : config **)

let empty_config =
  []

type candidate = seq_relation * (op_mem_assign * qubit_mem_assign)

(** val qubits_to_move :
    current_qubit_loc -> membrane -> var0 list -> var0 list **)

let qubits_to_move loc target qs =
  filter (fun q -> negb (var_eqb (loc q) target)) qs

(** val gen_prog_core :
    op_mem_assign -> exp list -> current_qubit_loc -> config -> int ->
    (config * int) * current_qubit_loc **)

let rec gen_prog_core moO remaining current_loc acc fresh =
  match remaining with
  | [] -> ((acc, fresh), current_loc)
  | op :: tl ->
    let target = moO op in
    let qs = vars_of_exp op in
    let to_move = qubits_to_move current_loc target qs in
    let (p, loc1) =
      match to_move with
      | [] -> ((acc, fresh), current_loc)
      | _ :: _ ->
        let p = (acc, fresh) in
        (p, (fun q ->
        if existsb (fun x -> var_eqb x q) to_move
        then target
        else current_loc q))
    in
    let (acc1, fresh1) = p in
    gen_prog_core moO tl loc1 (place_operation acc1 target op) fresh1

(** val gen_prog :
    seq_relation -> qubit_mem_assign -> op_mem_assign -> op_list ->
    distributed_prog **)

let gen_prog _ moQ moO ops =
  let (p, _) = gen_prog_core moO ops moQ empty_config 0 in
  let (cfg, _) = p in cfg

(** val auto_disq_search :
    op_list -> membranes -> candidate list -> distributed_prog ->
    fitness_value -> int -> distributed_prog **)

let rec auto_disq_search ops avail seen best _ fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> best)
    (fun n ->
    let seq = fun _ -> 0 in
    let moO = fun _ -> 0 in
    let moQ = fun _ -> 0 in
    let prog =
      let (p, _) = gen_prog_core moO ops moQ empty_config 0 in
      let (cfg, _) = p in cfg
    in
    auto_disq_search ops avail ((seq, (moO, moQ)) :: seen) prog 0 n)
    fuel

(** val fuel_from_ops : op_list -> int **)

let fuel_from_ops ops =
  mul (length ops) (length ops)

(** val auto_disq : op_list -> membranes -> distributed_prog **)

let auto_disq ops avail =
  auto_disq_search ops avail [] empty_config 0 (fuel_from_ops ops)

(** val compute_scc : exp list -> exp list list **)

let compute_scc ops =
  ops :: []

(** val parallelize_in_membrane :
    seq_relation -> exp list -> exp list list **)

let parallelize_in_membrane _ =
  compute_scc

Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import SQIR.SQIR.
Require Import QuantumLib.VectorStates.
Require Import SQIR.UnitaryOps.
Require Import Coq.btauto.Btauto Coq.NArith.Nnat. 
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import DisQSyntax.
(*Require Import OQASM.*)
(**********************)
(** Unitary Programs **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope cexp_scope.
Delimit Scope cexp_scope with cexp.
Local Open Scope cexp_scope.
Local Open Scope nat_scope.
From Coq Require Import List Arith Bool.
Import ListNotations.



Parameter var   : Type.


(* Membrane identifier  *)
Definition membrane := var.
Definition membranes := list membrane.

(* Equality on membranes (vars) *)
Parameter var_eqb : var -> var -> bool.

(* "qubits used by an operation" *)
Parameter vars_of_exp : exp -> list var.

Parameter place_operation : config -> membrane -> exp -> config.

(* Insert teleport/channels for sending/receiving qubits  *)
Parameter insert_teleport_sends :
  config -> list var -> nat -> membrane -> config * nat.

Parameter insert_teleport_receives :
  config -> list var -> nat -> membrane ->
  (* current location map *)
  (var -> membrane) ->
  (* returns updated cfg, fresh, and updated location *)
  config * nat * (var -> membrane).

(* A reasonable empty configuration for starting accumulation *)
Parameter empty_config : config.

(* ========================================================================= *)
(*                  AutoDisQ helper types and aliases                        *)
(* ========================================================================= *)

Definition hb_relation : Type := exp -> exp -> Prop.
Definition op_list : Type := list exp.

(* Assignment : operation → membrane *)
Definition op_mem_assign := exp -> membrane.

(* Assignment : qubit variable → initial membrane *)
Definition qubit_mem_assign := var -> membrane.

(* Current location of each qubit variable during program generation *)
Definition current_qubit_loc := var -> membrane.

(* Rank-based sequencing (seq relation) *)
Definition rank := nat.
Definition seq_relation := exp -> rank.

(* Fitness value — smaller is better *)
Definition fitness_value := nat.

(* Abstract distributed program — a configuration *)
Definition distributed_prog := config.

(* ========================================================================= *)
(*                 Algorithm 1: Search-loop building blocks                  *)
(* ========================================================================= *)

Parameter gen_hp : op_list -> hb_relation.
Parameter gen_os : op_list -> op_list.

Parameter gen_seq :
  list (seq_relation * (op_mem_assign * qubit_mem_assign)) ->
  hb_relation ->
  seq_relation.

Parameter gen_mem :
  list (seq_relation * (op_mem_assign * qubit_mem_assign)) ->
  membranes ->
  seq_relation ->
  (op_mem_assign * qubit_mem_assign).

Parameter fit : distributed_prog -> fitness_value.

Parameter order_by_seq : seq_relation -> op_list -> op_list.

(* ========================================================================= *)
(*        Algorithm 2: gen_prog — build DisQ config from relations           *)
(* ========================================================================= *)

Definition update_loc_for (loc : current_qubit_loc) (qs : list var) (target : membrane)
  : current_qubit_loc :=
  fun q => if existsb (fun x => var_eqb x q) qs then target else loc q.

Definition qubits_to_move (loc : current_qubit_loc) (target_mem : membrane) (qs : list var)
  : list var :=
  filter (fun q => negb (var_eqb (loc q) target_mem)) qs.

Fixpoint gen_prog_core
  (moO : op_mem_assign)
  (remaining : list exp)
  (current_loc : current_qubit_loc)
  (acc_config : config)
  (fresh_counter : nat)
  : config * nat * current_qubit_loc :=
  match remaining with
  | [] =>
      (acc_config, fresh_counter, current_loc)

  | op :: rest =>
      let target_mem := moO op in
      let qs := vars_of_exp op in
      let to_move := qubits_to_move current_loc target_mem qs in

      let '(acc1, fresh1, loc1) :=
        match to_move with
        | [] => (acc_config, fresh_counter, current_loc)
        | _  =>
            let '(cfg_s, fresh_s) :=
              insert_teleport_sends acc_config to_move fresh_counter target_mem in
            let '(cfg_sr, fresh_sr, loc_sr) :=
              insert_teleport_receives cfg_s to_move fresh_s target_mem current_loc in

            let loc_fixed := update_loc_for loc_sr to_move target_mem in
            (cfg_sr, fresh_sr, loc_fixed)
        end
      in

      let acc2 := place_operation acc1 target_mem op in

      gen_prog_core moO rest loc1 acc2 fresh1
  end.


Definition gen_prog
  (seq : seq_relation)
  (moQ_init : qubit_mem_assign)
  (moO : op_mem_assign)
  (ops : op_list)
  : distributed_prog :=
  let ordered := order_by_seq seq ops in
  let '(cfg, _fresh, _loc) := gen_prog_core moO ordered moQ_init empty_config 0 in
  cfg.

(* ========================================================================= *)
(*               Algorithm 1 – AutoDisQ main search loop                     *)
(* ========================================================================= *)

Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

Fixpoint auto_disq_search
  (ops : op_list)
  (avail_mem : membranes)
  (hp : hb_relation)
  (seen : list candidate)
  (best : distributed_prog)
  (best_score : fitness_value)
  (fuel : nat) : distributed_prog :=
  match fuel with
  | 0 => best
  | S fuel' =>
      let seq := gen_seq seen hp in
      let '(moO, moQ) := gen_mem seen avail_mem seq in
      let prog := gen_prog seq moQ moO ops in
      let score := fit prog in

      let '(new_best, new_score) :=
        if score <? best_score then (prog, score) else (best, best_score)
      in

      auto_disq_search ops avail_mem hp
        ((seq, (moO, moQ)) :: seen)
        new_best new_score fuel'
  end.

Parameter INF_SCORE : fitness_value.
Parameter DEFAULT_FUEL : nat.
Definition fuel_from_ops (ops : op_list) : nat :=
  length ops * length ops.

Definition auto_disq (ops : op_list) (avail : membranes) : distributed_prog :=
  let hp := gen_hp ops in
  let fuel := fuel_from_ops ops in
  auto_disq_search ops avail hp [] empty_config INF_SCORE fuel.


(* ========================================================================= *)
(*         Algorithm 3 – Parallelization inside one membrane                 *)
(* ========================================================================= *)

Parameter opt_hp : hb_relation -> seq_relation -> hb_relation.

Parameter compute_scc :
  hb_relation -> list exp -> list (list exp).

Parameter order_ops_in_scc : list exp -> list exp.

Definition parallelize_in_membrane
  (hp_local : hb_relation)
  (seq_local : seq_relation)
  (ops_in_mem : list exp)
  : list (list exp) :=
  let hp_opt := opt_hp hp_local seq_local in
  let components := compute_scc hp_opt ops_in_mem in
  map order_ops_in_scc components.

(* ========================================================================= *)
(*                  Top-level example usage sketch                           *)
(* ========================================================================= *)

Parameter example_sequential_shor : op_list.
Parameter example_membranes : membranes.

Definition distributed_shor : distributed_prog :=
  auto_disq example_sequential_shor example_membranes.
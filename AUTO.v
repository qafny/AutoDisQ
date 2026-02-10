

From Coq Require Import List Arith Bool.
Import ListNotations.
Require Import List.
Local Open Scope list_scope.


Require Import Reals Psatz.
Require Import SQIR.SQIR.
Require Import QuantumLib.VectorStates.
Require Import SQIR.UnitaryOps.

Require Import Coq.btauto.Btauto Coq.NArith.Nnat.
Require Import Classical_Prop.

Require Import BasicUtility.
Require Import MathSpec.
Require Import DisQSyntax.

(* ========================================================================= *)
(* Mapping                                                                   *)
(* ========================================================================= *)
Definition var := nat.

Definition membrane_id := var.
Definition membranes : Type := config.

Definition var_eqb (x y : var) : bool := Nat.eqb x y.

(* ========================================================================= *)
(* vars_of_exp                                        *)
(* ========================================================================= *)

Fixpoint vars_of_exp (e : exp) : list var :=
  match e with
  | SKIP _ _ => []
  | X x _ => x :: nil
  | H x _ => x :: nil
  | RZ _ x _ => x :: nil
  | RRZ _ x _ => x :: nil
  | SR _ x => x :: nil
  | SRR _ x => x :: nil
  | QFT x _ => x :: nil
  | RQFT x _ => x :: nil
  | Addto x q => x :: q :: nil
  | CU x _ e1 => x :: vars_of_exp e1
  | Seq e1 e2 => vars_of_exp e1 ++ vars_of_exp e2
  end.

Definition vars_of_exp_nodup (e : exp) : list var :=
  nodup Nat.eq_dec (vars_of_exp e).



(* ========================================================================= *)
(* Core aliases                                                               *)
(* ========================================================================= *)

Definition hb_relation : Type := exp -> exp -> Prop.
Definition op_list := list exp.


Definition op_mem_assign := exp -> membrane_id.
Definition qubit_mem_assign := var -> membrane_id.
Definition current_qubit_loc := var -> membrane_id.

Definition rank := nat.
Definition seq_relation := exp -> rank.

Definition fitness_value := nat.
Definition distributed_prog := config.


(* ========================================================================= *)
(* Config utilities                                                           *)
(* ========================================================================= *)

Definition memb_id (m : memb) : var :=
  match m with
  | Memb l _ => l
  | LockMemb l _ _ => l
  end.

Definition memb_procs (m : memb) : list process :=
  match m with
  | Memb _ lp => lp
  | LockMemb _ _ lp => lp
  end.

Definition rebuild_memb (m : memb) (lp' : list process) : memb :=
  match m with
  | Memb l _ => Memb l lp'
  | LockMemb l r _ => LockMemb l r lp'
  end.

Fixpoint memb_exists (cfg : config) (mid : var) : bool :=
  match cfg with
  | [] => false
  | m :: tl =>
      if var_eqb (memb_id m) mid then true else memb_exists tl mid
  end.
Definition is_locked (m : memb) : bool :=
  match m with
  | Memb _ _ => false
  | LockMemb _ _ _ => true
  end.
Definition ensure_memb (cfg : config) (mid : var) : config :=
  if memb_exists cfg mid then cfg else Memb mid [] :: cfg.

Fixpoint update_memb_procs
  (cfg : config) (mid : var) (f : list process -> list process) : config :=
  match cfg with
  | [] => []
  | m :: tl =>
      if var_eqb (memb_id m) mid
      then rebuild_memb m (f (memb_procs m)) :: tl
      else m :: update_memb_procs tl mid f
  end.

Fixpoint flatten_config (cfg : config) : list process :=
  match cfg with
  | [] => []
  | m :: tl => memb_procs m ++ flatten_config tl
  end.

Definition memb_exists_prop (cfg : config) (mid : var) : Prop :=
  exists m, In m cfg /\ memb_id m = mid.
(* ========================================================================= *)
(* Operation → process                                                        *)
(* ========================================================================= *)


Definition op_to_process (op : exp) : process :=
  AP (CAppU (nil : locus) op) PNil.

(*  place_operation takes membrane_id (nat), and builds/updates memb *)
Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : exp) : config :=
  match cfg with
  | [] => [Memb mid [op_to_process op]]
  | (Memb l ps) :: tl =>
      if Nat.eqb l mid
      then (Memb l (ps ++ [op_to_process op])) :: tl
      else (Memb l ps) :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
     
      (LockMemb l r ps) :: place_operation tl mid op
  end.

(* ========================================================================= *)
(* Teleport insertion                                        *)
(* ========================================================================= *)


(* target is membrane_id; loc maps qubit -> membrane_id *)
Definition insert_teleport_sends
  (cfg : config) (_qs : list var) (fresh : nat) (_target : membrane_id)
  : config * nat :=
  (cfg, fresh).

Definition insert_teleport_receives
  (cfg : config) (_qs : list var) (fresh : nat) (_target : membrane_id)
  (loc : var -> membrane_id)
  : config * nat * (var -> membrane_id) :=
  (cfg, fresh, loc).

Definition empty_config : config := nil.


(* ========================================================================= *)
(* Algorithm 1 helpers — trivial but total                                    *)
(* ========================================================================= *)

Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

Definition INF_SCORE : fitness_value := Nat.pow 10 6.


(* Generate happens-before relation *)
Definition gen_hp (_ops : op_list) : hb_relation := fun _ _ => False.

(* Generate schedule*)
Definition gen_seq (_seen : list candidate) (_hp : hb_relation) : seq_relation :=
  fun _ => 0%nat.

(* Generate assignments: map everything to membrane 0 *)
Definition gen_mem
  (_seen : list candidate)
  (_cfg : membranes)
  (_seq : seq_relation)
  : op_mem_assign * qubit_mem_assign :=
  ( (fun _ : exp => 0%nat),
    (fun _ : var => 0%nat) ).

Definition fit (_ : distributed_prog) : fitness_value := 0%nat.


Definition order_by_seq (_ : seq_relation) (ops : op_list) : op_list := ops.

(* ========================================================================= *)
(* Algorithm 2 — program generation                                           *)
(* ========================================================================= *)


Definition update_loc_for
  (loc : current_qubit_loc) (qs : list var) (target : membrane_id)
  : current_qubit_loc :=
  fun q => if existsb (fun x => var_eqb x q) qs then target else loc q.

Definition qubits_to_move
  (loc : current_qubit_loc) (target : membrane_id) (qs : list var)
  : list var :=
  filter (fun q => negb (var_eqb (loc q) target)) qs.

Fixpoint gen_prog_core
  (moO : op_mem_assign)
  (remaining : list exp)
  (current_loc : current_qubit_loc)
  (acc : config)
  (fresh : nat)
  : config * nat * current_qubit_loc :=
  match remaining with
  | [] => (acc, fresh, current_loc)
  | op :: tl =>
      let target := moO op in
      let qs := vars_of_exp op in
      let to_move := qubits_to_move current_loc target qs in
      let '(acc1, fresh1, loc1) :=
        match to_move with
        | [] => (acc, fresh, current_loc)
        | _ =>
            let '(cfg1, f1) := insert_teleport_sends acc to_move fresh target in
            let '(cfg2, f2, loc2) :=
              insert_teleport_receives cfg1 to_move f1 target current_loc in
            (cfg2, f2, update_loc_for loc2 to_move target)
        end
      in
      gen_prog_core moO tl loc1 (place_operation acc1 target op) fresh1
  end.

Definition gen_prog
  (seq : seq_relation)
  (moQ : qubit_mem_assign)
  (moO : op_mem_assign)
  (ops : op_list)
  : distributed_prog :=
  let '(cfg, _, _) :=
    gen_prog_core moO (order_by_seq seq ops) moQ empty_config 0
  in cfg.



(* ========================================================================= *)
(* Algorithm 1 — main AutoDisQ loop                                           *)
(* ========================================================================= *)


Fixpoint auto_disq_search
  (ops : op_list)
  (avail : membranes)
  (hp : hb_relation)
  (seen : list candidate)
  (best : distributed_prog)
  (_ : fitness_value)
  (fuel : nat) : distributed_prog :=
  match fuel with
  | 0%nat => best
  | S n =>
      let seq := gen_seq seen hp in
      let '(moO, moQ) := gen_mem seen avail seq in
      let prog := gen_prog seq moQ moO ops in
      auto_disq_search ops avail hp ((seq,(moO,moQ))::seen) prog 0%nat n
  end.



Definition fuel_from_ops (ops : op_list) : nat :=
  length ops * length ops.

Definition auto_disq (ops : op_list) (avail : membranes) : distributed_prog :=
  auto_disq_search ops avail (gen_hp ops) [] empty_config 0%nat (fuel_from_ops ops).


Definition auto_disq_as_processes (ops : op_list) (avail : membranes) : list process :=
  flatten_config (auto_disq ops avail).

(* ========================================================================= *)
(* Algorithm 3 — parallelization                                  *)
(* ========================================================================= *)

Definition overlaps (e1 e2 : exp) : bool :=
  existsb
    (fun x => existsb (fun y => var_eqb x y) (vars_of_exp e2))
    (vars_of_exp e1).


Definition fits_block (op : exp) (block : list exp) : bool :=
  existsb (fun e => overlaps op e) block.

Fixpoint insert_first_fit (op : exp) (blocks : list (list exp)) : list (list exp) :=
  match blocks with
  | [] => [[op]]
  | b :: bs =>
      if fits_block op b
      then (op :: b) :: bs
      else b :: insert_first_fit op bs
  end.


Fixpoint compute_scc (_hp : hb_relation) (ops : list exp) : list (list exp) :=
  match ops with
  | [] => []
  | op :: tl => insert_first_fit op (compute_scc _hp tl)
  end.

Definition opt_hp (hp : hb_relation) (_seq : seq_relation) : hb_relation := hp.

Definition order_ops_in_scc (ops : list exp) : list exp := ops.


Definition parallelize_in_membrane
  (hp : hb_relation)
  (seq : seq_relation)
  (ops : list exp)
  : list (list exp) :=
  compute_scc (opt_hp hp seq) ops.

Definition example_sequential_shor : op_list := nil.
Definition example_membranes : membranes := nil.

Definition distributed_shor : distributed_prog :=
  auto_disq example_sequential_shor example_membranes.


Definition my_vars_of_exp := vars_of_exp.
Definition my_place_operation := place_operation.
Definition my_insert_teleport_sends := insert_teleport_sends.
Definition my_insert_teleport_receives := insert_teleport_receives.
Definition my_empty_config : config := empty_config.
Definition my_gen_seq := gen_seq.
Definition my_gen_mem := gen_mem.
Definition my_fit := fit.
Definition my_order_by_seq := order_by_seq.

Check my_vars_of_exp.

Set Extraction AutoInline.
Extraction Inline
  my_vars_of_exp my_place_operation
  my_insert_teleport_sends my_insert_teleport_receives
  my_empty_config my_gen_seq my_gen_mem
  my_fit my_order_by_seq.


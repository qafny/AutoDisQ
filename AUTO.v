From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Definition hb_relation : Type := exp -> exp -> bool.

Definition op_list     : Type := list exp.

Definition rank         : Type := nat.
Definition seq_relation : Type := exp -> rank.

Definition op_mem_assign    : Type := exp -> membrane_id.
Definition qubit_mem_assign : Type := var -> membrane_id.

Definition fitness_value    : Type := nat.
Definition distributed_prog : Type := config.

Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

(* ------------------------------------------------------------------------- *)
(* Basic list helpers                                                        *)
(* ------------------------------------------------------------------------- *)

Definition var_eqb (x y : var) : bool := Nat.eqb x y.

Fixpoint mem_var (x : var) (xs : list var) : bool :=
  match xs with
  | [] => false
  | y :: tl => if var_eqb x y then true else mem_var x tl
  end.

Fixpoint uniq (xs : list var) : list var :=
  match xs with
  | [] => []
  | x :: tl => if mem_var x tl then uniq tl else x :: uniq tl
  end.

Fixpoint intersect (xs ys : list var) : list var :=
  match xs with
  | [] => []
  | x :: tl => if mem_var x ys then x :: intersect tl ys else intersect tl ys
  end.

(* ------------------------------------------------------------------------- *)
(* vars_of_exp                                                               *)
(* ------------------------------------------------------------------------- *)

Fixpoint vars_of_exp (e : exp) : list var :=
  match e with
  | SKIP _ _ => []
  | X x _ => [x]
  | H x _ => [x]
  | RZ _ x _ => [x]
  | RRZ _ x _ => [x]
  | SR _ x => [x]
  | SRR _ x => [x]
  | QFT x _ => [x]
  | RQFT x _ => [x]
  | Addto x q => [x; q]
  | CU x _ e1 => x :: vars_of_exp e1
  | Seq e1 e2 => vars_of_exp e1 ++ vars_of_exp e2
  end.

Definition share_qubit (e1 e2 : exp) : bool :=
  negb (Nat.eqb (length (intersect (uniq (vars_of_exp e1)) (uniq (vars_of_exp e2)))) 0).

(* ------------------------------------------------------------------------- *)
(*                        exp equality                                      *)
(* ------------------------------------------------------------------------- *)

Scheme Equality for exp.

Definition exp_eqb (a b : exp) : bool :=
  if exp_beq a b then true else false.

Fixpoint mem_exp (x : exp) (xs : list exp) : bool :=
  match xs with
  | [] => false
  | y :: tl => if exp_eqb x y then true else mem_exp x tl
  end.

Fixpoint remove_exp (x : exp) (xs : list exp) : list exp :=
  match xs with
  | [] => []
  | y :: tl => if exp_eqb x y then tl else y :: remove_exp x tl
  end.

(* ------------------------------------------------------------------------- *)
(*                          os <- gen_os(R)                                  *)                                        
(* ------------------------------------------------------------------------- *)
Definition gen_os (R : op_list) : op_list := R.

(* ------------------------------------------------------------------------- *)
(*                          hp <- gen_hp(R)                                  *)
(* ------------------------------------------------------------------------- *)

Fixpoint index_of_exp (x : exp) (xs : list exp) : nat :=
  match xs with
  | [] => 0
  | y :: tl => if exp_eqb x y then 0 else S (index_of_exp x tl)
  end.

Definition gen_hp (R : op_list) : hb_relation :=
  fun e1 e2 =>
    let i := index_of_exp e1 R in
    let j := index_of_exp e2 R in
    andb (Nat.ltb i j) (share_qubit e1 e2).

(* ------------------------------------------------------------------------- *)
(*                          MANY schedules                                   *)
(* ------------------------------------------------------------------------- *)

Definition has_incoming_from (hp : hb_relation) (nodes : list exp) (x : exp) : bool :=
  existsb (fun y => hp y x) nodes.

Definition available (hp : hb_relation) (nodes : list exp) : list exp :=
  filter (fun x => negb (has_incoming_from hp nodes x)) nodes.

Fixpoint nth_default {A} (d : A) (xs : list A) (n : nat) : A :=
  match xs, n with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: tl, S n' => nth_default d tl n'
  end.


(* ---------------- Permutations  ---------------- *)

Fixpoint insert_all (x : exp) (xs : list exp) : list (list exp) :=
  match xs with
  | [] => [[x]]
  | y :: tl =>
      (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations (xs : list exp) : list (list exp) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.

(* ---------------- Check if an order respects hp ---------------- *)

Fixpoint respects_hp (hp : hb_relation) (order : list exp) : bool :=
  match order with
  | [] => true
  | x :: tl =>
      let ok_x := forallb (fun y => negb (hp y x)) tl in
      andb ok_x (respects_hp hp tl)
  end.

(* ---------------- Return at most k valid schedules ---------------- *)

Definition topo_orders_k (hp : hb_relation) (nodes : list exp) (k : nat)
  : list (list exp) :=
  let perms := permutations nodes in
  let good  := filter (respects_hp hp) perms in
  firstn k good.

Definition seq_from_order (order : list exp) : seq_relation :=
  fun e => index_of_exp e order.

(* Paper line 9: seq <- gen_seq(S,hp)
   Here we pick different valid schedules by taking schedule_index mod #schedules. *)

Definition gen_seq_many
  (Kseq : nat)
  (schedule_index : nat)
  (hp : hb_relation)
  (os : op_list)
  : seq_relation :=
  let schedules := topo_orders_k hp os Kseq in
  let n := length schedules in
  match n with
  | 0 => fun _ => 0
  | _ =>
      let idx := Nat.modulo schedule_index n in
      let order := nth_default ([] : list exp) schedules idx in
      seq_from_order order
  end.

(* ------------------------------------------------------------------------- *)
(* Membrane ids from config                                                   *)
(* ------------------------------------------------------------------------- *)

Definition default_mid : membrane_id := 0%nat.

Definition first_mid (cfg : config) : membrane_id :=
  match cfg with
  | [] => default_mid
  | Memb l _ :: _ => l
  | LockMemb l _ _ :: _ => l
  end.

Definition mem_count (cfg : config) : nat := length cfg.

Definition nth_mid_default (cfg : config) (i : nat) : membrane_id :=
  match nth_error cfg i with
  | Some (Memb l _) => l
  | Some (LockMemb l _ _) => l
  | None => first_mid cfg
  end.

Fixpoint exp_tag (e : exp) : nat :=
  match e with
  | SKIP _ _ => 1
  | X _ _ => 2
  | CU _ _ e1 => 3 + exp_tag e1
  | RZ q _ _ => 10 + q
  | RRZ q _ _ => 20 + q
  | SR q _ => 30 + q
  | SRR q _ => 40 + q
  | QFT _ b => 50 + b
  | RQFT _ b => 60 + b
  | H _ _ => 70
  | Addto _ _ => 80
  | Seq e1 e2 => 90 + exp_tag e1 + exp_tag e2
  end.

Fixpoint sum_vars (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: tl => x + sum_vars tl
  end.

Definition exp_hash (e : exp) : nat :=
  exp_tag e + sum_vars (vars_of_exp e).

(* ------------------------------------------------------------------------- *)
(* gen_mem: parameterized by seed so different candidates differ              *)
(* ------------------------------------------------------------------------- *)

Definition subset_vars (xs ys : list var) : bool :=
  forallb (fun x => mem_var x ys) xs.

Definition overlap_big (xs ys : list var) : bool :=
  let xs' := uniq xs in
  let ys' := uniq ys in
  let inter := length (intersect xs' ys') in
  let denom := Nat.max 1 (Nat.max (length xs') (length ys')) in
  Nat.leb (Nat.div denom 2) inter. (* >= half overlap *)

Fixpoint insert_by_seq (seq : seq_relation) (op : exp) (ops : list exp) : list exp :=
  match ops with
  | [] => [op]
  | x :: tl =>
      if Nat.leb (seq op) (seq x) then op :: x :: tl
      else x :: insert_by_seq seq op tl
  end.

Fixpoint sort_by_seq (seq : seq_relation) (ops : list exp) : list exp :=
  match ops with
  | [] => []
  | x :: tl => insert_by_seq seq x (sort_by_seq seq tl)
  end.

Definition order_by_seq (seq : seq_relation) (ops : op_list) : op_list :=
  sort_by_seq seq ops.

Definition choose_mid (cfg : config) (seed k : nat) : membrane_id :=
  let m := mem_count cfg in
  let idx :=
    match m with
    | 0 => 0
    | S m' => Nat.modulo (k + seed) (S m')
    end
  in nth_mid_default cfg idx.

Fixpoint build_moO
  (cfg : config) (seed : nat) (ops_sorted : list exp)
  (prev : option (exp * membrane_id))
  (tbl : list (nat * membrane_id)) : list (nat * membrane_id) :=
  match ops_sorted with
  | [] => tbl
  | op :: tl =>
      let mid :=
        match prev with
        | None => choose_mid cfg seed (exp_hash op)
        | Some (op_prev, mid_prev) =>
            let vars := uniq (vars_of_exp op) in
            let vars_prev := uniq (vars_of_exp op_prev) in
            if orb (subset_vars vars vars_prev) (overlap_big vars vars_prev)
            then mid_prev
            else choose_mid cfg seed (exp_hash op)
        end
      in
      build_moO cfg seed tl (Some (op, mid)) ((exp_hash op, mid) :: tbl)
  end.

Fixpoint lookup_mid (h : nat) (tbl : list (nat * membrane_id)) : membrane_id :=
  match tbl with
  | [] => default_mid
  | (k,v) :: tl => if Nat.eqb k h then v else lookup_mid h tl
  end.

Definition moO_of_tbl (tbl : list (nat * membrane_id)) : op_mem_assign :=
  fun op => lookup_mid (exp_hash op) tbl.

Fixpoint first_use_mid
  (ops_sorted : list exp) (moO : op_mem_assign) (q : var) : membrane_id :=
  match ops_sorted with
  | [] => default_mid
  | op :: tl =>
      if mem_var q (vars_of_exp op) then moO op else first_use_mid tl moO q
  end.

Definition gen_mem_seed
  (seed : nat)
  (cfg  : config)
  (seq  : seq_relation)
  (os   : op_list)
  : op_mem_assign * qubit_mem_assign :=
  let ops_sorted := order_by_seq seq os in
  let moO_tbl := build_moO cfg seed ops_sorted None [] in
  let moO := moO_of_tbl moO_tbl in
  let moQ : qubit_mem_assign := fun q => first_use_mid ops_sorted moO q in
  (moO, moQ).

(* ------------------------------------------------------------------------- *)
(*                          gen_prog                                         *)
(* ------------------------------------------------------------------------- *)

Definition mk_reloc (src dst : membrane_id) : exp :=
  SKIP src (Num dst).

Definition op_to_process (op : exp) : process :=
  AP (CAppU ([] : locus) op) PNil.

Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : exp) : config :=
  match cfg with
  | [] => [Memb mid [op_to_process op]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [op_to_process op]) :: tl
      else Memb l ps :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [op_to_process op]) :: tl
      else LockMemb l r ps :: place_operation tl mid op
  end.

Definition qloc_tbl : Type := list (var * membrane_id).

Fixpoint qloc_lookup (q : var) (tbl : qloc_tbl) (d : membrane_id) : membrane_id :=
  match tbl with
  | [] => d
  | (k,v) :: tl => if var_eqb k q then v else qloc_lookup q tl d
  end.

Fixpoint qloc_update (q : var) (mid : membrane_id) (tbl : qloc_tbl) : qloc_tbl :=
  match tbl with
  | [] => [(q, mid)]
  | (k,v) :: tl =>
      if var_eqb k q then (k, mid) :: tl else (k, v) :: qloc_update q mid tl
  end.

Fixpoint init_qloc (qs : list var) (moQ : qubit_mem_assign) : qloc_tbl :=
  match qs with
  | [] => []
  | q :: tl => (q, moQ q) :: init_qloc tl moQ
  end.

Fixpoint all_qubits (ops : list exp) : list var :=
  match ops with
  | [] => []
  | op :: tl => vars_of_exp op ++ all_qubits tl
  end.

Fixpoint ensure_qubits
  (qs : list var) (target : membrane_id) (qloc : qloc_tbl) (acc : config)
  : (qloc_tbl * config) :=
  match qs with
  | [] => (qloc, acc)
  | q :: tl =>
      let cur := qloc_lookup q qloc default_mid in
      if var_eqb cur target
      then ensure_qubits tl target qloc acc
      else
        let acc' := place_operation acc target (mk_reloc cur target) in
        let qloc' := qloc_update q target qloc in
        ensure_qubits tl target qloc' acc'
  end.

Fixpoint gen_prog_core
  (moO : op_mem_assign) (moQ : qubit_mem_assign)
  (ops_sorted : list exp)
  (qloc : qloc_tbl)
  (acc  : config) : config :=
  match ops_sorted with
  | [] => acc
  | op :: tl =>
      let target := moO op in
      let qs := uniq (vars_of_exp op) in
      let '(qloc1, acc1) := ensure_qubits qs target qloc acc in
      let acc2 := place_operation acc1 target op in
      gen_prog_core moO moQ tl qloc1 acc2
  end.

Definition gen_prog
  (seq : seq_relation) (moO : op_mem_assign) (moQ : qubit_mem_assign) (os : op_list)
  : distributed_prog :=
  let ops_sorted := order_by_seq seq os in
  let qs := uniq (all_qubits ops_sorted) in
  let qloc0 := init_qloc qs moQ in
  gen_prog_core moO moQ ops_sorted qloc0 [].

(* ------------------------------------------------------------------------- *)
(*             fit: relocation-aware cost                                    *)
(* ------------------------------------------------------------------------- *)

Definition is_reloc (e : exp) : bool :=
  match e with
  | SKIP _ (Num _) => true
  | _ => false
  end.

Definition reloc_pair (e : exp) : (membrane_id * membrane_id) :=
  match e with
  | SKIP a (Num b) => (a, b)
  | _ => (0, 0)
  end.

Fixpoint mem_pair (p : membrane_id * membrane_id) (ps : list (membrane_id * membrane_id)) : bool :=
  match ps with
  | [] => false
  | q :: tl =>
      if andb (var_eqb (fst p) (fst q)) (var_eqb (snd p) (snd q))
      then true else mem_pair p tl
  end.

Fixpoint uniq_pairs (ps : list (membrane_id * membrane_id)) : list (membrane_id * membrane_id) :=
  match ps with
  | [] => []
  | p :: tl => if mem_pair p tl then uniq_pairs tl else p :: uniq_pairs tl
  end.

Fixpoint extract_exps_from_proc (p : process) : list exp :=
  match p with
  | PNil => []
  | AP c tl =>
      match c with
      | CAppU _ e => e :: extract_exps_from_proc tl
      | _ => extract_exps_from_proc tl
      end
  | DP _ tl => extract_exps_from_proc tl
  | PIf _ p1 p2 => extract_exps_from_proc p1 ++ extract_exps_from_proc p2
  end.

Fixpoint extract_all_exps (cfg : config) : list exp :=
  match cfg with
  | [] => []
  | Memb _ ps :: tl =>
      (concat (map extract_exps_from_proc ps)) ++ extract_all_exps tl
  | LockMemb _ _ ps :: tl =>
      (concat (map extract_exps_from_proc ps)) ++ extract_all_exps tl
  end.

Fixpoint count_relocs (es : list exp) : nat :=
  match es with
  | [] => 0
  | e :: tl => (if is_reloc e then 1 else 0) + count_relocs tl
  end.

Fixpoint collect_pairs (es : list exp) : list (membrane_id * membrane_id) :=
  match es with
  | [] => []
  | e :: tl =>
      if is_reloc e then reloc_pair e :: collect_pairs tl else collect_pairs tl
  end.

Definition fit (P : distributed_prog) : fitness_value :=
  let es := extract_all_exps P in
  let reloc := count_relocs es in
  let pairs := length (uniq_pairs (collect_pairs es)) in
  reloc + 5 * pairs.


Definition INF_SCORE : fitness_value := Nat.pow 10 9.

(* ============================================================ *)
(*      S-loop encoding                                   *)
(* ============================================================ *)

(* A finite identifier for a candidate (seq,mo). *)

Definition case : Type := (nat * nat)%type.  (* (schedule_index, mem_seed) *)


Definition case_eqb (c d : case) : bool :=
  andb (Nat.eqb (fst c) (fst d)) (Nat.eqb (snd c) (snd d)).

Fixpoint mem_case (c : case) (cs : list case) : bool :=
  match cs with
  | [] => false
  | d :: tl => if case_eqb c d then true else mem_case c tl
  end.

(* ------------------------------------------------------------ *)
(* Finite universe of cases (schedule_index × mem_seed)        *)
(* ------------------------------------------------------------ *)

Fixpoint range_from (start count : nat) : list nat :=
  match count with
  | 0 => []
  | S k => start :: range_from (S start) k
  end.

Definition mk_cases (Kseq Kmem : nat) : list case :=
  let scheds := range_from 0 Kseq in
  let seeds  := range_from 0 Kmem in
  concat (map (fun si => map (fun sd => (si, sd)) seeds) scheds).

Fixpoint filter_fresh (all : list case) (seen : list case) : list case :=
  match all with
  | [] => []
  | c :: tl =>
      if mem_case c seen then filter_fresh tl seen
      else c :: filter_fresh tl seen
  end.

(* are_still_cases(S) *)
Definition are_still_cases (S : list case) (ALL : list case) : bool :=
  negb (Nat.eqb (length (filter_fresh ALL S)) 0).

(* gen_seq(S,hp) — pick a not-yet-seen case and build seq from it *)
Definition pick_case (S : list case) (ALL : list case) : option case :=
  match filter_fresh ALL S with
  | [] => None
  | c :: _ => Some c
  end.

Definition gen_seq_paper
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (S    : list case)
  (ALL  : list case)
  : option (case * seq_relation) :=
  match pick_case S ALL with
  | None => None
  | Some c =>
      let sched_i := fst c in
      let seq := gen_seq_many Kseq sched_i hp os in
      Some (c, seq)
  end.

(* gen_mem(S,L,seq) — use chosen case’s seed to build mo *)
Definition gen_mem_paper
  (cfg  : config)   (* this plays the role of L (available membranes) *)
  (seq  : seq_relation)
  (os   : op_list)
  (c    : case)
  : op_mem_assign * qubit_mem_assign :=
  let seed := snd c in
  gen_mem_seed seed cfg seq os.

(*  while-loop:
   S ← ∅
   while are_still_cases(S) do ... S ← {(seq,mo)} ∪ S *)
Fixpoint auto_disq_loop_paper
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (cfg  : config)
  (ALL  : list case)          (* finite set of possible cases *)
  (S    : list case)
  (Qbest: distributed_prog)
  (zmin : fitness_value)
  (fuel : nat)                (* only for Coq termination; set to |ALL| *)
  : distributed_prog :=
  match fuel with
  | 0 => Qbest
  | S fuel' =>
      if are_still_cases S ALL then
        match gen_seq_paper Kseq hp os S ALL with
        | None => Qbest
        | Some (c, seq) =>
            let '(moO, moQ) := gen_mem_paper cfg seq os c in
            let P := gen_prog seq moO moQ os in
            let z := fit P in
            let S' := c :: S in  (* S ← {(seq,mo)} ∪ S, represented by case id *)
            if Nat.ltb z zmin
            then auto_disq_loop_paper Kseq hp os cfg ALL S' P z fuel'
            else auto_disq_loop_paper Kseq hp os cfg ALL S' Qbest zmin fuel'
        end
      else Qbest
  end.

(* Full Algorithm 1  *)
Definition auto_disq_alg1_paper
  (Kseq : nat)
  (Kmem : nat)
  (R    : op_list)
  (cfg  : config)
  : distributed_prog :=
  let hp := gen_hp R in
  let os := gen_os R in
  let ALL := mk_cases Kseq Kmem in
  auto_disq_loop_paper Kseq hp os cfg ALL [] ([] : config) INF_SCORE (length ALL).








(*
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
(*
Definition gen_seq (_S : list candidate) (_hp : hb_relation) : seq_relation :=
  let seed := length _S in
  fun e => exp_hash e + seed.
*)
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

*)

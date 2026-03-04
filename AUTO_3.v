

From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Inductive myOp : Type :=
| OpAP  (a : cexp)                         
| OpDP  (a : cdexp)                       
| OpIf  (b : cbexp) (p q : process). 

Definition op_list : Type := list myOp.
Definition hb_relation : Type := myOp -> myOp -> bool.
Definition rank         : Type := nat.
Definition seq_relation : Type := myOp -> rank.
Definition op_mem_assign : Type := myOp -> membrane_id.

Fixpoint list_eqb {A : Type} (beq : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => andb (beq x y) (list_eqb beq xs' ys')
  | _, _ => false
  end.

Fixpoint aexp_eqb (e1 e2 : aexp) : bool :=
  match e1, e2 with
  | BA x1, BA x2 => Nat.eqb x1 x2
  | Num n1, Num n2 => Nat.eqb n1 n2
  | APlus a1 b1, APlus a2 b2 =>
      andb (aexp_eqb a1 a2) (aexp_eqb b1 b2)
  | AMult a1 b1, AMult a2 b2 =>
      andb (aexp_eqb a1 a2) (aexp_eqb b1 b2)
  | _, _ => false
  end.

Definition cbexp_eqb (b1 b2 : cbexp) : bool :=
  match b1, b2 with
  | CEq x1 y1, CEq x2 y2 =>
      andb (aexp_eqb x1 x2) (aexp_eqb y1 y2)
  | CLt x1 y1, CLt x2 y2 =>
      andb (aexp_eqb x1 x2) (aexp_eqb y1 y2)
  | _, _ => false
  end.

Definition bound_eqb (b1 b2 : bound) : bool :=
  match b1, b2 with
  | BVar v1 n1, BVar v2 n2 =>
      andb (Nat.eqb v1 v2) (Nat.eqb n1 n2)
  | BNum n1, BNum n2 =>
      Nat.eqb n1 n2
  | _, _ => false
  end.

Definition range_eqb (r1 r2 : range) : bool :=
  match r1, r2 with
  | (x1, lo1, hi1), (x2, lo2, hi2) =>
      andb (Nat.eqb x1 x2)
           (andb (bound_eqb lo1 lo2)
                 (bound_eqb hi1 hi2))
  end.

Definition locus_eqb (l1 l2 : locus) : bool :=
  list_eqb range_eqb l1 l2.

Fixpoint exp_eqb (e1 e2 : exp) : bool :=
  match e1, e2 with
  | SKIP x1 a1, SKIP x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | X x1 a1, X x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | CU x1 a1 e1', CU x2 a2 e2' =>
      andb (Nat.eqb x1 x2) (andb (aexp_eqb a1 a2) (exp_eqb e1' e2'))
  | RZ q1 x1 a1, RZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2) (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | RRZ q1 x1 a1, RRZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2) (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | SR q1 x1, SR q2 x2 =>
      andb (Nat.eqb q1 q2) (Nat.eqb x1 x2)
  | SRR q1 x1, SRR q2 x2 =>
      andb (Nat.eqb q1 q2) (Nat.eqb x1 x2)
  | QFT x1 b1, QFT x2 b2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb b1 b2)
  | RQFT x1 b1, RQFT x2 b2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb b1 b2)
  | H x1 a1, H x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | Addto x1 q1, Addto x2 q2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb q1 q2)
  | Seq s1 t1, Seq s2 t2 =>
      andb (exp_eqb s1 s2) (exp_eqb t1 t2)
  | _, _ => false
  end.

Definition cexp_eqb (c1 c2 : cexp) : bool :=
  match c1, c2 with
  | CNew x1 n1, CNew x2 n2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb n1 n2)
  | CAppU l1 e1, CAppU l2 e2 =>
      andb (locus_eqb l1 l2) (exp_eqb e1 e2)
  | CMeas x1 k1, CMeas x2 k2 =>
      andb (Nat.eqb x1 x2) (locus_eqb k1 k2)
  | _, _ => false
  end.

Definition cdexp_eqb (d1 d2 : cdexp) : bool :=
  match d1, d2 with
  | NewCh c1 n1, NewCh c2 n2 =>
      andb (Nat.eqb c1 c2) (Nat.eqb n1 n2)
  | Send c1 a1, Send c2 a2 =>
      andb (Nat.eqb c1 c2) (aexp_eqb a1 a2)
  | Recv c1 x1, Recv c2 x2 =>
      andb (Nat.eqb c1 c2) (Nat.eqb x1 x2)
  | _, _ => false
  end.

Fixpoint process_eqb (p1 p2 : process) : bool :=
  match p1, p2 with
  | PNil, PNil => true
  | AP a1 p1', AP a2 p2' =>
      andb (cexp_eqb a1 a2) (process_eqb p1' p2')
  | DP a1 p1', DP a2 p2' =>
      andb (cdexp_eqb a1 a2) (process_eqb p1' p2')
  | PIf b1 p1a p1b, PIf b2 p2a p2b =>
      andb (cbexp_eqb b1 b2)
           (andb (process_eqb p1a p2a) (process_eqb p1b p2b))
  | _, _ => false
  end.



Definition myOp_eqb (x y : myOp) : bool :=
  match x, y with
  | OpAP a1, OpAP a2 => cexp_eqb a1 a2
  | OpDP a1, OpDP a2 => cdexp_eqb a1 a2
  | OpIf b1 p1 q1, OpIf b2 p2 q2 =>
      andb (cbexp_eqb b1 b2)
           (andb (process_eqb p1 p2) (process_eqb q1 q2))
  | _, _ => false
  end.

Definition qubit_mem_assign : Type := var -> membrane_id.

Definition fitness_value    : Type := nat.
Definition distributed_prog : Type := config.



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

Scheme Equality for exp.

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
(*                     os <- gen_os(R)                                  *)
(* ------------------------------------------------------------------------- *)
Definition gen_os (R : op_list) : op_list := R.

(* ------------------------------------------------------------------------- *)
(* Paper Algorithm 1 line 3: hp <- gen_hp(R)                                  *)
(* You used: order-in-R + share_qubit => dependency.                          *)
(* ------------------------------------------------------------------------- *)

Fixpoint index_of_exp (x : exp) (xs : list exp) : nat :=
  match xs with
  | [] => 0
  | y :: tl => if exp_eqb x y then 0 else S (index_of_exp x tl)
  end.

Fixpoint vars_of_aexp (a : aexp) : list var :=
  match a with
  | BA x => [x]
  | Num _ => []
  | APlus a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  | AMult a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  end.

Definition vars_of_cbexp (b : cbexp) : list var :=
  match b with
  | CEq a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  | CLt a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  end.


Definition vars_of_myOp (op : myOp) : list var :=
  match op with
  | OpAP a =>
      match a with
      | CAppU _ e => vars_of_exp e
      | CNew x _ => [x]
      | CMeas x _ => [x]
      end
  | OpDP a =>
      match a with
      | NewCh c _ => [c]
      | Send c e => c :: vars_of_aexp e
      | Recv c x => [c; x]
      end
  | OpIf b _ _ =>
      vars_of_cbexp b
  end.


Definition qubits_of_range (r : range) : list var :=
  match r with
  | (q, _lo, _hi) => [q]
  end.

Definition qubits_of_locus (L : locus) : list var :=
  concat (map qubits_of_range L).


Definition qubits_of_cexp (c : cexp) : list var :=
  match c with
  | CNew q _     => [q]
  | CAppU _ e    => vars_of_exp e
  | CMeas _ k    => qubits_of_locus k   (* NOT vars_of_locus *)
  end.

(* Extract qubits touched by a locus *)
Definition vars_of_bound (b : bound) : list var :=
  match b with
  | BVar v _ => [v]
  | BNum _ => []
  end.

Definition vars_of_range (r : range) : list var :=
  match r with
  | (x, lo, hi) => x :: vars_of_bound lo ++ vars_of_bound hi
  end.

Definition vars_of_locus (L : locus) : list var :=
  concat (map vars_of_range L).

(*
(* Qubits touched by a cexp *)
Definition qubits_of_cexp (c : cexp) : list var :=
  match c with
  | CNew q _     => [q]
  | CAppU _ e    => vars_of_exp e
  | CMeas _ k    => vars_of_locus k   (* IMPORTANT: not [x] *)
  end.
*)
Definition qubits_of_myOp (o : myOp) : list var :=
  match o with
  | OpAP a => qubits_of_cexp a
  | OpDP _ => []          (* DP are classical comm ops, not “qubit sharing” *)
  | OpIf _ _ _ => []      (* guard is classical *)
  end.

Definition share_qubit_myOp (o1 o2 : myOp) : bool :=
  negb (Nat.eqb
          (length (intersect (uniq (qubits_of_myOp o1))
                             (uniq (qubits_of_myOp o2))))
          0).

(*

Definition share_qubit_myOp (o1 o2 : myOp) : bool :=
  negb (Nat.eqb
          (length
             (intersect
                (uniq (vars_of_myOp o1))
                (uniq (vars_of_myOp o2))))
          0).
*)
Fixpoint index_of_myOp (x : myOp) (xs : list myOp) : nat :=
  match xs with
  | [] => 0
  | y :: tl =>
      if myOp_eqb x y
      then 0
      else S (index_of_myOp x tl)
  end.

Definition gen_hp (R : op_list) : hb_relation :=
  fun o1 o2 =>
    let i := index_of_myOp o1 R in
    let j := index_of_myOp o2 R in
    andb (Nat.ltb i j) (share_qubit_myOp o1 o2).


(* ------------------------------------------------------------------------- *)
(*                         MANY schedules                                    *)
(* ------------------------------------------------------------------------- *)
Definition has_incoming_from
  (hp : hb_relation)
  (nodes : list myOp)
  (x : myOp) : bool :=
  existsb (fun y => hp y x) nodes.

Definition available
  (hp : hb_relation)
  (nodes : list myOp) : list myOp :=
  filter (fun x => negb (has_incoming_from hp nodes x)) nodes.

Fixpoint nth_default {A} (d : A) (xs : list A) (n : nat) : A :=
  match n with
  | 0 =>
      match xs with
      | [] => d
      | x :: _ => x
      end
  | S n' =>
      match xs with
      | [] => d
      | _ :: tl => nth_default d tl n'
      end
  end.
(* ------------------------------------------------------------ *)
(* Safe topological ordering without permutations (Kahn-style)   *)
(* ------------------------------------------------------------ *)

Fixpoint remove_one (eqb : myOp -> myOp -> bool) (x : myOp) (xs : list myOp) : list myOp :=
  match xs with
  | [] => []
  | y :: tl => if eqb x y then tl else y :: remove_one eqb x tl
  end.

Definition has_incoming_from_nodes
  (hp : hb_relation) (nodes : list myOp) (x : myOp) : bool :=
  existsb (fun y => hp y x) nodes.

Definition available_nodes (hp : hb_relation) (nodes : list myOp) : list myOp :=
  filter (fun x => negb (has_incoming_from_nodes hp nodes x)) nodes.

Fixpoint nth_default_myOp (d : myOp) (xs : list myOp) (n : nat) : myOp :=
  match n with
  | 0 =>
      match xs with
      | [] => d
      | x :: _ => x
      end
  | S n' =>
      match xs with
      | [] => d
      | _ :: tl => nth_default_myOp d tl n'
      end
  end.

(* choose an available node based on schedule_index (tie-break) *)
Definition pick_available
  (schedule_index : nat) (avs : list myOp) : option myOp :=
  match avs with
  | [] => None
  | _ =>
      let idx := Nat.modulo schedule_index (length avs) in
      Some (nth_default_myOp (hd (OpAP (CNew 0 0)) avs) avs idx)
  end.

Fixpoint topo_kahn_fuel
  (hp : hb_relation)
  (schedule_index : nat)
  (nodes : list myOp)
  (fuel : nat)
  (acc  : list myOp)
  : option (list myOp) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match nodes with
      | [] => Some (rev acc)
      | _  =>
          let avs := available_nodes hp nodes in
          match pick_available schedule_index avs with
          | None => None (* cycle or inconsistent hp *)
          | Some x =>
              topo_kahn_fuel hp (S schedule_index)
                             (remove_one myOp_eqb x nodes)
                             fuel' (x :: acc)
          end
      end
  end.

Definition topo_kahn
  (hp : hb_relation)
  (schedule_index : nat)
  (nodes : list myOp)
  : option (list myOp) :=
  topo_kahn_fuel hp schedule_index nodes (S (length nodes)) [].

(*

(* ---------------- Permutations ---------------- *)

Fixpoint insert_all (x : myOp) (xs : list myOp) : list (list myOp) :=
  match xs with
  | [] => [[x]]
  | y :: tl =>
      (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations (xs : list myOp) : list (list myOp) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.


(* ---------------- Check if an order respects hp ---------------- *)

(* "order respects hp" iff there is no edge from a later op to an earlier op.
   Equivalent: for each x, no y in the suffix has hp y x = true. *)

Fixpoint respects_hp (hp : hb_relation) (order : list myOp) : bool :=
  match order with
  | [] => true
  | x :: tl =>
      let ok_x := forallb (fun y => negb (hp y x)) tl in
      andb ok_x (respects_hp hp tl)
  end.
(* ---------------- Return at most k valid schedules ---------------- *)

Definition topo_orders_k
  (hp : hb_relation)
  (nodes : list myOp)
  (k : nat)
  : list (list myOp) :=
  let perms := permutations nodes in
  let good  := filter (respects_hp hp) perms in
  firstn k good.
*)
Definition seq_from_order (order : list myOp) : seq_relation :=
  fun o => index_of_myOp o order.


(*  seq <- gen_seq(S,hp) *)
Definition gen_seq_many
  (Kseq : nat)
  (schedule_index : nat)
  (hp : hb_relation)
  (os : op_list)
  : seq_relation :=
  (* Instead of enumerating Kseq different schedules, we generate one topo order
     and vary tie-breaking using schedule_index. *)
  match topo_kahn hp schedule_index os with
  | None => fun _ => 0
  | Some order => seq_from_order order
  end.

(*
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
      let order := nth_default ([] : list myOp) schedules idx in
      seq_from_order order
  end.
*)
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

Definition mem_count (cfg : config) : nat :=
  length cfg.

Definition nth_mid_default (cfg : config) (i : nat) : membrane_id :=
  match cfg with
  | [] => default_mid
  | _ =>
      match nth_error cfg i with
      | Some (Memb l _) => l
      | Some (LockMemb l _ _) => l
      | None => first_mid cfg
      end
  end.


(* ------------------------------------------------------------------------- *)
(* A total “hash” for exp (for deterministic membrane choice tables)          *)
(* ------------------------------------------------------------------------- *)


Fixpoint sum_vars (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: tl => x + sum_vars tl
  end.

Definition myOp_tag (o : myOp) : nat :=
  match o with
  | OpAP a =>
      match a with
      | CNew _ _ => 1
      | CAppU _ _ => 2
      | CMeas _ _ => 3
      end
  | OpDP a =>
      match a with
      | NewCh _ _ => 4
      | Send _ _  => 5
      | Recv _ _  => 6
      end
  | OpIf _ _ _ => 7
  end.

(* Hash for myOp *)
Definition myOp_hash (o : myOp) : nat :=
  myOp_tag o + sum_vars (vars_of_myOp o).

(* ------------------------------------------------------------------------- *)
(*                        gen_mem                                           *)
(* ------------------------------------------------------------------------- *)
Definition subset_vars (xs ys : list var) : bool :=
  forallb (fun x => mem_var x ys) xs.

Definition overlap_big (xs ys : list var) : bool :=
  let xs' := uniq xs in
  let ys' := uniq ys in
  let inter := length (intersect xs' ys') in
  let denom := Nat.max 1 (Nat.max (length xs') (length ys')) in
  Nat.leb (Nat.div denom 2) inter. (* >= half overlap *)

Fixpoint insert_by_seq (seq : seq_relation) (op : myOp) (ops : list myOp) : list myOp :=
  match ops with
  | [] => [op]
  | x :: tl =>
      if Nat.leb (seq op) (seq x) then op :: x :: tl
      else x :: insert_by_seq seq op tl
  end.

Fixpoint sort_by_seq (seq : seq_relation) (ops : list myOp) : list myOp :=
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
  (cfg : config) (seed : nat) (ops_sorted : list myOp)
  (prev : option (myOp * membrane_id))
  (tbl : list (nat * membrane_id)) : list (nat * membrane_id) :=
  match ops_sorted with
  | [] => tbl
  | op :: tl =>
      let mid :=
        match prev with
        | None => choose_mid cfg seed (myOp_hash op)
        | Some (op_prev, mid_prev) =>
            let vars := uniq (vars_of_myOp op) in
            let vars_prev := uniq (vars_of_myOp op_prev) in
            if orb (subset_vars vars vars_prev) (overlap_big vars vars_prev)
            then mid_prev
            else choose_mid cfg seed (myOp_hash op)
        end
      in
      build_moO cfg seed tl (Some (op, mid)) ((myOp_hash op, mid) :: tbl)
  end.

Fixpoint lookup_mid (h : nat) (tbl : list (nat * membrane_id)) : membrane_id :=
  match tbl with
  | [] => default_mid
  | (k,v) :: tl => if Nat.eqb k h then v else lookup_mid h tl
  end.

Definition moO_of_tbl (tbl : list (nat * membrane_id)) : op_mem_assign :=
  fun op => lookup_mid (myOp_hash op) tbl.

Fixpoint first_use_mid
  (ops_sorted : list myOp) (moO : op_mem_assign) (q : var) : membrane_id :=
  match ops_sorted with
  | [] => default_mid
  | op :: tl =>
      if mem_var q (vars_of_myOp op) then moO op else first_use_mid tl moO q
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
(*                              gen_prog                             *)
(* ------------------------------------------------------------------------- *)
Definition mk_reloc (src dst : membrane_id) : exp :=
  SKIP src (Num dst).

(* Convert a myOp into a process we can store in a membrane *)
Definition myOp_to_process (op : myOp) : process :=
  match op with
  | OpAP a => AP a PNil
  | OpDP a => DP a PNil
  | OpIf b p q => PIf b p q
  end.

(* Relocation step is encoded as a local action that applies SKIP src (Num dst) *)
Definition reloc_process (src dst : membrane_id) : process :=
  AP (CAppU ([] : locus) (mk_reloc src dst)) PNil.

Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : myOp) : config :=
  match cfg with
  | [] => [Memb mid [myOp_to_process op]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [myOp_to_process op]) :: tl
      else Memb l ps :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [myOp_to_process op]) :: tl
      else LockMemb l r ps :: place_operation tl mid op
  end.

Fixpoint place_reloc (cfg : config) (mid : membrane_id) (src dst : membrane_id) : config :=
  match cfg with
  | [] => [Memb mid [reloc_process src dst]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [reloc_process src dst]) :: tl
      else Memb l ps :: place_reloc tl mid src dst
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [reloc_process src dst]) :: tl
      else LockMemb l r ps :: place_reloc tl mid src dst
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

Fixpoint all_qubits (ops : list myOp) : list var :=
  match ops with
  | [] => []
  | op :: tl => vars_of_myOp op ++ all_qubits tl
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
        let acc'  := place_reloc acc target cur target in
        let qloc' := qloc_update q target qloc in
        ensure_qubits tl target qloc' acc'
  end.

Fixpoint gen_prog_core
  (moO : op_mem_assign) (moQ : qubit_mem_assign)
  (ops_sorted : list myOp)
  (qloc : qloc_tbl)
  (acc  : config) : config :=
  match ops_sorted with
  | [] => acc
  | op :: tl =>
      let target := moO op in
      let qs := uniq (vars_of_myOp op) in
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
(* fit: relocation-aware cost                                         *)
(* ------------------------------------------------------------------------- *)

Fixpoint count_comm_proc (p : process) : nat :=
  match p with
  | PNil => 0
  | AP _ p' => count_comm_proc p'
  | DP d p' =>
      match d with
      | Send _ _ => S (count_comm_proc p')
      | Recv _ _ => S (count_comm_proc p')
      | _ => count_comm_proc p'
      end
  | PIf _ p1 p2 => count_comm_proc p1 + count_comm_proc p2
  end.

Fixpoint count_comm_cfg (cfg : config) : nat :=
  match cfg with
  | [] => 0
  | Memb _ ps :: tl =>
      fold_right (fun p acc => count_comm_proc p + acc) 0 ps + count_comm_cfg tl
  | LockMemb _ _ ps :: tl =>
      fold_right (fun p acc => count_comm_proc p + acc) 0 ps + count_comm_cfg tl
  end.

Definition fit (P : distributed_prog) : fitness_value :=
  count_comm_cfg P.

Definition INF_SCORE : fitness_value := 1000000000%nat.


(* ============================================================ *)
(*      S-loop encoding                                   *)
(* ============================================================ *)

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

(* Keep only cases not already in S *)
Fixpoint filter_fresh (all : list case) (seen : list case) : list case :=
  match all with
  | [] => []
  | c :: tl =>
      if mem_case c seen then filter_fresh tl seen
      else c :: filter_fresh tl seen
  end.
(* candidate element stores: id + the actual functions (seq, mo) *)
Definition candidate : Type :=
  (case * (seq_relation * (op_mem_assign * qubit_mem_assign)))%type.

Definition seen_cases (S : list candidate) : list case :=
  map fst S.

(* are_still_cases(S) *)
Definition are_still_cases_cases (seen : list case) (ALL : list case) : bool :=
  match filter_fresh ALL seen with
  | [] => false
  | _  => true
  end.

Definition pick_case (S : list case) (ALL : list case) : option case :=
  match filter_fresh ALL S with
  | [] => None
  | c :: _ => Some c
  end.

(* gen_seq(S,hp) *)
Definition gen_seq
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (ALL  : list case)
  (S    : list candidate)
  : option (case * seq_relation) :=
  match pick_case (seen_cases S) ALL with
  | None => None
  | Some c =>
      let sched_i := fst c in
      let seq := gen_seq_many Kseq sched_i hp os in
      Some (c, seq)
  end.

(* gen_mem(S,L,seq) *)
Definition gen_mem
  (cfg  : config)  
  (seq  : seq_relation)
  (os   : op_list)
  (c    : case)     
  : op_mem_assign * qubit_mem_assign :=
  let seed := snd c in
  gen_mem_seed seed cfg seq os.



Definition Smap : Type := list (var * membrane_id).
Definition locus_myOp (op : myOp) : list var := qubits_of_myOp op.

Definition diff_mem
  (mo_cur : var -> membrane_id)
  (qs : list var)
  (l  : membrane_id)
  : Smap :=
  fold_right
    (fun q acc =>
       let src := mo_cur q in
       if var_eqb src l then acc else (q, src) :: acc)
    [] qs.

Fixpoint mem_up_smap
  (mo_cur : var -> membrane_id)
  (S : Smap)
  (l : membrane_id)
  : var -> membrane_id :=
  match S with
  | [] => mo_cur
  | (q,_) :: tl =>
      let mo_cur' := fun x => if var_eqb x q then l else mo_cur x in
      mem_up_smap mo_cur' tl l
  end.

Fixpoint insert_send_recv
  (P : config)
  (Sp : Smap)
  (l  : membrane_id)
  (name : nat)
  : config * nat :=
  match Sp with
  | [] => (P, name)
  | (q, src) :: tl =>
      let c     : var := name in
      let alias : var := name + 1 in
      let P0 := place_operation P src (OpDP (NewCh c 1)) in
      let P1 := place_operation P0 src (OpDP (Send c (BA q))) in
      let P2 := place_operation P1 l (OpDP (Recv c alias)) in
      insert_send_recv P2 tl l (name + 2)
  end.


Fixpoint mem_up (mo_cur : qubit_mem_assign) (qs : list var) (l : membrane_id) : qubit_mem_assign :=
  match qs with
  | [] => mo_cur
  | q :: qs' =>
      let mo_cur' := fun x => if Nat.eqb x q then l else mo_cur x in
      mem_up mo_cur' qs' l
  end.

Definition place
  (P    : config)
  (op   : myOp)
  (l    : membrane_id)
  (name : nat)
  : config :=
  place_operation P l op.

Fixpoint gen_prog_loop_alg2
  (seq    : list myOp)
  (mo_cur : var -> membrane_id)
  (moO    : myOp -> membrane_id)
  (P      : config)
  (name   : nat)
  : config :=
  match seq with
  | [] => P
  | op :: seq' =>
      let l : membrane_id := moO op in
      let S : Smap := diff_mem mo_cur (locus_myOp op) l in

      let '(P1, name1) :=
        match S with
        | [] => (P, name)
        | _  => insert_send_recv P S l name
        end in

      let mo_cur' : var -> membrane_id := mem_up_smap mo_cur S l in
      let P2 : config := place P1 op l name1 in
      gen_prog_loop_alg2 seq' mo_cur' moO P2 name1
  end.

Definition empty_config : config := [].

Definition gen_prog_alg2
  (seq : list myOp)
  (moQ : var -> membrane_id)
  (moO : myOp -> membrane_id)
  : config :=
  gen_prog_loop_alg2 seq moQ moO empty_config 0.

Definition gen_prog_paper
  (seq : seq_relation)
  (moQ : qubit_mem_assign)
  (moO : op_mem_assign)
  (os  : op_list)
  : distributed_prog :=
  let ops_sorted : list myOp := order_by_seq seq os in
  gen_prog_alg2 ops_sorted moQ moO.

(*  while-loop:
   S ← ∅
   while are_still_cases(S) do ... S ← {(seq,mo)} ∪ S *)
Fixpoint auto_disq_loop
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (cfg  : config)
  (ALL  : list case)
  (S    : list candidate)
  (Qbest: distributed_prog)
  (zmin : fitness_value)
  (fuel : nat)
  : distributed_prog :=
  match fuel with
  | 0 => Qbest
  | S fuel' =>
      if are_still_cases_cases (seen_cases S) ALL then
        match gen_seq Kseq hp os ALL S with
        | None => Qbest
        | Some (c, seq) =>
            let '(moO, moQ) := gen_mem cfg seq os c in
            let P := gen_prog_paper seq moQ moO os in
            let z := fit P in
            let S' : list candidate := (c, (seq, (moO, moQ))) :: S in
            if Nat.ltb z zmin
            then auto_disq_loop Kseq hp os cfg ALL S' P z fuel'
            else auto_disq_loop Kseq hp os cfg ALL S' Qbest zmin fuel'
        end
      else
        Qbest
  end.

Definition auto_disq_alg1_paper
  (Kseq : nat)
  (Kmem : nat)
  (R    : op_list)
  (cfg  : config)
  : distributed_prog :=
  let hp := gen_hp R in
  let os := gen_os R in
  let ALL := mk_cases Kseq Kmem in
  (* S ← ∅ *)
  auto_disq_loop Kseq hp os cfg ALL [] ([] : config) INF_SCORE (length ALL).


(* ---------- membership for myOp ---------- *)
Fixpoint mem_myOp (x : myOp) (xs : list myOp) : bool :=
  match xs with
  | [] => false
  | y :: tl => if myOp_eqb x y then true else mem_myOp x tl
  end.

Fixpoint remove_myOp (x : myOp) (xs : list myOp) : list myOp :=
  match xs with
  | [] => []
  | y :: tl => if myOp_eqb x y then tl else y :: remove_myOp x tl
  end.

(* outgoing edges *)
Definition succs (hp : hb_relation) (nodes : list myOp) (x : myOp) : list myOp :=
  filter (fun y => hp x y) nodes.

(* DFS: returns true iff a cycle is found reachable from x *)
Fixpoint dfs_cycle_fuel
  (hp : hb_relation)
  (nodes : list myOp)
  (fuel : nat)
  (visiting visited : list myOp)
  (x : myOp)
  : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      if mem_myOp x visiting then true          (* back-edge => cycle *)
      else if mem_myOp x visited then false     (* already done *)
      else
        let visiting' := x :: visiting in
        let nxt := succs hp nodes x in
        if existsb (dfs_cycle_fuel hp nodes fuel' visiting' visited) nxt
        then true
        else false
  end.

(* Outer loop: check all nodes (graph may be disconnected) *)
Fixpoint has_cycle_from_all_fuel
  (hp : hb_relation)
  (nodes todo : list myOp)
  (fuel : nat)
  (visited : list myOp)
  : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      match todo with
      | [] => false
      | x :: tl =>
          if mem_myOp x visited then
            has_cycle_from_all_fuel hp nodes tl fuel' visited
          else
            if dfs_cycle_fuel hp nodes (length nodes + 1) [] visited x
            then true
            else
              (* mark x visited to avoid restarting from it again *)
              has_cycle_from_all_fuel hp nodes tl fuel' (x :: visited)
      end
  end.

Definition hp_has_cycle_dfs (hp : hb_relation) (nodes : list myOp) : bool :=
  has_cycle_from_all_fuel hp nodes nodes (length nodes + 1) [].

Definition hp_acyclic (hp : hb_relation) (nodes : list myOp) : bool :=
  negb (hp_has_cycle_dfs hp nodes).





Fixpoint mem_op (eqb : myOp -> myOp -> bool) (x : myOp) (xs : list myOp) : bool :=
  match xs with
  | [] => false
  | y :: tl => if eqb x y then true else mem_op eqb x tl
  end.

Fixpoint uniq_ops (eqb : myOp -> myOp -> bool) (xs : list myOp) : list myOp :=
  match xs with
  | [] => []
  | x :: tl => if mem_op eqb x tl then uniq_ops eqb tl else x :: uniq_ops eqb tl
  end.

Fixpoint remove_ops (eqb : myOp -> myOp -> bool) (xs rem : list myOp) : list myOp :=
  match xs with
  | [] => []
  | x :: tl => if mem_op eqb x rem then remove_ops eqb tl rem else x :: remove_ops eqb tl rem
  end.

Definition opt_hp (hp_l : hb_relation) (seq_l : seq_relation) : hb_relation :=
  fun a b => andb (hp_l a b) (Nat.ltb (seq_l a) (seq_l b)).

Fixpoint reachable_fuel
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (fuel : nat)
  (seen : list myOp)
  (x target : myOp) : bool :=
  if eqb x target then true else
  match fuel with
  | 0 => false
  | S fuel' =>
      if mem_op eqb x seen then false
      else
        let seen' := x :: seen in
        existsb (fun y => reachable_fuel eqb hp nodes fuel' seen' y target)
                (succs hp nodes x)
  end.

Definition reachable
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (x y : myOp) : bool :=
  reachable_fuel eqb hp nodes (length nodes) [] x y.

Definition scc_of
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (x : myOp) : list myOp :=
  filter
    (fun y =>
       andb (reachable eqb hp nodes x y)
            (reachable eqb hp nodes y x))
    nodes.

Fixpoint scc_partition_fuel
  (fuel : nat)
  (eqb  : myOp -> myOp -> bool)
  (hp   : hb_relation)
  (nodes : list myOp)
  : list (list myOp) :=
  match fuel with
  | 0 => []  
  | S fuel' =>
      match nodes with
      | [] => []
      | x :: _ =>
          let comp := scc_of eqb hp nodes x in
          let rest := remove_ops eqb nodes comp in
          comp :: scc_partition_fuel fuel' eqb hp rest
      end
  end.

Definition scc_partition
  (eqb  : myOp -> myOp -> bool)
  (hp   : hb_relation)
  (nodes : list myOp)
  : list (list myOp) :=
  scc_partition_fuel (length nodes) eqb hp nodes.

Definition gen_ops (seq_l : seq_relation) (sbar : list myOp) : list process :=
  map myOp_to_process (sort_by_seq seq_l sbar).

Fixpoint alg3_loop
  (seq_l : seq_relation)
  (S     : list (list myOp))
  (Rbar  : list process)
  : list process :=
  match S with
  | [] =>
      Rbar
  | sbar :: S' =>
      let R := gen_ops seq_l sbar in
      let Rbar' := Rbar ++ R in
      alg3_loop seq_l S' Rbar'
  end.


Definition auto_parallelize_alg3
  (eqb  : myOp -> myOp -> bool)   
  (ops_l : list myOp)            
  (hp_l  : hb_relation)
  (seq_l : seq_relation)
  : list process :=
  let hp_l' := opt_hp hp_l seq_l in  
  let S := scc_partition eqb hp_l' (uniq_ops eqb ops_l) in  
  alg3_loop seq_l S ([] : list process).




























From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)
Require Import DisQ.AUTO.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.


Definition cfg1 : config := [Memb 0 []; Memb 1 []].

Definition op1 : myOp := OpAP (CNew 0 1).
Definition op2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition R1  : op_list := [op1; op2].

Definition P1 : distributed_prog :=
  auto_disq_alg1_paper 2 2 R1 cfg1.

Compute P1.

Compute fit P1.

Definition cfg_test : config := [Memb 0 []; Memb 1 []].

Definition S_empty : Smap := [].

Definition T1 :=
  insert_send_recv cfg_test S_empty 1 0.

Compute T1.

Definition S_one : Smap := [(0, 0)].

Definition T2 :=
  insert_send_recv cfg_test S_one 1 0.

Compute T2.


Definition S_two : Smap := [(0,0); (1,0)].
Definition T3 := insert_send_recv cfg_test S_two 1 0.
Compute T3.
Definition memb_procs (m : memb) : list process :=
  match m with
  | Memb _ ps => ps
  | LockMemb _ _ ps => ps
  end.

Fixpoint flatten_config (cfg : config) : list process :=
  match cfg with
  | [] => []
  | m :: tl => memb_procs m ++ flatten_config tl
  end.

Compute flatten_config (fst T2).
Definition opAP1 : myOp := OpAP (CNew 0 1).

Definition moQ0 : var -> membrane_id := fun _ => 0.
Definition moO_to_1 : myOp -> membrane_id := fun _ => 1.

Definition TB :=
  gen_prog_loop_alg2 ([opAP1] : list myOp) moQ0 moO_to_1 empty_config 0.

Compute TB.
Compute flatten_config TB.

Definition cond0 : cbexp := CEq (BA 0) (Num 0).

Definition p_then : process := AP (CNew 0 1) PNil.
Definition p_else : process := PNil.

Definition opIF1 : myOp := OpIf cond0 p_then p_else.

Definition TC :=
  gen_prog_loop_alg2 ((opIF1 :: nil) : list myOp) moQ0 moO_to_1 empty_config 0.


Compute TC.
Compute flatten_config TC.

Definition opAP2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition seq2 : list myOp := [opAP1; opAP2].

Definition TD :=
  gen_prog_alg2 seq2 moQ0 moO_to_1.

Compute TD.
Compute flatten_config TD.
Compute diff_mem moQ0 (locus_myOp opAP1) 1.
Compute diff_mem (mem_up_smap moQ0 (diff_mem moQ0 (locus_myOp opAP1) 1) 1)
                (locus_myOp opAP2) 1.

(* ============================================================ *)
(* Tests for Algorithm 1                                         *)
(* ============================================================ *)

Definition cfgA : config := [Memb 0 []; Memb 1 []].

(* Simple: two ops share qubit 0 *)
Definition Aop1 : myOp := OpAP (CNew 0 1).
Definition Aop2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition AR1  : op_list := [Aop1; Aop2].

Definition AP1 : distributed_prog :=
  auto_disq_alg1_paper 2 2 AR1 cfgA.

Compute AP1.
Compute fit AP1.

Definition Aop3 : myOp := OpAP (CNew 1 1).
Definition Aop4 : myOp := OpDP (NewCh 7 1).
Definition AR2  : op_list := [Aop1; Aop3; Aop4; Aop2].

Definition AP2 : distributed_prog :=
  auto_disq_alg1_paper 3 3 AR2 cfgA.

Compute AP2.
Compute fit AP2.

(* ============================================================ *)
(* Tests for Algorithm 2                                         *)
(* ============================================================ *)

Definition seq0 : seq_relation := fun _ => 0.

Definition moO_all0 : op_mem_assign := fun _ => 0.
Definition moQ_all0 : qubit_mem_assign := fun _ => 0.

Definition P2A : distributed_prog :=
  gen_prog_paper seq0 moQ_all0 moO_all0 AR1.

Compute P2A.
Compute fit P2A.  

Definition moO_all1 : op_mem_assign := fun _ => 1.
Definition moQ_all0_again : qubit_mem_assign := fun _ => 0.

Definition P2B : distributed_prog :=
  gen_prog_paper seq0 moQ_all0_again moO_all1 AR1.

Compute P2B.
Compute fit P2B.  

Fixpoint flat_cfg (cfg : config) : list process :=
  match cfg with
  | [] => []
  | Memb _ ps :: tl => ps ++ flat_cfg tl
  | LockMemb _ _ ps :: tl => ps ++ flat_cfg tl
  end.

Compute flat_cfg P2A.
Compute flat_cfg P2B.




(* ============================================================ *)
(* Tests for Algorithm 3                                         *)
(* ============================================================ *)

Definition B1 : myOp := OpAP (CNew 0 1).
Definition B2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition B3 : myOp := OpAP (CNew 1 1).

Definition Bops : list myOp := [B1; B2; B3].

(* A custom hp that creates a cycle B1 <-> B2, and B2 -> B3 *)
Definition hpB : hb_relation :=
  fun a b =>
    orb
      (orb (andb (myOp_eqb a B1) (myOp_eqb b B2))
           (andb (myOp_eqb a B2) (myOp_eqb b B1)))
      (andb (myOp_eqb a B2) (myOp_eqb b B3)).

(* A seq that orders B1 then B2 then B3 *)
Definition seqB : seq_relation :=
  fun o =>
    if myOp_eqb o B1 then 0
    else if myOp_eqb o B2 then 1
    else 2.

Definition Rpar : list process :=
  auto_parallelize_alg3 myOp_eqb Bops hpB seqB.

Compute Rpar.


(* --------------------------------------------- *)
(* Example quantum program in your input format  *)
(* --------------------------------------------- *)

Definition q0 : var := 0.
Definition q1 : var := 1.

(* empty locus for “apply U on these qubits” — depends on your DisQSyntax meaning *)
Definition L : locus := ([] : locus).

(* exp programs (unitary-ish) *)
Definition eH_q0 : exp := H q0 (Num 0).
Definition eX_q1 : exp := X q1 (Num 0).

(* “Controlled-X on q1 controlled by q0”  *)
Definition eCX : exp := CU q0 (Num 0) eX_q1.

(* Wrap into cexp actions: CAppU locus exp *)
Definition appH_q0 : cexp := CAppU L eH_q0.
Definition appCX   : cexp := CAppU L eCX.

(* Allocate 1-qubit registers (your CNew takes x and n) *)
Definition new_q0 : cexp := CNew q0 1.
Definition new_q1 : cexp := CNew q1 1.

(* Measure q0 and q1 into classical x0 and x1 *)
Definition x0 : var := 10.
Definition x1 : var := 11.

Definition meas_q0 : cexp := CMeas x0 L.
Definition meas_q1 : cexp := CMeas x1 L.

(* Now the program as op_list *)
Definition Qprog : op_list :=
  [ OpAP new_q0;
    OpAP new_q1;
    OpAP appH_q0;
    OpAP appCX;
    OpAP meas_q0;
    OpAP meas_q1
  ].

Definition cfg2 : config := [Memb 0 []; Memb 1 []].
Definition Pbest : distributed_prog :=
  auto_disq_alg1_paper 3 3 Qprog cfg2.

Compute Pbest.
Compute fit Pbest.


Definition P_alg2 : distributed_prog :=
  gen_prog_paper seq0 moQ_all0 moO_all0 Qprog.

Compute P_alg2.
Compute fit P_alg2.

Definition moQ_start0 : qubit_mem_assign := fun _ => 0.


Definition P_reloc : distributed_prog :=
  gen_prog_paper seq0 moQ_start0 moO_all1 Qprog.

Compute P_reloc.
Compute fit P_reloc.


Definition P1_q : var := 0.
Definition P1_x : var := 10.

Definition P_1 : op_list :=
  [ OpAP (CNew P1_q 1);
    OpAP (CAppU L (H P1_q 0));
    OpAP (CMeas P1_x L)
  ].


(* Test harness *)


Definition moO0 : op_mem_assign := fun _ => 0.

Definition P_1_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_1.

Compute P_1_dist0.
Compute fit P_1_dist0.

Definition moO1 : op_mem_assign := fun _ => 1.

Definition P_1_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_1.

Compute P_1_dist1.
Compute fit P_1_dist1.

Definition P_2_q : var := 0.
Definition P_2_x : var := 10.

Definition P_2 : op_list :=
  [ OpAP (CNew P_2_q 1);
    OpAP (CAppU L (H P_2_q 0));
    OpAP (CAppU L (RZ 0 P_2_q 0));
    OpAP (CMeas P_2_x L)
  ].

Definition P_2_dist0 :=
  gen_prog_paper seq0 moQ0 moO0 P_2.

Compute P_2_dist0.
Compute fit P_2_dist0.

(* 6 membranes available *)
Definition cfg6 : config :=
  [ Memb 0 []; Memb 1 []; Memb 2 []; Memb 3 []; Memb 4 []; Memb 5 [] ].

(* initial location: all qubits start on membrane 0 *)


(* send all operations to a chosen membrane *)
Definition moO2 : op_mem_assign := fun _ => 2.
Definition moO3 : op_mem_assign := fun _ => 3.
Definition moO4 : op_mem_assign := fun _ => 4.
Definition moO5 : op_mem_assign := fun _ => 5.

(* Algorithm 2 placement tests for P_1 *)
Definition P_1_dist2 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO2 P_1.
Compute P_1_dist2.
Compute fit P_1_dist2.

Definition P_1_dist3 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO3 P_1.
Compute P_1_dist3.
Compute fit P_1_dist3.

Definition P_1_dist4 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO4 P_1.
Compute P_1_dist4.
Compute fit P_1_dist4.

Definition P_1_dist5 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO5 P_1.
Compute P_1_dist5.
Compute fit P_1_dist5.

Definition P_3_q0 : var := 0.
Definition P_3_q1 : var := 1.
Definition P_3_q2 : var := 2.

Definition P_3_x0 : var := 10.
Definition P_3_x1 : var := 11.
Definition P_3_x2 : var := 12.

(* CNOT-like: control P_3_q0, apply X on target *)
Definition CX_01 : exp := CU P_3_q0 0 (X P_3_q1 0).
Definition CX_02 : exp := CU P_3_q0 0 (X P_3_q2 0).

Definition P_3 : op_list :=
  [ OpAP (CNew P_3_q0 1);
    OpAP (CNew P_3_q1 1);
    OpAP (CNew P_3_q2 1);

    OpAP (CAppU L (H P_3_q0 0));
    OpAP (CAppU L CX_01);
    OpAP (CAppU L CX_02);

    OpAP (CMeas P_3_x0 L);
    OpAP (CMeas P_3_x1 L);
    OpAP (CMeas P_3_x2 L)
  ].


Definition P_3_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_3.

Compute P_3_dist0.
Compute fit P_3_dist0.


Definition P_3_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_3.

Compute P_3_dist1.
Compute fit P_3_dist1.

(* QFT *)

Definition P_4_q : var := 0.
Definition P_4_n : nat := 3.
Definition P_4_x : var := 10.

Definition P_4 : op_list :=
  [ OpAP (CNew P_4_q 1);
    OpAP (CAppU L (H P_4_q 0));
    OpAP (CAppU L (QFT P_4_q P_4_n));
    OpAP (CAppU L (RQFT P_4_q P_4_n));
    OpAP (CMeas P_4_x L)
  ].



Definition P_4_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_4.

Compute P_4_dist0.
Compute fit P_4_dist0.


Definition P_4_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_4.

Compute P_4_dist1.
Compute fit P_4_dist1.


Definition P_4_dist5 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO5 P_4.

Compute P_4_dist5.
Compute fit P_4_dist5.

(* ============================================================ *)
(* P_5 : 2-qubit Grover (one iteration)                          *)
(* ============================================================ *)

Definition P_5_q0 : var := 0.
Definition P_5_q1 : var := 1.
Definition P_5_x0 : var := 10.
Definition P_5_x1 : var := 11.

(* a symbolic “pi phase” parameter  *)
Definition theta_pi : nat := 1.

(* Controlled phase-like oracle: control q0, apply RZ on q1 *)
Definition ORACLE_01 : exp := CU P_5_q0 0 (RZ 0 P_5_q1 theta_pi).

(* Diffusion (in the usual circuit form): H,H; X,X; controlled-phase; X,X; H,H *)
Definition P_5 : op_list :=
  [ OpAP (CNew P_5_q0 1);
    OpAP (CNew P_5_q1 1);

    (* Prepare uniform superposition *)
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));

    (* Oracle (phase flip on marked state, here approximated by ORACLE_01) *)
    OpAP (CAppU L ORACLE_01);

    (* Diffusion *)
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));
    OpAP (CAppU L (X P_5_q0 0));
    OpAP (CAppU L (X P_5_q1 0));
    OpAP (CAppU L ORACLE_01);
    OpAP (CAppU L (X P_5_q0 0));
    OpAP (CAppU L (X P_5_q1 0));
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));

    (* Measure *)
    OpAP (CMeas P_5_x0 L);
    OpAP (CMeas P_5_x1 L)
  ].


Definition P_5_dist0 := gen_prog_paper seq0 moQ0 moO0 P_5.
Compute P_5_dist0.
Compute fit P_5_dist0.

Definition P_5_dist5 := gen_prog_paper seq0 moQ0 moO5 P_5.
Compute P_5_dist5.
Compute fit P_5_dist5.


(* ============================================================ *)
(* P_6 : Quantum teleportation                                  *)
(* ============================================================ *)

Definition P_6_qs : var := 0.   (* source qubit to teleport *)
Definition P_6_qa : var := 1.   (* Alice half of EPR *)
Definition P_6_qb : var := 2.   (* Bob half of EPR (target) *)

Definition P_6_m1 : var := 10.  (* classical measurement bit from qs *)
Definition P_6_m2 : var := 11.  (* classical measurement bit from qa *)

(* Build the usual CNOTs  *)
Definition CNOT_a_b : exp := CU P_6_qa 0 (X P_6_qb 0).
Definition CNOT_s_a : exp := CU P_6_qs 0 (X P_6_qa 0).

(* “Z correction” approximated via RZ(pi) on qb *)
Definition Zcorr_qb : exp := RZ 0 P_6_qb theta_pi.
Definition Xcorr_qb : exp := X  P_6_qb 0.

(* Processes used in OpIf branches *)
Definition proc_Xcorr : process := AP (CAppU L Xcorr_qb) PNil.
Definition proc_Zcorr : process := AP (CAppU L Zcorr_qb) PNil.

Definition P_6 : op_list :=
  [ (* Allocate qubits *)
    OpAP (CNew P_6_qs 1);
    OpAP (CNew P_6_qa 1);
    OpAP (CNew P_6_qb 1);

    (* Prepare an example “unknown” state on qs *)
    OpAP (CAppU L (H P_6_qs 0));

    (* Create EPR pair between qa and qb *)
    OpAP (CAppU L (H P_6_qa 0));
    OpAP (CAppU L CNOT_a_b);

    (* Bell measurement on (qs, qa) *)
    OpAP (CAppU L CNOT_s_a);
    OpAP (CAppU L (H P_6_qs 0));

    OpAP (CMeas P_6_m1 L);
    OpAP (CMeas P_6_m2 L);

    OpIf (CEq (BA P_6_m2) (Num 1)) proc_Xcorr PNil;
    OpIf (CEq (BA P_6_m1) (Num 1)) proc_Zcorr PNil

  ].

Definition P_6_dist0 := gen_prog_paper seq0 moQ0 moO0 P_6.
Compute P_6_dist0.
Compute fit P_6_dist0.

Definition P_6_dist5 := gen_prog_paper seq0 moQ0 moO5 P_6.
Compute P_6_dist5.
Compute fit P_6_dist5.

(* ============================================================ *)
(* FULL TEST: Shor-like period finding + factor extraction test  *)
(* ============================================================ *)

From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.



Inductive myOp : Type :=
| OpAP  (a : cexp)
| OpDP  (a : cdexp)
| OpIf  (b : cbexp) (p q : process).

Definition op_list : Type := list myOp.

(* ------------------------------------------------------------ *)
(* Test instance: N=15, a=2                        *)
(* ------------------------------------------------------------ *)
Definition N : nat := 15.
Definition a : nat := 2.

(* Use t=8 phase bits like your earlier Shor skeleton *)
Definition t_phase : nat := 8.

(* Work register: we will use only 2 qubits (mod 4 period oracle) *)
Definition w0 : var := 20.
Definition w1 : var := 21.
Definition work_qubits : list var := [w0; w1].

(* Phase qubits: 0..7 contiguous so RQFT q0 8 works *)
Definition q2 : var := 2.  Definition q3 : var := 3.
Definition q4 : var := 4.  Definition q5 : var := 5.
Definition q6 : var := 6.  Definition q7 : var := 7.
Definition phase_qubits : list var := [q0;q1;q2;q3;q4;q5;q6;q7].

(* Classical measurement outputs for the phase register *)
Definition c0 : var := 100. Definition c1 : var := 101.
Definition c2 : var := 102. Definition c3 : var := 103.
Definition c4 : var := 104. Definition c5 : var := 105.
Definition c6 : var := 106. Definition c7 : var := 107.
Definition phase_bits : list var := [c0;c1;c2;c3;c4;c5;c6;c7].

(* ------------------------------------------------------------ *)
(* Helpers: allocation / H / measurement                         *)
(* ------------------------------------------------------------ *)
Fixpoint alloc_qubits (qs : list var) : op_list :=
  match qs with
  | [] => []
  | q :: tl => OpAP (CNew q 1) :: alloc_qubits tl
  end.

Fixpoint apply_H_all (qs : list var) : op_list :=
  match qs with
  | [] => []
  | q :: tl => OpAP (CAppU L (H q (Num 0))) :: apply_H_all tl
  end.

Fixpoint meas_all (xs : list var) : op_list :=
  match xs with
  | [] => []
  | x :: tl => OpAP (CMeas x L) :: meas_all tl
  end.

(* ------------------------------------------------------------ *)
(* A REAL, EXECUTABLE oracle : INC mod 4 on (w1 w0)         *)
(* Period is exactly 4.                                         *)
(*   INC: flip LSB (w0), then if w0==0 (i.e. carry) flip MSB.    *)
(* Using your CU + X, a standard reversible incrementer is:      *)
(*   X w0 ; CU w0 (Num 0) (X w1 (Num 0))                         *)
(* This gives a 4-cycle on 2-bit states -> period 4.             *)
(* ------------------------------------------------------------ *)

Definition INC_mod4 : exp :=
  Seq (X w0 (Num 0))
      (CU w0 (Num 0) (X w1 (Num 0))).

Fixpoint repeat_exp (n : nat) (e : exp) : exp :=
  match n with
  | 0 => SKIP 0 (Num 0) (* harmless no-op in your exp grammar *)
  | S n' => Seq e (repeat_exp n' e)
  end.

Definition pow2 (k : nat) : nat := Nat.pow 2 k.

(* “U^(2^k)” for our toy U = INC_mod4 *)
Definition UModExpPow (a N k : nat) (_ws : list var) : exp :=
  repeat_exp (pow2 k) INC_mod4.

Definition controlled_pow (control : var) (k : nat) : op_list :=
  [ OpAP (CAppU L (CU control (Num 0) (UModExpPow a N k work_qubits))) ].

Fixpoint qpe_controlled_pows (qs : list var) (k : nat) : op_list :=
  match qs with
  | [] => []
  | q :: tl => controlled_pow q k ++ qpe_controlled_pows tl (S k)
  end.

Definition inv_qft_phase : op_list :=
  [ OpAP (CAppU L (RQFT q0 t_phase)) ].

(* ------------------------------------------------------------ *)
(* The “Shor/QPE program” we will test structurally              *)
(* ------------------------------------------------------------ *)
Definition Shor_QPE_prog : op_list :=
  alloc_qubits phase_qubits ++
  alloc_qubits work_qubits ++
  apply_H_all phase_qubits ++
  qpe_controlled_pows phase_qubits 0 ++
  inv_qft_phase ++
  meas_all phase_bits.

(* ------------------------------------------------------------ *)
(* Structural tests              *)
(* ------------------------------------------------------------ *)

(* Count how many controlled powers were generated: should be t_phase = 8. *)
Fixpoint count_controlled (ops : op_list) : nat :=
  match ops with
  | [] => 0
  | OpAP (CAppU _ (CU _ _ _)) :: tl => S (count_controlled tl)
  | _ :: tl => count_controlled tl
  end.

Example test_controlled_count :
  count_controlled Shor_QPE_prog = t_phase.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------ *)
(* Classical postprocessing test             *)
(* ------------------------------------------------------------ *)



Program Fixpoint gcd (x y : nat) {measure y} : nat :=
  match y with
  | 0 => x
  | _ => gcd y (Nat.modulo x y)
  end.
Next Obligation.
  apply Nat.mod_upper_bound.
  lia.
Qed.

(* pow_mod (small, fine for this test) *)
Fixpoint pow_mod (a e n : nat) : nat :=
  match e with
  | 0 => 1 mod n
  | S e' => Nat.modulo (a * pow_mod a e' n) n
  end.


Definition two_pow (t : nat) : nat := Nat.pow 2 t.

Fixpoint find_period_exact_from (m t r fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      if Nat.eqb (Nat.modulo (m * r) (two_pow t)) 0
      then r
      else find_period_exact_from m t (S r) fuel'
  end.

Definition find_period_exact (m t Rmax : nat) : nat :=
  find_period_exact_from m t 1 Rmax.


Definition shor_factors_from_r (a N r : nat) : (nat * nat) :=
  if Nat.even r then
    let x := pow_mod a (Nat.div r 2) N in
    let f1 := Nat.gcd (Nat.sub x 1) N in
    let f2 := Nat.gcd (x + 1) N in
    (f1, f2)
  else (1, N).



(* Ideal Shor test case for N=15,a=2:
   The true order is r=4, and QPE ideally can output m = 2^t / 4 = 256/4 = 64 (for s=1).
*)
Definition m_ideal : nat := 64.

Example test_period_is_4 :
  find_period_exact m_ideal t_phase 16 = 4.
Proof. reflexivity. Qed.

Example test_factors_are_3_and_5 :
  shor_factors_from_r a N 4 = (3, 5).
Proof. reflexivity. Qed.


(* ============================================================ *)
(* Shor period-finding ( N=15, a=2, r=4)                     *)
(* Written exactly in op_list style like Qprog                  *)
(* ============================================================ *)


(* ---------------------------- *)
(* Qubit ids                    *)
(* ---------------------------- *)

(* Phase register (3 qubits for demo) *)
Definition p0 : var := 0.
Definition p1 : var := 1.
Definition p2 : var := 2.

(* Work register (2 qubits → period 4 oracle) *)


(* Classical measurement outputs *)
Definition m0 : var := 100.
Definition m1 : var := 101.
Definition m2 : var := 102.

(* ---------------------------- *)
(* Allocate qubits              *)
(* ---------------------------- *)

Definition new_p0 : cexp := CNew p0 1.
Definition new_p1 : cexp := CNew p1 1.
Definition new_p2 : cexp := CNew p2 1.

Definition new_w0 : cexp := CNew w0 1.
Definition new_w1 : cexp := CNew w1 1.

(* ---------------------------- *)
(* Hadamards on phase register  *)
(* ---------------------------- *)

Definition appH_p0 : cexp := CAppU L (H p0 (Num 0)).
Definition appH_p1 : cexp := CAppU L (H p1 (Num 0)).
Definition appH_p2 : cexp := CAppU L (H p2 (Num 0)).

(* ---------------------------- *)
(* Toy oracle: INC mod 4        *)
(* Period = 4                   *)
(* ---------------------------- *)


(* Controlled powers U^(2^k) *)

Definition CU_p0 : cexp :=
  CAppU L (CU p0 (Num 0) INC_mod4).

Definition CU_p1 : cexp :=
  CAppU L (CU p1 (Num 0)
            (Seq INC_mod4 INC_mod4)).   (* U^2 *)

Definition CU_p2 : cexp :=
  CAppU L (CU p2 (Num 0)
            (Seq INC_mod4
                 (Seq INC_mod4
                      (Seq INC_mod4 INC_mod4)))).  (* U^4 *)

(* ---------------------------- *)
(* Inverse QFT on phase register *)
(* ---------------------------- *)

Definition appRQFT : cexp :=
  CAppU L (RQFT p0 3).

(* ---------------------------- *)
(* Measurements                 *)
(* ---------------------------- *)

Definition meas_p0 : cexp := CMeas m0 L.
Definition meas_p1 : cexp := CMeas m1 L.
Definition meas_p2 : cexp := CMeas m2 L.

Require Import DisQ.AUTO.
Import AUTO.

(* ============================================================ *)
(* The program as op_list   *)
(* ============================================================ *)

Definition Shor_Qprog : op_list :=
  [ OpAP new_p0;
    OpAP new_p1;
    OpAP new_p2;

    OpAP new_w0;
    OpAP new_w1;

    OpAP appH_p0;
    OpAP appH_p1;
    OpAP appH_p2;

    OpAP CU_p0;
    OpAP CU_p1;
    OpAP CU_p2;

    OpAP appRQFT;

    OpAP meas_p0;
    OpAP meas_p1;
    OpAP meas_p2
  ].

(* ============================================================ *)
(* Tests for Shor_Qprog              *)
(* ============================================================ *)

(* --- All qubits and operations on membrane 0 --- *)

Definition Shor_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 Shor_Qprog.

Compute Shor_dist0.
Compute fit Shor_dist0.


(* --- All operations forced to membrane 1 --- *)

Definition Shor_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 Shor_Qprog.

Compute Shor_dist1.
Compute fit Shor_dist1.


(* --- Force everything to membrane 2 --- *)

Definition Shor_dist2 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO2 Shor_Qprog.

Compute Shor_dist2.
Compute fit Shor_dist2.


(* --- Force everything to membrane 3 --- *)

Definition Shor_dist3 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO3 Shor_Qprog.

Compute Shor_dist3.
Compute fit Shor_dist3.


(* --- Force everything to membrane 5 --- *)

Definition Shor_dist5 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO5 Shor_Qprog.

Compute Shor_dist5.
Compute fit Shor_dist5.




























From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Inductive myOp : Type :=
| OpAP  (a : cexp)                         
| OpDP  (a : cdexp)                       
| OpIf  (b : cbexp) (p q : process). 

Definition op_list : Type := list myOp.
Definition hb_relation : Type := myOp -> myOp -> bool.
Definition rank         : Type := nat.
Definition seq_relation : Type := myOp -> rank.
Definition op_mem_assign : Type := myOp -> membrane_id.

Print aexp.
Print cbexp.
Print locus.
Fixpoint list_eqb {A : Type} (beq : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => andb (beq x y) (list_eqb beq xs' ys')
  | _, _ => false
  end.

Fixpoint aexp_eqb (e1 e2 : aexp) : bool :=
  match e1, e2 with
  | BA x1, BA x2 => Nat.eqb x1 x2
  | Num n1, Num n2 => Nat.eqb n1 n2
  | APlus a1 b1, APlus a2 b2 =>
      andb (aexp_eqb a1 a2) (aexp_eqb b1 b2)
  | AMult a1 b1, AMult a2 b2 =>
      andb (aexp_eqb a1 a2) (aexp_eqb b1 b2)
  | _, _ => false
  end.

Definition cbexp_eqb (b1 b2 : cbexp) : bool :=
  match b1, b2 with
  | CEq x1 y1, CEq x2 y2 =>
      andb (aexp_eqb x1 x2) (aexp_eqb y1 y2)
  | CLt x1 y1, CLt x2 y2 =>
      andb (aexp_eqb x1 x2) (aexp_eqb y1 y2)
  | _, _ => false
  end.

Definition bound_eqb (b1 b2 : bound) : bool :=
  match b1, b2 with
  | BVar v1 n1, BVar v2 n2 =>
      andb (Nat.eqb v1 v2) (Nat.eqb n1 n2)
  | BNum n1, BNum n2 =>
      Nat.eqb n1 n2
  | _, _ => false
  end.

Definition range_eqb (r1 r2 : range) : bool :=
  match r1, r2 with
  | (x1, lo1, hi1), (x2, lo2, hi2) =>
      andb (Nat.eqb x1 x2)
           (andb (bound_eqb lo1 lo2)
                 (bound_eqb hi1 hi2))
  end.

Definition locus_eqb (l1 l2 : locus) : bool :=
  list_eqb range_eqb l1 l2.

Fixpoint exp_eqb (e1 e2 : exp) : bool :=
  match e1, e2 with
  | SKIP x1 a1, SKIP x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | X x1 a1, X x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | CU x1 a1 e1', CU x2 a2 e2' =>
      andb (Nat.eqb x1 x2) (andb (aexp_eqb a1 a2) (exp_eqb e1' e2'))
  | RZ q1 x1 a1, RZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2) (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | RRZ q1 x1 a1, RRZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2) (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | SR q1 x1, SR q2 x2 =>
      andb (Nat.eqb q1 q2) (Nat.eqb x1 x2)
  | SRR q1 x1, SRR q2 x2 =>
      andb (Nat.eqb q1 q2) (Nat.eqb x1 x2)
  | QFT x1 b1, QFT x2 b2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb b1 b2)
  | RQFT x1 b1, RQFT x2 b2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb b1 b2)
  | H x1 a1, H x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | Addto x1 q1, Addto x2 q2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb q1 q2)
  | Seq s1 t1, Seq s2 t2 =>
      andb (exp_eqb s1 s2) (exp_eqb t1 t2)
  | _, _ => false
  end.

Definition cexp_eqb (c1 c2 : cexp) : bool :=
  match c1, c2 with
  | CNew x1 n1, CNew x2 n2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb n1 n2)
  | CAppU l1 e1, CAppU l2 e2 =>
      andb (locus_eqb l1 l2) (exp_eqb e1 e2)
  | CMeas x1 k1, CMeas x2 k2 =>
      andb (Nat.eqb x1 x2) (locus_eqb k1 k2)
  | _, _ => false
  end.

Definition cdexp_eqb (d1 d2 : cdexp) : bool :=
  match d1, d2 with
  | NewCh c1 n1, NewCh c2 n2 =>
      andb (Nat.eqb c1 c2) (Nat.eqb n1 n2)
  | Send c1 a1, Send c2 a2 =>
      andb (Nat.eqb c1 c2) (aexp_eqb a1 a2)
  | Recv c1 x1, Recv c2 x2 =>
      andb (Nat.eqb c1 c2) (Nat.eqb x1 x2)
  | _, _ => false
  end.

Fixpoint process_eqb (p1 p2 : process) : bool :=
  match p1, p2 with
  | PNil, PNil => true
  | AP a1 p1', AP a2 p2' =>
      andb (cexp_eqb a1 a2) (process_eqb p1' p2')
  | DP a1 p1', DP a2 p2' =>
      andb (cdexp_eqb a1 a2) (process_eqb p1' p2')
  | PIf b1 p1a p1b, PIf b2 p2a p2b =>
      andb (cbexp_eqb b1 b2)
           (andb (process_eqb p1a p2a) (process_eqb p1b p2b))
  | _, _ => false
  end.



Definition myOp_eqb (x y : myOp) : bool :=
  match x, y with
  | OpAP a1, OpAP a2 => cexp_eqb a1 a2
  | OpDP a1, OpDP a2 => cdexp_eqb a1 a2
  | OpIf b1 p1 q1, OpIf b2 p2 q2 =>
      andb (cbexp_eqb b1 b2)
           (andb (process_eqb p1 p2) (process_eqb q1 q2))
  | _, _ => false
  end.

Definition qubit_mem_assign : Type := var -> membrane_id.

Definition fitness_value    : Type := nat.
Definition distributed_prog : Type := config.



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

Scheme Equality for exp.

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
(*                     os <- gen_os(R)                                  *)
(* ------------------------------------------------------------------------- *)
Definition gen_os (R : op_list) : op_list := R.

(* ------------------------------------------------------------------------- *)
(* Paper Algorithm 1 line 3: hp <- gen_hp(R)                                  *)
(* You used: order-in-R + share_qubit => dependency.                          *)
(* ------------------------------------------------------------------------- *)

Fixpoint index_of_exp (x : exp) (xs : list exp) : nat :=
  match xs with
  | [] => 0
  | y :: tl => if exp_eqb x y then 0 else S (index_of_exp x tl)
  end.

Fixpoint vars_of_aexp (a : aexp) : list var :=
  match a with
  | BA x => [x]
  | Num _ => []
  | APlus a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  | AMult a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  end.

Definition vars_of_cbexp (b : cbexp) : list var :=
  match b with
  | CEq a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  | CLt a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  end.


Definition vars_of_myOp (op : myOp) : list var :=
  match op with
  | OpAP a =>
      match a with
      | CAppU _ e => vars_of_exp e
      | CNew x _ => [x]
      | CMeas x _ => [x]
      end
  | OpDP a =>
      match a with
      | NewCh c _ => [c]
      | Send c e => c :: vars_of_aexp e
      | Recv c x => [c; x]
      end
  | OpIf b _ _ =>
      vars_of_cbexp b
  end.

Definition share_qubit_myOp (o1 o2 : myOp) : bool :=
  negb (Nat.eqb
          (length
             (intersect
                (uniq (vars_of_myOp o1))
                (uniq (vars_of_myOp o2))))
          0).

Fixpoint index_of_myOp (x : myOp) (xs : list myOp) : nat :=
  match xs with
  | [] => 0
  | y :: tl =>
      if myOp_eqb x y
      then 0
      else S (index_of_myOp x tl)
  end.

Definition gen_hp (R : op_list) : hb_relation :=
  fun o1 o2 =>
    let i := index_of_myOp o1 R in
    let j := index_of_myOp o2 R in
    andb (Nat.ltb i j) (share_qubit_myOp o1 o2).


(* ------------------------------------------------------------------------- *)
(*                         MANY schedules                                    *)
(* ------------------------------------------------------------------------- *)
Definition has_incoming_from
  (hp : hb_relation)
  (nodes : list myOp)
  (x : myOp) : bool :=
  existsb (fun y => hp y x) nodes.

Definition available
  (hp : hb_relation)
  (nodes : list myOp) : list myOp :=
  filter (fun x => negb (has_incoming_from hp nodes x)) nodes.

Fixpoint nth_default {A} (d : A) (xs : list A) (n : nat) : A :=
  match n with
  | 0 =>
      match xs with
      | [] => d
      | x :: _ => x
      end
  | S n' =>
      match xs with
      | [] => d
      | _ :: tl => nth_default d tl n'
      end
  end.



(* ---------------- Permutations ---------------- *)

Fixpoint insert_all (x : myOp) (xs : list myOp) : list (list myOp) :=
  match xs with
  | [] => [[x]]
  | y :: tl =>
      (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations (xs : list myOp) : list (list myOp) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.


(* ---------------- Check if an order respects hp ---------------- *)

(* "order respects hp" iff there is no edge from a later op to an earlier op.
   Equivalent: for each x, no y in the suffix has hp y x = true. *)

Fixpoint respects_hp (hp : hb_relation) (order : list myOp) : bool :=
  match order with
  | [] => true
  | x :: tl =>
      let ok_x := forallb (fun y => negb (hp y x)) tl in
      andb ok_x (respects_hp hp tl)
  end.
(* ---------------- Return at most k valid schedules ---------------- *)

Definition topo_orders_k
  (hp : hb_relation)
  (nodes : list myOp)
  (k : nat)
  : list (list myOp) :=
  let perms := permutations nodes in
  let good  := filter (respects_hp hp) perms in
  firstn k good.

Definition seq_from_order (order : list myOp) : seq_relation :=
  fun o => index_of_myOp o order.


(*  seq <- gen_seq(S,hp) *)

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
      let order := nth_default ([] : list myOp) schedules idx in
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

Definition mem_count (cfg : config) : nat :=
  length cfg.

Definition nth_mid_default (cfg : config) (i : nat) : membrane_id :=
  match cfg with
  | [] => default_mid
  | _ =>
      match nth_error cfg i with
      | Some (Memb l _) => l
      | Some (LockMemb l _ _) => l
      | None => first_mid cfg
      end
  end.


(* ------------------------------------------------------------------------- *)
(* A total “hash” for exp (for deterministic membrane choice tables)          *)
(* ------------------------------------------------------------------------- *)


Fixpoint sum_vars (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: tl => x + sum_vars tl
  end.

Definition myOp_tag (o : myOp) : nat :=
  match o with
  | OpAP a =>
      match a with
      | CNew _ _ => 1
      | CAppU _ _ => 2
      | CMeas _ _ => 3
      end
  | OpDP a =>
      match a with
      | NewCh _ _ => 4
      | Send _ _  => 5
      | Recv _ _  => 6
      end
  | OpIf _ _ _ => 7
  end.

(* Hash for myOp *)
Definition myOp_hash (o : myOp) : nat :=
  myOp_tag o + sum_vars (vars_of_myOp o).

(* ------------------------------------------------------------------------- *)
(*                        gen_mem                                           *)
(* ------------------------------------------------------------------------- *)
Definition subset_vars (xs ys : list var) : bool :=
  forallb (fun x => mem_var x ys) xs.

Definition overlap_big (xs ys : list var) : bool :=
  let xs' := uniq xs in
  let ys' := uniq ys in
  let inter := length (intersect xs' ys') in
  let denom := Nat.max 1 (Nat.max (length xs') (length ys')) in
  Nat.leb (Nat.div denom 2) inter. (* >= half overlap *)

Fixpoint insert_by_seq (seq : seq_relation) (op : myOp) (ops : list myOp) : list myOp :=
  match ops with
  | [] => [op]
  | x :: tl =>
      if Nat.leb (seq op) (seq x) then op :: x :: tl
      else x :: insert_by_seq seq op tl
  end.

Fixpoint sort_by_seq (seq : seq_relation) (ops : list myOp) : list myOp :=
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
  (cfg : config) (seed : nat) (ops_sorted : list myOp)
  (prev : option (myOp * membrane_id))
  (tbl : list (nat * membrane_id)) : list (nat * membrane_id) :=
  match ops_sorted with
  | [] => tbl
  | op :: tl =>
      let mid :=
        match prev with
        | None => choose_mid cfg seed (myOp_hash op)
        | Some (op_prev, mid_prev) =>
            let vars := uniq (vars_of_myOp op) in
            let vars_prev := uniq (vars_of_myOp op_prev) in
            if orb (subset_vars vars vars_prev) (overlap_big vars vars_prev)
            then mid_prev
            else choose_mid cfg seed (myOp_hash op)
        end
      in
      build_moO cfg seed tl (Some (op, mid)) ((myOp_hash op, mid) :: tbl)
  end.

Fixpoint lookup_mid (h : nat) (tbl : list (nat * membrane_id)) : membrane_id :=
  match tbl with
  | [] => default_mid
  | (k,v) :: tl => if Nat.eqb k h then v else lookup_mid h tl
  end.

Definition moO_of_tbl (tbl : list (nat * membrane_id)) : op_mem_assign :=
  fun op => lookup_mid (myOp_hash op) tbl.

Fixpoint first_use_mid
  (ops_sorted : list myOp) (moO : op_mem_assign) (q : var) : membrane_id :=
  match ops_sorted with
  | [] => default_mid
  | op :: tl =>
      if mem_var q (vars_of_myOp op) then moO op else first_use_mid tl moO q
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
(*                              gen_prog                             *)
(* ------------------------------------------------------------------------- *)
Definition mk_reloc (src dst : membrane_id) : exp :=
  SKIP src (Num dst).

(* Convert a myOp into a process we can store in a membrane *)
Definition myOp_to_process (op : myOp) : process :=
  match op with
  | OpAP a => AP a PNil
  | OpDP a => DP a PNil
  | OpIf b p q => PIf b p q
  end.

(* Relocation step is encoded as a local action that applies SKIP src (Num dst) *)
Definition reloc_process (src dst : membrane_id) : process :=
  AP (CAppU ([] : locus) (mk_reloc src dst)) PNil.

Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : myOp) : config :=
  match cfg with
  | [] => [Memb mid [myOp_to_process op]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [myOp_to_process op]) :: tl
      else Memb l ps :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [myOp_to_process op]) :: tl
      else LockMemb l r ps :: place_operation tl mid op
  end.

Fixpoint place_reloc (cfg : config) (mid : membrane_id) (src dst : membrane_id) : config :=
  match cfg with
  | [] => [Memb mid [reloc_process src dst]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [reloc_process src dst]) :: tl
      else Memb l ps :: place_reloc tl mid src dst
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [reloc_process src dst]) :: tl
      else LockMemb l r ps :: place_reloc tl mid src dst
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

Fixpoint all_qubits (ops : list myOp) : list var :=
  match ops with
  | [] => []
  | op :: tl => vars_of_myOp op ++ all_qubits tl
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
        let acc'  := place_reloc acc target cur target in
        let qloc' := qloc_update q target qloc in
        ensure_qubits tl target qloc' acc'
  end.

Fixpoint gen_prog_core
  (moO : op_mem_assign) (moQ : qubit_mem_assign)
  (ops_sorted : list myOp)
  (qloc : qloc_tbl)
  (acc  : config) : config :=
  match ops_sorted with
  | [] => acc
  | op :: tl =>
      let target := moO op in
      let qs := uniq (vars_of_myOp op) in
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
(* fit: relocation-aware cost                                         *)
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

(* Extract all exp that appear in local actions CAppU inside a process *)
Fixpoint extract_exps_from_proc (p : process) : list exp :=
  match p with
  | PNil => []
  | AP a p' =>
      match a with
      | CAppU _ e => e :: extract_exps_from_proc p'
      | _ => extract_exps_from_proc p'
      end
  | DP _ p' => extract_exps_from_proc p'
  | PIf _ p1 p2 => extract_exps_from_proc p1 ++ extract_exps_from_proc p2
  end.

Fixpoint extract_all_exps (cfg : config) : list exp :=
  match cfg with
  | [] => []
  | Memb _ ps :: tl =>
      concat (map extract_exps_from_proc ps) ++ extract_all_exps tl
  | LockMemb _ _ ps :: tl =>
      concat (map extract_exps_from_proc ps) ++ extract_all_exps tl
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

(* Keep only cases not already in S *)
Fixpoint filter_fresh (all : list case) (seen : list case) : list case :=
  match all with
  | [] => []
  | c :: tl =>
      if mem_case c seen then filter_fresh tl seen
      else c :: filter_fresh tl seen
  end.
(* candidate element stores: id + the actual functions (seq, mo) *)
Definition candidate : Type :=
  (case * (seq_relation * (op_mem_assign * qubit_mem_assign)))%type.

Definition seen_cases (S : list candidate) : list case :=
  map fst S.

(* are_still_cases(S) *)
Definition are_still_cases_cases (seen : list case) (ALL : list case) : bool :=
  match filter_fresh ALL seen with
  | [] => false
  | _  => true
  end.

Definition pick_case (S : list case) (ALL : list case) : option case :=
  match filter_fresh ALL S with
  | [] => None
  | c :: _ => Some c
  end.

(* gen_seq(S,hp) *)
Definition gen_seq
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (ALL  : list case)
  (S    : list candidate)
  : option (case * seq_relation) :=
  match pick_case (seen_cases S) ALL with
  | None => None
  | Some c =>
      let sched_i := fst c in
      let seq := gen_seq_many Kseq sched_i hp os in
      Some (c, seq)
  end.

(* gen_mem(S,L,seq) *)
Definition gen_mem
  (cfg  : config)  
  (seq  : seq_relation)
  (os   : op_list)
  (c    : case)     
  : op_mem_assign * qubit_mem_assign :=
  let seed := snd c in
  gen_mem_seed seed cfg seq os.



(*  while-loop:
   S ← ∅
   while are_still_cases(S) do ... S ← {(seq,mo)} ∪ S *)


Fixpoint auto_disq_loop
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (cfg  : config)
  (ALL  : list case)
  (S    : list candidate)        
  (Qbest: distributed_prog)
  (zmin : fitness_value)
  (fuel : nat)                
  : distributed_prog :=
  match fuel with
  | 0 => Qbest
  | S fuel' =>
      
      if are_still_cases_cases (seen_cases S) ALL then
        match gen_seq Kseq hp os ALL S with
        | None => Qbest   
        | Some (c, seq) =>
            let '(moO, moQ) := gen_mem cfg seq os c in
            let P := gen_prog seq moO moQ os in
            let z := fit P in
          
            let S' : list candidate := (c, (seq, (moO, moQ))) :: S in
            if Nat.ltb z zmin
            then auto_disq_loop Kseq hp os cfg ALL S' P z fuel'
            else auto_disq_loop Kseq hp os cfg ALL S' Qbest zmin fuel'
        end
      else
        Qbest
  end.

Definition auto_disq_alg1_paper
  (Kseq : nat)
  (Kmem : nat)
  (R    : op_list)
  (cfg  : config)
  : distributed_prog :=
  let hp := gen_hp R in
  let os := gen_os R in
  let ALL := mk_cases Kseq Kmem in
  (* S ← ∅ *)
  auto_disq_loop Kseq hp os cfg ALL [] ([] : config) INF_SCORE (length ALL).


(*    *)

(* S' is a list of (qubit, src_membrane) that need relocation to l *)
Definition Smap : Type := list (var * membrane_id).
Definition locus_myOp (op : myOp) : list var := vars_of_myOp op.

Definition diff_mem
  (mo_cur : var -> membrane_id)
  (qs : list var)
  (l  : membrane_id)
  : Smap :=
  fold_right
    (fun q acc =>
       let src := mo_cur q in
       if var_eqb src l then acc else (q, src) :: acc)
    [] qs.

(* update mo_cur for all qubits mentioned in S' to now be in l *)
Fixpoint mem_up_smap
  (mo_cur : var -> membrane_id)
  (S : Smap)
  (l : membrane_id)
  : var -> membrane_id :=
  match S with
  | [] => mo_cur
  | (q,_) :: tl =>
      let mo_cur' := fun x => if var_eqb x q then l else mo_cur x in
      mem_up_smap mo_cur' tl l
  end.


(* Paper line 11: insert_send(P, S', name)
   Minimal: no-op OR record “send intention”.
   Here: we insert relocation markers to target l later, so we do nothing now. *)

Fixpoint insert_send
  (P : config)
  (Sp : Smap)
  (name : nat)
  : config * nat * (list (var * var)) :=
  match Sp with
  | [] =>
      (P, name, [])

  | (q, src) :: tl =>
      (* fresh channel id *)
      let c : var := name in
      (* fresh alias variable for q after receiving *)
      let alias : var := S name in

      (* insert Send(c, q) on membrane src *)
      let P1 :=
        place_operation
          P
          src
          (OpDP (Send c (BA q))) in

      (* recurse with name advanced by 2 (we consumed c and alias) *)
      let '(P2, name2, m') :=
        insert_send P1 tl (name + 2) in

      (* record renaming map: q ↦ alias *)
      (P2, name2, (q, alias) :: m')
  end.

(* Paper line 12: insert_rev(P, locus(S'), l, name)
   Minimal: actually insert the relocation “receive” side into membrane l.
   We also bump name by |S| to mimic fresh-name consumption. *)

Fixpoint insert_rev
  (P : config) (Sp : Smap) (l : membrane_id) (name : nat)
  : config * nat :=
  match Sp with
  | [] => (P, name)

  | (_q, src) :: tl =>
      let c : var := name in
      let alias : var := S name in

      (* “reverse” side: receive into alias on membrane l *)
      let P1 := place_operation P l (OpDP (Recv c alias)) in

      (* plus your relocation bookkeeping step (if you encode it this way) *)
      let P2 := place_reloc P1 l src l in

      insert_rev P2 tl l (name + 2)
  end.

Fixpoint mem_up (mo_cur : qubit_mem_assign) (qs : list var) (l : membrane_id) : qubit_mem_assign :=
  match qs with
  | [] => mo_cur
  | q :: qs' =>
      let mo_cur' := fun x => if Nat.eqb x q then l else mo_cur x in
      mem_up mo_cur' qs' l
  end.

Definition place
  (P    : config)
  (op   : myOp)
  (l    : membrane_id)
  (name : nat)
  : config :=
  place_operation P l op.  (* name is present exactly like paper line 15 *)

Fixpoint gen_prog_loop_alg2
  (seq    : list myOp)
  (mo_cur : var -> membrane_id)      (* mo_cur in the paper *)
  (moO    : myOp -> membrane_id)
  (P      : config)
  (name   : nat)
  : config :=
  match seq with
  | [] =>
      (* Line 17: Return P *)
      P

  | op :: seq' =>
      (* Line 8: l <- moO(op) *)
      let l : membrane_id := moO op in

      (* Line 9: S <- diff_mem(mo_cur(locus(op)), l) *)
      let S : Smap := diff_mem mo_cur (locus_myOp op) l in

      (* Lines 10–14: if S != ∅ then insert_send; insert_rev; mem_up *)
      let '(P1, name1, mo1) :=
        match S with
        | [] =>
            (* if S = ∅ do nothing *)
            (P, name, ([] : list (var * var)))
        | _ =>
            (* Line 11 *)
            let '(Psend, nameS, renS) := insert_send P S name in
            (* Line 12 *)
            let '(Prev, nameR) := insert_rev Psend S l nameS in
            (* renaming map renS is returned if your place needs it later *)
            (Prev, nameR, renS)
        end in

      (* Line 13 *)
      let mo_cur' : var -> membrane_id := mem_up_smap mo_cur S l in

      (* Line 15: P <- place(P, op, l, name) *)
      let P2 : config := place P1 op l name1 in

      (* Line 16: end while *)
      gen_prog_loop_alg2 seq' mo_cur' moO P2 name1
  end.
Definition empty_config : config := [].

Definition gen_prog_alg2
  (seq : list myOp)
  (moQ : var -> membrane_id)
  (moO : myOp -> membrane_id)
  : config :=
  (* Lines 3–5: P <- ⊥ ; mo_cur <- moQ ; name <- 0 *)
  gen_prog_loop_alg2 seq moQ moO empty_config 0.





(* ============================================================ *)
(* Algorithm 3 (Paper): Automated Parallelization Algorithm     *)
(* Input: hp_l, seq_l                                            *)
(* Output: Rbar                                                  *)
(* ============================================================ *)

(* ---------- helpers: membership / remove duplicates ---------- *)



Fixpoint mem_op (eqb : myOp -> myOp -> bool) (x : myOp) (xs : list myOp) : bool :=
  match xs with
  | [] => false
  | y :: tl => if eqb x y then true else mem_op eqb x tl
  end.

Fixpoint uniq_ops (eqb : myOp -> myOp -> bool) (xs : list myOp) : list myOp :=
  match xs with
  | [] => []
  | x :: tl => if mem_op eqb x tl then uniq_ops eqb tl else x :: uniq_ops eqb tl
  end.

Fixpoint remove_ops (eqb : myOp -> myOp -> bool) (xs rem : list myOp) : list myOp :=
  match xs with
  | [] => []
  | x :: tl => if mem_op eqb x rem then remove_ops eqb tl rem else x :: remove_ops eqb tl rem
  end.

Definition opt_hp (hp_l : hb_relation) (seq_l : seq_relation) : hb_relation :=
  fun a b => andb (hp_l a b) (Nat.ltb (seq_l a) (seq_l b)).

Definition succs (hp : hb_relation) (nodes : list myOp) (x : myOp) : list myOp :=
  filter (fun y => hp x y) nodes.

Fixpoint reachable_fuel
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (fuel : nat)
  (seen : list myOp)
  (x target : myOp) : bool :=
  if eqb x target then true else
  match fuel with
  | 0 => false
  | S fuel' =>
      if mem_op eqb x seen then false
      else
        let seen' := x :: seen in
        existsb (fun y => reachable_fuel eqb hp nodes fuel' seen' y target)
                (succs hp nodes x)
  end.

Definition reachable
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (x y : myOp) : bool :=
  reachable_fuel eqb hp nodes (length nodes) [] x y.

Definition scc_of
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (x : myOp) : list myOp :=
  filter
    (fun y =>
       andb (reachable eqb hp nodes x y)
            (reachable eqb hp nodes y x))
    nodes.

Fixpoint scc_partition_fuel
  (fuel : nat)
  (eqb  : myOp -> myOp -> bool)
  (hp   : hb_relation)
  (nodes : list myOp)
  : list (list myOp) :=
  match fuel with
  | 0 => []  
  | S fuel' =>
      match nodes with
      | [] => []
      | x :: _ =>
          let comp := scc_of eqb hp nodes x in
          let rest := remove_ops eqb nodes comp in
          comp :: scc_partition_fuel fuel' eqb hp rest
      end
  end.

Definition scc_partition
  (eqb  : myOp -> myOp -> bool)
  (hp   : hb_relation)
  (nodes : list myOp)
  : list (list myOp) :=
  scc_partition_fuel (length nodes) eqb hp nodes.

Definition gen_ops (seq_l : seq_relation) (sbar : list myOp) : list process :=
  map myOp_to_process (sort_by_seq seq_l sbar).

Fixpoint alg3_loop
  (seq_l : seq_relation)
  (S     : list (list myOp))
  (Rbar  : list process)
  : list process :=
  match S with
  | [] =>
      Rbar
  | sbar :: S' =>
      let R := gen_ops seq_l sbar in
      let Rbar' := Rbar ++ R in
      alg3_loop seq_l S' Rbar'
  end.


Definition auto_parallelize_alg3
  (eqb  : myOp -> myOp -> bool)   
  (ops_l : list myOp)            
  (hp_l  : hb_relation)
  (seq_l : seq_relation)
  : list process :=
  let hp_l' := opt_hp hp_l seq_l in  
  let S := scc_partition eqb hp_l' (uniq_ops eqb ops_l) in  
  alg3_loop seq_l S ([] : list process).            






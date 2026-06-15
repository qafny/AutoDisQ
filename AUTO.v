
(* AUTO.v *)

From Coq Require Import List Arith Bool Nat NArith Lia.
Import ListNotations.

Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import QArith.

Local Open Scope list_scope.
Local Open Scope bool_scope.

Require Import QuantumLib.Prelim.
Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Inductive myOp : Type :=
| OpAP  (a : cexp)
| OpIf  (b : cbexp) (p q : list cexp).

Definition op_list : Type := list myOp.
Definition hb_relation : Type := N -> N -> bool.
Definition rank : Type := N.
Definition seq_relation : Type := myOp -> rank.
Definition op_mem_assign : Type := myOp -> membrane_id.

Inductive myOpAux : Type :=
| OpNum (n : N)
| OpExp (a : cexp).

Definition qubit_mem_assign : Type := var -> membrane_id.
Definition fitness_value : Type := nat.
Definition distributed_prog : Type := config.

Definition scored_cand : Type :=
  (nat * membrane_id * ((list (N * N)%type * list (N * N)%type)%type))%type.

Definition nposi : Type := (N * N)%type.

Fixpoint list_eqb {A : Type} (beq : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (beq x y) (list_eqb beq xs' ys')
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
  | AModMult a1 b1 c1, AModMult a2 b2 c2 =>
      andb (aexp_eqb a1 a2)
           (andb (aexp_eqb b1 b2) (aexp_eqb c1 c2))
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

Definition range_eqb (r1 r2 : range) : bool :=
  match r1, r2 with
  | (x1, (lo1, hi1)), (x2, (lo2, hi2)) =>
      andb (Nat.eqb x1 x2)
           (andb (Nat.eqb lo1 lo2) (Nat.eqb hi1 hi2))
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
      andb (Nat.eqb x1 x2)
           (andb (aexp_eqb a1 a2) (exp_eqb e1' e2'))
  | RZ q1 x1 a1, RZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2)
           (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | RRZ q1 x1 a1, RRZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2)
           (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
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

Module RangeOrder <: TotalLeBool'.
  Definition t := range.

  Definition leb (x y : range) : bool :=
    if Nat.ltb (fst x) (fst y) then true
    else if Nat.eqb (fst x) (fst y) then
           if Nat.ltb (fst (snd x)) (fst (snd y)) then true
           else if Nat.eqb (fst (snd x)) (fst (snd y))
                then Nat.leb (snd (snd x)) (snd (snd y))
                else false
    else false.

  Infix "[<=]" := leb (at level 50).

  Theorem leb_total : forall x y, (x [<=] y) = true \/ (y [<=] x) = true.
  Proof.
    intros [vx [lx hx]] [vy [ly hy]].
    unfold leb; simpl.
    destruct (Nat.ltb vx vy) eqn:Hvxy.
    - left; reflexivity.
    - destruct (Nat.eqb vx vy) eqn:Heqv.
      + apply Nat.eqb_eq in Heqv; subst.
        destruct (Nat.ltb lx ly) eqn:Hlxy.
        * left; reflexivity.
        * destruct (Nat.eqb lx ly) eqn:Heql.
          -- apply Nat.eqb_eq in Heql; subst.
             destruct (Nat.leb hx hy) eqn:Hh.
             ++ left; reflexivity.
             ++ right.
                rewrite Nat.ltb_irrefl, Nat.eqb_refl, Nat.ltb_irrefl, Nat.eqb_refl.
                apply Nat.leb_gt in Hh.
                apply Nat.leb_le; lia.
          -- apply Nat.eqb_neq in Heql.
             right.
             rewrite Nat.ltb_irrefl, Nat.eqb_refl.
             destruct (Nat.ltb ly lx) eqn:Hlyx.
             ++ reflexivity.
             ++ apply Nat.ltb_ge in Hlxy.
                apply Nat.ltb_ge in Hlyx.
                exfalso; lia.
      + apply Nat.eqb_neq in Heqv.
        right.
        destruct (Nat.ltb vy vx) eqn:Hvyx.
        * reflexivity.
        * apply Nat.ltb_ge in Hvyx.
          apply Nat.ltb_ge in Hvxy.
          exfalso; lia.
  Qed.
End RangeOrder.

Module SortRange := Sort(RangeOrder).

Definition nat_range_inter (x y : (nat * nat)%type) : bool :=
      (Nat.leb (fst x) (fst y) && Nat.ltb (fst y) (snd x))
  ||  (Nat.ltb (fst y) (fst x) && Nat.ltb (fst x) (snd y)).

Definition range_intersect (x y : range) : bool :=
  Nat.eqb (fst x) (fst y) && nat_range_inter (snd x) (snd y).

Definition same_name (x y : range) : bool :=
  Nat.eqb (fst x) (fst y).

Fixpoint intersect' (x : range) (y : locus) : bool :=
  match y with
  | [] => false
  | a :: yas =>
      if (same_name x a) && (nat_range_inter (snd x) (snd a))
      then true
      else intersect' x yas
  end.

Fixpoint intersect (x y : locus) : bool :=
  match x with
  | [] => false
  | a :: xas => if intersect' a y then true else intersect xas y
  end.

Definition get_locus (x : cexp) : locus :=
  match x with
  | CNew a => [a]
  | CAppU l _ => l
  | CMeas _ k => k
  | Send _ x a => [(x, (a, Nat.succ a))]
  | Recv _ x y => [(x, (y, Nat.succ y))]
  end.

Definition get_loci (x : list cexp) : locus :=
  fold_left (fun a b => get_locus b ++ a) x [].

Definition get_vars_cexp (x : cexp) : list var :=
  match x with
  | CMeas x _ => [x]
  | _ => []
  end.

Fixpoint get_vars_aexp (x : aexp) : list var :=
  match x with
  | BA a => [a]
  | Num _ => []
  | APlus e1 e2 => get_vars_aexp e1 ++ get_vars_aexp e2
  | AMult e1 e2 => get_vars_aexp e1 ++ get_vars_aexp e2
  | AModMult e1 e2 e3 => get_vars_aexp e1 ++ get_vars_aexp e2 ++ get_vars_aexp e3
  end.

Definition get_vars_bexp (x : cbexp) : list var :=
  match x with
  | CEq a b => get_vars_aexp a ++ get_vars_aexp b
  | CLt a b => get_vars_aexp a ++ get_vars_aexp b
  end.

Definition is_inter (x y : cexp) : bool :=
  intersect (get_locus x) (get_locus y).

Definition inter_vars (xs ys : list var) : bool :=
  match Coq.Lists.ListSet.set_inter Nat.eq_dec xs ys with
  | [] => false
  | _ => true
  end.

Definition gen_hb_single (x y : (N * myOp)%type) (acc : N -> N -> bool) : N -> N -> bool :=
  match snd x, snd y with
  | OpAP xa, OpAP ya =>
      fun i j =>
        if (N.eqb i (fst x)) && (N.eqb j (fst y))
        then is_inter xa ya
        else acc i j
  | OpAP xa, OpIf ya la ra =>
      fun i j =>
        if (N.eqb i (fst x)) && (N.eqb j (fst y))
        then intersect (get_locus xa) (get_loci (la ++ ra))
             || inter_vars (get_vars_cexp xa) (get_vars_bexp ya)
        else acc i j
  | OpIf ya la ra, OpAP xa =>
      fun i j =>
        if (N.eqb i (fst y)) && (N.eqb j (fst x))
        then intersect (get_locus xa) (get_loci (la ++ ra))
             || inter_vars (get_vars_cexp xa) (get_vars_bexp ya)
        else acc i j
  | OpIf xa la ra, OpIf ya lb rb =>
      fun i j =>
        if (N.eqb i (fst y)) && (N.eqb j (fst x))
        then intersect (get_loci (la ++ ra)) (get_loci (lb ++ rb))
             || inter_vars (get_vars_bexp xa) (get_vars_bexp ya)
        else acc i j
  end.

Fixpoint opListOrder' (l : op_list) (n : N) : list ((N * myOp)%type) :=
  match l with
  | [] => []
  | x :: xs => (n, x) :: opListOrder' xs (N.succ n)
  end.

Definition opListOrder (l : op_list) : list ((N * myOp)%type) :=
  opListOrder' l 0%N.

Definition empty_hp : hb_relation := fun _ _ => false.

Fixpoint gen_hb' (x : (N * myOp)%type) (l : list ((N * myOp)%type)) (acc : hb_relation) : hb_relation :=
  match l with
  | [] => acc
  | a :: xas => gen_hb_single x a (gen_hb' x xas acc)
  end.

Fixpoint gen_hb_a (R : list ((N * myOp)%type)) (acc : hb_relation) : hb_relation :=
  match R with
  | [] => acc
  | a :: xas => gen_hb_a xas (gen_hb' a xas acc)
  end.

Definition trans_closure (n : N) (x : N) (acc : hb_relation) : hb_relation :=
  fun a b =>
    if (N.ltb a x) && (N.ltb x b) && (N.ltb b n) && acc a x && acc x b
    then true
    else acc a b.

Fixpoint gen_hb_trans (size : N) (n : nat) (acc : hb_relation) : hb_relation :=
  match n with
  | O => acc
  | S m => gen_hb_trans size m (trans_closure size (N.of_nat m) acc)
  end.

Definition gen_hb (R : list ((N * myOp)%type)) : hb_relation :=
  gen_hb_trans (N.of_nat (length R)) (length R) (gen_hb_a R empty_hp).

Fixpoint sim_exp (x y : exp) : bool :=
  match x, y with
  | SKIP _ _, SKIP _ _ => true
  | X _ _, X _ _ => true
  | CU _ _ x1, CU _ _ y1 => sim_exp x1 y1
  | RZ _ _ _, RZ _ _ _ => true
  | RRZ _ _ _, RRZ _ _ _ => true
  | SR _ _, SR _ _ => true
  | SRR _ _, SRR _ _ => true
  | QFT _ _, QFT _ _ => true
  | RQFT _ _, RQFT _ _ => true
  | H _ _, H _ _ => true
  | Addto _ _, Addto _ _ => true
  | Seq x1 x2, Seq y1 y2 => sim_exp x1 y1 && sim_exp x2 y2
  | _, _ => false
  end.

Definition sim_cexp (x y : cexp) : bool :=
  match x, y with
  | CNew _, CNew _ => true
  | CAppU _ a, CAppU _ b => sim_exp a b
  | CMeas _ _, CMeas _ _ => true
  | Send _ _ _, Send _ _ _ => true
  | Recv _ _ _, Recv _ _ _ => true
  | _, _ => false
  end.

Definition insert_op (a : (N * myOp)%type) (acc : list (list ((N * myOp)%type))) :=
  match acc with
  | [] => [[a]]
  | [] :: xl => [a] :: xl
  | ((i, OpAP b) :: xl) :: al =>
      match a with
      | (j, OpAP q) =>
          if sim_cexp q b
          then ((i, OpAP b) :: xl ++ [(j, OpAP q)]) :: al
          else [(j, OpAP q)] :: acc
      | (j, OpIf c d e) => [(j, OpIf c d e)] :: (((i, OpAP b) :: xl) :: al)
      end
  | ((i, OpIf c d e) :: xl) :: al => [a] :: ((i, OpIf c d e) :: xl) :: al
  end.

Fixpoint partition_op' (l : list ((N * myOp)%type)) (acc : list (list ((N * myOp)%type))) :=
  match l with
  | [] => acc
  | x :: xl => partition_op' xl (insert_op x acc)
  end.

Definition partition_op (l : list ((N * myOp)%type)) :=
  rev (partition_op' l []).

Definition nposi_eq (r1 r2 : nposi) : bool :=
  match r1, r2 with
  | (x1, y1), (x2, y2) => (N.eqb x1 x2) && (N.eqb y1 y2)
  end.

Fixpoint insert_all
  (x : (myOpAux * list nposi)%type)
  (xs : list ((myOpAux * list nposi)%type))
  : list (list ((myOpAux * list nposi)%type)) :=
  match xs with
  | [] => [[x]]
  | y :: tl => (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations
  (xs : list ((myOpAux * list nposi)%type))
  : list (list ((myOpAux * list nposi)%type)) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.

Definition permutations_one
  (l : list ((myOpAux * list nposi)%type))
  : list (list ((myOpAux * list nposi)%type)) :=
  [l].

Fixpoint car_concat'
  (x : list ((myOpAux * list nposi)%type))
  (y : list (list ((myOpAux * list nposi)%type)))
  : list (list ((myOpAux * list nposi)%type)) :=
  match y with
  | [] => []
  | a :: ys => (x ++ a) :: car_concat' x ys
  end.

Fixpoint car_concat
  (x y : list (list ((myOpAux * list nposi)%type)))
  : list (list ((myOpAux * list nposi)%type)) :=
  match x with
  | [] => []
  | a :: xs => car_concat' a y ++ car_concat xs y
  end.

Fixpoint get_first (l : list (list ((N * myOp)%type))) : list ((N * myOp)%type) :=
  match l with
  | [] => []
  | [] :: xs => get_first xs
  | (a :: _) :: ys => a :: get_first ys
  end.

Fixpoint in_list_a (x : (N * myOp)%type) (l : list ((N * myOp)%type)) : bool :=
  match l with
  | [] => false
  | a :: xs => if N.eqb (fst x) (fst a) then true else in_list_a x xs
  end.

Fixpoint remove_first
  (l : list (list ((N * myOp)%type)))
  (x : list ((N * myOp)%type))
  : list (list ((N * myOp)%type)) :=
  match l with
  | [] => []
  | [] :: xs => [] :: remove_first xs x
  | (a :: xs) :: ys =>
      if in_list_a a x
      then xs :: remove_first ys x
      else (a :: xs) :: remove_first ys x
  end.

Fixpoint grab_related'
  (x : (N * myOp)%type)
  (l : list ((N * myOp)%type))
  (re : hb_relation)
  (acc : list ((N * myOp)%type))
  : list ((N * myOp)%type) :=
  match l with
  | [] => acc
  | a :: xs =>
      if re (fst x) (fst a)
      then grab_related' x xs re acc
      else grab_related' x xs re (acc ++ [a])
  end.

Fixpoint up_qubits (x : var) (i : nat) (n : nat) (acc : list nposi) : list nposi :=
  match n with
  | O => acc
  | S m =>
      up_qubits x i m
        (acc ++ [(N.of_nat x, N.add (N.of_nat i) (N.of_nat m))])
  end.

Fixpoint cutToQubits' (l : list range) : list nposi :=
  match l with
  | [] => []
  | (x, (l0, r)) :: xs => up_qubits x l0 (Nat.sub r l0) [] ++ cutToQubits' xs
  end.

Definition cutToQubits (l : list range) : list nposi :=
  cutToQubits' (SortRange.sort l).

Fixpoint get_locus_in_op (l : list ((N * myOp)%type)) : list range :=
  match l with
  | [] => []
  | (_, OpAP y) :: la =>
      match get_locus y with
      | [] => get_locus_in_op la
      | re => re ++ get_locus_in_op la
      end
  | (_, OpIf _ _ _) :: la => get_locus_in_op la
  end.

Fixpoint get_nlocus
  (l : list ((N * myOp)%type))
  : list ((myOpAux * list nposi)%type) :=
  match l with
  | [] => []
  | x :: xs =>
      (OpNum (fst x), cutToQubits (get_locus_in_op (x :: nil))) :: get_nlocus xs
  end.

Fixpoint assign_each
  (n : nat)
  (l : list (list ((N * myOp)%type)))
  (re : hb_relation)
  (acc : list (list ((myOpAux * list nposi)%type)))
  : list (list ((myOpAux * list nposi)%type)) :=
  match n with
  | O => acc
  | S m =>
      match get_first l with
      | [] => acc
      | p :: l0 =>
          let good := grab_related' p l0 re [p] in
          let next_acc := car_concat acc (permutations_one (get_nlocus good)) in
          assign_each m (remove_first l good) re next_acc
      end
  end.

Definition gen_seq
  (l : list ((N * myOp)%type))
  (re : hb_relation)
  : ((list ((myOpAux * list nposi)%type) *
      list (list ((myOpAux * list nposi)%type)))%type) :=
  let can := partition_op l in
  match can with
  | [] => ([], [])
  | x :: xs => (get_nlocus x, assign_each (Nat.sub (length l) (length x)) xs re [[]])
  end.

Fixpoint count_a
  (new0 : list ((myOpAux * list nposi)%type))
  (l : list membrane_id)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (list (((myOpAux * list nposi)%type * membrane_id)%type) *
     list ((myOpAux * list nposi)%type))%type :=
  match l with
  | [] => (acc, new0)
  | a :: ys =>
      match new0 with
      | [] => (acc, [])
      | x :: xs => count_a xs ys ((x, a) :: acc)
      end
  end.

Fixpoint gen_mem_new'
  (t : nat)
  (news : list ((myOpAux * list nposi)%type))
  (l : list membrane_id)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : list (((myOpAux * list nposi)%type * membrane_id)%type) :=
  match t with
  | O => acc
  | S m =>
      let '(re, next) := count_a news l [] in
      gen_mem_new' m next l (acc ++ re)
  end.

Definition gen_mem_new
  (news : list ((myOpAux * list nposi)%type))
  (l : list membrane_id)
  : list (((myOpAux * list nposi)%type * membrane_id)%type) :=
  match l with
  | [] => []
  | _ =>
      let v := Nat.add (Nat.div (length news) (length l)) 1%nat in
      gen_mem_new' v news l []
  end.

Fixpoint insert_posis
  (l : list ((membrane_id * list nposi)%type))
  (a : membrane_id)
  (x : list nposi)
  : list ((membrane_id * list nposi)%type) :=
  match l with
  | [] => []
  | (n, y) :: ys =>
      if Nat.eqb a n then (n, y ++ x) :: ys else (n, y) :: insert_posis ys a x
  end.

Fixpoint turn_new
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (acc : list ((membrane_id * list nposi)%type))
  : list ((membrane_id * list nposi)%type) :=
  match l with
  | [] => acc
  | (x, y) :: xs => turn_new xs (insert_posis acc y (snd x))
  end.

Fixpoint posi_set_in (a : nposi) (l : list nposi) : bool :=
  match l with
  | [] => false
  | x :: xs => if nposi_eq a x then true else posi_set_in a xs
  end.

Fixpoint set_inter0
  (x y : list nposi)
  (acc : (list nposi * list nposi)%type)
  : (list nposi * list nposi)%type :=
  match x with
  | [] => acc
  | a :: xs =>
      if posi_set_in a y
      then set_inter0 xs y (a :: fst acc, snd acc)
      else set_inter0 xs y (fst acc, a :: snd acc)
  end.

Fixpoint dec_mem (l : list ((list nposi * membrane_id)%type)) (x : nposi) : option membrane_id :=
  match l with
  | [] => None
  | (y, i) :: ys => if posi_set_in x y then Some i else dec_mem ys x
  end.

Fixpoint search_mem
  (new0 : list ((membrane_id * list nposi)%type))
  (x : list nposi)
  (acc : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list ((membrane_id * ((list nposi * list nposi)%type))%type) :=
  match new0 with
  | [] => acc
  | (i, y) :: ys =>
      let inter := set_inter0 x y ([], []) in
      search_mem ys x ((i, inter) :: acc)
  end.

Fixpoint all_no_mem
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type)) : bool :=
  match l with
  | [] => true
  | (_, ([], _)) :: ys => all_no_mem ys
  | _ :: _ => false
  end.

Fixpoint is_one_mem
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type)) : bool :=
  match l with
  | [] => false
  | (_, ([], _)) :: ys => is_one_mem ys
  | _ :: ys => all_no_mem ys
  end.

Fixpoint get_one
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : option membrane_id :=
  match l with
  | [] => None
  | (a, ([], _)) :: ys => get_one ys
  | (a, _) :: _ => Some a
  end.

Fixpoint grab_good
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list ((membrane_id * ((list nposi * list nposi)%type))%type) :=
  match l with
  | [] => acc
  | (a, ([], _)) :: ys => grab_good ys acc
  | (a, (ha, hb)) :: ys => grab_good ys ((a, (ha, hb)) :: acc)
  end.

Fixpoint nlength {A : Type} (l : list A) : N :=
  match l with
  | [] => 0%N
  | _ :: xs => N.add 1%N (nlength xs)
  end.

Fixpoint max_one
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (v : N)
  (acc : (membrane_id * ((list nposi * list nposi)%type))%type)
  (accb : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : ((membrane_id * ((list nposi * list nposi)%type))%type *
     list ((membrane_id * ((list nposi * list nposi)%type))%type))%type :=
  match l with
  | [] => (acc, accb)
  | (i, y) :: ys =>
      if N.ltb v (nlength (fst y))
      then max_one ys (nlength (fst y)) (i, y) (acc :: accb)
      else max_one ys v acc ((i, y) :: accb)
  end.

Fixpoint max_mem_id
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (v : membrane_id)
  (acc : (list nposi * list nposi)%type)
  (accb : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : (((membrane_id * ((list nposi * list nposi)%type))%type) *
     (list ((membrane_id * ((list nposi * list nposi)%type))%type)))%type :=
  match l with
  | [] => ((v, acc), accb)
  | (i, y) :: ys =>
      if Nat.ltb v i
      then max_mem_id ys i y ((v, acc) :: accb)
      else max_mem_id ys v acc ((i, y) :: accb)
  end.

Fixpoint gen_comm'
  (i j : membrane_id)
  (l : list nposi)
  (chan : var)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : list (((myOpAux * list nposi)%type * membrane_id)%type) :=
  match l with
  | [] => acc
  | x :: xs =>
      gen_comm' i j xs (Nat.succ chan)
        ((((OpExp (Recv chan (N.to_nat (fst x)) (N.to_nat (snd x)))), [x]), j) ::
         (((OpExp (Send chan (N.to_nat (fst x)) (N.to_nat (snd x)))), [x]), i) :: acc)
  end.

Fixpoint gen_comm
  (j : membrane_id)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (chan : var)
  (acc accb : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var *
     (list (((myOpAux * list nposi)%type * membrane_id)%type) *
      list (((myOpAux * list nposi)%type * membrane_id)%type)))%type :=
  match l with
  | [] => (chan, (acc, accb))
  | (i, (x, _)) :: xs =>
      gen_comm j xs (Nat.add chan (Nat.mul 2%nat (length x)))
        (gen_comm' j i x chan acc)
        (gen_comm' i j x chan accb)
  end.

Definition gen_comm_insert
  (j : membrane_id)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (chan : var)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (v : (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var * list (((myOpAux * list nposi)%type * membrane_id)%type))%type :=
  let mid := gen_comm j l chan acc [] in
  (fst mid, snd (snd mid) ++ v :: fst (snd mid)).

Fixpoint gen_comm_b
  (j : membrane_id)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (chan : var)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var * list (((myOpAux * list nposi)%type * membrane_id)%type))%type :=
  match l with
  | [] => (chan, acc)
  | (i, (x, _)) :: xs =>
      gen_comm_b j xs (Nat.add chan (length x)) (gen_comm' j i x chan acc)
  end.

Fixpoint collect_all_posi
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list nposi)
  : list nposi :=
  match l with
  | [] => acc
  | (_, (x, _)) :: xs => collect_all_posi xs (x ++ acc)
  end.

Fixpoint push_to_mem_i
  (i j : membrane_id)
  (v : list nposi)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list ((membrane_id * list nposi)%type))
  : list ((membrane_id * list nposi)%type) :=
  match l with
  | [] => acc
  | (k, (x, y)) :: xs =>
      if Nat.eqb i k
      then push_to_mem_i i j v xs ((k, v ++ y) :: acc)
      else if Nat.eqb j k
           then push_to_mem_i i j v xs ((k, x ++ y) :: acc)
           else push_to_mem_i i j v xs ((k, y) :: acc)
  end.

Definition post_dec
  (i : membrane_id)
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (xnum : N)
  (xset : list nposi)
  (chan : var)
  (rea input : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var *
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))%type :=
  let v := collect_all_posi rea [] in
  match v with
  | [] => (chan, [])
  | y :: _ =>
      match dec_mem dc y with
      | Some j =>
          let mid := gen_comm_insert i rea chan acc ((OpNum xnum, xset), i) in
          let pre_gen := gen_comm_b i rea (fst mid) acc in
          let post_gen :=
            gen_comm' i j v (fst pre_gen) (((OpNum xnum, xset), i) :: snd pre_gen) in
          (Nat.add (fst pre_gen) (length v),
           [((((OpNum xnum, xset), i) :: snd mid), new0);
            (post_gen, push_to_mem_i j i v input [])])
      | None =>
          let pre_gen := gen_comm_insert i rea chan acc ((OpNum xnum, xset), i) in
          (fst pre_gen, [(snd pre_gen, new0)])
      end
  end.

Fixpoint mem_pos (p : nposi) (xs : list nposi) : bool :=
  match xs with
  | [] => false
  | y :: ys => if nposi_eq y p then true else mem_pos p ys
  end.

Fixpoint add_nodup (xs ys : list nposi) : list nposi :=
  match xs with
  | [] => ys
  | x :: tl => if mem_pos x ys then add_nodup tl ys else add_nodup tl (x :: ys)
  end.

Fixpoint add_qubits_to_mem
  (i : membrane_id)
  (xs : list nposi)
  (new0 : list ((membrane_id * list nposi)%type))
  : list ((membrane_id * list nposi)%type) :=
  match new0 with
  | [] => []
  | (j, ys) :: tl =>
      if Nat.eqb i j
      then (j, add_nodup xs ys) :: add_qubits_to_mem i xs tl
      else (j, ys) :: add_qubits_to_mem i xs tl
  end.

Fixpoint assoc_opt_mem
  (i : membrane_id)
  (new0 : list ((membrane_id * list nposi)%type))
  : option (list nposi) :=
  match new0 with
  | [] => None
  | (j, xs) :: tl => if Nat.eqb i j then Some xs else assoc_opt_mem i tl
  end.

Definition mem_qubit_load (new0 : list ((membrane_id * list nposi)%type)) (i : membrane_id) : nat :=
  match assoc_opt_mem i new0 with
  | Some xs => length xs
  | None => 0%nat
  end.

Definition membrane_capacity : nat := 8%nat.
Definition op_capacity : nat := 6%nat.

Definition mem_has_capacity
  (new0 : list ((membrane_id * list nposi)%type))
  (i : membrane_id)
  (xset : list nposi) : bool :=
  let current := mem_qubit_load new0 i in
  Nat.leb (Nat.add current (length xset)) membrane_capacity.

Fixpoint op_load_in_partial
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (mid : membrane_id) : nat :=
  match l with
  | [] => 0%nat
  | (((_, _), m)) :: xs =>
      if Nat.eqb m mid
      then Nat.succ (op_load_in_partial xs mid)
      else op_load_in_partial xs mid
  end.

Definition overlap_size (x y : list nposi) : nat :=
  length (fst (set_inter0 x y ([], []))).

Definition import_cost (xset local_qs : list nposi) : nat :=
  Nat.sub (length xset) (overlap_size xset local_qs).

Definition score_mem_for_op
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (xset : list nposi)
  (mid : membrane_id)
  (local_qs : list nposi) : nat :=
  let imports := import_cost xset local_qs in
  let opl := op_load_in_partial partial mid in
  Nat.add (Nat.mul 4%nat imports) (Nat.mul 5%nat opl).

Definition over_op_capacity
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (mid : membrane_id) : bool :=
  Nat.ltb op_capacity (op_load_in_partial partial mid).

Fixpoint insert_scored_candidate
  (cand : scored_cand)
  (scored : list scored_cand) : list scored_cand :=
  match scored with
  | [] => [cand]
  | ((s1, m1, d1) as c1) :: tl =>
      let '(s, _, _) := cand in
      if Nat.ltb s s1 then cand :: scored else c1 :: insert_scored_candidate cand tl
  end.

Fixpoint take_scored (n : nat) (xs : list scored_cand) : list scored_cand :=
  match n, xs with
  | O, _ => []
  | _, [] => []
  | S n', x :: tl => x :: take_scored n' tl
  end.

Fixpoint scored_candidates
  (new0 : list ((membrane_id * list nposi)%type))
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (xset : list nposi)
  (candidates : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list scored_cand :=
  match candidates with
  | [] => []
  | (mid, (local_qs, rest_qs)) :: tl =>
      if orb (over_op_capacity partial mid)
             (negb (mem_has_capacity new0 mid xset))
      then scored_candidates new0 partial xset tl
      else
        let s := score_mem_for_op partial xset mid local_qs in
        insert_scored_candidate (s, mid, (local_qs, rest_qs))
          (scored_candidates new0 partial xset tl)
  end.

Fixpoint scored_candidates_nocap
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (xset : list nposi)
  (candidates : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list scored_cand :=
  match candidates with
  | [] => []
  | (mid, (local_qs, rest_qs)) :: tl =>
      if over_op_capacity partial mid
      then scored_candidates_nocap partial xset tl
      else
        let s := score_mem_for_op partial xset mid local_qs in
        insert_scored_candidate (s, mid, (local_qs, rest_qs))
          (scored_candidates_nocap partial xset tl)
  end.

Fixpoint build_choices
  (cs : list scored_cand)
  (re : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (xnum : N)
  (xset : list nposi)
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (chan : var)
  (acc :
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))
  : list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
           list ((membrane_id * list nposi)%type))%type) :=
  match cs with
  | [] => acc
  | (_, chosen_mid, _) :: tl =>
      if is_one_mem re then
        let choice := (((((OpNum xnum), xset), chosen_mid) :: l), new0) in
        build_choices tl re new0 dc xnum xset l chan (choice :: acc)
      else
        let others := filter (fun p => negb (Nat.eqb (fst p) chosen_mid)) re in
        let mid_res := post_dec chosen_mid new0 dc xnum xset chan others re l in
        let choices := snd mid_res in
        build_choices tl re new0 dc xnum xset l chan (choices ++ acc)
  end.

Definition assign_mem_s
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (x : (N * list nposi)%type)
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (chan : var)
  : (var *
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))%type :=
  let xset := snd x in
  let re :=
    search_mem new0 xset
      ([] : list ((membrane_id * ((list nposi * list nposi)%type))%type)) in
  match re with
  | [] => (chan, [])
  | _ =>
      let ranked :=
        match scored_candidates new0 l xset re with
        | [] => scored_candidates_nocap l xset re
        | ys => ys
        end in
      let top := take_scored 3%nat ranked in
      (chan,
       build_choices top re new0 dc (fst x) xset l chan
         ([] :
           list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
                  list ((membrane_id * list nposi)%type))%type)))
  end.

Definition channel : var := 6%nat.

Fixpoint assign_mem'
  (dc : list ((list nposi * membrane_id)%type))
  (l : list ((myOpAux * list nposi)%type))
  (acc :
     (var *
      list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
             list ((membrane_id * list nposi)%type))%type))%type)
  : (var *
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))%type :=
  match l with
  | [] => acc
  | (OpNum x, y) :: xs =>
      assign_mem' dc xs
        (fold_left
           (fun a b =>
              let mid := assign_mem_s (snd b) dc (x, y) (fst b) (fst a) in
              (fst mid, snd a ++ snd mid))
           (snd acc) (fst acc, []))
  | _ :: xs => assign_mem' dc xs acc
  end.

Fixpoint assign_mem_more
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (l : list (list ((myOpAux * list nposi)%type)))
  (acc : list (list (((myOpAux * list nposi)%type * membrane_id)%type)))
  : list (list (((myOpAux * list nposi)%type * membrane_id)%type)) :=
  match l with
  | [] => acc
  | x :: xs =>
      let seed :=
        (channel,
         [ (([] : list (((myOpAux * list nposi)%type * membrane_id)%type)), new0) ]) in
      assign_mem_more new0 dc xs
        (map (fun l0 => rev l0)
             (fst (split (snd (assign_mem' dc x seed))))
         ++ acc)
  end.

Fixpoint find_empty_new'
  (l : list ((membrane_id * list nposi)%type))
  (m : membrane_id)
  (acc : list membrane_id)
  : list membrane_id :=
  match l with
  | [] => m :: acc
  | (x, _) :: xs => if Nat.eqb x m then acc else find_empty_new' xs m acc
  end.

Fixpoint find_empy_new
  (l : list ((membrane_id * list nposi)%type))
  (al acc : list membrane_id)
  : list membrane_id :=
  match al with
  | [] => acc
  | x :: xs => find_empy_new l xs (find_empty_new' l x acc)
  end.

Fixpoint assign_new_mem
  (l : list ((myOpAux * list nposi)%type))
  (al : list membrane_id)
  : list ((list nposi * membrane_id)%type) :=
  match al with
  | [] => []
  | x :: xs =>
      match l with
      | [] => []
      | y :: ys => (snd y, x) :: assign_new_mem ys xs
      end
  end.

Fixpoint gen_empty_mem (m : list membrane_id) : list ((membrane_id * list nposi)%type) :=
  match m with
  | [] => []
  | a :: xl => (a, []) :: gen_empty_mem xl
  end.

Fixpoint take {A : Type} (n : nat) (xs : list A) : list A :=
  match n, xs with
  | O, _ => []
  | _, [] => []
  | S n', x :: tl => x :: take n' tl
  end.

Definition fallback_mid
  (ql : list (((myOpAux * list nposi)%type * membrane_id)%type)) : membrane_id :=
  match ql with
  | [] => 0%nat
  | (_, mid) :: _ => mid
  end.

Definition gen_mem
  (news : list ((myOpAux * list nposi)%type))
  (l : list (list ((myOpAux * list nposi)%type)))
  (ids : list membrane_id)
  : list (list (((myOpAux * list nposi)%type * membrane_id)%type)) :=
  let ql := gen_mem_new news ids in
  let vl := turn_new (gen_mem_new news ids) [] in
  let al := find_empy_new vl ids [] in
  let dc := assign_new_mem news al in
  let base_new0 := gen_empty_mem al ++ vl in
  let res := map (fun a => ql ++ a) (assign_mem_more base_new0 dc l []) in
  match res with
  | [] =>
      let mid := fallback_mid ql in
      match take 3%nat l with
      | [] => [ql]
      | xs => map (fun x => ql ++ map (fun y => (y, mid)) x) xs
      end
  | _ => res
  end.

Fixpoint insert_mem_id
  (i : membrane_id)
  (x : (myOpAux * list nposi)%type)
  (acc : list ((membrane_id * list ((myOpAux * list nposi)%type))%type))
  : list ((membrane_id * list ((myOpAux * list nposi)%type))%type) :=
  match acc with
  | [] => [(i, [x])]
  | (a, b) :: xs =>
      if Nat.eqb i a
      then (a, b ++ [x]) :: xs
      else (a, b) :: insert_mem_id i x xs
  end.

Fixpoint distribute_op
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (acc : list ((membrane_id * list ((myOpAux * list nposi)%type))%type))
  : list ((membrane_id * list ((myOpAux * list nposi)%type))%type) :=
  match l with
  | [] => acc
  | x :: xs => distribute_op xs (insert_mem_id (snd x) (fst x) acc)
  end.

Fixpoint get_op (l : list ((N * myOp)%type)) (i : N) : option myOp :=
  match l with
  | [] => None
  | (x, y) :: xs => if N.eqb i x then Some y else get_op xs i
  end.

Fixpoint turn_cexp_to_proc (l : list cexp) (p : process) : process :=
  match l with
  | [] => p
  | x :: xs => AP x (turn_cexp_to_proc xs p)
  end.

Definition turn_op_to_proc (x : myOp) (p : process) : process :=
  match x with
  | OpAP a => AP a p
  | OpIf b l r => PIf b (turn_cexp_to_proc l p) (turn_cexp_to_proc r p)
  end.

Fixpoint to_process
  (l : list ((myOpAux * list nposi)%type))
  (os : list ((N * myOp)%type))
  : option process :=
  match l with
  | [] => Some PNil
  | (OpNum n, _) :: xs =>
      match get_op os n, to_process xs os with
      | Some x, Some p => Some (turn_op_to_proc x p)
      | _, _ => None
      end
  | (OpExp a, _) :: xs =>
      match to_process xs os with
      | Some p => Some (AP a p)
      | None => None
      end
  end.

Fixpoint to_prog
  (l : list ((nat * list ((myOpAux * list nposi)%type))%type))
  (os : list ((N * myOp)%type))
  : list memb :=
  match l with
  | [] => []
  | x :: xs =>
      match to_process (snd x) os with
      | None => []
      | Some a => Memb (fst x) a :: to_prog xs os
      end
  end.

Fixpoint has_if_ops (os : list ((N * myOp)%type)) : bool :=
  match os with
  | [] => false
  | (_, OpIf _ _ _) :: _ => true
  | _ :: xs => has_if_ops xs
  end.

Fixpoint owner_of_pos
  (owners : list ((nposi * membrane_id)%type))
  (p : nposi) : option membrane_id :=
  match owners with
  | [] => None
  | (q, mid) :: xs =>
      if nposi_eq q p then Some mid else owner_of_pos xs p
  end.

Fixpoint set_owner
  (owners : list ((nposi * membrane_id)%type))
  (p : nposi)
  (mid : membrane_id)
  : list ((nposi * membrane_id)%type) :=
  match owners with
  | [] => [(p, mid)]
  | (q, m) :: xs =>
      if nposi_eq q p
      then (p, mid) :: xs
      else (q, m) :: set_owner xs p mid
  end.

Fixpoint set_owner_many
  (owners : list ((nposi * membrane_id)%type))
  (ps : list nposi)
  (mid : membrane_id)
  : list ((nposi * membrane_id)%type) :=
  match ps with
  | [] => owners
  | p :: xs => set_owner_many (set_owner owners p mid) xs mid
  end.

Fixpoint append_cexp_to_mem
  (mid : membrane_id)
  (ce : cexp)
  (acc : list ((membrane_id * list cexp)%type))
  : list ((membrane_id * list cexp)%type) :=
  match acc with
  | [] => [(mid, [ce])]
  | (m, xs) :: tl =>
      if Nat.eqb mid m
      then (m, xs ++ [ce]) :: tl
      else (m, xs) :: append_cexp_to_mem mid ce tl
  end.

Fixpoint add_initial_owners_from_solution
  (sol : list ((((myOpAux * list nposi)%type) * membrane_id)%type))
  (os : list ((N * myOp)%type))
  (owners : list ((nposi * membrane_id)%type))
  : list ((nposi * membrane_id)%type) :=
  match sol with
  | [] => owners
  | ((aux, qs), mid) :: xs =>
      let owners' :=
        match aux with
        | OpNum n =>
            match get_op os n with
            | Some (OpAP (CNew r)) =>
                set_owner_many owners (cutToQubits (r :: nil)) mid
            | _ => owners
            end
        | OpExp (CNew r) =>
            set_owner_many owners (cutToQubits (r :: nil)) mid
        | _ => owners
        end
      in
      add_initial_owners_from_solution xs os owners'
  end.



Fixpoint ensure_local_qubits_aux
  (dst : membrane_id)
  (qs : list nposi)
  (owners : list ((nposi * membrane_id)%type))
  (bufs : list ((membrane_id * list cexp)%type))
  (chan : var)
  : (var * list ((nposi * membrane_id)%type) * list ((membrane_id * list cexp)%type))%type :=
  match qs with
  | [] => (chan, owners, bufs)
  | q :: tl =>
      match owner_of_pos owners q with
      | Some src =>
          if Nat.eqb src dst then
            ensure_local_qubits_aux dst tl owners bufs chan
          else
            let v := N.to_nat (fst q) in
            let idx := N.to_nat (snd q) in
            let bufs1 := append_cexp_to_mem src (Send chan v idx) bufs in
            let bufs2 := append_cexp_to_mem dst (Recv chan v idx) bufs1 in
            let owners' := set_owner owners q dst in
            ensure_local_qubits_aux dst tl owners' bufs2 (Nat.succ chan)
      | None =>
          ensure_local_qubits_aux dst tl owners bufs chan
      end
  end.

Definition ensure_local_qubits := ensure_local_qubits_aux.

Fixpoint to_prog_from_cexps
  (grouped : list ((membrane_id * list cexp)%type)) : config :=
  match grouped with
  | [] => []
  | (mid, ces) :: xs => Memb mid (turn_cexp_to_proc ces PNil) :: to_prog_from_cexps xs
  end.

Fixpoint lower_solution_distributed_go
  (xs : list ((((myOpAux * list nposi)%type) * membrane_id)%type))
  (os : list ((N * myOp)%type))
  (owners : list ((nposi * membrane_id)%type))
  (bufs : list ((membrane_id * list cexp)%type))
  (chan : var)
  : config :=
  match xs with
  | [] => to_prog_from_cexps bufs
  | ((aux, qs), mid) :: tl =>
      match aux with
      | OpExp ce =>
          match ce with
          | CNew r =>
              let owners' := set_owner_many owners (cutToQubits (r :: nil)) mid in
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners' bufs' chan
          | Recv _ x y =>
              let owners' := set_owner owners (N.of_nat x, N.of_nat y) mid in
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners' bufs' chan
          | _ =>
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners bufs' chan
          end
      | OpNum n =>
          match get_op os n with
          | Some (OpAP ce) =>
              match ce with
              | CNew r =>
                  let owners' := set_owner_many owners (cutToQubits (r :: nil)) mid in
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners' bufs' chan
              | CAppU loc e =>
                  let qbs := cutToQubits loc in
                  let tmp := ensure_local_qubits mid qbs owners bufs chan in
                  let p1 := fst tmp in
                  let chan' := fst p1 in
                  let owners' := snd p1 in
                  let bufs' := snd tmp in
                  let bufs'' := append_cexp_to_mem mid (CAppU loc e) bufs' in
                  lower_solution_distributed_go tl os owners' bufs'' chan'
              | CMeas x loc =>
                  let qbs := cutToQubits loc in
                  let tmp := ensure_local_qubits mid qbs owners bufs chan in
                  let p1 := fst tmp in
                  let chan' := fst p1 in
                  let owners' := snd p1 in
                  let bufs' := snd tmp in
                  let bufs'' := append_cexp_to_mem mid (CMeas x loc) bufs' in
                  lower_solution_distributed_go tl os owners' bufs'' chan'
              | Send _ _ _ =>
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners bufs' chan
              | Recv _ _ _ =>
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners bufs' chan
              end
          | _ =>
              lower_solution_distributed_go tl os owners bufs chan
          end
      end
  end.



Definition lower_solution_distributed
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (os : list ((N * myOp)%type))
  : config :=
  let owners0 := add_initial_owners_from_solution sol os [] in
  lower_solution_distributed_go sol os owners0 [] 100000%nat.

Fixpoint gen_prog
  (l : list (list (((myOpAux * list nposi)%type * membrane_id)%type)))
  (os : list ((N * myOp)%type))
  : list config :=
  if has_if_ops os then
    match l with
    | [] => []
    | x :: xs => to_prog (distribute_op x []) os :: gen_prog xs os
    end
  else
    match l with
    | [] => []
    | x :: xs => lower_solution_distributed x os :: gen_prog xs os
    end.

Fixpoint count_send_in_process (p : process) : nat :=
  match p with
  | PNil => 0%nat
  | AP a p' =>
      match a with
      | Send _ _ _ => Nat.succ (count_send_in_process p')
      | Recv _ _ _ => Nat.succ (count_send_in_process p')
      | _ => count_send_in_process p'
      end
  | PIf _ p1 p2 => Nat.add (count_send_in_process p1) (count_send_in_process p2)
  end.

Definition count_send_in_memb (m : memb) : nat :=
  match m with
  | Memb _ p => count_send_in_process p
  end.

Fixpoint count_comm_ops (cfg : config) : nat :=
  match cfg with
  | [] => 0%nat
  | m :: xs => Nat.add (count_send_in_memb m) (count_comm_ops xs)
  end.

Fixpoint process_size (p : process) : nat :=
  match p with
  | PNil => 0%nat
  | AP _ p' => Nat.succ (process_size p')
  | PIf _ p1 p2 => Nat.add (process_size p1) (process_size p2)
  end.

Definition memb_load (m : memb) : nat :=
  match m with
  | Memb _ p => process_size p
  end.

Fixpoint max_load (cfg : config) : nat :=
  match cfg with
  | [] => 0%nat
  | m :: xs => Nat.max (memb_load m) (max_load xs)
  end.

Definition alpha : nat := 10%nat.

Definition fit (cfg : config) : fitness_value :=
  Nat.add (Nat.mul alpha (count_comm_ops cfg)) (max_load cfg).

Fixpoint best_prog_aux
  (best : config)
  (bestv : nat)
  (xs : list config)
  : config :=
  match xs with
  | [] => best
  | x :: tl =>
      let vx := fit x in
      if Nat.ltb vx bestv
      then best_prog_aux x vx tl
      else best_prog_aux best bestv tl
  end.

Definition best_prog (xs : list config) : option config :=
  match xs with
  | [] => None
  | x :: tl => Some (best_prog_aux x (fit x) tl)
  end.


Definition op_assignment :=
  (((myOpAux * list nposi)%type * membrane_id)%type).

Definition autodisq_solution := list op_assignment.

Definition autodisq_solutions
  (ops : op_list)
  (mids : list membrane_id)
  : list autodisq_solution :=
  let os := opListOrder ops in
  let hb := gen_hb os in
  let sq := gen_seq os hb in
  gen_mem (fst sq) (snd sq) mids.

Definition lower_autodisq_solution
  (sol : autodisq_solution)
  (os : list ((N * myOp)%type))
  : config :=
  if has_if_ops os
  then to_prog (distribute_op sol []) os
  else lower_solution_distributed sol os.

Definition solution_fit
  (ops : op_list)
  (sol : autodisq_solution)
  : nat :=
  fit (lower_autodisq_solution sol (opListOrder ops)).

Fixpoint best_solution_aux
  (ops : op_list)
  (best : autodisq_solution)
  (bestv : nat)
  (xs : list autodisq_solution)
  : autodisq_solution :=
  match xs with
  | [] => best
  | x :: tl =>
      let vx := solution_fit ops x in
      if Nat.ltb vx bestv
      then best_solution_aux ops x vx tl
      else best_solution_aux ops best bestv tl
  end.

Definition autodisq_best_solution
  (ops : op_list)
  (mids : list membrane_id)
  : option autodisq_solution :=
  match autodisq_solutions ops mids with
  | [] => None
  | x :: xs => Some (best_solution_aux ops x (solution_fit ops x) xs)
  end.

Definition autodisq_all
  (ops : op_list)
  (mids : list membrane_id)
  : list config :=
  map
    (fun sol => lower_autodisq_solution sol (opListOrder ops))
    (autodisq_solutions ops mids).

Definition autodisq_best
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  match autodisq_best_solution ops mids with
  | Some sol =>
      Some (lower_autodisq_solution sol (opListOrder ops))
  | None => None
  end.

(*
Definition autodisq_all
  (ops : op_list)
  (mids : list membrane_id)
  : list config :=
  let os := opListOrder ops in
  let hb := gen_hb os in
  let sq := gen_seq os hb in
  let mem := gen_mem (fst sq) (snd sq) mids in
  gen_prog mem os.

Definition autodisq_best
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  best_prog (autodisq_all ops mids).
*)
Fixpoint auto_disq_loop
  (best : option config)
  (cands : list config)
  : option config :=
  match cands with
  | [] => best
  | P :: xs =>
      match best with
      | None => auto_disq_loop (Some P) xs
      | Some B =>
          if Nat.ltb (fit P) (fit B)
          then auto_disq_loop (Some P) xs
          else auto_disq_loop best xs
      end
  end.

Definition autodisq_first
  (ops : list ((N * myOp)%type))
  (mids : list membrane_id)
  : option config :=
  let nl := get_nlocus ops in
  let init := gen_mem_new nl mids in
  let new0 := turn_new init [] in
  let dc := ([] : list ((list nposi * membrane_id)%type)) in
  let sols := assign_mem_more new0 dc (map (fun x => [x]) nl) [] in
  match sols with
  | [] => None
  | sol :: _ => Some (lower_solution_distributed sol ops)
  end.

Definition autodisq_best_1
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  auto_disq_loop None (autodisq_all ops mids).













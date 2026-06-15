
(*****************************************************************)
(* TeleportationCompilerCore.v                                 *)
(* Corrected two-level IR: abstract distributed IR + protocol IR *)
(*****************************************************************)

Require Import DisQ.BasicUtility DisQ.DisQSyntax DisQ.AUTO.
From Coq Require Import List Arith Bool Nat NArith.BinNat.
Import ListNotations.

Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope bool_scope.

(*****************************************************************)
(* Basic types                                                   *)
(*****************************************************************)

Definition membrane_id : Type := var.
Definition ownership   : Type := list (nposi * membrane_id)%type.

(*****************************************************************)
(* Fresh-name generation                                         *)
(*****************************************************************)

Record fresh_state := {
  next_chan : nat;
  next_var  : nat
}.

Definition init_fresh_state : fresh_state :=
  {| next_chan := 100000; next_var := 200000 |}.

Definition fresh_chan (st : fresh_state) : nat * fresh_state :=
  (next_chan st,
   {| next_chan := S (next_chan st);
      next_var  := next_var st |}).

Definition fresh_var (st : fresh_state) : nat * fresh_state :=
  (next_var st,
   {| next_chan := next_chan st;
      next_var  := S (next_var st) |}).

Record lowering_state := {
  ls_fresh  : fresh_state;
  ls_owners : ownership
}.

Definition init_ls : lowering_state :=
  {| ls_fresh := init_fresh_state;
     ls_owners := [] |}.

(*****************************************************************)
(* Corrected abstract IR                                         *)
(*****************************************************************)
(* This layer captures distributed quantum intent.               *)
(* It does NOT contain Send/Recv/EPR protocol steps.             *)
(*****************************************************************)

Inductive dist_ir : Type :=
| IR_Base         : cexp -> dist_ir
| IR_Move         : locus -> membrane_id -> membrane_id -> dist_ir
| IR_NonlocalCNOT : locus -> locus -> membrane_id -> membrane_id -> dist_ir
| IR_NonlocalCZ   : locus -> locus -> membrane_id -> membrane_id -> dist_ir
| IR_If           : cbexp -> list dist_ir -> list dist_ir -> dist_ir.

Definition ir_buffers : Type := list (membrane_id * list dist_ir)%type.



(*****************************************************************)
(* Concrete protocol IR                                          *)
(*****************************************************************)
(* This layer captures HOW abstract actions are implemented.     *)
(*****************************************************************)

Inductive dist_proto : Type :=
| PP_Base        : cexp -> dist_proto
| PP_AllocEPR    : var -> var -> membrane_id -> membrane_id -> dist_proto
| PP_BellMeasure : locus -> var -> var -> dist_proto
| PP_SendBit     : var -> var -> dist_proto
| PP_RecvBit     : var -> var -> dist_proto
| PP_CorrectX    : locus -> var -> dist_proto
| PP_CorrectZ    : locus -> var -> dist_proto
| PP_LocalCNOT   : locus -> locus -> dist_proto
| PP_LocalCZ     : locus -> locus -> dist_proto
| PP_If          : cbexp -> list dist_proto -> list dist_proto -> dist_proto.

Definition proto_buffers : Type := list (membrane_id * list dist_proto)%type.
Definition proto_program : Type := list (membrane_id * list dist_proto)%type.

(*****************************************************************)
(* Qubit/position extraction                                     *)
(*****************************************************************)

Definition first_pos (loc : locus) : option nposi :=
  match cutToQubits loc with
  | [] => None
  | p :: _ => Some p
  end.

Definition first_qubit (loc : locus) : option nat :=
  match first_pos loc with
  | None => None
  | Some (q, _) => Some (N.to_nat q)
  end.

(*****************************************************************)
(* Basic helpers                                                 *)
(*****************************************************************)

Definition nat_to_var (n : nat) : var := n.

Definition combine_locus (l1 l2 : locus) : locus := l1 ++ l2.

Definition one_qubit_range (x a : nat) : range :=
  (x, (a, S a)).

Definition default_locus_of_q (x a : nat) : locus :=
  [one_qubit_range x a].

Definition gate_on (q : nat) (g : exp) : cexp :=
  CAppU (default_locus_of_q q 0) g.

Definition x_gate (q : nat) : cexp :=
  gate_on q (X q 0).

Definition h_gate (q : nat) : cexp :=
  gate_on q (H q 0).

Definition z_gate (q : nat) : cexp :=
  gate_on q (RZ 1 q 0).

Definition cnot_gate (ctrl tgt : nat) : cexp :=
  CAppU (combine_locus (default_locus_of_q ctrl 0)
                       (default_locus_of_q tgt 0))
        (CU ctrl 0 (X tgt 0)).

Definition cz_gate (ctrl tgt : nat) : cexp :=
  CAppU (combine_locus (default_locus_of_q ctrl 0)
                       (default_locus_of_q tgt 0))
        (CU ctrl 0 (RZ 1 tgt 0)).

(*****************************************************************)
(* Ownership utilities                                           *)
(*****************************************************************)

Fixpoint owner_of_pos
  (owners : ownership)
  (p : nposi) : option membrane_id :=
  match owners with
  | [] => None
  | (q, mid) :: xs =>
      if nposi_eq q p then Some mid else owner_of_pos xs p
  end.

Fixpoint set_owner
  (owners : ownership)
  (p : nposi)
  (mid : membrane_id) : ownership :=
  match owners with
  | [] => [(p, mid)]
  | (q, m) :: xs =>
      if nposi_eq q p
      then (p, mid) :: xs
      else (q, m) :: set_owner xs p mid
  end.

Fixpoint set_owner_many
  (owners : ownership)
  (ps : list nposi)
  (mid : membrane_id) : ownership :=
  match ps with
  | [] => owners
  | p :: xs => set_owner_many (set_owner owners p mid) xs mid
  end.

(*****************************************************************)
(* Buffer utilities                                              *)
(*****************************************************************)

Fixpoint append_proto_to_mem
  (mid : membrane_id) (op : dist_proto) (bufs : proto_buffers) : proto_buffers :=
  match bufs with
  | [] => [(mid, [op])]
  | (m, ops) :: xs =>
      if Nat.eqb m mid
      then (m, ops ++ [op]) :: xs
      else (m, ops) :: append_proto_to_mem mid op xs
  end.

Definition append_many_proto_to_mem
  (mid : membrane_id) (ops : list dist_proto) (bufs : proto_buffers) : proto_buffers :=
  fold_left (fun acc op => append_proto_to_mem mid op acc) ops bufs.

(*****************************************************************)
(* Result records                                                *)
(*****************************************************************)

Record move_result := {
  mr_state   : lowering_state;
  mr_bufs    : proto_buffers;
  mr_dst_q   : nat;
  mr_dst_loc : locus
}.

Record gate_result := {
  gr_state : lowering_state;
  gr_bufs  : proto_buffers
}.

(*****************************************************************)
(* Lowering helpers                                              *)
(*****************************************************************)

Definition lower_move
  (loc : locus) (src dst : membrane_id)
  (st : lowering_state) (bufs : proto_buffers)
  : option move_result :=
  match first_pos loc, first_qubit loc with
  | Some p, Some loc_q =>
      let '(ea_n, st1_f) := fresh_var (ls_fresh st) in
      let '(eb_n, st2_f) := fresh_var st1_f in
      let '(m1_n, st3_f) := fresh_var st2_f in
      let '(m2_n, st4_f) := fresh_var st3_f in
      let '(ch1_n, st5_f) := fresh_chan st4_f in
      let '(ch2_n, st6_f) := fresh_chan st5_f in

      let ea_v  := nat_to_var ea_n in
      let eb_v  := nat_to_var eb_n in
      let m1_v  := nat_to_var m1_n in
      let m2_v  := nat_to_var m2_n in
      let ch1_v := nat_to_var ch1_n in
      let ch2_v := nat_to_var ch2_n in

      let ea_loc  := default_locus_of_q ea_n 0 in
      let dst_loc := default_locus_of_q eb_n 0 in

      let src_ops := [
        PP_AllocEPR ea_v eb_v src dst;
        PP_Base
          (CAppU
             (combine_locus loc ea_loc)
             (CU loc_q 0 (X ea_n 0)));
        PP_Base (h_gate loc_q);
        PP_BellMeasure loc m1_v m2_v;
        PP_SendBit ch1_v m1_v;
        PP_SendBit ch2_v m2_v
      ] in

      let dst_ops := [
        PP_RecvBit ch1_v m1_v;
        PP_RecvBit ch2_v m2_v;
        PP_If (CEq (BA m2_v) (Num 1)) [PP_CorrectX dst_loc m2_v] [];
        PP_If (CEq (BA m1_v) (Num 1)) [PP_CorrectZ dst_loc m1_v] []
      ] in

      let bufs'  := append_many_proto_to_mem src src_ops bufs in
      let bufs'' := append_many_proto_to_mem dst dst_ops bufs' in

      let new_st :=
        {| ls_fresh := st6_f;
           ls_owners := set_owner (ls_owners st) p dst |} in

      Some {| mr_state := new_st;
              mr_bufs := bufs'';
              mr_dst_q := eb_n;
              mr_dst_loc := dst_loc |}
  | _, _ => None
  end.



Definition lower_nonlocal_cnot
  (loc_ctrl loc_tgt : locus)
  (mid_ctrl mid_tgt : membrane_id)
  (st : lowering_state)
  (bufs : proto_buffers)
  : option gate_result :=
  match lower_move loc_ctrl mid_ctrl mid_tgt st bufs with
  | None => None
  | Some mr1 =>
      let loc_ctrl_interm := mr_dst_loc mr1 in
      let st1 := mr_state mr1 in
      let bufs1 := mr_bufs mr1 in

      let cnot_op := PP_LocalCNOT loc_ctrl_interm loc_tgt in
      let bufs2 := append_proto_to_mem mid_tgt cnot_op bufs1 in

      match lower_move loc_ctrl_interm mid_tgt mid_ctrl st1 bufs2 with
      | None => None
      | Some mr2 =>
          Some {| gr_state := mr_state mr2;
                  gr_bufs  := mr_bufs mr2 |}
      end
  end.

Definition owner_of_locus
  (owners : ownership)
  (loc : locus)
  : option membrane_id :=
  match first_pos loc with
  | None => None
  | Some p => owner_of_pos owners p
  end.

Definition default_owner_of_cexp
  (st : lowering_state)
  (ce : cexp)
  : option membrane_id :=
  match ce with
  | CNew _ => Some 0
  | CAppU loc _ => owner_of_locus (ls_owners st) loc
  | CMeas _ loc => owner_of_locus (ls_owners st) loc
  | Send _ _ _ => Some 0
  | Recv _ _ _ => Some 0
  end.

Definition lower_nonlocal_cz
  (ctrl_loc tgt_loc : locus) (ctrl_mem tgt_mem : membrane_id)
  (st : lowering_state) (bufs : proto_buffers)
  : option gate_result :=
  match lower_move ctrl_loc ctrl_mem tgt_mem st bufs with
  | None => None
  | Some mr =>
      let bufs' := append_proto_to_mem tgt_mem (PP_LocalCZ (mr_dst_loc mr) tgt_loc) (mr_bufs mr) in
      Some {| gr_state := mr_state mr; gr_bufs := bufs' |}
  end.
Definition hl_op_with_qubits := (dist_ir * list nposi)%type.



Fixpoint lower_ir_list
  (ops : list dist_ir)
  (st : lowering_state)
  (bufs : proto_buffers)
  : option gate_result :=
  match ops with
  | [] =>
      Some {| gr_state := st; gr_bufs := bufs |}

  | o :: os =>
      match o with
      | IR_Base ce =>
          match default_owner_of_cexp st ce with
          | None => None
          | Some mid =>
              let bufs' := append_proto_to_mem mid (PP_Base ce) bufs in
              lower_ir_list os st bufs'
          end

      | IR_Move loc src dst =>
          match lower_move loc src dst st bufs with
          | None => None
          | Some mr =>
              lower_ir_list os (mr_state mr) (mr_bufs mr)
          end

      | IR_NonlocalCNOT loc_c loc_t mid_c mid_t =>
          match lower_nonlocal_cnot loc_c loc_t mid_c mid_t st bufs with
          | None => None
          | Some gr =>
              lower_ir_list os (gr_state gr) (gr_bufs gr)
          end

      | IR_NonlocalCZ loc_c loc_t mid_c mid_t =>
          match lower_nonlocal_cz loc_c loc_t mid_c mid_t st bufs with
          | None => None
          | Some gr =>
              lower_ir_list os (gr_state gr) (gr_bufs gr)
          end

      | IR_If _ _ _ =>
          None
      end
  end.

(*****************************************************************)
(* Helpers                                                       *)
(*****************************************************************)

Fixpoint lookup_proto_mem
  (mid : membrane_id)
  (bufs : proto_buffers)
  : option (list dist_proto) :=
  match bufs with
  | nil => None
  | (m, ops) :: tl =>
      if Nat.eqb m mid then Some ops else lookup_proto_mem mid tl
  end.

(*****************************************************************)
(* Local-ops lowering                                            *)
(*****************************************************************)

Fixpoint lower_ir_list_to_proto_ops_fuel
  (fuel : nat)
  (mid : membrane_id)
  (ops : list dist_ir)
  (st : lowering_state)
  : option (lowering_state * list dist_proto) :=
  match fuel with
  | O => None
  | S fuel' =>
      let lower_one :=
        fun (op : dist_ir) (st0 : lowering_state) =>
          match op with
          | IR_Base (CNew r) =>
              let owners' := set_owner_many (ls_owners st0) (cutToQubits (r :: nil)) mid in
              let st' := {| ls_fresh := ls_fresh st0; ls_owners := owners' |} in
              Some (st', PP_Base (CNew r) :: nil)

          | IR_Base ce =>
              Some (st0, PP_Base ce :: nil)

          | IR_Move loc src dst =>
              match lower_move loc src dst st0 nil with
              | None => None
              | Some mr =>
                  match lookup_proto_mem mid (mr_bufs mr) with
                  | Some pops => Some (mr_state mr, pops)
                  | None => Some (mr_state mr, nil)
                  end
              end

          | IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem =>
              match lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem st0 nil with
              | None => None
              | Some gr =>
                  match lookup_proto_mem mid (gr_bufs gr) with
                  | Some pops => Some (gr_state gr, pops)
                  | None => Some (gr_state gr, nil)
                  end
              end

          | IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem =>
              match lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem st0 nil with
              | None => None
              | Some gr =>
                  match lookup_proto_mem mid (gr_bufs gr) with
                  | Some pops => Some (gr_state gr, pops)
                  | None => Some (gr_state gr, nil)
                  end
              end

          | IR_If b th el =>
              match lower_ir_list_to_proto_ops_fuel fuel' mid th st0 with
              | None => None
              | Some (st1, ops_th) =>
                  match lower_ir_list_to_proto_ops_fuel fuel' mid el st1 with
                  | None => None
                  | Some (st2, ops_el) =>
                      Some (st2, PP_If b ops_th ops_el :: nil)
                  end
              end
          end
      in
      match ops with
      | nil => Some (st, nil)
      | op :: tl =>
          match lower_one op st with
          | None => None
          | Some (st1, ops1) =>
              match lower_ir_list_to_proto_ops_fuel fuel' mid tl st1 with
              | None => None
              | Some (st2, ops2) =>
                  Some (st2, ops1 ++ ops2)
              end
          end
      end
  end.

(*****************************************************************)
(* Global-buffer lowering                                        *)
(*****************************************************************)

Fixpoint lower_ir_list_to_proto_fuel
  (fuel : nat)
  (mid : membrane_id)
  (ops : list dist_ir)
  (st : lowering_state)
  (bufs : proto_buffers)
  {struct fuel}
  : option (lowering_state * proto_buffers) :=
  match fuel with
  | O => None
  | S fuel' =>
      let lower_one :=
        fun (op : dist_ir) (st0 : lowering_state) (bufs0 : proto_buffers) =>
          match op with
          | IR_Base (CNew r) =>
              let owners' :=
                TeleportationCompilerCore.set_owner_many
                  (ls_owners st0)
                  (cutToQubits (r :: nil))
                  mid in
              let st' :=
                {|
                  ls_fresh := ls_fresh st0;
                  ls_owners := owners'
                |} in
              let bufs' :=
                append_proto_to_mem mid (PP_Base (CNew r)) bufs0 in
              Some (st', bufs')

          | IR_Base (CAppU _ _ as ce)
          | IR_Base (CMeas _ _ as ce)
          | IR_Base (Send _ _ _ as ce)
          | IR_Base (Recv _ _ _ as ce) =>
              Some (st0, append_proto_to_mem mid (PP_Base ce) bufs0)

          | IR_Move loc src dst =>
              match lower_move loc src dst st0 bufs0 with
              | Some mr => Some (mr_state mr, mr_bufs mr)
              | None => None
              end

          | IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem =>
              match lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem st0 bufs0 with
              | Some gr => Some (gr_state gr, gr_bufs gr)
              | None => None
              end

          | IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem =>
              match lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem st0 bufs0 with
              | Some gr => Some (gr_state gr, gr_bufs gr)
              | None => None
              end

          | IR_If b th el =>
              match lower_ir_list_to_proto_ops_fuel fuel' mid th st0 with
              | Some (st_th, ops_th) =>
                  match lower_ir_list_to_proto_ops_fuel fuel' mid el st0 with
                  | Some (_st_el, ops_el) =>
                      Some
                        (st_th,
                         append_proto_to_mem mid (PP_If b ops_th ops_el) bufs0)
                  | None => None
                  end
              | None => None
              end
          end
      in
      match ops with
      | nil => Some (st, bufs)
      | op :: tl =>
          match lower_one op st bufs with
          | Some (st1, bufs1) =>
              lower_ir_list_to_proto_fuel fuel' mid tl st1 bufs1
          | None => None
          end
      end
  end.


(*****************************************************************)
(* Compilation of protocol IR to process                         *)
(* FIXED: supports PP_If by compiling directly to process        *)
(*****************************************************************)

Definition compile_pp_sendbit (ch x : var) : cexp := Send ch x 0.
Definition compile_pp_recvbit (ch x : var) : cexp := Recv ch x 0.

Definition compile_pp_allocepr
  (a b : var) (_src _dst : membrane_id) : list cexp :=
  CNew (one_qubit_range a 0)
  :: CNew (one_qubit_range b 0)
  :: CAppU (default_locus_of_q a 0) (H a 0)
  :: CAppU (combine_locus (default_locus_of_q a 0)
                          (default_locus_of_q b 0))
           (CU a 0 (X b 0))
  :: nil.

Definition compile_pp_bellmeasure
  (loc : locus) (m1 m2 : var) : list cexp :=
  match first_qubit loc with
  | None => nil
  | Some q =>
      CAppU loc (CU q 0 (X q 0))
      :: CAppU loc (H q 0)
      :: CMeas m1 loc
      :: CMeas m2 loc
      :: nil
  end.

Fixpoint ops_to_process (ops : list cexp) : process :=
  match ops with
  | nil => PNil
  | op :: tl => AP op (ops_to_process tl)
  end.

Fixpoint process_append (p1 p2 : process) : process :=
  match p1 with
  | PNil => p2
  | AP op tl => AP op (process_append tl p2)
  | PIf b th el => PIf b (process_append th p2) (process_append el p2)
  end.

Fixpoint compile_dist_proto_base_process_fuel
  (fuel : nat)
  (op : dist_proto) : option process :=

  match fuel with
  | O => None
  | S fuel' =>
      match op with
      | PP_Base ce =>
          Some (AP ce PNil)

      | PP_AllocEPR a b src dst =>
          Some (ops_to_process (compile_pp_allocepr a b src dst))

      | PP_BellMeasure loc m1 m2 =>
          Some (ops_to_process (compile_pp_bellmeasure loc m1 m2))

      | PP_SendBit ch x =>
          Some (AP (compile_pp_sendbit ch x) PNil)

      | PP_RecvBit ch x =>
          Some (AP (compile_pp_recvbit ch x) PNil)

      | PP_CorrectX loc _ =>
          match first_qubit loc with
          | Some q => Some (AP (x_gate q) PNil)
          | None => None
          end

      | PP_CorrectZ loc _ =>
          match first_qubit loc with
          | Some q => Some (AP (z_gate q) PNil)
          | None => None
          end

      | PP_LocalCNOT l1 l2 =>
          match first_qubit l1, first_qubit l2 with
          | Some q1, Some q2 => Some (AP (cnot_gate q1 q2) PNil)
          | _, _ => None
          end

      | PP_LocalCZ l1 l2 =>
          match first_qubit l1, first_qubit l2 with
          | Some q1, Some q2 => Some (AP (cz_gate q1 q2) PNil)
          | _, _ => None
          end

      | PP_If b th el =>
          match compile_dist_proto_list_process_fuel fuel' th,
                compile_dist_proto_list_process_fuel fuel' el with
          | Some pth, Some pel => Some (PIf b pth pel)
          | _, _ => None
          end
      end
  end

with compile_dist_proto_list_process_fuel
  (fuel : nat)
  (ops : list dist_proto) : option process :=

  match fuel with
  | O => None
  | S fuel' =>
      match ops with
      | nil => Some PNil
      | op :: tl =>
          match compile_dist_proto_base_process_fuel fuel' op,
                compile_dist_proto_list_process_fuel fuel' tl with
          | Some p1, Some p2 => Some (process_append p1 p2)
          | _, _ => None
          end
      end
  end.

Definition compile_dist_proto_base_process
  (op : dist_proto) : option process :=
  compile_dist_proto_base_process_fuel 1000 op.

Definition compile_dist_proto_list_process
  (ops : list dist_proto) : option process :=
  compile_dist_proto_list_process_fuel 1000 ops.


Definition compile_mem_buffer
  (entry : membrane_id * list dist_proto) : option memb :=
  let '(mid, ops) := entry in
  match compile_dist_proto_list_process ops with
  | Some p => Some (Memb mid p)
  | None => None
  end.

Fixpoint proto_buffers_to_config
  (bufs : proto_buffers) : option config :=
  match bufs with
  | nil => Some nil
  | e :: tl =>
      match compile_mem_buffer e, proto_buffers_to_config tl with
      | Some m, Some cfg => Some (m :: cfg)
      | _, _ => None
      end
  end.

(*****************************************************************)
(* Compilation of protocol IR to base cexp                       *)
(*****************************************************************)


Definition compile_dist_proto (op : dist_proto) : option (list cexp) :=
  match op with
  | PP_Base ce =>
      Some (ce :: nil)

  | PP_AllocEPR a b src dst =>
      Some (compile_pp_allocepr a b src dst)

  | PP_BellMeasure loc m1 m2 =>
      Some (compile_pp_bellmeasure loc m1 m2)

  | PP_SendBit ch x =>
      Some (compile_pp_sendbit ch x :: nil)

  | PP_RecvBit ch x =>
      Some (compile_pp_recvbit ch x :: nil)

  | PP_CorrectX loc _ =>
      match first_qubit loc with
      | Some q => Some (x_gate q :: nil)
      | None => None
      end

  | PP_CorrectZ loc _ =>
      match first_qubit loc with
      | Some q => Some (z_gate q :: nil)
      | None => None
      end

  | PP_LocalCNOT l1 l2 =>
      match first_qubit l1, first_qubit l2 with
      | Some q1, Some q2 => Some (cnot_gate q1 q2 :: nil)
      | _, _ => None
      end

  | PP_LocalCZ l1 l2 =>
      match first_qubit l1, first_qubit l2 with
      | Some q1, Some q2 => Some (cz_gate q1 q2 :: nil)
      | _, _ => None
      end

  | PP_If _ _ _ =>
      None
  end.

Fixpoint compile_dist_proto_list (ops : list dist_proto) : option (list cexp) :=
  match ops with
  | nil => Some nil
  | op :: tl =>
      match op with
      | PP_If _ _ _ => None
      | _ =>
          match compile_dist_proto op, compile_dist_proto_list tl with
          | Some xs, Some ys => Some (xs ++ ys)
          | _, _ => None
          end
      end
  end.





Definition lower_ir_list_to_proto
  (mid : membrane_id)
  (ops : list dist_ir)
  (st : lowering_state)
  (bufs : proto_buffers)
  : option (lowering_state * proto_buffers) :=
  lower_ir_list_to_proto_fuel 1000 mid ops st bufs.

Definition lower_ir_list_to_proto_ops
  (mid : membrane_id)
  (ops : list dist_ir)
  (st : lowering_state)
  : option (lowering_state * list dist_proto) :=
  lower_ir_list_to_proto_ops_fuel 1000 mid ops st.

Definition lower_ir_to_proto_op
  (op : dist_ir)
  (mid : membrane_id)
  (st : lowering_state)
  (bufs : proto_buffers)
  : option (lowering_state * proto_buffers) :=
  lower_ir_list_to_proto mid (op :: nil) st bufs.

Definition lower_ir_to_proto_ops
  (op : dist_ir)
  (mid : membrane_id)
  (st : lowering_state)
  : option (lowering_state * list dist_proto) :=
  lower_ir_list_to_proto_ops mid (op :: nil) st.



Definition lower_solution_distributed_full_ir
  (sol : list (dist_ir * membrane_id)%type)
  (st : lowering_state)
  (bufs : proto_buffers)
  : option (lowering_state * proto_buffers) :=
  fold_left
    (fun acc itm =>
       match acc with
       | None => None
       | Some (st_acc, bufs_acc) =>
           let '(op, mid) := itm in
           lower_ir_to_proto_op op mid st_acc bufs_acc
       end)
    sol
    (Some (st, bufs)).

Definition ir_solution := list (dist_ir * membrane_id).


Definition default_config : config := nil.

Definition lower_solution
  (sol : ir_solution)
  (st : lowering_state)
  (bufs : proto_buffers)
  : option config :=
  match lower_solution_distributed_full_ir sol st bufs with
  | Some (_, bufs') => proto_buffers_to_config bufs'
  | None => None
  end.

Definition lower_ir_total
  (sol : ir_solution)
  (st : lowering_state)
  (bufs : proto_buffers)
  : config :=
  match lower_solution sol st bufs with
  | Some cfg => cfg
  | None => default_config
  end.

Definition compile_solution
  (sol : ir_solution)
  (st : lowering_state)
  (bufs : proto_buffers)
  : config :=
  lower_ir_total sol st bufs.


Definition lower_solution_distributed_full_tp
  (sol : list (dist_ir * membrane_id)%type)
  : option config :=
  match lower_solution_distributed_full_ir sol init_ls [] with
  | Some (_, bufs') => proto_buffers_to_config bufs'
  | None => None
  end.

(*****************************************************************)
(* Protocol-level runtime semantics                              *)
(*****************************************************************)

Definition bitstore : Type := list (var * nat)%type.
Definition chanstore : Type := list (var * list nat)%type.

Inductive proto_obs : Type :=
| ObsBase       : membrane_id -> cexp -> proto_obs
| ObsSend       : membrane_id -> var -> var -> nat -> proto_obs
| ObsRecv       : membrane_id -> var -> var -> nat -> proto_obs
| ObsAllocEPR   : membrane_id -> membrane_id -> var -> var -> proto_obs
| ObsMove       : nposi -> membrane_id -> membrane_id -> proto_obs
| ObsLocalCNOT  : locus -> locus -> membrane_id -> proto_obs
| ObsLocalCZ    : locus -> locus -> membrane_id -> proto_obs.

Inductive qterm : Type :=
| QT_Init : qterm
| QT_Basis : nat -> qterm
| QT_Gate : exp -> list nposi -> list qterm -> qterm
| QT_EPR : nposi -> nposi -> qterm
| QT_Measured : nat -> qterm -> qterm
| QT_Moved : membrane_id -> membrane_id -> qterm -> qterm
| QT_CNOT : qterm -> qterm -> qterm
| QT_CZ : qterm -> qterm -> qterm.

Definition quantum_state : Type := list (nposi * qterm)%type.

Record proto_runtime := {
  rt_lstate : lowering_state;
  rt_bits   : bitstore;
  rt_chans  : chanstore;
  rt_qstate : quantum_state;
  rt_trace  : list proto_obs
}.

Definition init_runtime : proto_runtime :=
  {| rt_lstate := init_ls;
     rt_bits := [];
     rt_chans := [];
     rt_qstate := [];
     rt_trace := [] |}.

Fixpoint lookup_bit (bs : bitstore) (x : var) : nat :=
  match bs with
  | [] => 0
  | (y,v) :: tl => if Nat.eqb x y then v else lookup_bit tl x
  end.

Fixpoint set_bit (bs : bitstore) (x : var) (v : nat) : bitstore :=
  match bs with
  | [] => [(x,v)]
  | (y,w) :: tl =>
      if Nat.eqb x y then (x,v) :: tl else (y,w) :: set_bit tl x v
  end.

Fixpoint enqueue_chan (cs : chanstore) (ch : var) (v : nat) : chanstore :=
  match cs with
  | [] => [(ch,[v])]
  | (c,vs) :: tl =>
      if Nat.eqb ch c then (c, vs ++ [v]) :: tl
      else (c,vs) :: enqueue_chan tl ch v
  end.

Fixpoint dequeue_chan (cs : chanstore) (ch : var) : option (nat * chanstore) :=
  match cs with
  | [] => None
  | (c,vs) :: tl =>
      if Nat.eqb ch c then
        match vs with
        | [] => None
        | v :: vs' => Some (v, (c,vs') :: tl)
        end
      else
        match dequeue_chan tl ch with
        | None => None
        | Some (v, tl') => Some (v, (c,vs) :: tl')
        end
  end.

Definition emit_obs (rt : proto_runtime) (o : proto_obs) : proto_runtime :=
  {| rt_lstate := rt_lstate rt;
     rt_bits := rt_bits rt;
     rt_chans := rt_chans rt;
     rt_qstate := rt_qstate rt;
     rt_trace := rt_trace rt ++ [o] |}.

Definition runtime_set_bit (rt : proto_runtime) (x : var) (v : nat) : proto_runtime :=
  {| rt_lstate := rt_lstate rt;
     rt_bits := set_bit (rt_bits rt) x v;
     rt_chans := rt_chans rt;
     rt_qstate := rt_qstate rt;
     rt_trace := rt_trace rt |}.

Definition runtime_set_owner (rt : proto_runtime) (p : nposi) (mid : membrane_id) : proto_runtime :=
  {| rt_lstate := {| ls_fresh := ls_fresh (rt_lstate rt);
                     ls_owners := set_owner (ls_owners (rt_lstate rt)) p mid |};
     rt_bits := rt_bits rt;
     rt_chans := rt_chans rt;
     rt_qstate := rt_qstate rt;
     rt_trace := rt_trace rt |}.

Definition runtime_replace_chans (rt : proto_runtime) (cs : chanstore) : proto_runtime :=
  {| rt_lstate := rt_lstate rt;
     rt_bits := rt_bits rt;
     rt_chans := cs;
     rt_qstate := rt_qstate rt;
     rt_trace := rt_trace rt |}.

Definition pos_of_var (x : var) : nposi := (N.of_nat x, 0%N).

Fixpoint lookup_qterm (qs : quantum_state) (p : nposi) : qterm :=
  match qs with
  | [] => QT_Init
  | (q,t) :: tl => if nposi_eq q p then t else lookup_qterm tl p
  end.

Fixpoint set_qterm (qs : quantum_state) (p : nposi) (t : qterm) : quantum_state :=
  match qs with
  | [] => [(p,t)]
  | (q,u) :: tl =>
      if nposi_eq q p then (p,t) :: tl else (q,u) :: set_qterm tl p t
  end.

Fixpoint set_many_qterms (qs : quantum_state) (ps : list nposi) (t : qterm) : quantum_state :=
  match ps with
  | [] => qs
  | p :: tl => set_many_qterms (set_qterm qs p t) tl t
  end.

Definition alloc_qubits (qs : quantum_state) (ps : list nposi) : quantum_state :=
  set_many_qterms qs ps (QT_Basis 0).

Definition apply_gate_symbolic (loc : locus) (e : exp) (qs : quantum_state) : quantum_state :=
  let ps := cutToQubits loc in
  let olds := map (lookup_qterm qs) ps in
  let t := QT_Gate e ps olds in
  set_many_qterms qs ps t.

Definition use_epr_symbolic
  (a b : var) (src dst : membrane_id) (rt : proto_runtime) : proto_runtime :=
  let pa := pos_of_var a in
  let pb := pos_of_var b in
  let t := QT_EPR pa pb in
  let qs1 := set_qterm (rt_qstate rt) pa t in
  let qs2 := set_qterm qs1 pb t in
  let own1 := set_owner (ls_owners (rt_lstate rt)) pa src in
  let own2 := set_owner own1 pb dst in
  {| rt_lstate := {| ls_fresh := ls_fresh (rt_lstate rt); ls_owners := own2 |};
     rt_bits := rt_bits rt;
     rt_chans := rt_chans rt;
     rt_qstate := qs2;
     rt_trace := rt_trace rt |}.

Definition move_symbolic
  (loc : locus) (src dst : membrane_id) (rt : proto_runtime) : option proto_runtime :=
  match first_pos loc with
  | None => None
  | Some p =>
      let t := lookup_qterm (rt_qstate rt) p in
      Some {| rt_lstate := {| ls_fresh := ls_fresh (rt_lstate rt);
                              ls_owners := set_owner (ls_owners (rt_lstate rt)) p dst |};
              rt_bits := rt_bits rt;
              rt_chans := rt_chans rt;
              rt_qstate := set_qterm (rt_qstate rt) p (QT_Moved src dst t);
              rt_trace := rt_trace rt |}
  end.

Definition local_cnot_symbolic
  (ctrl_loc tgt_loc : locus) (rt : proto_runtime) : option proto_runtime :=
  match first_pos ctrl_loc, first_pos tgt_loc with
  | Some pc, Some pt =>
      let tc := lookup_qterm (rt_qstate rt) pc in
      let tt := lookup_qterm (rt_qstate rt) pt in
      let t := QT_CNOT tc tt in
      Some {| rt_lstate := rt_lstate rt;
              rt_bits := rt_bits rt;
              rt_chans := rt_chans rt;
              rt_qstate := set_qterm (set_qterm (rt_qstate rt) pc t) pt t;
              rt_trace := rt_trace rt |}
  | _, _ => None
  end.

Definition local_cz_symbolic
  (ctrl_loc tgt_loc : locus) (rt : proto_runtime) : option proto_runtime :=
  match first_pos ctrl_loc, first_pos tgt_loc with
  | Some pc, Some pt =>
      let tc := lookup_qterm (rt_qstate rt) pc in
      let tt := lookup_qterm (rt_qstate rt) pt in
      let t := QT_CZ tc tt in
      Some {| rt_lstate := rt_lstate rt;
              rt_bits := rt_bits rt;
              rt_chans := rt_chans rt;
              rt_qstate := set_qterm (set_qterm (rt_qstate rt) pc t) pt t;
              rt_trace := rt_trace rt |}
  | _, _ => None
  end.

Definition eval_aexp_bits (bs : bitstore) (a : aexp) : nat :=
  match a with
  | BA x => lookup_bit bs x
  | Num n => n
  | _ => 0
  end.

Definition eval_cbexp_bits (bs : bitstore) (b : cbexp) : bool :=
  match b with
  | CEq a1 a2 => Nat.eqb (eval_aexp_bits bs a1) (eval_aexp_bits bs a2)
  | _ => false
  end.

Fixpoint exec_dist_proto_fuel
  (fuel : nat) (mid : membrane_id) (op : dist_proto) (rt : proto_runtime)
  : option proto_runtime :=
  match fuel with
  | O => None
  | S fuel' =>
      match op with
      | PP_Base (CNew r) =>
          let ps := cutToQubits (r :: nil) in
          let qs' := alloc_qubits (rt_qstate rt) ps in
          let own' := set_owner_many (ls_owners (rt_lstate rt)) ps mid in
          Some
            (emit_obs
               {| rt_lstate := {| ls_fresh := ls_fresh (rt_lstate rt);
                                  ls_owners := own' |};
                  rt_bits := rt_bits rt;
                  rt_chans := rt_chans rt;
                  rt_qstate := qs';
                  rt_trace := rt_trace rt |}
               (ObsBase mid (CNew r)))

      | PP_Base (CAppU loc e) =>
          Some
            (emit_obs
               {| rt_lstate := rt_lstate rt;
                  rt_bits := rt_bits rt;
                  rt_chans := rt_chans rt;
                  rt_qstate := apply_gate_symbolic loc e (rt_qstate rt);
                  rt_trace := rt_trace rt |}
               (ObsBase mid (CAppU loc e)))

      | PP_Base ce =>
          Some (emit_obs rt (ObsBase mid ce))

      | PP_AllocEPR a b src dst =>
          Some (emit_obs (use_epr_symbolic a b src dst rt) (ObsAllocEPR src dst a b))

      | PP_BellMeasure loc m1 m2 =>
          match move_symbolic loc mid mid rt with
          | None => None
          | Some rt1 =>
              Some
                {| rt_lstate := rt_lstate rt1;
                   rt_bits := set_bit (set_bit (rt_bits rt1) m1 0) m2 0;
                   rt_chans := rt_chans rt1;
                   rt_qstate := rt_qstate rt1;
                   rt_trace := rt_trace rt1 |}
          end

      | PP_SendBit ch x =>
          let v := lookup_bit (rt_bits rt) x in
          Some
            (emit_obs
               {| rt_lstate := rt_lstate rt;
                  rt_bits := rt_bits rt;
                  rt_chans := enqueue_chan (rt_chans rt) ch v;
                  rt_qstate := rt_qstate rt;
                  rt_trace := rt_trace rt |}
               (ObsSend mid ch x v))

      | PP_RecvBit ch x =>
          match dequeue_chan (rt_chans rt) ch with
          | None => None
          | Some (v, cs') =>
              Some
                (emit_obs
                   {| rt_lstate := rt_lstate rt;
                      rt_bits := set_bit (rt_bits rt) x v;
                      rt_chans := cs';
                      rt_qstate := rt_qstate rt;
                      rt_trace := rt_trace rt |}
                   (ObsRecv mid ch x v))
          end

      | PP_CorrectX loc _ =>
          match first_qubit loc with
          | None => None
          | Some q =>
              Some
                (emit_obs
                   {| rt_lstate := rt_lstate rt;
                      rt_bits := rt_bits rt;
                      rt_chans := rt_chans rt;
                      rt_qstate := apply_gate_symbolic loc (X q 0) (rt_qstate rt);
                      rt_trace := rt_trace rt |}
                   (ObsBase mid (x_gate q)))
          end

      | PP_CorrectZ loc _ =>
          match first_qubit loc with
          | None => None
          | Some q =>
              Some
                (emit_obs
                   {| rt_lstate := rt_lstate rt;
                      rt_bits := rt_bits rt;
                      rt_chans := rt_chans rt;
                      rt_qstate := apply_gate_symbolic loc (RZ 1 q 0) (rt_qstate rt);
                      rt_trace := rt_trace rt |}
                   (ObsBase mid (z_gate q)))
          end

      | PP_LocalCNOT ctrl_loc tgt_loc =>
          match local_cnot_symbolic ctrl_loc tgt_loc rt with
          | None => None
          | Some rt' => Some (emit_obs rt' (ObsLocalCNOT ctrl_loc tgt_loc mid))
          end

      | PP_LocalCZ ctrl_loc tgt_loc =>
          match local_cz_symbolic ctrl_loc tgt_loc rt with
          | None => None
          | Some rt' => Some (emit_obs rt' (ObsLocalCZ ctrl_loc tgt_loc mid))
          end

      | PP_If b th el =>
          if eval_cbexp_bits (rt_bits rt) b
          then exec_dist_proto_list_fuel fuel' mid th rt
          else exec_dist_proto_list_fuel fuel' mid el rt
      end
  end

with exec_dist_proto_list_fuel
  (fuel : nat) (mid : membrane_id) (ops : list dist_proto) (rt : proto_runtime)
  : option proto_runtime :=
  match fuel with
  | O => None
  | S fuel' =>
      match ops with
      | nil => Some rt
      | op :: tl =>
          match exec_dist_proto_fuel fuel' mid op rt with
          | None => None
          | Some rt' => exec_dist_proto_list_fuel fuel' mid tl rt'
          end
      end
  end.




Definition exec_dist_proto
  (mid : membrane_id) (op : dist_proto) (rt : proto_runtime) : option proto_runtime :=
  exec_dist_proto_fuel 1000 mid op rt.

Definition exec_dist_proto_list
  (mid : membrane_id) (ops : list dist_proto) (rt : proto_runtime) : option proto_runtime :=
  exec_dist_proto_list_fuel 1000 mid ops rt.

(*****************************************************************)
(* Optional abstract denotation interfaces for the new IR        *)
(*****************************************************************)

Record den_state := {
  ds_lstate : lowering_state;
  ds_bits   : bitstore;
  ds_chans  : chanstore;
  ds_qstate : quantum_state
}.

Definition erase_trace (rt : proto_runtime) : den_state :=
  {| ds_lstate := rt_lstate rt;
     ds_bits := rt_bits rt;
     ds_chans := rt_chans rt;
     ds_qstate := rt_qstate rt |}.

Definition mk_runtime (ds : den_state) : proto_runtime :=
  {| rt_lstate := ds_lstate ds;
     rt_bits := ds_bits ds;
     rt_chans := ds_chans ds;
     rt_qstate := ds_qstate ds;
     rt_trace := [] |}.

Definition denote_dist_proto
  (mid : membrane_id) (op : dist_proto) (ds : den_state) : option den_state :=
  match exec_dist_proto mid op (mk_runtime ds) with
  | Some rt' => Some (erase_trace rt')
  | None => None
  end.

Fixpoint denote_dist_proto_list
  (mid : membrane_id) (ops : list dist_proto) (ds : den_state) : option den_state :=
  match ops with
  | [] => Some ds
  | op :: tl =>
      match denote_dist_proto mid op ds with
      | Some ds' => denote_dist_proto_list mid tl ds'
      | None => None
      end
  end.

Definition exec_dist_ir
  (mid : membrane_id)
  (op : dist_ir)
  (rt : proto_runtime)
  : option proto_runtime :=
  match lower_ir_to_proto_op op mid (rt_lstate rt) nil with
  | None => None
  | Some (st', bufs') =>
      match lookup_proto_mem mid bufs' with
      | None =>
          (* no protocol generated → state update only *)
          Some {| rt_lstate := st';
                  rt_bits := rt_bits rt;
                  rt_chans := rt_chans rt;
                  rt_qstate := rt_qstate rt;
                  rt_trace := rt_trace rt |}

      | Some ops =>
          (* execute generated protocol *)
          exec_dist_proto_list mid ops
            {| rt_lstate := st';
               rt_bits := rt_bits rt;
               rt_chans := rt_chans rt;
               rt_qstate := rt_qstate rt;
               rt_trace := rt_trace rt |}
      end
  end.

Definition den_state_to_runtime (st : den_state) : proto_runtime :=
  {| rt_lstate := ds_lstate st;
     rt_bits := ds_bits st;
     rt_chans := ds_chans st;
     rt_qstate := ds_qstate st;
     rt_trace := nil |}.

Definition runtime_to_den_state (rt : proto_runtime) : den_state :=
  {| ds_lstate := rt_lstate rt;
     ds_bits := rt_bits rt;
     ds_chans := rt_chans rt;
     ds_qstate := rt_qstate rt |}.

Definition denote_dist_ir
  (mid : membrane_id)
  (op : dist_ir)
  (st : den_state)
  : option den_state :=
  match exec_dist_ir mid op (den_state_to_runtime st) with
  | None => None
  | Some rt' => Some (runtime_to_den_state rt')
  end.

Definition qdenote_proto_program
  (mid : membrane_id)
  (p : proto_program)
  (st : den_state)
  : option den_state :=
  match lookup_proto_mem mid p with
  | None => Some st
  | Some ops =>
      match exec_dist_proto_list mid ops (den_state_to_runtime st) with
      | None => None
      | Some rt' => Some (runtime_to_den_state rt')
      end
  end.

Definition exec_proto_buffer
  (mid : membrane_id)
  (bufs : proto_buffers)
  (rt : proto_runtime)
  : option proto_runtime :=
  match lookup_proto_mem mid bufs with
  | None => Some rt
  | Some ops => exec_dist_proto_list mid ops rt
  end.
Definition cpmap_equiv
  (f g : den_state -> option den_state) : Prop :=
  forall st st',
    f st = Some st' <-> g st = Some st'.

Definition ideal_move_denotation
  (loc : locus) (src dst : membrane_id)
  (ds : den_state) : option den_state :=
  match first_pos loc with
  | None => None
  | Some p =>
      let t := lookup_qterm (ds_qstate ds) p in
      Some
        {| ds_lstate :=
             {| ls_fresh := ls_fresh (ds_lstate ds);
                ls_owners := set_owner (ls_owners (ds_lstate ds)) p dst |};
           ds_bits := ds_bits ds;
           ds_chans := ds_chans ds;
           ds_qstate := set_qterm (ds_qstate ds) p (QT_Moved src dst t) |}
  end.





open Autodisq_extract

(* ============================================================ *)
(* Small safe test file                                         *)
(* ============================================================ *)

let mids_small : membrane_id list = [0; 1]

(* ============================================================ *)
(* SMALL PROGRAM TEST                                           *)
(* ============================================================ *)

let opA : myOp = OpAP (CNew (0, (0, 1)))
let opB : myOp = OpAP (CMeas (0, []))
let opC : myOp = OpAP (CNew (1, (0, 1)))

let small_prog1 : op_list = [opA; opB]
let small_prog2 : op_list = [opA; opC; opB]

(* ============================================================ *)
(* Helpers                                                      *)
(* ============================================================ *)

let one_qubit_range (q : var) : (var * (int * int)) = (q, (0, 1))
let l : locus = []

let rec seq start len =
  if len <= 0 then [] else start :: seq (start + 1) (len - 1)

let rec alloc_qubits_from (qs : var list) : op_list =
  match qs with
  | [] -> []
  | q :: tl -> OpAP (CNew (one_qubit_range q)) :: alloc_qubits_from tl

let rec cnot_from (ctrl : var) (qs : var list) : op_list =
  match qs with
  | [] -> []
  | q :: tl ->
      OpAP (CAppU (l, CU (ctrl, Num 0, X (q, Num 0)))) :: cnot_from ctrl tl

let rec meas_all_from (cs : var list) : op_list =
  match cs with
  | [] -> []
  | c :: tl -> OpAP (CMeas (c, l)) :: meas_all_from tl

let rec apply_H_all_from (qs : var list) : op_list =
  match qs with
  | [] -> []
  | q :: tl -> OpAP (CAppU (l, H (q, Num 0))) :: apply_H_all_from tl

let rec controlled_x_chain_from (ctrls : var list) (tgts : var list) : op_list =
  match ctrls, tgts with
  | c :: ctrls', t :: tgts' ->
      OpAP (CAppU (l, CU (c, Num 0, X (t, Num 0))))
      :: controlled_x_chain_from ctrls' tgts'
  | _, _ -> []

(* ============================================================ *)
(* Benchmarks                                                   *)
(* ============================================================ *)

let ghz8_n = 8
let ghz8_qs : var list = seq 0 ghz8_n
let ghz8_outs : var list = seq 100 ghz8_n
let ghz8_prog : op_list =
  alloc_qubits_from ghz8_qs
  @ [OpAP (CAppU (l, H (0, Num 0)))]
  @ cnot_from 0 (seq 1 (ghz8_n - 1))
  @ meas_all_from ghz8_outs

let ghz16_n = 16
let ghz16_qs : var list = seq 0 ghz16_n
let ghz16_outs : var list = seq 200 ghz16_n
let ghz16_prog : op_list =
  alloc_qubits_from ghz16_qs
  @ [OpAP (CAppU (l, H (0, Num 0)))]
  @ cnot_from 0 (seq 1 (ghz16_n - 1))
  @ meas_all_from ghz16_outs

let ghz32_n = 32
let ghz32_qs : var list = seq 0 ghz32_n
let ghz32_outs : var list = seq 300 ghz32_n
let ghz32_prog : op_list =
  alloc_qubits_from ghz32_qs
  @ [OpAP (CAppU (l, H (0, Num 0)))]
  @ cnot_from 0 (seq 1 (ghz32_n - 1))
  @ meas_all_from ghz32_outs

let shor8_qs : var list = seq 0 8
let shor8_ctrls : var list = seq 0 4
let shor8_tgts : var list = seq 4 4
let shor8_outs : var list = seq 300 8
let shor8_prog : op_list =
  alloc_qubits_from shor8_qs
  @ apply_H_all_from shor8_ctrls
  @ controlled_x_chain_from shor8_ctrls shor8_tgts
  @ [OpAP (CAppU (l, QFT (0, 4)))]
  @ meas_all_from shor8_outs

let shor16_qs : var list = seq 0 16
let shor16_ctrls : var list = seq 0 8
let shor16_tgts : var list = seq 8 8
let shor16_outs : var list = seq 400 16
let shor16_prog : op_list =
  alloc_qubits_from shor16_qs
  @ apply_H_all_from shor16_ctrls
  @ controlled_x_chain_from shor16_ctrls shor16_tgts
  @ [OpAP (CAppU (l, QFT (0, 8)))]
  @ meas_all_from shor16_outs

let qft8_n = 8
let qft8_q0 = 0
let qft8_qubits : var list = seq qft8_q0 qft8_n
let qft8_outs : var list = seq 600 qft8_n
let qft8_prog : op_list =
  alloc_qubits_from qft8_qubits
  @ [ OpAP (CAppU (l, QFT (qft8_q0, qft8_n)));
      OpAP (CAppU (l, RQFT (qft8_q0, qft8_n))) ]
  @ meas_all_from qft8_outs

let qft16_n = 16
let qft16_q0 = 0
let qft16_qubits : var list = seq qft16_q0 qft16_n
let qft16_outs : var list = seq 700 qft16_n
let qft16_prog : op_list =
  alloc_qubits_from qft16_qubits
  @ [ OpAP (CAppU (l, QFT (qft16_q0, qft16_n)));
      OpAP (CAppU (l, RQFT (qft16_q0, qft16_n))) ]
  @ meas_all_from qft16_outs

let qft32_n = 32
let qft32_q0 = 0
let qft32_qubits : var list = seq qft32_q0 qft32_n
let qft32_outs : var list = seq 1000 qft32_n
let qft32_prog : op_list =
  alloc_qubits_from qft32_qubits
  @ [ OpAP (CAppU (l, QFT (qft32_q0, qft32_n)));
      OpAP (CAppU (l, RQFT (qft32_q0, qft32_n))) ]
  @ meas_all_from qft32_outs

let qadd8_n = 8
let qadd8_q0 = 0
let qadd8_qubits : var list = seq qadd8_q0 qadd8_n
let qadd8_outs : var list = seq 800 qadd8_n
let qadd8_x = 100
let qftAdder8_prog : op_list =
  alloc_qubits_from qadd8_qubits
  @ [ OpAP (CAppU (l, QFT (qadd8_q0, 4)));
      OpAP (CAppU (l, Addto (qadd8_x, qadd8_q0)));
      OpAP (CAppU (l, RQFT (qadd8_q0, 4))) ]
  @ meas_all_from qadd8_outs

let qadd16_n = 16
let qadd16_q0 = 0
let qadd16_qubits : var list = seq qadd16_q0 qadd16_n
let qadd16_outs : var list = seq 900 qadd16_n
let qadd16_x = 101
let qftAdder16_prog : op_list =
  alloc_qubits_from qadd16_qubits
  @ [ OpAP (CAppU (l, QFT (qadd16_q0, 8)));
      OpAP (CAppU (l, Addto (qadd16_x, qadd16_q0)));
      OpAP (CAppU (l, RQFT (qadd16_q0, 8))) ]
  @ meas_all_from qadd16_outs

let qadd32_n = 32
let qadd32_q0 = 0
let qadd32_qubits : var list = seq qadd32_q0 qadd32_n
let qadd32_outs : var list = seq 1100 qadd32_n
let qadd32_x = 102
let qftAdder32_prog : op_list =
  alloc_qubits_from qadd32_qubits
  @ [ OpAP (CAppU (l, QFT (qadd32_q0, 16)));
      OpAP (CAppU (l, Addto (qadd32_x, qadd32_q0)));
      OpAP (CAppU (l, RQFT (qadd32_q0, 16))) ]
  @ meas_all_from qadd32_outs

(* ============================================================ *)
(* Counters                                                     *)
(* ============================================================ *)

let rec count_QFT (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, QFT (_, _))) :: tl -> 1 + count_QFT tl
  | _ :: tl -> count_QFT tl

let rec count_RQFT (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, RQFT (_, _))) :: tl -> 1 + count_RQFT tl
  | _ :: tl -> count_RQFT tl

let rec count_Addto (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, Addto (_, _))) :: tl -> 1 + count_Addto tl
  | _ :: tl -> count_Addto tl

let rec count_CU (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, CU (_, _, _))) :: tl -> 1 + count_CU tl
  | _ :: tl -> count_CU tl

(* ============================================================ *)
(* Compact pretty printers                                      *)
(* ============================================================ *)

let take n xs =
  let rec aux k acc = function
    | [] -> List.rev acc
    | _ when k <= 0 -> List.rev acc
    | x :: tl -> aux (k - 1) (x :: acc) tl
  in
  aux n [] xs

let string_of_list sep f xs =
  String.concat sep (List.map f xs)

let string_of_range (q, (lo, hi)) =
  Printf.sprintf "(%d,(%d,%d))" q lo hi

let string_of_locus (k : locus) =
  "[" ^ string_of_list "; " string_of_range k ^ "]"

let rec string_of_aexp = function
  | BA x -> Printf.sprintf "BA %d" x
  | Num n -> Printf.sprintf "Num %d" n
  | APlus (a, b) -> Printf.sprintf "APlus(%s,%s)" (string_of_aexp a) (string_of_aexp b)
  | AMult (a, b) -> Printf.sprintf "AMult(%s,%s)" (string_of_aexp a) (string_of_aexp b)
  | AModMult (a, b, c) ->
      Printf.sprintf "AModMult(%s,%s,%s)"
        (string_of_aexp a) (string_of_aexp b) (string_of_aexp c)

let string_of_cbexp = function
  | CEq (a, b) -> Printf.sprintf "CEq(%s,%s)" (string_of_aexp a) (string_of_aexp b)
  | CLt (a, b) -> Printf.sprintf "CLt(%s,%s)" (string_of_aexp a) (string_of_aexp b)

let rec string_of_exp = function
  | SKIP (x, a) -> Printf.sprintf "SKIP(%d,%s)" x (string_of_aexp a)
  | X (x, a) -> Printf.sprintf "X(%d,%s)" x (string_of_aexp a)
  | CU (x, a, e) -> Printf.sprintf "CU(%d,%s,%s)" x (string_of_aexp a) (string_of_exp e)
  | RZ (q, x, a) -> Printf.sprintf "RZ(%d,%d,%s)" q x (string_of_aexp a)
  | RRZ (q, x, a) -> Printf.sprintf "RRZ(%d,%d,%s)" q x (string_of_aexp a)
  | SR (q, x) -> Printf.sprintf "SR(%d,%d)" q x
  | SRR (q, x) -> Printf.sprintf "SRR(%d,%d)" q x
  | QFT (x, n) -> Printf.sprintf "QFT(%d,%d)" x n
  | RQFT (x, n) -> Printf.sprintf "RQFT(%d,%d)" x n
  | H (x, a) -> Printf.sprintf "H(%d,%s)" x (string_of_aexp a)
  | Addto (x, q) -> Printf.sprintf "Addto(%d,%d)" x q
  | Seq (e1, e2) -> Printf.sprintf "Seq(%s,%s)" (string_of_exp e1) (string_of_exp e2)

let string_of_cexp = function
  | CNew r -> Printf.sprintf "CNew%s" (string_of_range r)
  | CAppU (k, e) -> Printf.sprintf "CAppU(%s,%s)" (string_of_locus k) (string_of_exp e)
  | CMeas (x, k) -> Printf.sprintf "CMeas(%d,%s)" x (string_of_locus k)
  | Send (c, x, a) -> Printf.sprintf "Send(%d,%d,%d)" c x a
  | Recv (c, x, y) -> Printf.sprintf "Recv(%d,%d,%d)" c x y

let process_ops_limit = 12

let process_to_ops (p : process) : string list * bool =
  let rec aux acc n p =
    if n <= 0 then (List.rev acc, true)
    else
      match p with
      | PNil -> (List.rev acc, false)
      | AP (a, p') -> aux (string_of_cexp a :: acc) (n - 1) p'
      | PIf (b, p1, p2) ->
          let s =
            Printf.sprintf "IF %s THEN (...) ELSE (...)"
              (string_of_cbexp b)
          in
          (List.rev (s :: acc), true)
  in
  aux [] process_ops_limit p

let string_of_process (p : process) =
  let ops, truncated = process_to_ops p in
  let body = String.concat " ; " ops in
  if truncated then body ^ " ; ..." else body

let process_length (p : process) =
  let rec aux acc = function
    | PNil -> acc
    | AP (_, p') -> aux (acc + 1) p'
    | PIf (_, p1, p2) -> acc + 1 + aux 0 p1 + aux 0 p2
  in
  aux 0 p

let string_of_memb (Memb (mid, p)) =
  Printf.sprintf "Memb %d { len=%d; %s }"
    mid (process_length p) (string_of_process p)

let string_of_config (cfg : config) =
  "[\n  " ^ String.concat ";\n  " (List.map string_of_memb cfg) ^ "\n]"

(* ============================================================ *)
(* Safe reporting                                               *)
(* ============================================================ *)

let print_separator () =
  print_endline "------------------------------------------------------------"

let print_int name x =
  Printf.printf "%s = %d\n%!" name x

let report_best name = function
  | None ->
      print_separator ();
      Printf.printf "%s = None\n%!" name
  | Some cfg ->
      print_separator ();
      Printf.printf "%s = Some\n%s\n%!" name (string_of_config cfg);
      Printf.printf "fit = %d\n%!" (fit cfg);
      Printf.printf "count_comm_ops = %d\n%!" (count_comm_ops cfg);
      Printf.printf "max_load = %d\n%!" (max_load cfg)

let protect name f =
  try f ()
  with
  | Stack_overflow ->
      print_separator ();
      Printf.printf "%s = ERROR(Stack_overflow)\n%!" name
  | Out_of_memory ->
      print_separator ();
      Printf.printf "%s = ERROR(Out_of_memory)\n%!" name
  | exn ->
      print_separator ();
      Printf.printf "%s = ERROR(%s)\n%!" name (Printexc.to_string exn)

let run_best name prog mids =
  protect name (fun () -> report_best name (autodisq_best prog mids))

let run_best_1 name prog mids =
  protect name (fun () -> report_best name (autodisq_best_1 prog mids))

let run_int name thunk =
  protect name (fun () -> print_int name (thunk ()))

(* ============================================================ *)
(* Main                                                         *)
(* ============================================================ *)

let () =
  Printexc.record_backtrace true;

  run_best "autodisq_best small_prog1 mids_small" small_prog1 mids_small;
  run_best "autodisq_best small_prog2 mids_small" small_prog2 mids_small;

  run_best   "autodisq_best GHZ8_prog [0;1]" ghz8_prog [0;1];
  run_best_1 "autodisq_best_1 GHZ8_prog [0;1]" ghz8_prog [0;1];

  run_best   "autodisq_best GHZ16_prog [0;1]" ghz16_prog [0;1];
  run_best_1 "autodisq_best_1 GHZ16_prog [0;1]" ghz16_prog [0;1];

  run_best   "autodisq_best SHOR8_prog [0;1]" shor8_prog [0;1];
  run_best_1 "autodisq_best_1 SHOR8_prog [0;1]" shor8_prog [0;1];

  run_best   "autodisq_best SHOR16_prog [0;1]" shor16_prog [0;1];

  run_best   "autodisq_best QFT8_prog [0;1]" qft8_prog [0;1];
  run_best_1 "autodisq_best_1 QFT8_prog [0;1]" qft8_prog [0;1];

  run_best   "autodisq_best QFT16_prog [0;1]" qft16_prog [0;1];
  run_best_1 "autodisq_best_1 QFT16_prog [0;1]" qft16_prog [0;1];

  run_best   "autodisq_best QFTAdder8_prog [0;1]" qftAdder8_prog [0;1];
  run_best_1 "autodisq_best_1 QFTAdder8_prog [0;1]" qftAdder8_prog [0;1];

  run_best   "autodisq_best QFTAdder16_prog [0;1]" qftAdder16_prog [0;1];
  run_best_1 "autodisq_best_1 QFTAdder16_prog [0;1]" qftAdder16_prog [0;1];

  run_int "count_QFT QFT32_prog" (fun () -> count_QFT qft32_prog);
  run_int "count_RQFT QFT32_prog" (fun () -> count_RQFT qft32_prog);
  run_int "count_Addto QFTAdder32_prog" (fun () -> count_Addto qftAdder32_prog);
  run_int "count_CU GHZ32_prog" (fun () -> count_CU ghz32_prog);

  run_best "autodisq_best QFT32_prog [0;1]" qft32_prog [0;1];
  run_best "autodisq_best QFTAdder32_prog [0;1]" qftAdder32_prog [0;1]








(*


ocamlc -w -3 -c autodisq_extract.mli
ocamlc -w -3 -c autodisq_extract.ml
ocamlc -c main.ml
ocamlc -o test autodisq_extract.cmo main.cmo
./test





*)







(*
open Autodisq_extract

(* ============================================================ *)
(* Small safe test file                                         *)
(* ============================================================ *)

let mids_small : membrane_id list = [0; 1]

(* ============================================================ *)
(* SMALL PROGRAM TEST                                           *)
(* ============================================================ *)

let opA : myOp = OpAP (CNew (0, (0, 1)))
let opB : myOp = OpAP (CMeas (0, []))
let opC : myOp = OpAP (CNew (1, (0, 1)))

let small_prog1 : op_list = [opA; opB]
let small_prog2 : op_list = [opA; opC; opB]

(* ============================================================ *)
(* Helpers for building GHZ / Shor / QFT programs               *)
(* ============================================================ *)

let one_qubit_range (q : var) : (var * (int * int)) = (q, (0, 1))

let l : locus = []

let rec alloc_qubits_from (qs : var list) : op_list =
  match qs with
  | [] -> []
  | q :: tl -> OpAP (CNew (one_qubit_range q)) :: alloc_qubits_from tl

let rec cnot_from (ctrl : var) (qs : var list) : op_list =
  match qs with
  | [] -> []
  | q :: tl ->
      OpAP (CAppU (l, CU (ctrl, Num 0, X (q, Num 0)))) :: cnot_from ctrl tl

let rec meas_all_from (cs : var list) : op_list =
  match cs with
  | [] -> []
  | c :: tl -> OpAP (CMeas (c, l)) :: meas_all_from tl

let rec apply_H_all_from (qs : var list) : op_list =
  match qs with
  | [] -> []
  | q :: tl -> OpAP (CAppU (l, H (q, Num 0))) :: apply_H_all_from tl

let rec controlled_x_chain_from (ctrls : var list) (tgts : var list) : op_list =
  match ctrls, tgts with
  | c :: ctrls', t :: tgts' ->
      OpAP (CAppU (l, CU (c, Num 0, X (t, Num 0))))
      :: controlled_x_chain_from ctrls' tgts'
  | _, _ -> []

(* ============================================================ *)
(* GHZ benchmarks                                               *)
(* ============================================================ *)

let ghz8_n = 8
let ghz8_qs : var list = seq 0 ghz8_n
let ghz8_outs : var list = seq 100 ghz8_n

let ghz8_prog : op_list =
  alloc_qubits_from ghz8_qs
  @ [OpAP (CAppU (l, H (0, Num 0)))]
  @ cnot_from 0 (seq 1 (ghz8_n - 1))
  @ meas_all_from ghz8_outs

let ghz16_n = 16
let ghz16_qs : var list = seq 0 ghz16_n
let ghz16_outs : var list = seq 200 ghz16_n

let ghz16_prog : op_list =
  alloc_qubits_from ghz16_qs
  @ [OpAP (CAppU (l, H (0, Num 0)))]
  @ cnot_from 0 (seq 1 (ghz16_n - 1))
  @ meas_all_from ghz16_outs

let ghz32_n = 32
let ghz32_qs : var list = seq 0 ghz32_n
let ghz32_outs : var list = seq 300 ghz32_n

let ghz32_prog : op_list =
  alloc_qubits_from ghz32_qs
  @ [OpAP (CAppU (l, H (0, Num 0)))]
  @ cnot_from 0 (seq 1 (ghz32_n - 1))
  @ meas_all_from ghz32_outs

(* ============================================================ *)
(* Shor-style skeleton benchmarks                               *)
(* ============================================================ *)

let shor8_qs : var list = seq 0 8
let shor8_ctrls : var list = seq 0 4
let shor8_tgts : var list = seq 4 4
let shor8_outs : var list = seq 300 8

let shor8_prog : op_list =
  alloc_qubits_from shor8_qs
  @ apply_H_all_from shor8_ctrls
  @ controlled_x_chain_from shor8_ctrls shor8_tgts
  @ [OpAP (CAppU (l, QFT (0, 4)))]
  @ meas_all_from shor8_outs

let shor16_qs : var list = seq 0 16
let shor16_ctrls : var list = seq 0 8
let shor16_tgts : var list = seq 8 8
let shor16_outs : var list = seq 400 16

let shor16_prog : op_list =
  alloc_qubits_from shor16_qs
  @ apply_H_all_from shor16_ctrls
  @ controlled_x_chain_from shor16_ctrls shor16_tgts
  @ [OpAP (CAppU (l, QFT (0, 8)))]
  @ meas_all_from shor16_outs

(* ============================================================ *)
(* QFT benchmarks                                               *)
(* ============================================================ *)

let qft8_n = 8
let qft8_q0 = 0
let qft8_qubits : var list = seq qft8_q0 qft8_n
let qft8_outs : var list = seq 600 qft8_n

let qft8_prog : op_list =
  alloc_qubits_from qft8_qubits
  @ [ OpAP (CAppU (l, QFT (qft8_q0, qft8_n)));
      OpAP (CAppU (l, RQFT (qft8_q0, qft8_n))) ]
  @ meas_all_from qft8_outs

let qft16_n = 16
let qft16_q0 = 0
let qft16_qubits : var list = seq qft16_q0 qft16_n
let qft16_outs : var list = seq 700 qft16_n

let qft16_prog : op_list =
  alloc_qubits_from qft16_qubits
  @ [ OpAP (CAppU (l, QFT (qft16_q0, qft16_n)));
      OpAP (CAppU (l, RQFT (qft16_q0, qft16_n))) ]
  @ meas_all_from qft16_outs

let qft32_n = 32
let qft32_q0 = 0
let qft32_qubits : var list = seq qft32_q0 qft32_n
let qft32_outs : var list = seq 1000 qft32_n

let qft32_prog : op_list =
  alloc_qubits_from qft32_qubits
  @ [ OpAP (CAppU (l, QFT (qft32_q0, qft32_n)));
      OpAP (CAppU (l, RQFT (qft32_q0, qft32_n))) ]
  @ meas_all_from qft32_outs

(* ============================================================ *)
(* QFT adder benchmarks                                         *)
(* ============================================================ *)

let qadd8_n = 8
let qadd8_q0 = 0
let qadd8_qubits : var list = seq qadd8_q0 qadd8_n
let qadd8_outs : var list = seq 800 qadd8_n
let qadd8_x = 100

let qftAdder8_prog : op_list =
  alloc_qubits_from qadd8_qubits
  @ [ OpAP (CAppU (l, QFT (qadd8_q0, 4)));
      OpAP (CAppU (l, Addto (qadd8_x, qadd8_q0)));
      OpAP (CAppU (l, RQFT (qadd8_q0, 4))) ]
  @ meas_all_from qadd8_outs

let qadd16_n = 16
let qadd16_q0 = 0
let qadd16_qubits : var list = seq qadd16_q0 qadd16_n
let qadd16_outs : var list = seq 900 qadd16_n
let qadd16_x = 101

let qftAdder16_prog : op_list =
  alloc_qubits_from qadd16_qubits
  @ [ OpAP (CAppU (l, QFT (qadd16_q0, 8)));
      OpAP (CAppU (l, Addto (qadd16_x, qadd16_q0)));
      OpAP (CAppU (l, RQFT (qadd16_q0, 8))) ]
  @ meas_all_from qadd16_outs

let qadd32_n = 32
let qadd32_q0 = 0
let qadd32_qubits : var list = seq qadd32_q0 qadd32_n
let qadd32_outs : var list = seq 1100 qadd32_n
let qadd32_x = 102

let qftAdder32_prog : op_list =
  alloc_qubits_from qadd32_qubits
  @ [ OpAP (CAppU (l, QFT (qadd32_q0, 16)));
      OpAP (CAppU (l, Addto (qadd32_x, qadd32_q0)));
      OpAP (CAppU (l, RQFT (qadd32_q0, 16))) ]
  @ meas_all_from qadd32_outs

(* ============================================================ *)
(* Counters                                                     *)
(* ============================================================ *)

let rec count_QFT (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, QFT (_, _))) :: tl -> 1 + count_QFT tl
  | _ :: tl -> count_QFT tl

let rec count_RQFT (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, RQFT (_, _))) :: tl -> 1 + count_RQFT tl
  | _ :: tl -> count_RQFT tl

let rec count_Addto (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, Addto (_, _))) :: tl -> 1 + count_Addto tl
  | _ :: tl -> count_Addto tl

let rec count_CU (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, CU (_, _, _))) :: tl -> 1 + count_CU tl
  | _ :: tl -> count_CU tl

(* ============================================================ *)
(* Pretty printers                                              *)
(* ============================================================ *)

let string_of_list sep f xs =
  String.concat sep (List.map f xs)

let string_of_range (q, (lo, hi)) =
  Printf.sprintf "(%d,(%d,%d))" q lo hi

let string_of_locus (k : locus) =
  "[" ^ string_of_list "; " string_of_range k ^ "]"

let rec string_of_aexp = function
  | BA x -> Printf.sprintf "BA %d" x
  | Num n -> Printf.sprintf "Num %d" n
  | APlus (a, b) ->
      Printf.sprintf "APlus(%s,%s)" (string_of_aexp a) (string_of_aexp b)
  | AMult (a, b) ->
      Printf.sprintf "AMult(%s,%s)" (string_of_aexp a) (string_of_aexp b)
  | AModMult (a, b, c) ->
      Printf.sprintf "AModMult(%s,%s,%s)"
        (string_of_aexp a) (string_of_aexp b) (string_of_aexp c)

let string_of_cbexp = function
  | CEq (a, b) ->
      Printf.sprintf "CEq(%s,%s)" (string_of_aexp a) (string_of_aexp b)
  | CLt (a, b) ->
      Printf.sprintf "CLt(%s,%s)" (string_of_aexp a) (string_of_aexp b)

let rec string_of_exp = function
  | SKIP (x, a) ->
      Printf.sprintf "SKIP(%d,%s)" x (string_of_aexp a)
  | X (x, a) ->
      Printf.sprintf "X(%d,%s)" x (string_of_aexp a)
  | CU (x, a, e) ->
      Printf.sprintf "CU(%d,%s,%s)" x (string_of_aexp a) (string_of_exp e)
  | RZ (q, x, a) ->
      Printf.sprintf "RZ(%d,%d,%s)" q x (string_of_aexp a)
  | RRZ (q, x, a) ->
      Printf.sprintf "RRZ(%d,%d,%s)" q x (string_of_aexp a)
  | SR (q, x) ->
      Printf.sprintf "SR(%d,%d)" q x
  | SRR (q, x) ->
      Printf.sprintf "SRR(%d,%d)" q x
  | QFT (x, n) ->
      Printf.sprintf "QFT(%d,%d)" x n
  | RQFT (x, n) ->
      Printf.sprintf "RQFT(%d,%d)" x n
  | H (x, a) ->
      Printf.sprintf "H(%d,%s)" x (string_of_aexp a)
  | Addto (x, q) ->
      Printf.sprintf "Addto(%d,%d)" x q
  | Seq (e1, e2) ->
      Printf.sprintf "Seq(%s,%s)" (string_of_exp e1) (string_of_exp e2)

let string_of_cexp = function
  | CNew r ->
      Printf.sprintf "CNew%s" (string_of_range r)
  | CAppU (k, e) ->
      Printf.sprintf "CAppU(%s,%s)" (string_of_locus k) (string_of_exp e)
  | CMeas (x, k) ->
      Printf.sprintf "CMeas(%d,%s)" x (string_of_locus k)
  | Send (c, x, a) ->
      Printf.sprintf "Send(%d,%d,%d)" c x a
  | Recv (c, x, y) ->
      Printf.sprintf "Recv(%d,%d,%d)" c x y

let rec flatten_process = function
  | PNil -> []
  | AP (a, p) -> string_of_cexp a :: flatten_process p
  | PIf (b, p1, p2) ->
      [ Printf.sprintf "IF %s THEN (%s) ELSE (%s)"
          (string_of_cbexp b)
          (string_of_process p1)
          (string_of_process p2) ]

and string_of_process p =
  match flatten_process p with
  | [] -> "PNil"
  | xs -> String.concat " ; " xs

let string_of_memb (Memb (mid, p)) =
  Printf.sprintf "Memb %d { %s }" mid (string_of_process p)

let string_of_config (cfg : config) =
  "[\n  " ^ String.concat ";\n  " (List.map string_of_memb cfg) ^ "\n]"

let string_of_option_config = function
  | None -> "None"
  | Some cfg -> "Some " ^ string_of_config cfg

(* ============================================================ *)
(* Report helpers                                               *)
(* ============================================================ *)

let print_separator () =
  print_endline "------------------------------------------------------------"

let print_int name x =
  Printf.printf "%s = %d\n" name x

let report_best name = function
  | None ->
      print_separator ();
      Printf.printf "%s = None\n" name
  | Some cfg ->
      print_separator ();
      Printf.printf "%s = Some\n%s\n" name (string_of_config cfg);
      Printf.printf "fit = %d\n" (fit cfg);
      Printf.printf "count_comm_ops = %d\n" (count_comm_ops cfg);
      Printf.printf "max_load = %d\n" (max_load cfg)

let run_best name prog mids =
  report_best name (autodisq_best prog mids)

let run_best_1 name prog mids =
  report_best name (autodisq_best_1 prog mids)

(* ============================================================ *)
(* Main                                                         *)
(* ============================================================ *)

let () =
  run_best "autodisq_best small_prog1 mids_small" small_prog1 mids_small;
  run_best "autodisq_best small_prog2 mids_small" small_prog2 mids_small;

  run_best   "autodisq_best GHZ8_prog [0;1]" ghz8_prog [0;1];
  run_best_1 "autodisq_best_1 GHZ8_prog [0;1]" ghz8_prog [0;1];

  run_best   "autodisq_best GHZ16_prog [0;1]" ghz16_prog [0;1];
  run_best_1 "autodisq_best_1 GHZ16_prog [0;1]" ghz16_prog [0;1];

  run_best   "autodisq_best SHOR8_prog [0;1]" shor8_prog [0;1];
  run_best_1 "autodisq_best_1 SHOR8_prog [0;1]" shor8_prog [0;1];

  run_best   "autodisq_best SHOR16_prog [0;1]" shor16_prog [0;1];

  run_best   "autodisq_best QFT8_prog [0;1]" qft8_prog [0;1];
  run_best_1 "autodisq_best_1 QFT8_prog [0;1]" qft8_prog [0;1];

  run_best   "autodisq_best QFT16_prog [0;1]" qft16_prog [0;1];
  run_best_1 "autodisq_best_1 QFT16_prog [0;1]" qft16_prog [0;1];

  run_best   "autodisq_best QFTAdder8_prog [0;1]" qftAdder8_prog [0;1];
  run_best_1 "autodisq_best_1 QFTAdder8_prog [0;1]" qftAdder8_prog [0;1];

  run_best   "autodisq_best QFTAdder16_prog [0;1]" qftAdder16_prog [0;1];
  run_best_1 "autodisq_best_1 QFTAdder16_prog [0;1]" qftAdder16_prog [0;1];

  print_separator ();
  print_int "count_QFT QFT32_prog" (count_QFT qft32_prog);
  print_int "count_RQFT QFT32_prog" (count_RQFT qft32_prog);
  print_int "count_Addto QFTAdder32_prog" (count_Addto qftAdder32_prog);
  print_int "count_CU GHZ32_prog" (count_CU ghz32_prog);

  run_best "autodisq_best QFT32_prog [0;1]" qft32_prog [0;1];
  run_best "autodisq_best QFTAdder32_prog [0;1]" qftAdder32_prog [0;1]
  
  
  *)

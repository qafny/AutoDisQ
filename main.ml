
open Autodisq_extract

(* ============================================================ *)
(* Small safe test file                                         *)
(* ============================================================ *)

let mids_small : membrane_id list = [0; 1]

let mids_2  : membrane_id list = [0; 1]
let mids_3  : membrane_id list = [0; 1; 2]
let mids_5  : membrane_id list = [0; 1; 2; 3; 4]
let mids_10 : membrane_id list = [0; 1; 2; 3; 4; 5; 6; 7; 8; 9]

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

let one_qubit_range (q : var) : var * (int * int) =
  (q, (0, 1))

let sub_range (x : var) (i : int) : var * (int * int) =
  (x, (i, i + 1))

let full_range (x : var) (n : int) : var * (int * int) =
  (x, (0, n))

let seq start len =
  let rec aux acc cur remaining =
    if remaining <= 0 then List.rev acc
    else aux (cur :: acc) (cur + 1) (remaining - 1)
  in
  aux [] start len

let alloc_qubits_from (qs : var list) : op_list =
  let rec aux acc = function
    | [] -> List.rev acc
    | q :: tl ->
        aux (OpAP (CNew (one_qubit_range q)) :: acc) tl
  in
  aux [] qs

(* Standard GHZ helper: control on ctrl[0], target on q[0] *)
let rec cnot_from (ctrl : var) (qs : var list) : op_list =
  match qs with
  | [] -> []
  | q :: tl ->
      OpAP
        (CAppU ([sub_range ctrl 0; sub_range q 0],
                CU (ctrl, Num 0, X (q, Num 0))))
      :: cnot_from ctrl tl

(* Requested by Liyi Li:
   CAppU ([x[0,1)], H(x[0]))
   CAppU ([x[1,2)], H(x[1]))
   ...
*)

let apply_H_all_from (x : var) (i : int) (k : int) : op_list =
  let rec aux acc j =
    if j >= k then List.rev acc
    else
      aux (OpAP (CAppU ([sub_range x j], H (x, Num j))) :: acc) (j + 1)
  in
  aux [] i

let controlled_x_chain_from (x : var) (y : var) (i : int) (k : int) : op_list =
  let rec aux acc j =
    if j >= k then List.rev acc
    else
      aux
        (OpAP
           (CAppU ([sub_range x j; sub_range y j],
                   CU (x, Num j, X (y, Num j)))) :: acc)
        (j + 1)
  in
  aux [] i

(* Optional measurement helper kept only for tiny tests *)
let rec meas_all_from (cs : var list) : op_list =
  match cs with
  | [] -> []
  | c :: tl ->
      OpAP (CMeas (c, [])) :: meas_all_from tl

(* ============================================================ *)
(* GHZ benchmarks (NO measurement)                              *)
(* ============================================================ *)

let rec cnot_chain (qs : var list) : op_list =
  match qs with
  | c :: ((t :: _) as tl) ->
      OpAP (CAppU ([sub_range c 0; sub_range t 0], CU (c, Num 0, X (t, Num 0))))
      :: cnot_chain tl
  | _ -> []

let ghz8_n = 8
let ghz8_qs : var list = seq 0 ghz8_n
let ghz8_prog : op_list =
  alloc_qubits_from ghz8_qs
  @ [OpAP (CAppU ([sub_range 0 0], H (0, Num 0)))]
  @ cnot_chain ghz8_qs

let ghz16_n = 16
let ghz16_qs : var list = seq 0 ghz16_n
let ghz16_prog : op_list =
  alloc_qubits_from ghz16_qs
  @ [OpAP (CAppU ([sub_range 0 0], H (0, Num 0)))]
  @ cnot_chain ghz16_qs

let ghz32_n = 32
let ghz32_qs : var list = seq 0 ghz32_n
let ghz32_prog : op_list =
  alloc_qubits_from ghz32_qs
  @ [OpAP (CAppU ([sub_range 0 0], H (0, Num 0)))]
  @ cnot_chain ghz32_qs

(* ============================================================ *)
(* Shor-style skeleton benchmarks (NO measurement)              *)
(* ============================================================ *)

let shor8_prog : op_list =
  [
    OpAP (CNew (0, (0, 8)));
    OpAP (CNew (1, (0, 8)));
  ]
  @ apply_H_all_from 0 0 8
  @ controlled_x_chain_from 0 1 0 8
  @ [OpAP (CAppU ([full_range 0 8], QFT (0, 8)))]

let shor16_prog n : op_list =
  [
    OpAP (CNew (0, (0, n)));
    OpAP (CNew (1, (0, n)));
  ]
  @ apply_H_all_from 0 0 n
  @ controlled_x_chain_from 0 1 0 n
  @ [OpAP (CAppU ([full_range 0 n], QFT (0, n)))]

let shor32_prog : op_list =
  [
    OpAP (CNew (0, (0, 32)));
    OpAP (CNew (1, (0, 32)));
  ]
  @ apply_H_all_from 0 0 32
  @ controlled_x_chain_from 0 1 0 32
  @ [OpAP (CAppU ([full_range 0 32], QFT (0, 32)))]

(* ============================================================ *)
(* QFT-based Adder (8 qubits)                                   *)
(* ============================================================ *)

let rec rz_full_adder' (x : var) (k : int) (size : int) (y : var) : op_list =
  match k with
  | 0 -> []
  | _ ->
      OpAP
        (CAppU
           ([sub_range x (size - k); (y, (0, size))],
            CU (y, Num (k - 1), SR (size - k, x))))
      :: rz_full_adder' x (k - 1) size y

let rz_full_adder (x : var) (n : int) (y : var) : op_list =
  rz_full_adder' x n n y

let qfta_n = 8
let qfta_x = 0
let qfta_y = 1

let qftAdder : op_list =
  [
    OpAP (CNew (qfta_x, (0, qfta_n)));
    OpAP (CNew (qfta_y, (0, qfta_n)));
    OpAP (CAppU ([(qfta_y, (0, qfta_n))], QFT (qfta_y, qfta_n)));
  ]
  @ rz_full_adder qfta_x qfta_n qfta_y
  @ [OpAP (CAppU ([(qfta_y, (0, qfta_n))], RQFT (qfta_y, qfta_n)))]

let qfta16_n = 16
let qfta16_x = 0
let qfta16_y = 1

let qftAdder16 : op_list =
  [
    OpAP (CNew (qfta16_x, (0, qfta16_n)));
    OpAP (CNew (qfta16_y, (0, qfta16_n)));
    OpAP (CAppU ([(qfta16_y, (0, qfta16_n))], QFT (qfta16_y, qfta16_n)));
  ]
  @ rz_full_adder qfta16_x qfta16_n qfta16_y
  @ [OpAP (CAppU ([(qfta16_y, (0, qfta16_n))], RQFT (qfta16_y, qfta16_n)))]
  
  
  (* ------------------------------------------------------------ *)
(* Reversed-version QFT                                         *)
(* x[n-1]: H; CRZ(x[0],x[n-1]); ... ; CRZ(x[n-2],x[n-1])        *)
(* x[n-2]: H; CRZ(x[0],x[n-2]); ... ; CRZ(x[n-3],x[n-2])        *)
(* ...                                                          *)
(* x[1]  : H; CRZ(x[0],x[1])                                    *)
(* x[0]  : H                                                    *)
(* ------------------------------------------------------------ *)

(* rotations from x[0] up to x[i-1] *)
let rec qft_rotations_rev (x : var) (i : int) (j : int) : op_list =
  if j >= i then []
  else
    OpAP
      (CAppU
         ([sub_range x j; sub_range x i],
          CU (x, Num j, RZ (i - j + 1, x, Num i))))
    :: qft_rotations_rev x i (j + 1)

(* main reversed QFT *)
let rec qft_rev' (x : var) (i : int) : op_list =
  if i < 0 then []
  else
    [OpAP (CAppU ([sub_range x i], H (x, Num i)))]
    @ qft_rotations_rev x i 0
    @ qft_rev' x (i - 1)

let qft (x : var) (size : int) : op_list =
  qft_rev' x (size - 1)

(* ------------------------------------------------------------ *)
(* QFT-8                                                        *)
(* ------------------------------------------------------------ *)

let qft_n = 8
let qft_x = 0

let qft_only_seq : op_list =
  [OpAP (CNew (qft_x, (0, qft_n)))]
  @ qft qft_x qft_n

(* ------------------------------------------------------------ *)
(* QFT-16                                                       *)
(* ------------------------------------------------------------ *)

let qft16_n = 16
let qft16_x = 0

let qft16_only_seq : op_list =
  [OpAP (CNew (qft16_x, (0, qft16_n)))]
  @ qft qft16_x qft16_n

(* ------------------------------------------------------------ *)
(* QFT-32                                                       *)
(* ------------------------------------------------------------ *)

let qft32_n = 32
let qft32_x = 0

let qft32_only_seq : op_list =
  [OpAP (CNew (qft32_x, (0, qft32_n)))]
  @ qft qft32_x qft32_n
  
(*
(* ============================================================ *)
(* QFT (8 qubits)                                               *)
(* ============================================================ *)

let rec qft_rotations (x : var) (n : int) (k : int) : op_list =
  match k with
  | 0 -> []
  | _ ->
      OpAP
        (CAppU
           ([sub_range x (n + k); sub_range x n],
            CU (x, Num (n + k), RZ (k + 1, x, Num n))))
      :: qft_rotations x n (k - 1)

let rec qft' (x : var) (size : int) (n : int) : op_list =
  match n with
  | 0 -> []
  | _ ->
      let i = n - 1 in
      [OpAP (CAppU ([sub_range x i], H (x, Num i)))]
      @ qft_rotations x i (size - i - 1)
      @ qft' x size i

let qft (x : var) (size : int) : op_list =
  qft' x size size

let qft_n = 8
let qft_x = 0

let qft_only_seq : op_list =
  [OpAP (CNew (qft_x, (0, qft_n)))]
  @ qft qft_x qft_n

let qft16_n = 16
let qft16_x = 0

let qft16_only_seq : op_list =
  [OpAP (CNew (qft16_x, (0, qft16_n)))]
  @ qft qft16_x qft16_n
*)
(* ============================================================ *)
(* Amplitude Estimation (8 qubits)                              *)
(* ============================================================ *)

let ae_n = 8
let ae_x = 0
let ae_y = 1

let qop (y : var) : exp =
  H (y, Num 0)

let rec control_Qs (x : var) (y : var) (k : int) : op_list =
  match k with
  | 0 -> []
  | _ ->
      OpAP
        (CAppU
           ([sub_range x (k - 1); full_range y ae_n],
            CU (x, Num (k - 1), qop y)))
      :: control_Qs x y (k - 1)

let rec applyH (x : var) (k : int) : op_list =
  match k with
  | 0 -> []
  | _ ->
      OpAP (CAppU ([sub_range x (k - 1)], H (x, Num (k - 1))))
      :: applyH x (k - 1)

let ampEstSeq : op_list =
  [
    OpAP (CNew (ae_x, (0, ae_n)));
    OpAP (CNew (ae_y, (0, ae_n)));
  ]
  @ applyH ae_x ae_n
  @ applyH ae_y ae_n
  @ control_Qs ae_x ae_y ae_n
  @ [OpAP (CAppU ([full_range ae_x ae_n], RQFT (ae_x, ae_n)))]

(* ============================================================ *)
(* Amplitude Estimation (16 qubits)                             *)
(* ============================================================ *)

let ae16_n = 16
let ae16_x = 0
let ae16_y = 1

let rec control_Qs16 (x : var) (y : var) (k : int) : op_list =
  match k with
  | 0 -> []
  | _ ->
      OpAP
        (CAppU
           ([sub_range x (k - 1); full_range y ae16_n],
            CU (x, Num (k - 1), qop y)))
      :: control_Qs16 x y (k - 1)

let ampEst16Seq : op_list =
  [
    OpAP (CNew (ae16_x, (0, ae16_n)));
    OpAP (CNew (ae16_y, (0, ae16_n)));
  ]
  @ applyH ae16_x ae16_n
  @ applyH ae16_y ae16_n
  @ control_Qs16 ae16_x ae16_y ae16_n
  @ [OpAP (CAppU ([full_range ae16_x ae16_n], RQFT (ae16_x, ae16_n)))]

(* ============================================================ *)
(* Ripple-Carry Adder (general n qubits)                        *)
(* ============================================================ *)

let bit (v : var) (i : int) = sub_range v i

let maj_at (a : var) (ia : int) (b : var) (ib : int) (c : var) (ic : int) : op_list =
  [
    OpAP (CAppU ([bit a ia; bit b ib; bit c ic], SKIP (0, Num 0)))
  ]

let uma_at (a : var) (ia : int) (b : var) (ib : int) (c : var) (ic : int) : op_list =
  [
    OpAP (CAppU ([bit a ia; bit b ib; bit c ic], X (0, Num 0)))
  ]

let rec majseq' n x y c =
  if n = 0 then maj_at c 0 y 0 x 0
  else majseq' (n - 1) x y c @ maj_at x (n - 1) y n x n

let majseq n x y c = majseq' (n - 1) x y c

let rec umaseq' n x y c =
  if n = 0 then uma_at c 0 y 0 x 0
  else uma_at x (n - 1) y n x n @ umaseq' (n - 1) x y c

let umaseq n x y c = umaseq' (n - 1) x y c

let ripple_adder n x y c : op_list =
  majseq n c y x
  @ umaseq n c y x

(* ============================================================ *)
(* Ripple-Carry Adder (8 qubits)                                *)
(* ============================================================ *)

let rc8_n = 8
let rc8_c = 0
let rc8_y = 1
let rc8_x = 2

let rippleCarry8 : op_list =
  [
    OpAP (CNew (rc8_c, (0, 1)));
    OpAP (CNew (rc8_y, (0, rc8_n)));
    OpAP (CNew (rc8_x, (0, rc8_n)));
  ]
  @ ripple_adder rc8_n rc8_x rc8_y rc8_c

let rc16_n = 16
let rc16_c = 0
let rc16_y = 1
let rc16_x = 2

let rippleCarry16 : op_list =
  [
    OpAP (CNew (rc16_c, (0, 1)));
    OpAP (CNew (rc16_y, (0, rc16_n)));
    OpAP (CNew (rc16_x, (0, rc16_n)));
  ]
  @ ripple_adder rc16_n rc16_x rc16_y rc16_c

(* ============================================================ *)
(* Discrete Log (8 qubits)                                      *)
(* ============================================================ *)

let rec control_ops (x : var) (y : var) (k : int) : op_list =
  match k with
  | 0 ->
      [OpAP (CAppU ([one_qubit_range y], H (y, Num 0)))]
  | _ ->
      OpAP
        (CAppU
           ([one_qubit_range x; (y, (0, k - 1))],
            CU (x, Num (k - 1), H (y, Num 0))))
      :: control_ops x y (k - 1)

let dlog_n = 8
let dlog_x = 0
let dlog_y = 1
let dlog_z = 2

let discreteLogSeq : op_list =
  [
    OpAP (CNew (dlog_x, (0, dlog_n)));
    OpAP (CNew (dlog_y, (0, dlog_n)));
    OpAP (CNew (dlog_z, (0, dlog_n)));
  ]
  @ apply_H_all_from dlog_x 0 dlog_n
  @ apply_H_all_from dlog_y 0 dlog_n
  @ controlled_x_chain_from dlog_x dlog_z 0 dlog_n
  @ controlled_x_chain_from dlog_y dlog_z 0 dlog_n
  @ [
      OpAP (CAppU ([full_range dlog_x dlog_n], QFT (dlog_x, dlog_n)));
      OpAP (CAppU ([full_range dlog_y dlog_n], QFT (dlog_y, dlog_n)));
    ]

let dlog16_n = 16
let dlog16_x = 0
let dlog16_y = 1
let dlog16_z = 2

let discreteLog16Seq : op_list =
  [
    OpAP (CNew (dlog16_x, (0, dlog16_n)));
    OpAP (CNew (dlog16_y, (0, dlog16_n)));
    OpAP (CNew (dlog16_z, (0, dlog16_n)));
  ]
  @ apply_H_all_from dlog16_x 0 dlog16_n
  @ apply_H_all_from dlog16_y 0 dlog16_n
  @ controlled_x_chain_from dlog16_x dlog16_z 0 dlog16_n
  @ controlled_x_chain_from dlog16_y dlog16_z 0 dlog16_n
  @ [
      OpAP (CAppU ([full_range dlog16_x dlog16_n], QFT (dlog16_x, dlog16_n)));
      OpAP (CAppU ([full_range dlog16_y dlog16_n], QFT (dlog16_y, dlog16_n)));
    ]

(* ============================================================ *)
(* Counters on source programs                                  *)
(* ============================================================ *)

let rec count_CU (ops : op_list) : int =
  match ops with
  | [] -> 0
  | OpAP (CAppU (_, CU (_, _, _))) :: tl -> 1 + count_CU tl
  | _ :: tl -> count_CU tl

(* ============================================================ *)
(* Counters on generated configs                                *)
(* ============================================================ *)

let rec count_send_in_process = function
  | PNil -> 0
  | AP (Send (_, _, _), p) -> 1 + count_send_in_process p
  | AP (Recv (_, _, _), p) -> 1 + count_send_in_process p
  | AP (_, p) -> count_send_in_process p
  | PIf (_, p1, p2) -> count_send_in_process p1 + count_send_in_process p2

let count_send_in_memb = function
  | Memb (_, p) -> count_send_in_process p

let rec count_send_in_config = function
  | [] -> 0
  | m :: tl -> count_send_in_memb m + count_send_in_config tl

let rec count_used_membranes cfg =
  match cfg with
  | [] -> 0
  | _ :: tl -> 1 + count_used_membranes tl



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

let process_ops_limit = 12

let process_to_ops (p : process) : string list * bool =
  let rec aux acc n p =
    if n <= 0 then (List.rev acc, true)
    else
      match p with
      | PNil -> (List.rev acc, false)
      | AP (a, p') -> aux (string_of_cexp a :: acc) (n - 1) p'
      | PIf (b, _p1, _p2) ->
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

let string_of_memb = function
  | Memb (mid, p) ->
      Printf.sprintf "Memb %d { len=%d; %s }"
        mid (process_length p) (string_of_process p)

let string_of_config (cfg : config) =
  "[\n  " ^ String.concat ";\n  " (List.map string_of_memb cfg) ^ "\n]"

let string_of_myaux a =
  match a with
  | OpNum v -> string_of_int v
  | _ -> "bad"

let rec string_of_lista l =
  match l with
  | [] -> ""
  | x :: xs -> (string_of_myaux (fst x)) ^ ", " ^ (string_of_lista xs)

let rec string_of_listaa l =
  match l with
  | [] -> ""
  | x :: xs -> (string_of_lista x) ^ "\n, " ^ (string_of_listaa xs)

let rec string_of_listb l =
  match l with
  | [] -> ""
  | x :: xs -> (string_of_int (fst x)) ^ ", " ^ (string_of_listb xs)

let rec string_of_hb i n re =
  if n > 0
  then string_of_hb i (n - 1) re ^ " @ " ^ string_of_int i ^ "," ^ string_of_int (n - 1) ^ "," ^ string_of_bool (re i (n - 1))
  else ""

let rec string_of_hbs n size re =
  if n > 0
  then string_of_hbs (n - 1) size re ^ "\n" ^ string_of_hb (n - 1) size re
  else ""

let rec take n list =
  match n, list with
  | 0, _ -> []
  | _, [] -> []
  | n, x :: xs -> x :: take (n - 1) xs

(* ============================================================ *)
(* Timing and protected execution                               *)
(* ============================================================ *)

type bench_result =
  | Bench_ok of config option * float
  | Bench_error of string

type summary = {
  name : string;
  fit : int;
  comm : int;
  used : int;
  load : int;
  time : float;
}

let results : summary list ref = ref []

let now () = Sys.time ()

let protect_bench f =
  try
    let t0 = now () in
    let r = f () in
    let t1 = now () in
    Bench_ok (r, t1 -. t0)
  with
  | Stack_overflow -> Bench_error "Stack_overflow"
  | Out_of_memory -> Bench_error "Out_of_memory"
  | exn -> Bench_error (Printexc.to_string exn)

let print_separator () =
  print_endline "------------------------------------------------------------"

let print_int name x =
  Printf.printf "%s = %d\n%!" name x

let report_best name = function
  | Bench_error msg ->
      print_separator ();
      Printf.printf "%s = ERROR(%s)\n%!" name msg

  | Bench_ok (None, tm) ->
      print_separator ();
      Printf.printf "%s = None\n%!" name;
      Printf.printf "time = %.6fs\n%!" tm

  | Bench_ok (Some cfg, tm) ->
      print_separator ();
      Printf.printf "%s = Some\n%s\n%!" name (string_of_config cfg);

      let f = fit cfg in
      let c = count_comm_ops cfg in
      let u = count_used_membranes cfg in
      let l = max_load cfg in

      Printf.printf "fit = %d\n%!" f;
      Printf.printf "count_comm_ops = %d\n%!" c;
      Printf.printf "used_membranes = %d\n%!" u;
      Printf.printf "max_load = %d\n%!" l;
      Printf.printf "time = %.6fs\n%!" tm;

      results := { name; fit = f; comm = c; used = u; load = l; time = tm } :: !results

let run_best name prog mids =
  report_best name (protect_bench (fun () -> autodisq_best prog mids))

let run_best_1 name prog mids =
  report_best name (protect_bench (fun () -> autodisq_best_1 prog mids))

let run_int name thunk =
  try print_int name (thunk ())
  with exn ->
    print_separator ();
    Printf.printf "%s = ERROR(%s)\n%!" name (Printexc.to_string exn)

(*
let report_best name = function
  | Bench_error msg ->
      print_separator ();
      Printf.printf "%s = ERROR(%s)\n%!" name msg
  | Bench_ok (None, tm) ->
      print_separator ();
      Printf.printf "%s = None\n%!" name;
      Printf.printf "time = %.6fs\n%!" tm
  | Bench_ok (Some cfg, tm) ->
      print_separator ();
      Printf.printf "%s = Some\n%s\n%!" name (string_of_config cfg);
      Printf.printf "fit = %d\n%!" (fit cfg);
      Printf.printf "count_comm_ops = %d\n%!" (count_comm_ops cfg);
      Printf.printf "send_recv_ops = %d\n%!" (count_send_in_config cfg);
      Printf.printf "max_load = %d\n%!" (max_load cfg);
      Printf.printf "time = %.6fs\n%!" tm
*)



let report_best name = function
  | Bench_error msg ->
      print_separator ();
      Printf.printf "%s = ERROR(%s)\n%!" name msg

  | Bench_ok (None, tm) ->
      print_separator ();
      Printf.printf "%s = None\n%!" name;
      Printf.printf "time = %.6fs\n%!" tm

  | Bench_ok (Some cfg, tm) ->
      print_separator ();
      Printf.printf "%s = Some\n%s\n%!" name (string_of_config cfg);

      let f = fit cfg in
      let c = count_comm_ops cfg in
      let u = count_used_membranes cfg in
      let l = max_load cfg in

      Printf.printf "fit = %d\n%!" f;
      Printf.printf "count_comm_ops = %d\n%!" c;
      Printf.printf "used_membranes = %d\n%!" u;
      Printf.printf "max_load = %d\n%!" l;
      Printf.printf "time = %.6fs\n%!" tm;

      results := {name; fit=f; comm=c; used=u; load=l; time=tm} :: !results
      
let run_best name prog mids =
  report_best name (protect_bench (fun () -> autodisq_best prog mids))

let run_best_1 name prog mids =
  report_best name (protect_bench (fun () -> autodisq_best_1 prog mids))

let run_int name thunk =
  try print_int name (thunk ())
  with exn ->
    print_separator ();
    Printf.printf "%s = ERROR(%s)\n%!" name (Printexc.to_string exn)

(* ============================================================ *)
(* Summary table                                                *)
(* ============================================================ *)

let summary_header () =
  print_endline "";
  print_endline "================ Benchmark Summary ================";
  print_endline "Benchmark               | status | fit  | comm | s/r  | load | time";
  print_endline "---------------------------------------------------------------------"

let summary_row name = function
  | Bench_error msg ->
      Printf.printf "%-23s | %-6s | %-4s | %-4s | %-4s | %-4s | %s\n%!"
        name "ERR" "-" "-" "-" "-" msg
  | Bench_ok (None, tm) ->
      Printf.printf "%-23s | %-6s | %-4s | %-4s | %-4s | %-4s | %.4fs\n%!"
        name "None" "-" "-" "-" "-" tm
  | Bench_ok (Some cfg, tm) ->
      Printf.printf "%-23s | %-6s | %-4d | %-4d | %-4d | %-4d | %.4fs\n%!"
        name "OK"
        (fit cfg)
        (count_comm_ops cfg)
        (count_send_in_config cfg)
        (max_load cfg)
        tm

(* ============================================================ *)
(* Debug reduction helpers (for stack overflow investigation)   *)
(* ============================================================ *)

let first_of_list = function
  | [] -> None
  | x :: _ -> Some x

let autodisq_first (ops : op_list) (mids : membrane_id list) : config option =
  first_of_list (autodisq_all ops mids)

type unit_bench =
  | UOk of float
  | UError of string

let protect_unit f =
  try
    let t0 = now () in
    let _ = f () in
    let t1 = now () in
    UOk (t1 -. t0)
  with
  | Stack_overflow -> UError "Stack_overflow"
  | Out_of_memory -> UError "Out_of_memory"
  | exn -> UError (Printexc.to_string exn)

let report_unit name = function
  | UOk tm ->
      print_separator ();
      Printf.printf "%s = OK\n%!" name;
      Printf.printf "time = %.6fs\n%!" tm
  | UError msg ->
      print_separator ();
      Printf.printf "%s = ERROR(%s)\n%!" name msg

let test_opListOrder ops =
  ignore (opListOrder ops)

let test_gen_hb ops =
  let os = opListOrder ops in
  let hb i j = gen_hb os i j in
  ignore (hb 0 0)

let test_gen_seq ops =
  let os = opListOrder ops in
  let hb i j = gen_hb os i j in
  ignore (gen_seq os hb)

let test_gen_mem ops mids =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  ignore (gen_mem (fst sq) (snd sq) mids)

let test_gen_prog ops mids =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  let mem = gen_mem (fst sq) (snd sq) mids in
  ignore (gen_prog mem os)

let test_num_configs ops mids =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  let mem = gen_mem (fst sq) (snd sq) mids in
  let progs = gen_prog mem os in
  Printf.printf "num_configs = %d\n%!" (List.length progs)

let test_show_first_config ops mids =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  let mem = gen_mem (fst sq) (snd sq) mids in
  let progs = gen_prog mem os in
  match progs with
  | [] -> print_endline "no generated configs"
  | cfg :: _ -> print_endline (string_of_config cfg)

let test_num_mem_configs ops mids =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  let mem = gen_mem (fst sq) (snd sq) mids in
  Printf.printf "num_mem = %d\n%!" (List.length mem)

let test_num_final_configs ops mids =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  let mem = gen_mem (fst sq) (snd sq) mids in
  let progs = gen_prog mem os in
  Printf.printf "num_final_configs = %d\n%!" (List.length progs)

let test_seq_count ops =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  Printf.printf "seq_count = %d\n%!" (List.length (snd sq))

let test_num_mem_configs_take5 ops mids =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  let mem = gen_mem (fst sq) (take 5 (snd sq)) mids in
  Printf.printf "num_mem_take5 = %d\n%!" (List.length mem)
  
  


let print_summary () =
  print_separator ();
  Printf.printf "\nSUMMARY TABLE\n";
  Printf.printf "------------------------------------------------------------\n";
  Printf.printf "%-25s | %-4s | %-4s | %-4s | %-4s | %-8s\n"
    "Program" "fit" "comm" "used" "load" "time";
  Printf.printf "------------------------------------------------------------\n";

  List.iter
    (fun r ->
      Printf.printf "%-25s | %-4d | %-4d | %-4d | %-4d | %.4f\n"
        r.name r.fit r.comm r.used r.load r.time)
    (List.rev !results);

  Printf.printf "------------------------------------------------------------\n"

let print_load_chart () =
  print_separator ();
  Printf.printf "\nMAX LOAD CHART\n";

  List.iter
    (fun r ->
      let bar = String.make r.load '#' in
      Printf.printf "%-20s | %s (%d)\n" r.name bar r.load)
    (List.rev !results)

(* ============================================================ *)
(* Main                                                         *)
(* ============================================================ *)
(**
let () =
  Printexc.record_backtrace true;

  (* ========================================================== *)
  (* GHZ 8                                                      *)
  (* ========================================================== *)
  report_unit "opListOrder GHZ8 [0;1]"
    (protect_unit (fun () -> test_opListOrder ghz8_prog));

  report_unit "gen_hb GHZ8 [0;1]"
    (protect_unit (fun () -> test_gen_hb ghz8_prog));

  report_unit "gen_seq GHZ8 [0;1]"
    (protect_unit (fun () -> test_gen_seq ghz8_prog));

  report_unit "gen_mem GHZ8 [0;1]"
    (protect_unit (fun () -> test_gen_mem ghz8_prog mids_2));

  report_unit "gen_prog GHZ8 [0;1]"
    (protect_unit (fun () -> test_gen_prog ghz8_prog mids_2));

  test_num_mem_configs ghz8_prog mids_2;
  test_num_final_configs ghz8_prog mids_2;

  report_best "autodisq_first GHZ8 [0;1]"
    (protect_bench (fun () -> autodisq_first ghz8_prog mids_2));

  report_best "autodisq_best GHZ8 [0;1]"
    (protect_bench (fun () -> autodisq_best ghz8_prog mids_2));

  report_best "autodisq_best_1 GHZ8 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 ghz8_prog mids_2));

  (* ========================================================== *)
  (* SHOR 8                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder SHOR8 [0;1]"
    (protect_unit (fun () -> test_opListOrder shor8_prog));

  report_unit "gen_hb SHOR8 [0;1]"
    (protect_unit (fun () -> test_gen_hb shor8_prog));

  report_unit "gen_seq SHOR8 [0;1]"
    (protect_unit (fun () -> test_gen_seq shor8_prog));

  report_unit "gen_mem SHOR8 [0;1]"
    (protect_unit (fun () -> test_gen_mem shor8_prog mids_2));

  report_unit "gen_prog SHOR8 [0;1]"
    (protect_unit (fun () -> test_gen_prog shor8_prog mids_2));

  report_best "autodisq_first SHOR8 [0;1]"
    (protect_bench (fun () -> autodisq_first shor8_prog mids_2));

  report_best "autodisq_best SHOR8 [0;1]"
    (protect_bench (fun () -> autodisq_best shor8_prog mids_2));

  report_best "autodisq_best_1 SHOR8 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 shor8_prog mids_2));

  (* ========================================================== *)
  (* Ripple-Carry Adder 8                                       *)
  (* ========================================================== *)
  report_unit "opListOrder RippleCarry8 [0;1]"
    (protect_unit (fun () -> test_opListOrder rippleCarry8));

  report_unit "gen_hb RippleCarry8 [0;1]"
    (protect_unit (fun () -> test_gen_hb rippleCarry8));

  report_unit "gen_seq RippleCarry8 [0;1]"
    (protect_unit (fun () -> test_gen_seq rippleCarry8));

  report_unit "gen_mem RippleCarry8 [0;1]"
    (protect_unit (fun () -> test_gen_mem rippleCarry8 mids_2));

  report_unit "gen_prog RippleCarry8 [0;1]"
    (protect_unit (fun () -> test_gen_prog rippleCarry8 mids_2));

  report_best "autodisq_first RippleCarry8 [0;1]"
    (protect_bench (fun () -> autodisq_first rippleCarry8 mids_2));

  report_best "autodisq_best RippleCarry8 [0;1]"
    (protect_bench (fun () -> autodisq_best rippleCarry8 mids_2));

  report_best "autodisq_best_1 RippleCarry8 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 rippleCarry8 mids_2));

  (* ========================================================== *)
  (* QFT Adder 8                                                *)
  (* ========================================================== *)
  report_unit "opListOrder QFTAdder8 [0;1]"
    (protect_unit (fun () -> test_opListOrder qftAdder));

  report_unit "gen_hb QFTAdder8 [0;1]"
    (protect_unit (fun () -> test_gen_hb qftAdder));

  report_unit "gen_seq QFTAdder8 [0;1]"
    (protect_unit (fun () -> test_gen_seq qftAdder));

  report_unit "gen_mem QFTAdder8 [0;1]"
    (protect_unit (fun () -> test_gen_mem qftAdder mids_2));

  report_unit "gen_prog QFTAdder8 [0;1]"
    (protect_unit (fun () -> test_gen_prog qftAdder mids_2));

  report_best "autodisq_first QFTAdder8 [0;1]"
    (protect_bench (fun () -> autodisq_first qftAdder mids_2));

  report_best "autodisq_best QFTAdder8 [0;1]"
    (protect_bench (fun () -> autodisq_best qftAdder mids_2));

  report_best "autodisq_best_1 QFTAdder8 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 qftAdder mids_2));

  (* ========================================================== *)
  (* QFT 8                                                      *)
  (* ========================================================== *)
  report_unit "opListOrder QFT8 [0;1]"
    (protect_unit (fun () -> test_opListOrder qft_only_seq));

  report_unit "gen_hb QFT8 [0;1]"
    (protect_unit (fun () -> test_gen_hb qft_only_seq));

  report_unit "gen_seq QFT8 [0;1]"
    (protect_unit (fun () -> test_gen_seq qft_only_seq));

  report_unit "gen_mem QFT8 [0;1]"
    (protect_unit (fun () -> test_gen_mem qft_only_seq mids_2));

  report_unit "gen_prog QFT8 [0;1]"
    (protect_unit (fun () -> test_gen_prog qft_only_seq mids_2));

  report_best "autodisq_first QFT8 [0;1]"
    (protect_bench (fun () -> autodisq_first qft_only_seq mids_2));

  report_best "autodisq_best QFT8 [0;1]"
    (protect_bench (fun () -> autodisq_best qft_only_seq mids_2));

  report_best "autodisq_best_1 QFT8 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 qft_only_seq mids_2));

  (* ========================================================== *)
  (* Amplitude Estimation 8                                     *)
  (* ========================================================== *)
  report_unit "opListOrder AmpEst8 [0;1]"
    (protect_unit (fun () -> test_opListOrder ampEstSeq));

  report_unit "gen_hb AmpEst8 [0;1]"
    (protect_unit (fun () -> test_gen_hb ampEstSeq));

  report_unit "gen_seq AmpEst8 [0;1]"
    (protect_unit (fun () -> test_gen_seq ampEstSeq));

  report_unit "gen_mem AmpEst8 [0;1]"
    (protect_unit (fun () -> test_gen_mem ampEstSeq mids_2));

  report_unit "gen_prog AmpEst8 [0;1]"
    (protect_unit (fun () -> test_gen_prog ampEstSeq mids_2));

  report_best "autodisq_first AmpEst8 [0;1]"
    (protect_bench (fun () -> autodisq_first ampEstSeq mids_2));

  report_best "autodisq_best AmpEst8 [0;1]"
    (protect_bench (fun () -> autodisq_best ampEstSeq mids_2));

  report_best "autodisq_best_1 AmpEst8 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 ampEstSeq mids_2));

  (* ========================================================== *)
  (* Discrete Log 8                                             *)
  (* ========================================================== *)
  report_unit "opListOrder DiscreteLog8 [0;1]"
    (protect_unit (fun () -> test_opListOrder discreteLogSeq));

  report_unit "gen_hb DiscreteLog8 [0;1]"
    (protect_unit (fun () -> test_gen_hb discreteLogSeq));

  report_unit "gen_seq DiscreteLog8 [0;1]"
    (protect_unit (fun () -> test_gen_seq discreteLogSeq));

  report_unit "gen_mem DiscreteLog8 [0;1]"
    (protect_unit (fun () -> test_gen_mem discreteLogSeq mids_2));

  report_unit "gen_prog DiscreteLog8 [0;1]"
    (protect_unit (fun () -> test_gen_prog discreteLogSeq mids_2));

  report_best "autodisq_first DiscreteLog8 [0;1]"
    (protect_bench (fun () -> autodisq_first discreteLogSeq mids_2));

  report_best "autodisq_best DiscreteLog8 [0;1]"
    (protect_bench (fun () -> autodisq_best discreteLogSeq mids_2));

  report_best "autodisq_best_1 DiscreteLog8 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 discreteLogSeq mids_2));

  (* ---- summary output ---- *)
  print_summary ();
  print_load_chart ();
  ()


**)


(**
let () =
  Printexc.record_backtrace true;

  (* ========================================================== *)
  (* GHZ 8                                                      *)
  (* ========================================================== *)
  report_unit "opListOrder GHZ8 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder ghz8_prog));

  report_unit "gen_hb GHZ8 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb ghz8_prog));

  report_unit "gen_seq GHZ8 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq ghz8_prog));

  report_unit "gen_mem GHZ8 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem ghz8_prog mids_3));

  report_unit "gen_prog GHZ8 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog ghz8_prog mids_3));

  test_num_mem_configs ghz8_prog mids_3;
  test_num_final_configs ghz8_prog mids_3;

  report_best "autodisq_first GHZ8 [0;1;2]"
    (protect_bench (fun () -> autodisq_first ghz8_prog mids_3));

  report_best "autodisq_best GHZ8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best ghz8_prog mids_3));

  report_best "autodisq_best_1 GHZ8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 ghz8_prog mids_3));

  (* ========================================================== *)
  (* SHOR 8                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder SHOR8 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder shor8_prog));

  report_unit "gen_hb SHOR8 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb shor8_prog));

  report_unit "gen_seq SHOR8 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq shor8_prog));

  report_unit "gen_mem SHOR8 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem shor8_prog mids_3));

  report_unit "gen_prog SHOR8 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog shor8_prog mids_3));

  report_best "autodisq_first SHOR8 [0;1;2]"
    (protect_bench (fun () -> autodisq_first shor8_prog mids_3));

  report_best "autodisq_best SHOR8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best shor8_prog mids_3));

  report_best "autodisq_best_1 SHOR8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 shor8_prog mids_3));

  (* ========================================================== *)
  (* Ripple-Carry Adder 8                                       *)
  (* ========================================================== *)
  report_unit "opListOrder RippleCarry8 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder rippleCarry8));

  report_unit "gen_hb RippleCarry8 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb rippleCarry8));

  report_unit "gen_seq RippleCarry8 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq rippleCarry8));

  report_unit "gen_mem RippleCarry8 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem rippleCarry8 mids_3));

  report_unit "gen_prog RippleCarry8 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog rippleCarry8 mids_3));

  report_best "autodisq_first RippleCarry8 [0;1;2]"
    (protect_bench (fun () -> autodisq_first rippleCarry8 mids_3));

  report_best "autodisq_best RippleCarry8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best rippleCarry8 mids_3));

  report_best "autodisq_best_1 RippleCarry8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 rippleCarry8 mids_3));

  (* ========================================================== *)
  (* QFT Adder 8                                                *)
  (* ========================================================== *)
  report_unit "opListOrder QFTAdder8 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder qftAdder));

  report_unit "gen_hb QFTAdder8 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb qftAdder));

  report_unit "gen_seq QFTAdder8 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq qftAdder));

  report_unit "gen_mem QFTAdder8 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem qftAdder mids_3));

  report_unit "gen_prog QFTAdder8 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog qftAdder mids_3));

  report_best "autodisq_first QFTAdder8 [0;1;2]"
    (protect_bench (fun () -> autodisq_first qftAdder mids_3));

  report_best "autodisq_best QFTAdder8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best qftAdder mids_3));

  report_best "autodisq_best_1 QFTAdder8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 qftAdder mids_3));

  (* ========================================================== *)
  (* QFT 8                                                      *)
  (* ========================================================== *)
  report_unit "opListOrder QFT8 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder qft_only_seq));

  report_unit "gen_hb QFT8 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb qft_only_seq));

  report_unit "gen_seq QFT8 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq qft_only_seq));

  report_unit "gen_mem QFT8 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem qft_only_seq mids_3));

  report_unit "gen_prog QFT8 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog qft_only_seq mids_3));

  report_best "autodisq_first QFT8 [0;1;2]"
    (protect_bench (fun () -> autodisq_first qft_only_seq mids_3));

  report_best "autodisq_best QFT8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best qft_only_seq mids_3));

  report_best "autodisq_best_1 QFT8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 qft_only_seq mids_3));

  (* ========================================================== *)
  (* Amplitude Estimation 8                                     *)
  (* ========================================================== *)
  report_unit "opListOrder AmpEst8 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder ampEstSeq));

  report_unit "gen_hb AmpEst8 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb ampEstSeq));

  report_unit "gen_seq AmpEst8 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq ampEstSeq));

  report_unit "gen_mem AmpEst8 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem ampEstSeq mids_3));

  report_unit "gen_prog AmpEst8 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog ampEstSeq mids_3));

  report_best "autodisq_first AmpEst8 [0;1;2]"
    (protect_bench (fun () -> autodisq_first ampEstSeq mids_3));

  report_best "autodisq_best AmpEst8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best ampEstSeq mids_3));

  report_best "autodisq_best_1 AmpEst8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 ampEstSeq mids_3));

  (* ========================================================== *)
  (* Discrete Log 8                                             *)
  (* ========================================================== *)
  report_unit "opListOrder DiscreteLog8 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder discreteLogSeq));

  report_unit "gen_hb DiscreteLog8 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb discreteLogSeq));

  report_unit "gen_seq DiscreteLog8 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq discreteLogSeq));

  report_unit "gen_mem DiscreteLog8 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem discreteLogSeq mids_3));

  report_unit "gen_prog DiscreteLog8 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog discreteLogSeq mids_3));

  report_best "autodisq_first DiscreteLog8 [0;1;2]"
    (protect_bench (fun () -> autodisq_first discreteLogSeq mids_3));

  report_best "autodisq_best DiscreteLog8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best discreteLogSeq mids_3));

  report_best "autodisq_best_1 DiscreteLog8 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 discreteLogSeq mids_3));

  (* ---- summary output ---- *)
  print_summary ();
  print_load_chart ();
  ()

**)

(**
let () =
  Printexc.record_backtrace true;

  (* ========================================================== *)
  (* GHZ 8                                                      *)
  (* ========================================================== *)
  report_unit "opListOrder GHZ8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder ghz8_prog));

  report_unit "gen_hb GHZ8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb ghz8_prog));

  report_unit "gen_seq GHZ8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq ghz8_prog));

  report_unit "gen_mem GHZ8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem ghz8_prog mids_5));

  report_unit "gen_prog GHZ8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog ghz8_prog mids_5));

  test_num_mem_configs ghz8_prog mids_5;
  test_num_final_configs ghz8_prog mids_5;

  report_best "autodisq_first GHZ8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first ghz8_prog mids_5));

  report_best "autodisq_best GHZ8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best ghz8_prog mids_5));

  report_best "autodisq_best_1 GHZ8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 ghz8_prog mids_5));

  (* ========================================================== *)
  (* SHOR 8                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder SHOR8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder shor8_prog));

  report_unit "gen_hb SHOR8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb shor8_prog));

  report_unit "gen_seq SHOR8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq shor8_prog));

  report_unit "gen_mem SHOR8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem shor8_prog mids_5));

  report_unit "gen_prog SHOR8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog shor8_prog mids_5));

  report_best "autodisq_first SHOR8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first shor8_prog mids_5));

  report_best "autodisq_best SHOR8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best shor8_prog mids_5));

  report_best "autodisq_best_1 SHOR8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 shor8_prog mids_5));

  (* ========================================================== *)
  (* Ripple-Carry Adder 8                                       *)
  (* ========================================================== *)
  report_unit "opListOrder RippleCarry8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder rippleCarry8));

  report_unit "gen_hb RippleCarry8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb rippleCarry8));

  report_unit "gen_seq RippleCarry8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq rippleCarry8));

  report_unit "gen_mem RippleCarry8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem rippleCarry8 mids_5));

  report_unit "gen_prog RippleCarry8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog rippleCarry8 mids_5));

  report_best "autodisq_first RippleCarry8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first rippleCarry8 mids_5));

  report_best "autodisq_best RippleCarry8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best rippleCarry8 mids_5));

  report_best "autodisq_best_1 RippleCarry8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 rippleCarry8 mids_5));

  (* ========================================================== *)
  (* QFT Adder 8                                                *)
  (* ========================================================== *)
  report_unit "opListOrder QFTAdder8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder qftAdder));

  report_unit "gen_hb QFTAdder8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb qftAdder));

  report_unit "gen_seq QFTAdder8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq qftAdder));

  report_unit "gen_mem QFTAdder8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem qftAdder mids_5));

  report_unit "gen_prog QFTAdder8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog qftAdder mids_5));

  report_best "autodisq_first QFTAdder8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first qftAdder mids_5));

  report_best "autodisq_best QFTAdder8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best qftAdder mids_5));

  report_best "autodisq_best_1 QFTAdder8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 qftAdder mids_5));

  (* ========================================================== *)
  (* QFT 8                                                      *)
  (* ========================================================== *)
  report_unit "opListOrder QFT8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder qft_only_seq));

  report_unit "gen_hb QFT8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb qft_only_seq));

  report_unit "gen_seq QFT8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq qft_only_seq));

  report_unit "gen_mem QFT8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem qft_only_seq mids_5));

  report_unit "gen_prog QFT8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog qft_only_seq mids_5));

  report_best "autodisq_first QFT8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first qft_only_seq mids_5));

  report_best "autodisq_best QFT8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best qft_only_seq mids_5));

  report_best "autodisq_best_1 QFT8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 qft_only_seq mids_5));

  (* ========================================================== *)
  (* Amplitude Estimation 8                                     *)
  (* ========================================================== *)
  report_unit "opListOrder AmpEst8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder ampEstSeq));

  report_unit "gen_hb AmpEst8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb ampEstSeq));

  report_unit "gen_seq AmpEst8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq ampEstSeq));

  report_unit "gen_mem AmpEst8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem ampEstSeq mids_5));

  report_unit "gen_prog AmpEst8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog ampEstSeq mids_5));

  report_best "autodisq_first AmpEst8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first ampEstSeq mids_5));

  report_best "autodisq_best AmpEst8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best ampEstSeq mids_5));

  report_best "autodisq_best_1 AmpEst8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 ampEstSeq mids_5));

  (* ========================================================== *)
  (* Discrete Log 8                                             *)
  (* ========================================================== *)
  report_unit "opListOrder DiscreteLog8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder discreteLogSeq));

  report_unit "gen_hb DiscreteLog8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb discreteLogSeq));

  report_unit "gen_seq DiscreteLog8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq discreteLogSeq));

  report_unit "gen_mem DiscreteLog8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem discreteLogSeq mids_5));

  report_unit "gen_prog DiscreteLog8 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog discreteLogSeq mids_5));

  report_best "autodisq_first DiscreteLog8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first discreteLogSeq mids_5));

  report_best "autodisq_best DiscreteLog8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best discreteLogSeq mids_5));

  report_best "autodisq_best_1 DiscreteLog8 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 discreteLogSeq mids_5));

  (* ---- summary output ---- *)
  print_summary ();
  print_load_chart ();
  ()

**)

(**

let () =
  Printexc.record_backtrace true;

  (* ========================================================== *)
  (* GHZ 16                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder GHZ16 [0;1]"
    (protect_unit (fun () -> test_opListOrder ghz16_prog));

  report_unit "gen_hb GHZ16 [0;1]"
    (protect_unit (fun () -> test_gen_hb ghz16_prog));

  report_unit "gen_seq GHZ16 [0;1]"
    (protect_unit (fun () -> test_gen_seq ghz16_prog));

  report_unit "gen_mem GHZ16 [0;1]"
    (protect_unit (fun () -> test_gen_mem ghz16_prog mids_2));

  report_unit "gen_prog GHZ16 [0;1]"
    (protect_unit (fun () -> test_gen_prog ghz16_prog mids_2));

  test_num_mem_configs ghz16_prog mids_2;
  test_num_final_configs ghz16_prog mids_2;

  report_best "autodisq_first GHZ16 [0;1]"
    (protect_bench (fun () -> autodisq_first ghz16_prog mids_2));

  report_best "autodisq_best GHZ16 [0;1]"
    (protect_bench (fun () -> autodisq_best ghz16_prog mids_2));

  report_best "autodisq_best_1 GHZ16 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 ghz16_prog mids_2));

  (* ========================================================== *)
  (* SHOR 16                                                    *)
  (* ========================================================== *)
  report_unit "opListOrder SHOR16 [0;1]"
    (protect_unit (fun () -> test_opListOrder (shor16_prog 16)));

  report_unit "gen_hb SHOR16 [0;1]"
    (protect_unit (fun () -> test_gen_hb (shor16_prog 16)));

  report_unit "gen_seq SHOR16 [0;1]"
    (protect_unit (fun () -> test_gen_seq (shor16_prog 16)));

  report_unit "gen_mem SHOR16 [0;1]"
    (protect_unit (fun () -> test_gen_mem (shor16_prog 16) mids_2));

  report_unit "gen_prog SHOR16 [0;1]"
    (protect_unit (fun () -> test_gen_prog (shor16_prog 16) mids_2));

  report_best "autodisq_first SHOR16 [0;1]"
    (protect_bench (fun () -> autodisq_first (shor16_prog 16) mids_2));

  report_best "autodisq_best SHOR16 [0;1]"
    (protect_bench (fun () -> autodisq_best (shor16_prog 16) mids_2));

  report_best "autodisq_best_1 SHOR16 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 (shor16_prog 16) mids_2));

  (* ========================================================== *)
  (* Ripple-Carry Adder 16                                      *)
  (* ========================================================== *)
  report_unit "opListOrder RippleCarry16 [0;1]"
    (protect_unit (fun () -> test_opListOrder rippleCarry16));

  report_unit "gen_hb RippleCarry16 [0;1]"
    (protect_unit (fun () -> test_gen_hb rippleCarry16));

  report_unit "gen_seq RippleCarry16 [0;1]"
    (protect_unit (fun () -> test_gen_seq rippleCarry16));

  report_unit "gen_mem RippleCarry16 [0;1]"
    (protect_unit (fun () -> test_gen_mem rippleCarry16 mids_2));

  report_unit "gen_prog RippleCarry16 [0;1]"
    (protect_unit (fun () -> test_gen_prog rippleCarry16 mids_2));

  report_best "autodisq_first RippleCarry16 [0;1]"
    (protect_bench (fun () -> autodisq_first rippleCarry16 mids_2));

  report_best "autodisq_best RippleCarry16 [0;1]"
    (protect_bench (fun () -> autodisq_best rippleCarry16 mids_2));

  report_best "autodisq_best_1 RippleCarry16 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 rippleCarry16 mids_2));

  (* ========================================================== *)
  (* QFT Adder 16                                               *)
  (* ========================================================== *)
  report_unit "opListOrder QFTAdder16 [0;1]"
    (protect_unit (fun () -> test_opListOrder qftAdder16));

  report_unit "gen_hb QFTAdder16 [0;1]"
    (protect_unit (fun () -> test_gen_hb qftAdder16));

  report_unit "gen_seq QFTAdder16 [0;1]"
    (protect_unit (fun () -> test_gen_seq qftAdder16));

  report_unit "gen_mem QFTAdder16 [0;1]"
    (protect_unit (fun () -> test_gen_mem qftAdder16 mids_2));

  report_unit "gen_prog QFTAdder16 [0;1]"
    (protect_unit (fun () -> test_gen_prog qftAdder16 mids_2));

  report_best "autodisq_first QFTAdder16 [0;1]"
    (protect_bench (fun () -> autodisq_first qftAdder16 mids_2));

  report_best "autodisq_best QFTAdder16 [0;1]"
    (protect_bench (fun () -> autodisq_best qftAdder16 mids_2));

  report_best "autodisq_best_1 QFTAdder16 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 qftAdder16 mids_2));

  (* ========================================================== *)
  (* QFT 16                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder QFT16 [0;1]"
    (protect_unit (fun () -> test_opListOrder qft16_only_seq));

  report_unit "gen_hb QFT16 [0;1]"
    (protect_unit (fun () -> test_gen_hb qft16_only_seq));

  report_unit "gen_seq QFT16 [0;1]"
    (protect_unit (fun () -> test_gen_seq qft16_only_seq));

  report_unit "gen_mem QFT16 [0;1]"
    (protect_unit (fun () -> test_gen_mem qft16_only_seq mids_2));

  report_unit "gen_prog QFT16 [0;1]"
    (protect_unit (fun () -> test_gen_prog qft16_only_seq mids_2));

  report_best "autodisq_first QFT16 [0;1]"
    (protect_bench (fun () -> autodisq_first qft16_only_seq mids_2));

  report_best "autodisq_best QFT16 [0;1]"
    (protect_bench (fun () -> autodisq_best qft16_only_seq mids_2));

  report_best "autodisq_best_1 QFT16 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 qft16_only_seq mids_2));

  (* ========================================================== *)
  (* Amplitude Estimation 16                                    *)
  (* ========================================================== *)
  report_unit "opListOrder AmpEst16 [0;1]"
    (protect_unit (fun () -> test_opListOrder ampEst16Seq));

  report_unit "gen_hb AmpEst16 [0;1]"
    (protect_unit (fun () -> test_gen_hb ampEst16Seq));

  report_unit "gen_seq AmpEst16 [0;1]"
    (protect_unit (fun () -> test_gen_seq ampEst16Seq));

  report_unit "gen_mem AmpEst16 [0;1]"
    (protect_unit (fun () -> test_gen_mem ampEst16Seq mids_2));

  report_unit "gen_prog AmpEst16 [0;1]"
    (protect_unit (fun () -> test_gen_prog ampEst16Seq mids_2));

  report_best "autodisq_first AmpEst16 [0;1]"
    (protect_bench (fun () -> autodisq_first ampEst16Seq mids_2));

  report_best "autodisq_best AmpEst16 [0;1]"
    (protect_bench (fun () -> autodisq_best ampEst16Seq mids_2));

  report_best "autodisq_best_1 AmpEst16 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 ampEst16Seq mids_2));

  (* ========================================================== *)
  (* Discrete Log 16                                            *)
  (* ========================================================== *)
  report_unit "opListOrder DiscreteLog16 [0;1]"
    (protect_unit (fun () -> test_opListOrder discreteLog16Seq));

  report_unit "gen_hb DiscreteLog16 [0;1]"
    (protect_unit (fun () -> test_gen_hb discreteLog16Seq));

  report_unit "gen_seq DiscreteLog16 [0;1]"
    (protect_unit (fun () -> test_gen_seq discreteLog16Seq));

  report_unit "gen_mem DiscreteLog16 [0;1]"
    (protect_unit (fun () -> test_gen_mem discreteLog16Seq mids_2));

  report_unit "gen_prog DiscreteLog16 [0;1]"
    (protect_unit (fun () -> test_gen_prog discreteLog16Seq mids_2));

  report_best "autodisq_first DiscreteLog16 [0;1]"
    (protect_bench (fun () -> autodisq_first discreteLog16Seq mids_2));

  report_best "autodisq_best DiscreteLog16 [0;1]"
    (protect_bench (fun () -> autodisq_best discreteLog16Seq mids_2));

  report_best "autodisq_best_1 DiscreteLog16 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 discreteLog16Seq mids_2));

  (* ---- summary output ---- *)
  print_summary ();
  print_load_chart ();
  ()
**)



(**

let () =
  Printexc.record_backtrace true;

  (* ========================================================== *)
  (* GHZ 16                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder GHZ16 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder ghz16_prog));

  report_unit "gen_hb GHZ16 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb ghz16_prog));

  report_unit "gen_seq GHZ16 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq ghz16_prog));

  report_unit "gen_mem GHZ16 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem ghz16_prog mids_3));

  report_unit "gen_prog GHZ16 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog ghz16_prog mids_3));

  test_num_mem_configs ghz16_prog mids_3;
  test_num_final_configs ghz16_prog mids_3;

  report_best "autodisq_first GHZ16 [0;1;2]"
    (protect_bench (fun () -> autodisq_first ghz16_prog mids_3));

  report_best "autodisq_best GHZ16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best ghz16_prog mids_3));

  report_best "autodisq_best_1 GHZ16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 ghz16_prog mids_3));

  (* ========================================================== *)
  (* SHOR 16                                                    *)
  (* ========================================================== *)
  report_unit "opListOrder SHOR16 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder (shor16_prog 16)));

  report_unit "gen_hb SHOR16 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb (shor16_prog 16)));

  report_unit "gen_seq SHOR16 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq (shor16_prog 16)));

  report_unit "gen_mem SHOR16 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem (shor16_prog 16) mids_3));

  report_unit "gen_prog SHOR16 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog (shor16_prog 16) mids_3));

  report_best "autodisq_first SHOR16 [0;1;2]"
    (protect_bench (fun () -> autodisq_first (shor16_prog 16) mids_3));

  report_best "autodisq_best SHOR16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best (shor16_prog 16) mids_3));

  report_best "autodisq_best_1 SHOR16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 (shor16_prog 16) mids_3));

  (* ========================================================== *)
  (* Ripple-Carry Adder 16                                      *)
  (* ========================================================== *)
  report_unit "opListOrder RippleCarry16 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder rippleCarry16));

  report_unit "gen_hb RippleCarry16 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb rippleCarry16));

  report_unit "gen_seq RippleCarry16 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq rippleCarry16));

  report_unit "gen_mem RippleCarry16 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem rippleCarry16 mids_3));

  report_unit "gen_prog RippleCarry16 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog rippleCarry16 mids_3));

  report_best "autodisq_first RippleCarry16 [0;1;2]"
    (protect_bench (fun () -> autodisq_first rippleCarry16 mids_3));

  report_best "autodisq_best RippleCarry16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best rippleCarry16 mids_3));

  report_best "autodisq_best_1 RippleCarry16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 rippleCarry16 mids_3));

  (* ========================================================== *)
  (* QFT Adder 16                                               *)
  (* ========================================================== *)
  report_unit "opListOrder QFTAdder16 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder qftAdder16));

  report_unit "gen_hb QFTAdder16 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb qftAdder16));

  report_unit "gen_seq QFTAdder16 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq qftAdder16));

  report_unit "gen_mem QFTAdder16 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem qftAdder16 mids_3));

  report_unit "gen_prog QFTAdder16 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog qftAdder16 mids_3));

  report_best "autodisq_first QFTAdder16 [0;1;2]"
    (protect_bench (fun () -> autodisq_first qftAdder16 mids_3));

  report_best "autodisq_best QFTAdder16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best qftAdder16 mids_3));

  report_best "autodisq_best_1 QFTAdder16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 qftAdder16 mids_3));


  (* ========================================================== *)
  (* QFT 16                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder QFT16 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder qft16_only_seq));

  report_unit "gen_hb QFT16 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb qft16_only_seq));

  report_unit "gen_seq QFT16 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq qft16_only_seq));

  report_unit "gen_mem QFT16 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem qft16_only_seq mids_3));

  report_unit "gen_prog QFT16 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog qft16_only_seq mids_3));

  report_best "autodisq_first QFT16 [0;1;2]"
    (protect_bench (fun () -> autodisq_first qft16_only_seq mids_3));

  report_best "autodisq_best QFT16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best qft16_only_seq mids_3));

  report_best "autodisq_best_1 QFT16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 qft16_only_seq mids_3));


  (* ========================================================== *)
  (* Amplitude Estimation 16                                    *)
  (* ========================================================== *)
  report_unit "opListOrder AmpEst16 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder ampEst16Seq));

  report_unit "gen_hb AmpEst16 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb ampEst16Seq));

  report_unit "gen_seq AmpEst16 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq ampEst16Seq));

  report_unit "gen_mem AmpEst16 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem ampEst16Seq mids_3));

  report_unit "gen_prog AmpEst16 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog ampEst16Seq mids_3));

  report_best "autodisq_first AmpEst16 [0;1;2]"
    (protect_bench (fun () -> autodisq_first ampEst16Seq mids_3));

  report_best "autodisq_best AmpEst16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best ampEst16Seq mids_3));

  report_best "autodisq_best_1 AmpEst16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 ampEst16Seq mids_3));

  (* ========================================================== *)
  (* Discrete Log 16                                            *)
  (* ========================================================== *)
  report_unit "opListOrder DiscreteLog16 [0;1;2]"
    (protect_unit (fun () -> test_opListOrder discreteLog16Seq));

  report_unit "gen_hb DiscreteLog16 [0;1;2]"
    (protect_unit (fun () -> test_gen_hb discreteLog16Seq));

  report_unit "gen_seq DiscreteLog16 [0;1;2]"
    (protect_unit (fun () -> test_gen_seq discreteLog16Seq));

  report_unit "gen_mem DiscreteLog16 [0;1;2]"
    (protect_unit (fun () -> test_gen_mem discreteLog16Seq mids_3));

  report_unit "gen_prog DiscreteLog16 [0;1;2]"
    (protect_unit (fun () -> test_gen_prog discreteLog16Seq mids_3));

  report_best "autodisq_first DiscreteLog16 [0;1;2]"
    (protect_bench (fun () -> autodisq_first discreteLog16Seq mids_3));

  report_best "autodisq_best DiscreteLog16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best discreteLog16Seq mids_3));

  report_best "autodisq_best_1 DiscreteLog16 [0;1;2]"
    (protect_bench (fun () -> autodisq_best_1 discreteLog16Seq mids_3));

  (* ---- summary output ---- *)
  print_summary ();
  print_load_chart ();
  ()

**)


(**
let () =
  Printexc.record_backtrace true;

  (* ========================================================== *)
  (* GHZ 16                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder GHZ16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder ghz16_prog));

  report_unit "gen_hb GHZ16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb ghz16_prog));

  report_unit "gen_seq GHZ16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq ghz16_prog));

  report_unit "gen_mem GHZ16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem ghz16_prog mids_5));

  report_unit "gen_prog GHZ16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog ghz16_prog mids_5));

  test_num_mem_configs ghz16_prog mids_5;
  test_num_final_configs ghz16_prog mids_5;

  report_best "autodisq_first GHZ16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first ghz16_prog mids_5));

  report_best "autodisq_best GHZ16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best ghz16_prog mids_5));

  report_best "autodisq_best_1 GHZ16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 ghz16_prog mids_5));

  (* ========================================================== *)
  (* SHOR 16                                                    *)
  (* ========================================================== *)
  report_unit "opListOrder SHOR16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder (shor16_prog 16)));

  report_unit "gen_hb SHOR16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb (shor16_prog 16)));

  report_unit "gen_seq SHOR16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq (shor16_prog 16)));

  report_unit "gen_mem SHOR16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem (shor16_prog 16) mids_5));

  report_unit "gen_prog SHOR16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog (shor16_prog 16) mids_5));

  report_best "autodisq_first SHOR16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first (shor16_prog 16) mids_5));

  report_best "autodisq_best SHOR16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best (shor16_prog 16) mids_5));

  report_best "autodisq_best_1 SHOR16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 (shor16_prog 16) mids_5));

  (* ========================================================== *)
  (* Ripple-Carry Adder 16                                      *)
  (* ========================================================== *)
  report_unit "opListOrder RippleCarry16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder rippleCarry16));

  report_unit "gen_hb RippleCarry16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb rippleCarry16));

  report_unit "gen_seq RippleCarry16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq rippleCarry16));

  report_unit "gen_mem RippleCarry16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem rippleCarry16 mids_5));

  report_unit "gen_prog RippleCarry16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog rippleCarry16 mids_5));

  report_best "autodisq_first RippleCarry16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first rippleCarry16 mids_5));

  report_best "autodisq_best RippleCarry16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best rippleCarry16 mids_5));

  report_best "autodisq_best_1 RippleCarry16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 rippleCarry16 mids_5));

  (* ========================================================== *)
  (* QFT Adder 16                                               *)
  (* ========================================================== *)
  report_unit "opListOrder QFTAdder16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder qftAdder16));

  report_unit "gen_hb QFTAdder16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb qftAdder16));

  report_unit "gen_seq QFTAdder16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq qftAdder16));

  report_unit "gen_mem QFTAdder16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem qftAdder16 mids_5));

  report_unit "gen_prog QFTAdder16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog qftAdder16 mids_5));

  report_best "autodisq_first QFTAdder16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first qftAdder16 mids_5));

  report_best "autodisq_best QFTAdder16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best qftAdder16 mids_5));

  report_best "autodisq_best_1 QFTAdder16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 qftAdder16 mids_5));

  (* ========================================================== *)
  (* QFT 16                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder QFT16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder qft16_only_seq));

  report_unit "gen_hb QFT16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb qft16_only_seq));

  report_unit "gen_seq QFT16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq qft16_only_seq));

  report_unit "gen_mem QFT16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem qft16_only_seq mids_5));

  report_unit "gen_prog QFT16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog qft16_only_seq mids_5));

  report_best "autodisq_first QFT16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first qft16_only_seq mids_5));

  report_best "autodisq_best QFT16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best qft16_only_seq mids_5));

  report_best "autodisq_best_1 QFT16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 qft16_only_seq mids_5));

  (* ========================================================== *)
  (* Amplitude Estimation 16                                    *)
  (* ========================================================== *)
  report_unit "opListOrder AmpEst16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder ampEst16Seq));

  report_unit "gen_hb AmpEst16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb ampEst16Seq));

  report_unit "gen_seq AmpEst16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq ampEst16Seq));

  report_unit "gen_mem AmpEst16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem ampEst16Seq mids_5));

  report_unit "gen_prog AmpEst16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog ampEst16Seq mids_5));

  report_best "autodisq_first AmpEst16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first ampEst16Seq mids_5));

  report_best "autodisq_best AmpEst16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best ampEst16Seq mids_5));

  report_best "autodisq_best_1 AmpEst16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 ampEst16Seq mids_5));

  (* ========================================================== *)
  (* Discrete Log 16                                            *)
  (* ========================================================== *)
  report_unit "opListOrder DiscreteLog16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_opListOrder discreteLog16Seq));

  report_unit "gen_hb DiscreteLog16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_hb discreteLog16Seq));

  report_unit "gen_seq DiscreteLog16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_seq discreteLog16Seq));

  report_unit "gen_mem DiscreteLog16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_mem discreteLog16Seq mids_5));

  report_unit "gen_prog DiscreteLog16 [0;1;2;3;4]"
    (protect_unit (fun () -> test_gen_prog discreteLog16Seq mids_5));

  report_best "autodisq_first DiscreteLog16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_first discreteLog16Seq mids_5));

  report_best "autodisq_best DiscreteLog16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best discreteLog16Seq mids_5));

  report_best "autodisq_best_1 DiscreteLog16 [0;1;2;3;4]"
    (protect_bench (fun () -> autodisq_best_1 discreteLog16Seq mids_5));

  (* ---- summary output ---- *)
  print_summary ();
  print_load_chart ();
  ()

**)




let () =
  Printexc.record_backtrace true;

  (* ========================================================== *)
  (* GHZ 32                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder GHZ32 [0;1]"
    (protect_unit (fun () -> test_opListOrder ghz32_prog));

  report_unit "gen_hb GHZ32 [0;1]"
    (protect_unit (fun () -> test_gen_hb ghz32_prog));

  report_unit "gen_seq GHZ32 [0;1]"
    (protect_unit (fun () -> test_gen_seq ghz32_prog));

  report_unit "gen_mem GHZ32 [0;1]"
    (protect_unit (fun () -> test_gen_mem ghz32_prog mids_2));

  report_unit "gen_prog GHZ32 [0;1]"
    (protect_unit (fun () -> test_gen_prog ghz32_prog mids_2));

  test_num_mem_configs ghz32_prog mids_2;
  test_num_final_configs ghz32_prog mids_2;

  report_best "autodisq_first GHZ32 [0;1]"
    (protect_bench (fun () -> autodisq_first ghz32_prog mids_2));

  report_best "autodisq_best GHZ32 [0;1]"
    (protect_bench (fun () -> autodisq_best ghz32_prog mids_2));

  report_best "autodisq_best_1 GHZ32 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 ghz32_prog mids_2));

  (* ========================================================== *)
  (* SHOR 32                                                    *)
  (* ========================================================== *)
  report_unit "opListOrder SHOR32 [0;1]"
    (protect_unit (fun () -> test_opListOrder shor32_prog));

  report_unit "gen_hb SHOR32 [0;1]"
    (protect_unit (fun () -> test_gen_hb shor32_prog));

  report_unit "gen_seq SHOR32 [0;1]"
    (protect_unit (fun () -> test_gen_seq shor32_prog));

  report_unit "gen_mem SHOR32 [0;1]"
    (protect_unit (fun () -> test_gen_mem shor32_prog mids_2));

  report_unit "gen_prog SHOR32 [0;1]"
    (protect_unit (fun () -> test_gen_prog shor32_prog mids_2));

  test_num_mem_configs shor32_prog mids_2;
  test_num_final_configs shor32_prog mids_2;

  report_best "autodisq_first SHOR32 [0;1]"
    (protect_bench (fun () -> autodisq_first shor32_prog mids_2));

  report_best "autodisq_best SHOR32 [0;1]"
    (protect_bench (fun () -> autodisq_best shor32_prog mids_2));

  report_best "autodisq_best_1 SHOR32 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 shor32_prog mids_2));

  (* ========================================================== *)
  (* QFT 32                                                     *)
  (* ========================================================== *)
  report_unit "opListOrder QFT32 [0;1]"
    (protect_unit (fun () -> test_opListOrder qft32_only_seq));

  report_unit "gen_hb QFT32 [0;1]"
    (protect_unit (fun () -> test_gen_hb qft32_only_seq));

  report_unit "gen_seq QFT32 [0;1]"
    (protect_unit (fun () -> test_gen_seq qft32_only_seq));

  report_unit "gen_mem QFT32 [0;1]"
    (protect_unit (fun () -> test_gen_mem qft32_only_seq mids_2));

  report_unit "gen_prog QFT32 [0;1]"
    (protect_unit (fun () -> test_gen_prog qft32_only_seq mids_2));

  test_num_mem_configs qft32_only_seq mids_2;
  test_num_final_configs qft32_only_seq mids_2;

  report_best "autodisq_first QFT32 [0;1]"
    (protect_bench (fun () -> autodisq_first qft32_only_seq mids_2));

  report_best "autodisq_best QFT32 [0;1]"
    (protect_bench (fun () -> autodisq_best qft32_only_seq mids_2));

  report_best "autodisq_best_1 QFT32 [0;1]"
    (protect_bench (fun () -> autodisq_best_1 qft32_only_seq mids_2));

  (* ---- summary output ---- *)
  print_summary ();
  print_load_chart ();
  ()


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


open Autodisq_extract

(* ---------- printers  ---------- *)

let rec pp_aexp = function
  | BA x -> Printf.sprintf "BA(%d)" x
  | Num n -> Printf.sprintf "Num(%d)" n
  | APlus (a,b) -> Printf.sprintf "APlus(%s,%s)" (pp_aexp a) (pp_aexp b)
  | AMult (a,b) -> Printf.sprintf "AMult(%s,%s)" (pp_aexp a) (pp_aexp b)

(* --- print bounds/ranges/loci so we can see measurement loci --- *)
let pp_bound = function
  | BNum n -> Printf.sprintf "BNum(%d)" n
  | BVar (v,off) -> Printf.sprintf "BVar(%d,%d)" v off

let pp_range (((q, lo), hi) : range) =
  Printf.sprintf "((%d,%s),%s)" q (pp_bound lo) (pp_bound hi)

let pp_locus (k : locus) =
  "[" ^ String.concat ";" (List.map pp_range k) ^ "]"

let rec pp_exp = function
  | SKIP (x,a)      -> Printf.sprintf "SKIP(%d,%s)" x (pp_aexp a)
  | X (q,a)         -> Printf.sprintf "X(%d,%s)" q (pp_aexp a)
  | H (q,a)         -> Printf.sprintf "H(%d,%s)" q (pp_aexp a)
  | RZ (k,q,a)      -> Printf.sprintf "RZ(%d,%d,%s)" k q (pp_aexp a)
  | RRZ (k,q,a)     -> Printf.sprintf "RRZ(%d,%d,%s)" k q (pp_aexp a)
  | SR (k,q)        -> Printf.sprintf "SR(%d,%d)" k q
  | SRR (k,q)       -> Printf.sprintf "SRR(%d,%d)" k q
  | QFT (q,n)       -> Printf.sprintf "QFT(%d,%d)" q n
  | RQFT (q,n)      -> Printf.sprintf "RQFT(%d,%d)" q n
  | Addto (x,q)     -> Printf.sprintf "Addto(%d,%d)" x q
  | CU (c,a,e)      -> Printf.sprintf "CU(%d,%s,%s)" c (pp_aexp a) (pp_exp e)
  | Seq (e1,e2)     -> Printf.sprintf "Seq(%s,%s)" (pp_exp e1) (pp_exp e2)

let pp_cexp = function
  | CNew (q,n)        -> Printf.sprintf "CNew(%d,%d)" q n
  | CAppU (loc,e)     -> Printf.sprintf "CAppU(%s,%s)" (pp_locus loc) (pp_exp e)
  | CMeas (x,loc)     -> Printf.sprintf "CMeas(%d,%s)" x (pp_locus loc)

let pp_cdexp = function
  | NewCh (c,n) -> Printf.sprintf "NewCh(%d,%d)" c n
  | Send (c,a)  -> Printf.sprintf "Send(%d,%s)" c (pp_aexp a)
  | Recv (c,x)  -> Printf.sprintf "Recv(%d,%d)" c x

let rec pp_process = function
  | PNil -> "PNil"
  | AP (a,p) -> Printf.sprintf "AP(%s); %s" (pp_cexp a) (pp_process p)
  | DP (d,p) -> Printf.sprintf "DP(%s); %s" (pp_cdexp d) (pp_process p)
  | PIf (_b,p1,p2) ->
      Printf.sprintf "PIf(...,%s,%s)" (pp_process p1) (pp_process p2)

let pp_memb (m : memb) : unit =
  match m with
  | Memb (id, ps) ->
      Printf.printf "Memb %d:\n%!" id;
      List.iter (fun p -> Printf.printf "  %s\n%!" (pp_process p)) ps
  | LockMemb (id, _, ps) ->
      Printf.printf "LockMemb %d:\n%!" id;
      List.iter (fun p -> Printf.printf "  %s\n%!" (pp_process p)) ps

let pp_cfg (cfg:config) : unit =
  List.iter pp_memb cfg

(* ---------- Shared compiler settings  ---------- *)

let seq0 : seq_relation = fun (_:myOp) -> 0
let moQ0 : qubit_mem_assign = fun (_:var) -> 0
let moO_const (k:int) : op_mem_assign = fun (_:myOp) -> k

(* ---------- Extra printers to SHOW partitions (Alg3) ---------- *)

let pp_myOp = function
  | OpAP a -> Printf.sprintf "OpAP(%s)" (pp_cexp a)
  | OpDP d -> Printf.sprintf "OpDP(%s)" (pp_cdexp d)
  | OpIf (_b, p, q) ->
      Printf.sprintf "OpIf(...,%s,%s)" (pp_process p) (pp_process q)

let pp_myOp_list (xs : myOp list) : unit =
  List.iter (fun o -> Printf.printf "  %s\n%!" (pp_myOp o)) xs

(* Use extracted opt_hp. *)
let hp_opt (hp : hb_relation) (seq : seq_relation) : hb_relation =
  opt_hp hp seq

(* Print SCC blocks (this is the REAL “partition” before flattening) *)
let show_alg3_blocks (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3] SCC partitions for %s\n%!" pname;

  let hp  : hb_relation  = gen_hp ops in
  let seq : seq_relation = seq0 in
  let hp' : hb_relation  = hp_opt hp seq in

  let blocks : myOp list list =
    scc_partition myOp_eqb hp' (uniq_ops myOp_eqb ops)
  in
  List.iteri
    (fun i block ->
      Printf.printf "Block %d:\n%!" i;
      pp_myOp_list block)
    blocks

(* print the flattened schedule returned by auto_parallelize_alg3 *)
let show_alg3_flat (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3] Flattened grouped schedule for %s\n%!" pname;

  let hp  : hb_relation  = gen_hp ops in
  let seq : seq_relation = seq0 in
  let procs : process list = auto_parallelize_alg3 myOp_eqb ops hp seq in
  List.iter (fun pr -> Printf.printf "  %s\n%!" (pp_process pr)) procs

(* --------- LAYER partition printers (Alg3-Layers) --------- *)

let show_alg3_layers_blocks (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3-Layers] Ready-layer partitions for %s\n%!" pname;

  let hp  : hb_relation  = gen_hp ops in
  let seq : seq_relation = seq0 in
  let hp' : hb_relation  = hp_opt hp seq in

  let layers : myOp list list =
    layer_partition myOp_eqb hp' (uniq_ops myOp_eqb ops)
  in
  List.iteri
    (fun i layer ->
      Printf.printf "Layer %d:\n%!" i;
      pp_myOp_list layer)
    layers

let show_alg3_layers_flat (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3-Layers] Flattened grouped schedule for %s\n%!" pname;

  let hp  : hb_relation  = gen_hp ops in
  let seq : seq_relation = seq0 in
  let procs : process list = auto_parallelize_alg3_layers myOp_eqb ops hp seq in
  List.iter (fun pr -> Printf.printf "  %s\n%!" (pp_process pr)) procs

let compare_alg3 (pname:string) (ops:op_list) : unit =
  show_alg3_blocks pname ops;
  show_alg3_flat   pname ops;
  show_alg3_layers_blocks pname ops;
  show_alg3_layers_flat   pname ops

(* ---------- Test harness ---------- *)

let show (title:string) (prog:distributed_prog) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "%s\n%!" title;
  Printf.printf "Cost = %d\n%!" (fit prog);
  pp_cfg prog

let test_alg2 (pname:string) (p:op_list) (mem:int) : unit =
  let prog = gen_prog_paper seq0 moQ0 (moO_const mem) p in
  show (Printf.sprintf "[Alg2] %s on mem%d" pname mem) prog

let test_alg1 (pname:string) (p:op_list) (kseq:int) (kmem:int) : unit =
  let cfg2 : config = [Memb (0, []); Memb (1, [])] in
  let prog = auto_disq_alg1_paper kseq kmem p cfg2 in
  show (Printf.sprintf "[Alg1] %s auto_disq_alg1_paper(kseq=%d,kmem=%d) on cfg2"
          pname kseq kmem) prog

let () =
  (* -------- Algorithm 2-------- *)
  test_alg2 "P_1" p_1 0;
  test_alg2 "P_1" p_1 1;

  test_alg2 "P_3" p_3 0;
  test_alg2 "P_3" p_3 1;

  test_alg2 "P_4" p_4 0;
  test_alg2 "P_4" p_4 1;
  test_alg2 "P_4" p_4 5;

  test_alg2 "P_5 (Grover)" p_5 0;
  test_alg2 "P_5 (Grover)" p_5 5;

  test_alg2 "P_6 (Teleport)" p_6 0;
  test_alg2 "P_6 (Teleport)" p_6 5;

  (* -------- Algorithm 2: Shor tests -------- *)
  test_alg2 "Shor_Qprog" shor_Qprog 0;
  test_alg2 "Shor_Qprog" shor_Qprog 1;
  test_alg2 "Shor_Qprog" shor_Qprog 3;
  test_alg2 "Shor_Qprog" shor_Qprog 5;

  (* -------- Algorithm 2:  -------- *)
  show "QFT32_dist0 (already distributed)" qFT32_dist0;
  show "GHZ32_best (already distributed)" gHZ32_best;

  test_alg2 "GHZ32_prog" gHZ32_prog 0;
  test_alg2 "GHZ32_prog" gHZ32_prog 1;
  test_alg2 "GHZ32_prog" gHZ32_prog 5;

  test_alg2 "QFT64_prog" qFT64_prog 0;
  test_alg2 "QFT64_prog" qFT64_prog 1;
  test_alg2 "QFT64_prog" qFT64_prog 5;

  test_alg2 "Shor_Qprog32" shor_Qprog32 0;
  test_alg2 "Shor_Qprog32" shor_Qprog32 1;
  test_alg2 "Shor_Qprog32" shor_Qprog32 3;
  test_alg2 "Shor_Qprog32" shor_Qprog32 5;

  test_alg2 "Shor_Qprog_64" shor_Qprog_64 0;
  test_alg2 "Shor_Qprog_64" shor_Qprog_64 1;
  test_alg2 "Shor_Qprog_64" shor_Qprog_64 3;
  test_alg2 "Shor_Qprog_64" shor_Qprog_64 5;

  (* -------- Algorithm 1: auto search tests -------- *)
  test_alg1 "P_1" p_1 3 3;
  test_alg1 "P_3" p_3 3 3;
  test_alg1 "P_4" p_4 3 3;
  test_alg1 "P_5" p_5 3 3;
  test_alg1 "P_6" p_6 3 3;

  (* -------- Algorithm 1: Shor auto search -------- *)
  test_alg1 "Shor_Qprog" shor_Qprog 3 3;

  (* -------- Algorithm 1:  -------- *)
  test_alg1 "GHZ32_prog"   gHZ32_prog   3 3;
  test_alg1 "QFT64_prog"   qFT64_prog   3 3;
  test_alg1 "Shor_Qprog32" shor_Qprog32 3 3;
  test_alg1 "Shor_Qprog_64" shor_Qprog_64 3 3;

  (* -------- Algorithm 3: SHOW PARTITIONS (SCC) -------- *)
  show_alg3_blocks "P_1" p_1;
  show_alg3_flat   "P_1" p_1;

  show_alg3_blocks "P_3" p_3;
  show_alg3_flat   "P_3" p_3;

  show_alg3_blocks "P_4" p_4;
  show_alg3_flat   "P_4" p_4;

  show_alg3_blocks "P_5 (Grover)" p_5;
  show_alg3_flat   "P_5 (Grover)" p_5;

  show_alg3_blocks "P_6 (Teleport)" p_6;
  show_alg3_flat   "P_6 (Teleport)" p_6;

  show_alg3_blocks "Shor_Qprog" shor_Qprog;
  show_alg3_flat   "Shor_Qprog" shor_Qprog;

  (* -------- Algorithm 3: SHOW PARTITIONS (SCC):  -------- *)

  show_alg3_blocks "GHZ32_prog" gHZ32_prog;
  show_alg3_flat   "GHZ32_prog" gHZ32_prog;

  show_alg3_blocks "QFT64_prog" qFT64_prog;
  show_alg3_flat   "QFT64_prog" qFT64_prog;

  show_alg3_blocks "Shor_Qprog32" shor_Qprog32;
  show_alg3_flat   "Shor_Qprog32" shor_Qprog32;

  show_alg3_blocks "Shor_Qprog_64" shor_Qprog_64;
  show_alg3_flat   "Shor_Qprog_64" shor_Qprog_64;

  (* -------- Algorithm 3: SHOW PARTITIONS (Layers) -------- *)
  show_alg3_layers_blocks "P_1" p_1;
  show_alg3_layers_flat   "P_1" p_1;

  show_alg3_layers_blocks "P_3" p_3;
  show_alg3_layers_flat   "P_3" p_3;

  show_alg3_layers_blocks "P_4" p_4;
  show_alg3_layers_flat   "P_4" p_4;

  show_alg3_layers_blocks "P_5 (Grover)" p_5;
  show_alg3_layers_flat   "P_5 (Grover)" p_5;

  show_alg3_layers_blocks "P_6 (Teleport)" p_6;
  show_alg3_layers_flat   "P_6 (Teleport)" p_6;

  show_alg3_layers_blocks "Shor_Qprog" shor_Qprog;
  show_alg3_layers_flat   "Shor_Qprog" shor_Qprog;

  (* -------- Algorithm 3: SHOW PARTITIONS (Layers):  -------- *)
  show_alg3_layers_blocks "GHZ32_prog" gHZ32_prog;
  show_alg3_layers_flat   "GHZ32_prog" gHZ32_prog;

  show_alg3_layers_blocks "QFT64_prog" qFT64_prog;
  show_alg3_layers_flat   "QFT64_prog" qFT64_prog;

  show_alg3_layers_blocks "Shor_Qprog32" shor_Qprog32;
  show_alg3_layers_flat   "Shor_Qprog32" shor_Qprog32;

  show_alg3_layers_blocks "Shor_Qprog_64" shor_Qprog_64;
  show_alg3_layers_flat   "Shor_Qprog_64" shor_Qprog_64;




(*

rm -f *.cmi *.cmo run_autodisq
ocamlc -c autodisq_extract.mli
ocamlc -c autodisq_extract.ml
ocamlc -c AUTO_Test.ml
ocamlc -o run_autodisq autodisq_extract.cmo AUTO_Test.cmo
./run_autodisq


*)

*)












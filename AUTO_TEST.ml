


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

(* Use your extracted opt_hp, but keep the name clear. *)
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

(* Also print the flattened schedule returned by auto_parallelize_alg3 *)
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

  (* -------- Algorithm 1: auto search tests -------- *)
  test_alg1 "P_1" p_1 3 3;
  test_alg1 "P_3" p_3 3 3;
  test_alg1 "P_4" p_4 3 3;
  test_alg1 "P_5" p_5 3 3;
  test_alg1 "P_6" p_6 3 3;

  (* -------- Algorithm 1: Shor auto search -------- *)
  test_alg1 "Shor_Qprog" shor_Qprog 3 3;

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

  (* -------- OPTIONAL: One-call comparison (uncomment to use) -------- *)
  (*
  compare_alg3 "P_1" p_1;
  compare_alg3 "P_3" p_3;
  compare_alg3 "P_4" p_4;
  compare_alg3 "P_5 (Grover)" p_5;
  compare_alg3 "P_6 (Teleport)" p_6;
  compare_alg3 "Shor_Qprog" shor_Qprog;
  *)

*)

























(*
open Autodisq_extract

(* ---------- printers  ---------- *)

let pp_aexp = function
  | BA x      -> Printf.sprintf "BA(%d)" x
  | Num n     -> Printf.sprintf "Num(%d)" n
  | APlus _   -> "APlus(...)"
  | AMult _   -> "AMult(...)"

(* ---  print bounds/ranges/loci so we can see measurement loci --- *)
let pp_bound = function
  | BNum n -> Printf.sprintf "BNum(%d)" n
  | _ -> "B(...)"

let pp_range ((q, lo), hi) =
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
  | CNew (q,n)     -> Printf.sprintf "CNew(%d,%d)" q n
  | CAppU (_l,e)   -> Printf.sprintf "CAppU(%s)" (pp_exp e)
  | CMeas (x,l)    -> Printf.sprintf "CMeas(%d,%s)" x (pp_locus l)

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

(* Print SCC blocks (this is the REAL “partition” before flattening) *)
let show_alg3_blocks (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3] SCC partitions for %s\n%!" pname;

  let hp : hb_relation = gen_hp ops in
  let seq : seq_relation = seq0 in

  (* opt_hp restricts edges to those consistent with seq  *)
  let hp' : hb_relation = opt_hp hp seq in

  (* uniq_ops + scc_partition gives list(list myOp) = partition blocks *)
  let blocks : myOp list list =
    scc_partition myOp_eqb hp' (uniq_ops myOp_eqb ops)
  in

  List.iteri
    (fun i block ->
       Printf.printf "Block %d:\n%!" i;
       pp_myOp_list block)
    blocks

(* Also print the flattened schedule returned by auto_parallelize_alg3 *)
let show_alg3_flat (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3] Flattened grouped schedule for %s\n%!" pname;

  let hp : hb_relation = gen_hp ops in
  let seq : seq_relation = seq0 in
  let procs : process list = auto_parallelize_alg3 myOp_eqb ops hp seq in

  List.iter (fun pr -> Printf.printf "  %s\n%!" (pp_process pr)) procs

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

  (* -------- Algorithm 1: auto search tests -------- *)
  test_alg1 "P_1" p_1 3 3;
  test_alg1 "P_3" p_3 3 3;
  test_alg1 "P_4" p_4 3 3;
  test_alg1 "P_5" p_5 3 3;
  test_alg1 "P_6" p_6 3 3;

  (* -------- Algorithm 1: Shor auto search -------- *)
  test_alg1 "Shor_Qprog" shor_Qprog 3 3;

  (* -------- Algorithm 3: SHOW PARTITIONS -------- *)
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
  show_alg3_flat   "Shor_Qprog" shor_Qprog


*)






























open Autodisq_extract

(* ---------- Pretty printers (compact but informative) ---------- *)

let pp_aexp = function
  | BA x      -> Printf.sprintf "BA(%d)" x
  | Num n     -> Printf.sprintf "Num(%d)" n
  | APlus _   -> "APlus(...)"
  | AMult _   -> "AMult(...)"

(* ---  print bounds/ranges/loci so we can see measurement loci --- *)
let pp_bound = function
  | BNum n -> Printf.sprintf "BNum(%d)" n
  | _ -> "B(...)"

let pp_range ((q, lo), hi) =
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
  | CNew (q,n)     -> Printf.sprintf "CNew(%d,%d)" q n
  | CAppU (_l,e)   -> Printf.sprintf "CAppU(%s)" (pp_exp e)
  | CMeas (x,l)    -> Printf.sprintf "CMeas(%d,%s)" x (pp_locus l)

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

(* ---------- Extra printers to SHOW partitions (Alg3) ---------- *)

let pp_myOp = function
  | OpAP a -> Printf.sprintf "OpAP(%s)" (pp_cexp a)
  | OpDP d -> Printf.sprintf "OpDP(%s)" (pp_cdexp d)
  | OpIf (_b, p, q) ->
      Printf.sprintf "OpIf(...,%s,%s)" (pp_process p) (pp_process q)

let pp_myOp_list (xs : myOp list) : unit =
  List.iter (fun o -> Printf.printf "  %s\n%!" (pp_myOp o)) xs

(* Print SCC blocks (this is the REAL “partition” before flattening) *)
let show_alg3_blocks (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3] SCC partitions for %s\n%!" pname;

  let hp : hb_relation = gen_hp ops in
  let seq : seq_relation = seq0 in

  (* opt_hp restricts edges to those consistent with seq (as in your Coq code) *)
  let hp' : hb_relation = opt_hp hp seq in

  (* uniq_ops + scc_partition gives list(list myOp) = partition blocks *)
  let blocks : myOp list list =
    scc_partition myOp_eqb hp' (uniq_ops myOp_eqb ops)
  in

  List.iteri
    (fun i block ->
       Printf.printf "Block %d:\n%!" i;
       pp_myOp_list block)
    blocks

(* Also print the flattened schedule returned by auto_parallelize_alg3 *)
let show_alg3_flat (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3] Flattened grouped schedule for %s\n%!" pname;

  let hp : hb_relation = gen_hp ops in
  let seq : seq_relation = seq0 in
  let procs : process list = auto_parallelize_alg3 myOp_eqb ops hp seq in

  List.iter (fun pr -> Printf.printf "  %s\n%!" (pp_process pr)) procs

(* ---------- Shared compiler settings ---------- *)

let seq0 : seq_relation = fun (_:myOp) -> 0
let moQ0 : qubit_mem_assign = fun (_:var) -> 0
let moO_const (k:int) : op_mem_assign = fun (_:myOp) -> k

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

  (* -------- Algorithm 1: auto search tests -------- *)
  test_alg1 "P_1" p_1 3 3;
  test_alg1 "P_3" p_3 3 3;
  test_alg1 "P_4" p_4 3 3;
  test_alg1 "P_5" p_5 3 3;
  test_alg1 "P_6" p_6 3 3;

  (* -------- Algorithm 1: Shor auto search -------- *)
  test_alg1 "Shor_Qprog" shor_Qprog 3 3;

  (* -------- Algorithm 3: SHOW PARTITIONS -------- *)
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
  show_alg3_flat   "Shor_Qprog" shor_Qprog












(*
open Autodisq_extract

(* ---------- Pretty printers (compact but informative) ---------- *)

let pp_aexp = function
  | BA x      -> Printf.sprintf "BA(%d)" x
  | Num n     -> Printf.sprintf "Num(%d)" n
  | APlus _   -> "APlus(...)"
  | AMult _   -> "AMult(...)"

(* ---  print bounds/ranges/loci so we can see measurement loci --- *)
let pp_bound = function
  | BNum n -> Printf.sprintf "BNum(%d)" n
  | _ -> "B(...)"

let pp_range ((q, lo), hi) =
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
  | CNew (q,n)     -> Printf.sprintf "CNew(%d,%d)" q n
  | CAppU (_l,e)   -> Printf.sprintf "CAppU(%s)" (pp_exp e)
  | CMeas (x,l)    -> Printf.sprintf "CMeas(%d,%s)" x (pp_locus l)  (* CHANGED *)

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
      Printf.printf "Memb %d:\n" id;
      List.iter (fun p -> Printf.printf "  %s\n" (pp_process p)) ps
  | LockMemb (id, _, ps) ->
      Printf.printf "LockMemb %d:\n" id;
      List.iter (fun p -> Printf.printf "  %s\n" (pp_process p)) ps

let pp_cfg (cfg:config) : unit =
  List.iter pp_memb cfg

(* ---------- Shared compiler settings ---------- *)

let seq0 : seq_relation = fun (_:myOp) -> 0
let moQ0 : qubit_mem_assign = fun (_:var) -> 0
let moO_const (k:int) : op_mem_assign = fun (_:myOp) -> k

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

  (* -------- Algorithm 1: auto search tests -------- *)
  test_alg1 "P_1" p_1 3 3;
  test_alg1 "P_3" p_3 3 3;
  test_alg1 "P_4" p_4 3 3;
  test_alg1 "P_5" p_5 3 3;
  test_alg1 "P_6" p_6 3 3;

  (* -------- Algorithm 1: Shor auto search -------- *)
  test_alg1 "Shor_Qprog" shor_Qprog 3 3

*)




















































  





(*
open Autodisq_extract

let () =
  Printexc.record_backtrace true

(* ============================================================ *)
(* Helpers                                                      *)
(* ============================================================ *)

let len = List.length

let safe_print_fit name (dp : distributed_prog) =
  Printf.printf "%s: dist_len=%d\n%!" name (len dp);
  ignore (fit dp);
  Printf.printf "%s: fit computed OK\n%!" name

let test_gen_hp name (r : op_list) =
  Printf.printf "\n== gen_hp on %s ==\n%!" name;
  let hp : hb_relation = gen_hp r in
  Printf.printf "hp computed OK (hb_relation)\n%!";
  match r with
  | a :: b :: _ ->
      Printf.printf "hp(a,b)=%b; hp(b,a)=%b\n%!" (hp a b) (hp b a)
  | _ ->
      Printf.printf "program too short to probe hp\n%!"

(* ============================================================ *)
(* Printers                                                     *)
(* ============================================================ *)

let rec pp_aexp = function
  | BA x -> Printf.sprintf "BA(%d)" x
  | Num n -> Printf.sprintf "Num(%d)" n
  | APlus (a,b) -> Printf.sprintf "APlus(%s,%s)" (pp_aexp a) (pp_aexp b)
  | AMult (a,b) -> Printf.sprintf "AMult(%s,%s)" (pp_aexp a) (pp_aexp b)

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

let pp_myOp = function
  | OpAP a -> Printf.sprintf "OpAP(%s)" (pp_cexp a)
  | OpDP d -> Printf.sprintf "OpDP(%s)" (pp_cdexp d)
  | OpIf (_b, p, q) ->
      Printf.sprintf "OpIf(...,%s,%s)" (pp_process p) (pp_process q)

let pp_myOp_list (xs : myOp list) : unit =
  List.iter (fun o -> Printf.printf "  %s\n%!" (pp_myOp o)) xs

(* ============================================================ *)
(* Shared settings                                               *)
(* ============================================================ *)

let seq0 : seq_relation = fun (_:myOp) -> 0
let moQ0 : qubit_mem_assign = fun (_:var) -> 0
let moO_const (k:int) : op_mem_assign = fun (_:myOp) -> k

let cfg2 : config = [Memb (0, []); Memb (1, [])]

let show (title:string) (prog:distributed_prog) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "%s\n%!" title;
  Printf.printf "Cost = %d\n%!" (fit prog);
  pp_cfg prog

let cfg_of_processes (id:int) (ps:process list) : config =
  [Memb (id, ps)]

let show_ps (title:string) (ps:process list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "%s\n%!" title;
  Printf.printf "Processes = %d\n%!" (List.length ps);
  pp_cfg (cfg_of_processes 0 ps)
(* ============================================================ *)
(* Alg3 partition visualization                                  *)
(* ============================================================ *)

let hp_opt (hp : hb_relation) (seq : seq_relation) : hb_relation =
  opt_hp hp seq

let show_alg3_blocks (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3] SCC partitions for %s\n%!" pname;
  let hp  : hb_relation  = gen_hp ops in
  let hp' : hb_relation  = hp_opt hp seq0 in
  let blocks : myOp list list =
    scc_partition myOp_eqb hp' (uniq_ops myOp_eqb ops)
  in
  List.iteri
    (fun i block ->
      Printf.printf "Block %d:\n%!" i;
      pp_myOp_list block)
    blocks

let show_alg3_layers_blocks (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3-Layers] Ready-layer partitions for %s\n%!" pname;
  let hp  : hb_relation  = gen_hp ops in
  let hp' : hb_relation  = hp_opt hp seq0 in
  let layers : myOp list list =
    layer_partition myOp_eqb hp' (uniq_ops myOp_eqb ops)
  in
  List.iteri
    (fun i layer ->
      Printf.printf "Layer %d:\n%!" i;
      pp_myOp_list layer)
    layers

(* ============================================================ *)
(* Tests                                                        *)
(* ============================================================ *)

let test_alg2_paper (pname:string) (p:op_list) (mem:int) : unit =
  let prog = gen_prog_paper seq0 moQ0 (moO_const mem) p in
  show (Printf.sprintf "[Alg2/paper] %s on mem%d" pname mem) prog

(* IMPORTANT FIX: gen_prog_alg2 does NOT take kseq/kmem in your extraction *)
let test_alg2_wrapper (pname:string) (p:op_list) (mem:int) : unit =
  ignore (gen_prog_alg2 p moQ0 (moO_const mem));
  Printf.printf "[Alg2] %s gen_prog_alg2 ran OK (returns config)\n%!" pname

(* =================== CORRECTED PART =================== *)
(* Extracted signature:
     gen_prog_loop_alg2 : op_list -> qubit_mem_assign -> op_mem_assign
                        -> config -> int -> config
   So it only takes 5 args. *)
let test_alg2_loop_core (pname:string) (p:op_list) (_kseq:int) (kmem:int) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg2-core] gen_prog_loop_alg2 for %s\n%!" pname;
  let prog : distributed_prog =
    gen_prog_loop_alg2 p moQ0 (moO_const kmem) cfg2 0
  in
  show (Printf.sprintf "[Alg2-core] %s gen_prog_loop_alg2(mem=%d)" pname kmem) prog
(* ================= END CORRECTED PART ================= *)

let test_alg1 (pname:string) (p:op_list) (kseq:int) (kmem:int) : unit =
  let prog = auto_disq_alg1_paper kseq kmem p cfg2 in
  show (Printf.sprintf "[Alg1] %s auto_disq_alg1_paper(kseq=%d,kmem=%d) on cfg2"
          pname kseq kmem) prog

let test_alg3 (pname:string) (ops:op_list) : unit =
  let hp : hb_relation = gen_hp ops in
  let hp' : hb_relation = opt_hp hp seq0 in
  let ps : process list = auto_parallelize_alg3 myOp_eqb ops hp' seq0 in
  show_ps (Printf.sprintf "[Alg3] %s auto_parallelize_alg3" pname) ps

let test_alg3_layers (pname:string) (ops:op_list) : unit =
  let hp : hb_relation = gen_hp ops in
  let hp' : hb_relation = opt_hp hp seq0 in
  let ps : process list = auto_parallelize_alg3_layers myOp_eqb ops hp' seq0 in
  show_ps (Printf.sprintf "[Alg3-Layers] %s auto_parallelize_alg3_layers" pname) ps

(* ============================================================ *)
(* Main                                                         *)
(* ============================================================ *)

let () =
  Printf.printf "\n==== TEST SUITE START ====\n%!";

  (* hp sanity check *)
  test_gen_hp "GHZ32" gHZ32_prog;

  (* Alg2: paper placement *)
  test_alg2_paper "GHZ32" gHZ32_prog 0;
  test_alg2_paper "GHZ32" gHZ32_prog 5;

  (* Alg1: search *)
  test_alg1 "GHZ32" gHZ32_prog 3 3;

  (* Alg2: wrapper (extracted signature) *)
  test_alg2_wrapper "GHZ32" gHZ32_prog 0;
  test_alg2_wrapper "GHZ32" gHZ32_prog 5;

  (* Alg2 core loop (corrected call) *)
  test_alg2_loop_core "GHZ32" gHZ32_prog 3 3;

  (* Alg3 schedules *)
  test_alg3        "GHZ32" gHZ32_prog;
  test_alg3_layers "GHZ32" gHZ32_prog;

  (* Alg3 partitions *)
  show_alg3_blocks        "GHZ32" gHZ32_prog;
  show_alg3_layers_blocks "GHZ32" gHZ32_prog;

  Printf.printf "\n==== ALL DONE ====\n%!"

*)
























(*
open Autodisq_extract

(* ============================================================ *)
(* Helpers                                                      *)
(* ============================================================ *)

let len = List.length

let safe_print_fit name (dp : distributed_prog) =
  Printf.printf "%s: dist_len=%d\n%!" name (len dp);
  ignore (fit dp);
  Printf.printf "%s: fit computed OK\n%!" name

let test_gen_hp name (r : op_list) =
  Printf.printf "\n== gen_hp on %s ==\n%!" name;
  let hp : hb_relation = gen_hp r in
  Printf.printf "hp computed OK (hb_relation)\n%!";
  match r with
  | a :: b :: _ ->
      Printf.printf "hp(a,b)=%b; hp(b,a)=%b\n%!" (hp a b) (hp b a)
  | _ ->
      Printf.printf "program too short to probe hp\n%!"

(* ============================================================ *)
(* Printers                                                     *)
(* ============================================================ *)

let rec pp_aexp = function
  | BA x -> Printf.sprintf "BA(%d)" x
  | Num n -> Printf.sprintf "Num(%d)" n
  | APlus (a,b) -> Printf.sprintf "APlus(%s,%s)" (pp_aexp a) (pp_aexp b)
  | AMult (a,b) -> Printf.sprintf "AMult(%s,%s)" (pp_aexp a) (pp_aexp b)

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

let pp_myOp = function
  | OpAP a -> Printf.sprintf "OpAP(%s)" (pp_cexp a)
  | OpDP d -> Printf.sprintf "OpDP(%s)" (pp_cdexp d)
  | OpIf (_b, p, q) ->
      Printf.sprintf "OpIf(...,%s,%s)" (pp_process p) (pp_process q)

let pp_myOp_list (xs : myOp list) : unit =
  List.iter (fun o -> Printf.printf "  %s\n%!" (pp_myOp o)) xs

(* ============================================================ *)
(* Shared settings                                               *)
(* ============================================================ *)

let seq0 : seq_relation = fun (_:myOp) -> 0
let moQ0 : qubit_mem_assign = fun (_:var) -> 0
let moO_const (k:int) : op_mem_assign = fun (_:myOp) -> k

let cfg2 : config = [Memb (0, []); Memb (1, [])]

let show (title:string) (prog:distributed_prog) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "%s\n%!" title;
  Printf.printf "Cost = %d\n%!" (fit prog);
  pp_cfg prog

(* ============================================================ *)
(* Alg3 partition visualization                                  *)
(* ============================================================ *)

let hp_opt (hp : hb_relation) (seq : seq_relation) : hb_relation =
  opt_hp hp seq

let show_alg3_blocks (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3] SCC partitions for %s\n%!" pname;
  let hp  : hb_relation  = gen_hp ops in
  let hp' : hb_relation  = hp_opt hp seq0 in
  let blocks : myOp list list =
    scc_partition myOp_eqb hp' (uniq_ops myOp_eqb ops)
  in
  List.iteri
    (fun i block ->
      Printf.printf "Block %d:\n%!" i;
      pp_myOp_list block)
    blocks

let show_alg3_layers_blocks (pname:string) (ops:op_list) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg3-Layers] Ready-layer partitions for %s\n%!" pname;
  let hp  : hb_relation  = gen_hp ops in
  let hp' : hb_relation  = hp_opt hp seq0 in
  let layers : myOp list list =
    layer_partition myOp_eqb hp' (uniq_ops myOp_eqb ops)
  in
  List.iteri
    (fun i layer ->
      Printf.printf "Layer %d:\n%!" i;
      pp_myOp_list layer)
    layers

(* ============================================================ *)
(* Tests                                                        *)
(* ============================================================ *)

let test_alg2_paper (pname:string) (p:op_list) (mem:int) : unit =
  let prog = gen_prog_paper seq0 moQ0 (moO_const mem) p in
  show (Printf.sprintf "[Alg2/paper] %s on mem%d" pname mem) prog

(* IMPORTANT FIX: gen_prog_alg2 does NOT take kseq/kmem in your extraction *)
let test_alg2_wrapper (pname:string) (p:op_list) (mem:int) : unit =
  ignore (gen_prog_alg2 p moQ0 (moO_const mem));
  Printf.printf "[Alg2] %s gen_prog_alg2 ran OK (returns config)\n%!" pname

let test_alg2_loop_core (pname:string) (p:op_list) (kseq:int) (kmem:int) : unit =
  Printf.printf "\n==============================\n%!";
  Printf.printf "[Alg2-core] gen_prog_loop_alg2 for %s\n%!" pname;
  let hp  = gen_hp p in
  let os  = gen_os p in
  let all = mk_cases kseq kmem in
  let prog =
    gen_prog_loop_alg2
      kseq
      hp os cfg2 all
      [] ([] : config) INF_SCORE (List.length all)
  in
  show (Printf.sprintf "[Alg2-core] %s gen_prog_loop_alg2(kseq=%d,kmem=%d)"
          pname kseq kmem) prog

let test_alg1 (pname:string) (p:op_list) (kseq:int) (kmem:int) : unit =
  let prog = auto_disq_alg1_paper kseq kmem p cfg2 in
  show (Printf.sprintf "[Alg1] %s auto_disq_alg1_paper(kseq=%d,kmem=%d) on cfg2"
          pname kseq kmem) prog

let test_alg3 (pname:string) (p:op_list) (kseq:int) (kmem:int) : unit =
  let prog = auto_parallelize_alg3 myOp_eqb kseq kmem p cfg2 in
  show (Printf.sprintf "[Alg3] %s auto_parallelize_alg3(kseq=%d,kmem=%d) on cfg2"
          pname kseq kmem) prog

let test_alg3_layers (pname:string) (p:op_list) (kseq:int) (kmem:int) : unit =
  let prog = auto_parallelize_alg3_layers myOp_eqb kseq kmem p cfg2 in
  show (Printf.sprintf "[Alg3-Layers] %s auto_parallelize_alg3_layers(kseq=%d,kmem=%d) on cfg2"
          pname kseq kmem) prog




(* ============================================================ *)
(* Main                                                         *)
(* ============================================================ *)

let () =
  Printf.printf "\n==== TEST SUITE START ====\n%!";

  (* hp sanity check *)
  test_gen_hp "GHZ32" gHZ32_prog;

  (* Alg2: paper placement *)
  test_alg2_paper "GHZ32" gHZ32_prog 0;
  test_alg2_paper "GHZ32" gHZ32_prog 5;

  (* Alg1: search *)
  test_alg1 "GHZ32" gHZ32_prog 3 3;

  (* Alg2: wrapper (extracted signature) *)
  test_alg2_wrapper "GHZ32" gHZ32_prog 0;
  test_alg2_wrapper "GHZ32" gHZ32_prog 5;

  (* Alg2 core loop (still uses mk_cases kseq kmem) *)
  test_alg2_loop_core "GHZ32" gHZ32_prog 3 3;

  (* Alg3 schedules *)
  test_alg3        "GHZ32" gHZ32_prog;
  test_alg3_layers "GHZ32" gHZ32_prog;

  (* Alg3 partitions *)
  show_alg3_blocks        "GHZ32" gHZ32_prog;
  show_alg3_layers_blocks "GHZ32" gHZ32_prog;

  Printf.printf "\n==== ALL DONE ====\n%!"
  
  *)

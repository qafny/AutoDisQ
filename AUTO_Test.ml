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






















































  

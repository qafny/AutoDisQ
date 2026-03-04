(* AUTO_Test.ml *)
open Autodisq_extract

(* ============================================================ *)
(* Pretty printers (minimal, but enough for debugging)           *)
(* ============================================================ *)

let pp_int (n:int) = string_of_int n

let pp_var (v:var) = string_of_int v

let rec pp_aexp = function
  | BA x -> "BA(" ^ pp_var x ^ ")"
  | Num n -> "Num(" ^ pp_int n ^ ")"
  | APlus (a,b) -> "APlus(" ^ pp_aexp a ^ "," ^ pp_aexp b ^ ")"
  | AMult (a,b) -> "AMult(" ^ pp_aexp a ^ "," ^ pp_aexp b ^ ")"

let pp_cbexp = function
  | CEq (a,b) -> "CEq(" ^ pp_aexp a ^ "," ^ pp_aexp b ^ ")"
  | CLt (a,b) -> "CLt(" ^ pp_aexp a ^ "," ^ pp_aexp b ^ ")"

let rec pp_exp = function
  | SKIP (q,a) -> "SKIP(" ^ pp_var q ^ "," ^ pp_aexp a ^ ")"
  | X (q,a) -> "X(" ^ pp_var q ^ "," ^ pp_aexp a ^ ")"
  | H (q,a) -> "H(" ^ pp_var q ^ "," ^ pp_aexp a ^ ")"
  | CU (c,a,e) -> "CU(" ^ pp_var c ^ "," ^ pp_aexp a ^ "," ^ pp_exp e ^ ")"
  | RZ (k,q,a) -> "RZ(" ^ pp_int k ^ "," ^ pp_var q ^ "," ^ pp_aexp a ^ ")"
  | RRZ (k,q,a) -> "RRZ(" ^ pp_int k ^ "," ^ pp_var q ^ "," ^ pp_aexp a ^ ")"
  | SR (k,q) -> "SR(" ^ pp_int k ^ "," ^ pp_var q ^ ")"
  | SRR (k,q) -> "SRR(" ^ pp_int k ^ "," ^ pp_var q ^ ")"
  | QFT (q,n) -> "QFT(" ^ pp_var q ^ "," ^ pp_int n ^ ")"
  | RQFT (q,n) -> "RQFT(" ^ pp_var q ^ "," ^ pp_int n ^ ")"
  | Addto (x,y) -> "Addto(" ^ pp_var x ^ "," ^ pp_var y ^ ")"
  | Seq (e1,e2) -> "Seq(" ^ pp_exp e1 ^ "," ^ pp_exp e2 ^ ")"

(* locus = range list, but in your tests you mostly use [].
   We'll still print it structurally. *)
let pp_bound = function
  | BVar (v,k) -> "BVar(" ^ pp_var v ^ "," ^ pp_int k ^ ")"
  | BNum n -> "BNum(" ^ pp_int n ^ ")"

let pp_range (((v,b1),b2) : range) =
  "((" ^ pp_var v ^ "," ^ pp_bound b1 ^ ")," ^ pp_bound b2 ^ ")"

let pp_locus (l:locus) =
  "[" ^ String.concat "; " (List.map pp_range l) ^ "]"

let pp_cexp = function
  | CNew (q,n) -> "CNew(" ^ pp_var q ^ "," ^ pp_int n ^ ")"
  | CMeas (x,l) -> "CMeas(" ^ pp_var x ^ "," ^ pp_locus l ^ ")"
  | CAppU (l,e) -> "CAppU(" ^ pp_locus l ^ "," ^ pp_exp e ^ ")"

let pp_cdexp = function
  | NewCh (x,n) -> "NewCh(" ^ pp_var x ^ "," ^ pp_int n ^ ")"
  | Send (x,a) -> "Send(" ^ pp_var x ^ "," ^ pp_aexp a ^ ")"
  | Recv (x,y) -> "Recv(" ^ pp_var x ^ "," ^ pp_var y ^ ")"

let rec pp_process = function
  | PNil -> "PNil"
  | AP (a,p) -> "AP(" ^ pp_cexp a ^ "," ^ pp_process p ^ ")"
  | DP (d,p) -> "DP(" ^ pp_cdexp d ^ "," ^ pp_process p ^ ")"
  | PIf (b,p,q) -> "PIf(" ^ pp_cbexp b ^ "," ^ pp_process p ^ "," ^ pp_process q ^ ")"

let pp_memb = function
  | Memb (mid, ps) ->
      "Memb(" ^ pp_var mid ^ ",[" ^ String.concat "; " (List.map pp_process ps) ^ "])"
  | LockMemb (mid, lk, ps) ->
      "LockMemb(" ^ pp_var mid ^ "," ^ pp_process lk ^ ",[" ^
      String.concat "; " (List.map pp_process ps) ^ "])"

let pp_config (cfg:config) =
  "[" ^ String.concat "; " (List.map pp_memb cfg) ^ "]"

let pp_smap (s:smap) =
  "[" ^ String.concat "; "
        (List.map (fun (v,mid) -> "(" ^ pp_var v ^ "," ^ pp_var mid ^ ")") s)
  ^ "]"

(* ============================================================ *)
(* Same helper functions as in Coq                              *)
(* ============================================================ *)

let memb_procs (m:memb) : process list =
  match m with
  | Memb (_,ps) -> ps
  | LockMemb (_,_,ps) -> ps

let rec flatten_config (cfg:config) : process list =
  match cfg with
  | [] -> []
  | m :: tl -> memb_procs m @ flatten_config tl

let pp_process_list ps =
  "[" ^ String.concat "; " (List.map pp_process ps) ^ "]"

let rec flat_cfg (cfg:config) : process list =
  match cfg with
  | [] -> []
  | Memb (_,ps) :: tl -> ps @ flat_cfg tl
  | LockMemb (_,_,ps) :: tl -> ps @ flat_cfg tl

(* ============================================================ *)
(* Your tests (translated 1-to-1)                               *)
(* ============================================================ *)

let () =
  Printf.printf "=============================\n";
  Printf.printf "AUTO_Test (extracted types)\n";
  Printf.printf "=============================\n%!"

(* cfg1 : [Memb 0 []; Memb 1 []] *)
let cfg1 : config = [Memb (0, []); Memb (1, [])]

let op1 : myOp = OpAP (CNew (0, 1))
let op2 : myOp = OpAP (CMeas (0, ([] : locus)))
let r1  : op_list = [op1; op2]

let p1 : distributed_prog = auto_disq_alg1_paper 2 2 r1 cfg1

let () =
  Printf.printf "P1 = %s\n%!" (pp_config p1);
  Printf.printf "fit(P1) = %d\n%!" (fit p1)

(* insert_send_recv tests *)
let cfg_test : config = [Memb (0, []); Memb (1, [])]
let s_empty : smap = []

let t1 = insert_send_recv cfg_test s_empty 1 0
let () =
  let (cfg_t1, k_t1) = t1 in
  Printf.printf "T1.cfg = %s\n%!" (pp_config cfg_t1);
  Printf.printf "T1.int = %d\n%!" k_t1

let s_one : smap = [ (0, 0) ]
let t2 = insert_send_recv cfg_test s_one 1 0
let () =
  let (cfg_t2, k_t2) = t2 in
  Printf.printf "T2.cfg = %s\n%!" (pp_config cfg_t2);
  Printf.printf "T2.int = %d\n%!" k_t2;
  Printf.printf "flatten_config (fst T2) = %s\n%!"
    (pp_process_list (flatten_config cfg_t2))

let s_two : smap = [ (0,0); (1,0) ]
let t3 = insert_send_recv cfg_test s_two 1 0
let () =
  let (cfg_t3, k_t3) = t3 in
  Printf.printf "T3.cfg = %s\n%!" (pp_config cfg_t3);
  Printf.printf "T3.int = %d\n%!" k_t3

(* gen_prog_loop_alg2 single op *)
let opAP1 : myOp = OpAP (CNew (0,1))

let moQ0 : var -> membrane_id = fun _ -> 0
let moO_to_1 : myOp -> membrane_id = fun _ -> 1

let tb =
  gen_prog_loop_alg2 ([opAP1] : myOp list) moQ0 moO_to_1 empty_config 0

let () =
  Printf.printf "TB = %s\n%!" (pp_config tb);
  Printf.printf "flatten_config TB = %s\n%!" (pp_process_list (flatten_config tb))

(* IF op *)
let cond0 : cbexp = CEq (BA 0, Num 0)

let p_then : process = AP (CNew (0,1), PNil)
let p_else : process = PNil

let opIF1 : myOp = OpIf (cond0, p_then, p_else)

let tc =
  gen_prog_loop_alg2 ([opIF1] : myOp list) moQ0 moO_to_1 empty_config 0

let () =
  Printf.printf "TC = %s\n%!" (pp_config tc);
  Printf.printf "flatten_config TC = %s\n%!" (pp_process_list (flatten_config tc))

(* gen_prog_alg2 for [CNew; CMeas] *)
let opAP2 : myOp = OpAP (CMeas (0, ([]:locus)))
let seq2 : myOp list = [opAP1; opAP2]

let td = gen_prog_alg2 seq2 moQ0 moO_to_1

let () =
  Printf.printf "TD = %s\n%!" (pp_config td);
  Printf.printf "flatten_config TD = %s\n%!" (pp_process_list (flatten_config td));
  Printf.printf "diff_mem moQ0 (locus_myOp opAP1) 1 = %s\n%!"
    (pp_smap (diff_mem moQ0 (locus_myOp opAP1) 1));
  Printf.printf "diff_mem (mem_up_smap ...) (locus_myOp opAP2) 1 = %s\n%!"
    (pp_smap
       (diff_mem
          (mem_up_smap moQ0 (diff_mem moQ0 (locus_myOp opAP1) 1) 1)
          (locus_myOp opAP2)
          1))

(* ============================================================ *)
(* Tests for Algorithm 1                                         *)
(* ============================================================ *)

let cfgA : config = [Memb (0, []); Memb (1, [])]

let aop1 : myOp = OpAP (CNew (0,1))
let aop2 : myOp = OpAP (CMeas (0, ([]:locus)))
let ar1  : op_list = [aop1; aop2]

let ap1 : distributed_prog = auto_disq_alg1_paper 2 2 ar1 cfgA

let () =
  Printf.printf "AP1 = %s\n%!" (pp_config ap1);
  Printf.printf "fit(AP1) = %d\n%!" (fit ap1)

let aop3 : myOp = OpAP (CNew (1,1))
let aop4 : myOp = OpDP (NewCh (7,1))
let ar2  : op_list = [aop1; aop3; aop4; aop2]

let ap2 : distributed_prog = auto_disq_alg1_paper 3 3 ar2 cfgA

let () =
  Printf.printf "AP2 = %s\n%!" (pp_config ap2);
  Printf.printf "fit(AP2) = %d\n%!" (fit ap2)

(* ============================================================ *)
(* Tests for Algorithm 2                                         *)
(* ============================================================ *)

let seq0 : seq_relation = fun _ -> 0

let moO_all0 : op_mem_assign = fun _ -> 0
let moQ_all0 : qubit_mem_assign = fun _ -> 0

let p2a : distributed_prog = gen_prog_paper seq0 moQ_all0 moO_all0 ar1

let () =
  Printf.printf "P2A = %s\n%!" (pp_config p2a);
  Printf.printf "fit(P2A) = %d\n%!" (fit p2a)

let moO_all1 : op_mem_assign = fun _ -> 1
let moQ_all0_again : qubit_mem_assign = fun _ -> 0

let p2b : distributed_prog = gen_prog_paper seq0 moQ_all0_again moO_all1 ar1

let () =
  Printf.printf "P2B = %s\n%!" (pp_config p2b);
  Printf.printf "fit(P2B) = %d\n%!" (fit p2b);
  Printf.printf "flat_cfg P2A = %s\n%!" (pp_process_list (flat_cfg p2a));
  Printf.printf "flat_cfg P2B = %s\n%!" (pp_process_list (flat_cfg p2b))

(* ============================================================ *)
(* Tests for Algorithm 3                                         *)
(* ============================================================ *)

let b1 : myOp = OpAP (CNew (0,1))
let b2 : myOp = OpAP (CMeas (0, ([]:locus)))
let b3 : myOp = OpAP (CNew (1,1))

let bops : myOp list = [b1; b2; b3]

(* hpB: cycle b1<->b2 and b2->b3 *)
let hpB : hb_relation =
  fun a b ->
    ( (myOp_eqb a b1 && myOp_eqb b b2)
      || (myOp_eqb a b2 && myOp_eqb b b1)
      || (myOp_eqb a b2 && myOp_eqb b b3) )

let seqB : seq_relation =
  fun o ->
    if myOp_eqb o b1 then 0
    else if myOp_eqb o b2 then 1
    else 2

let rpar : process list = auto_parallelize_alg3 myOp_eqb bops hpB seqB

let () =
  Printf.printf "Rpar = %s\n%!" (pp_process_list rpar);
  Printf.printf "=============================\nDONE\n=============================\n%!"






(*

rm -f *.cmi *.cmo run_autodisq
ocamlc -c autodisq_extract.mli
ocamlc -c autodisq_extract.ml
ocamlc -c AUTO_Test.ml
ocamlc -o run_autodisq autodisq_extract.cmo AUTO_Test.cmo
./run_autodisq


*)






















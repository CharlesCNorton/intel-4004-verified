(* Cross-validation vector dumper.

   Emits, as CSV on stdout, the extracted machine-checked model's outputs
   over vector sets covering the ALU, JCN and ISZ program-counter semantics,
   JUN/JMS/JIN/FIN targets, subroutine stack discipline, RAM main and status
   round trips, instruction timing, and the full first-byte decode table.
   crossval/pyntel_crossval.py replays these on the third-party Pyntel4004
   emulator; the same dump doubles as a bench vector set for eventual
   silicon validation. *)

open Intel4004_model

let pr = Printf.printf

(* ---- canonical string tag for an extracted instruction (as in driver.ml) ---- *)
let tag = function
  | NOP -> "NOP" | JCN (c,a) -> Printf.sprintf "JCN %d %d" c a
  | FIM (r,d) -> Printf.sprintf "FIM %d %d" r d | SRC r -> Printf.sprintf "SRC %d" r
  | FIN r -> Printf.sprintf "FIN %d" r | JIN r -> Printf.sprintf "JIN %d" r
  | JUN a -> Printf.sprintf "JUN %d" a | JMS a -> Printf.sprintf "JMS %d" a
  | INC r -> Printf.sprintf "INC %d" r | ISZ (r,a) -> Printf.sprintf "ISZ %d %d" r a
  | ADD r -> Printf.sprintf "ADD %d" r | SUB r -> Printf.sprintf "SUB %d" r
  | LD r -> Printf.sprintf "LD %d" r | XCH r -> Printf.sprintf "XCH %d" r
  | BBL d -> Printf.sprintf "BBL %d" d | LDM d -> Printf.sprintf "LDM %d" d
  | WRM->"WRM"|WMP->"WMP"|WRR->"WRR"|WPM->"WPM"|WR0->"WR0"|WR1->"WR1"|WR2->"WR2"|WR3->"WR3"
  | SBM->"SBM"|RDM->"RDM"|RDR->"RDR"|ADM->"ADM"|RD0->"RD0"|RD1->"RD1"|RD2->"RD2"|RD3->"RD3"
  | CLB->"CLB"|CLC->"CLC"|IAC->"IAC"|CMC->"CMC"|CMA->"CMA"|RAL->"RAL"|RAR->"RAR"|TCC->"TCC"
  | DAC->"DAC"|TCS->"TCS"|STC->"STC"|DAA->"DAA"|KBP->"KBP"|DCL->"DCL"

let zero_regs = List.init 16 (fun _ -> 0)
let zero_rom = List.init 4096 (fun _ -> 0)
let exec_list prog s = List.fold_left execute s prog
let b2i b = if b then 1 else 0

(* ---- ALU: alu,name,acc,cy,reg,macc,mcy ---- *)
let alu_ops = ["ADD";"SUB";"IAC";"DAC";"DAA";"CMA";"RAL";"RAR";
               "TCC";"TCS";"CLB";"CLC";"STC";"CMC";"KBP";"LD";"XCH";"LDM"]

let instr_of name reg = match name with
  | "ADD"->ADD 0 | "SUB"->SUB 0 | "IAC"->IAC | "DAC"->DAC | "DAA"->DAA
  | "CMA"->CMA | "RAL"->RAL | "RAR"->RAR | "TCC"->TCC | "TCS"->TCS
  | "CLB"->CLB | "CLC"->CLC | "STC"->STC | "CMC"->CMC | "KBP"->KBP
  | "LD"->LD 0 | "XCH"->XCH 0 | "LDM"->LDM reg | _ -> failwith name

let dump_alu () =
  List.iter (fun name ->
    for a = 0 to 15 do
      List.iter (fun c ->
        for reg = 0 to 15 do
          let st = test_state a c (List.init 16 (fun _ -> reg)) in
          let st' = execute st (instr_of name reg) in
          pr "alu,%s,%d,%d,%d,%d,%d\n" name a (b2i c) reg (aval st') (b2i (carry st'))
        done) [false; true]
    done) alu_ops

(* ---- JCN: jcn,cond,acc,cy,tp,pc,off,mpc ---- *)
let dump_jcn () =
  List.iter (fun p ->
    for c = 0 to 15 do
      List.iter (fun a ->
        List.iter (fun cy ->
          List.iter (fun tp ->
            List.iter (fun off ->
              let s = mk_state a cy zero_regs p tp zero_rom in
              let s' = execute s (JCN (c, off)) in
              pr "jcn,%d,%d,%d,%d,%d,%d,%d\n" c a (b2i cy) (b2i tp) p off (pcv s'))
              [0; 128; 255]) [false; true]) [false; true]) [0; 1; 15]
    done) [0; 253; 254; 255; 511; 2046; 4094; 4095]

(* ---- ISZ: isz,v,pc,off,mpc,mreg ---- *)
let dump_isz () =
  List.iter (fun p ->
    for v = 0 to 15 do
      List.iter (fun off ->
        let regs = List.init 16 (fun i -> if i = 3 then v else 0) in
        let s = mk_state 0 false regs p false zero_rom in
        let s' = execute s (ISZ (3, off)) in
        pr "isz,%d,%d,%d,%d,%d\n" v p off (pcv s') (rval s' 3))
        [0; 255]
    done) [0; 254; 255; 4094; 4095]

(* ---- JUN/JMS: jun,pc,addr,mpc ; jms,pc,addr,mpc,mret ---- *)
let dump_jump () =
  List.iter (fun p ->
    List.iter (fun a ->
      let s = mk_state 0 false zero_regs p false zero_rom in
      let s1 = execute s (JUN a) in
      let s2 = execute s (JMS a) in
      let ret = stkv1 s2 in
      pr "jun,%d,%d,%d\n" p a (pcv s1);
      pr "jms,%d,%d,%d,%d\n" p a (pcv s2) ret)
      [0; 255; 256; 2047; 4095])
    [0; 254; 255; 2046; 4094; 4095]

(* ---- JIN: jin,pc,pair,mpc ; FIN: fin,pc,pair,mr4,mr5,mpc ---- *)
let dump_jin_fin () =
  let romarr = Array.init 4096 (fun i -> (i * 7 + 3) mod 256) in
  let romlist = Array.to_list romarr in
  List.iter (fun p ->
    List.iter (fun pv ->
      let regs = List.init 16
        (fun i -> if i = 2 then pv / 16 else if i = 3 then pv mod 16 else 0) in
      let s = mk_state 0 false regs p false zero_rom in
      let s' = execute s (JIN 3) in
      pr "jin,%d,%d,%d\n" p pv (pcv s');
      let regs0 = List.init 16
        (fun i -> if i = 0 then pv / 16 else if i = 1 then pv mod 16 else 0) in
      let sf = mk_state 0 false regs0 p false romlist in
      let sf' = execute sf (FIN 4) in
      pr "fin,%d,%d,%d,%d,%d\n" p pv (rval sf' 4) (rval sf' 5) (pcv sf'))
      [0; 37; 128; 255])
    [0; 254; 255; 511; 4094; 4095]

(* ---- stack: stack,scenario,op,arg,depth_before,mpc (one line per op) ---- *)
(* The machine's address ring has no depth flag; the dumper tracks the
   observable depth (capped at 3) so the adjudicator can classify
   underflow rows. *)
let dump_stack () =
  List.iteri (fun si addrs ->
    let s = ref (mk_state 0 false zero_regs 0 false zero_rom) in
    let depth = ref 0 in
    List.iter (fun a ->
      let d0 = !depth in
      s := execute !s (JMS a);
      depth := min 3 (!depth + 1);
      pr "stack,%d,jms,%d,%d,%d\n" si a d0 (pcv !s)) addrs;
    for d = 1 to 3 do
      let d0 = !depth in
      s := execute !s (BBL d);
      depth := max 0 (!depth - 1);
      pr "stack,%d,bbl,%d,%d,%d\n" si d d0 (pcv !s)
    done)
    [ [100; 500; 1000; 2000]; [4094; 1; 4095; 256]; [7; 7; 7; 7]; [10; 20] ]

(* ---- RAM: rammain,bankcode,src,v,macc ; ramstat,bankcode,src,macc ---- *)
let bank_codes = [| 0; 1; 2; 4 |]

let dump_ram () =
  for bi = 0 to 3 do
    List.iter (fun srcv ->
      List.iter (fun v ->
        let s0 = mk_state 0 false zero_regs 0 false zero_rom in
        let s1 = exec_list [LDM bank_codes.(bi); DCL; FIM (0, srcv); SRC 1;
                            LDM v; WRM;
                            LDM 0; FIM (0, srcv); SRC 1; RDM] s0 in
        pr "rammain,%d,%d,%d,%d\n" bank_codes.(bi) srcv v (aval s1))
        [3; 9])
      [0; 17; 100; 255]
  done;
  for bi = 0 to 3 do
    List.iter (fun srcv ->
      let s0 = mk_state 0 false zero_regs 0 false zero_rom in
      let s1 = exec_list [LDM bank_codes.(bi); DCL; FIM (0, srcv); SRC 1;
                          LDM 11; WR0;
                          LDM 0; FIM (0, srcv); SRC 1; RD0] s0 in
      pr "ramstat,%d,%d,%d\n" bank_codes.(bi) srcv (aval s1))
      [0; 16; 240]
  done

(* ---- timing: timing,tag,cycles ---- *)
let sample_instrs =
  [NOP; JCN (0,0); FIM (0,0); SRC 1; FIN 0; JIN 1; JUN 0; JMS 0; INC 0;
   ISZ (0,0); ADD 0; SUB 0; LD 0; XCH 0; BBL 0; LDM 0; WRM; WMP; WRR; WPM;
   WR0; WR1; WR2; WR3; SBM; RDM; RDR; ADM; RD0; RD1; RD2; RD3; CLB; CLC;
   IAC; CMC; CMA; RAL; RAR; TCC; DAC; TCS; STC; DAA; KBP; DCL]

let dump_timing () =
  List.iter (fun i -> pr "timing,%s,%d\n" (tag i) (cycles i)) sample_instrs

(* ---- decode: decode,b1,tag (second byte fixed at 0) ---- *)
let dump_decode () =
  for b1 = 0 to 255 do
    pr "decode,%d,%s\n" b1 (tag (decode b1 0))
  done

let () =
  dump_alu (); dump_jcn (); dump_isz (); dump_jump (); dump_jin_fin ();
  dump_stack (); dump_ram (); dump_timing (); dump_decode ()

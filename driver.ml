(* Differential test harness.

   Left side  : the extracted, machine-checked model (intel4004_model.ml).
   Right side : an independent reference implemented here from the MCS-4 data
                sheet, in a different style, as the cross-checking oracle.

   The ISA decode is checked exhaustively over all 65536 byte pairs; the ALU
   and flags exhaustively over all accumulator/carry/register inputs; DAA
   additionally against decimal (mod-10 / div-10) arithmetic; branch and jump
   program-counter semantics exhaustively over all 4096 program-counter
   values and all sixteen JCN condition codes (covering page-boundary and
   12-bit wraparound cases); FIN against
   the page-of-next-instruction fetch rule; the subroutine address ring
   against a four-row rotating reference, including the overflow discard and
   the stale-row underflow; RAM main and status memory over the full
   bank/chip/register/character address space under two independent value
   patterns (so address aliasing cannot pass); the multi-line DCL codes
   against their data-sheet bank sets; memory-operand arithmetic against the
   ALU reference; and the timing against the data-sheet machine-cycle rule.
   Any disagreement is a finding. *)

open Intel4004_model

let fails = ref 0
let checks = ref 0
let report name = if !fails = 0 then Printf.printf "  PASS  %-36s (%d checks)\n" name !checks
                  else Printf.printf "  FAIL  %-36s (%d checks, %d mismatches)\n" name !checks !fails
let section name = fails := 0; checks := 0; ignore name

(* ---- canonical string tag for an extracted instruction ---- *)
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

(* ---- independent reference decoder (data-sheet opcode table) ---- *)
let ref_decode b1 b2 =
  let op = b1 / 16 and d = b1 mod 16 in
  match op with
  | 0 -> "NOP"
  | 1 -> Printf.sprintf "JCN %d %d" d b2
  | 2 -> if d mod 2 = 0 then Printf.sprintf "FIM %d %d" d b2 else Printf.sprintf "SRC %d" d
  | 3 -> if d mod 2 = 0 then Printf.sprintf "FIN %d" d else Printf.sprintf "JIN %d" d
  | 4 -> Printf.sprintf "JUN %d" (((d*256)+b2) mod 4096)
  | 5 -> Printf.sprintf "JMS %d" (((d*256)+b2) mod 4096)
  | 6 -> Printf.sprintf "INC %d" d
  | 7 -> Printf.sprintf "ISZ %d %d" d b2
  | 8 -> Printf.sprintf "ADD %d" d
  | 9 -> Printf.sprintf "SUB %d" d
  | 10 -> Printf.sprintf "LD %d" d
  | 11 -> Printf.sprintf "XCH %d" d
  | 12 -> Printf.sprintf "BBL %d" d
  | 13 -> Printf.sprintf "LDM %d" d
  | 14 -> [|"WRM";"WMP";"WRR";"WPM";"WR0";"WR1";"WR2";"WR3";
            "SBM";"RDM";"RDR";"ADM";"RD0";"RD1";"RD2";"RD3"|].(d)
  | 15 -> if d <= 13 then
            [|"CLB";"CLC";"IAC";"CMC";"CMA";"RAL";"RAR";"TCC";
              "DAC";"TCS";"STC";"DAA";"KBP";"DCL"|].(d)
          else "NOP"
  | _ -> "NOP"

(* ---- independent reference ALU: (acc,carry,reg) -> (acc',carry') ---- *)
let ref_alu name acc carry reg =
  let b i = if i then 1 else 0 in
  match name with
  | "ADD" -> let s = acc + reg + b carry in (s mod 16, s >= 16)
  | "SUB" -> let s = acc + 16 - reg - b carry in (s mod 16, s >= 16)
  | "IAC" -> let s = acc + 1 in (s mod 16, s >= 16)
  | "DAC" -> ((acc + 15) mod 16, acc <> 0)
  | "DAA" -> let adj = carry || acc > 9 in
             let s = acc + (if adj then 6 else 0) in (s mod 16, s >= 16 || carry)
  | "CMA" -> ((15 - acc) mod 16, carry)
  | "RAL" -> ((acc*2 + b carry) mod 16, acc >= 8)
  | "RAR" -> ((acc/2 + (if carry then 8 else 0)) mod 16, acc mod 2 = 1)
  | "TCC" -> (b carry, false)
  | "TCS" -> ((if carry then 10 else 9), false)
  | "CLB" -> (0, false)
  | "CLC" -> (acc, false)
  | "STC" -> (acc, true)
  | "CMC" -> (acc, not carry)
  | "KBP" -> ((match acc with 0->0|1->1|2->2|4->3|8->4|_->15), carry)
  | "LD"  -> (reg, carry)
  | "XCH" -> (reg, carry)
  | "LDM" -> (reg, carry)
  | _ -> failwith ("no ref for " ^ name)

(* build the extracted instruction for an op, using register 0 / immediate reg *)
let instr_of name reg = match name with
  | "ADD"->ADD 0 | "SUB"->SUB 0 | "IAC"->IAC | "DAC"->DAC | "DAA"->DAA
  | "CMA"->CMA | "RAL"->RAL | "RAR"->RAR | "TCC"->TCC | "TCS"->TCS
  | "CLB"->CLB | "CLC"->CLC | "STC"->STC | "CMC"->CMC | "KBP"->KBP
  | "LD"->LD 0 | "XCH"->XCH 0 | "LDM"->LDM reg | _ -> failwith name

(* ---- independent reference timing (data-sheet machine-cycle rule) ---- *)
let ref_cycles = function
  | FIM _ | FIN _ | JUN _ | JMS _ | JCN _ | ISZ _ -> 16
  | _ -> 8

(* ---- helpers for the machine-level suites ---- *)
let zero_regs = List.init 16 (fun _ -> 0)
let zero_rom = List.init 4096 (fun _ -> 0)
let exec_list prog s = List.fold_left execute s prog

(* ---- independent PC references (data-sheet addressing rules) ---- *)
let ref_next p len = (p + len) mod 4096
(* conditional branches land in the page of the next sequential instruction *)
let ref_page_target p len off = (ref_next p len) / 256 * 256 + off
let ref_jcn_cond c a cy tp =
  let c1 = c / 8 and c2 = c / 4 mod 2 and c3 = c / 2 mod 2 and c4 = c mod 2 in
  let base = (a = 0 && c2 = 1) || (cy && c3 = 1) || ((not tp) && c4 = 1) in
  if c1 = 1 then not base else base

(* =================== Test 1: decode, exhaustive =================== *)
let test_decode () =
  section "decode";
  for b1 = 0 to 255 do
    for b2 = 0 to 255 do
      incr checks;
      let got = tag (decode b1 b2) and want = ref_decode b1 b2 in
      if got <> want then begin
        incr fails;
        if !fails <= 5 then
          Printf.printf "    decode %d %d -> model=%s ref=%s\n" b1 b2 got want
      end
    done
  done;
  report "decode (all 65536 pairs)"

(* =================== Test 2: ALU + flags, exhaustive =================== *)
let alu_ops = ["ADD";"SUB";"IAC";"DAC";"DAA";"CMA";"RAL";"RAR";
               "TCC";"TCS";"CLB";"CLC";"STC";"CMC";"KBP";"LD";"XCH";"LDM"]

let test_alu () =
  section "alu";
  List.iter (fun name ->
    for a = 0 to 15 do
      List.iter (fun c ->
        for reg = 0 to 15 do
          incr checks;
          let st = test_state a c (List.init 16 (fun _ -> reg)) in
          let st' = execute st (instr_of name reg) in
          let (ga, gc) = (aval st', carry st') in
          let (wa, wc) = ref_alu name a c reg in
          if ga <> wa || gc <> wc then begin
            incr fails;
            if !fails <= 5 then
              Printf.printf "    %s acc=%d carry=%b reg=%d -> model=(%d,%b) ref=(%d,%b)\n"
                name a c reg ga gc wa wc
          end
        done) [false;true]
    done) alu_ops;
  report "ALU + flags (exhaustive)"

(* ============ Test 3: DAA against decimal arithmetic ============ *)
let test_daa_decimal () =
  section "daa";
  for x = 0 to 9 do
    for y = 0 to 9 do
      for cin = 0 to 1 do
        incr checks;
        let raw = x + y + cin in
        let st = test_state (raw mod 16) (raw >= 16) (List.init 16 (fun _ -> 0)) in
        let st' = execute st DAA in
        let got_lo = aval st' and got_carry = if carry st' then 1 else 0 in
        if got_lo <> raw mod 10 || got_carry <> raw / 10 then begin
          incr fails;
          if !fails <= 5 then
            Printf.printf "    BCD %d+%d+%d=%d -> model=(%d,%d) decimal=(%d,%d)\n"
              x y cin raw got_lo got_carry (raw mod 10) (raw / 10)
        end
      done
    done
  done;
  report "DAA vs decimal (mod10/div10)"

(* =================== Test 4: INC increments the register =================== *)
let test_inc () =
  section "inc";
  for reg = 0 to 15 do
    incr checks;
    let st = test_state 0 false (List.init 16 (fun _ -> reg)) in
    let st' = execute st (INC 0) in
    let got = rval st' 0 and want = (reg + 1) mod 16 in
    if got <> want then begin
      incr fails;
      Printf.printf "    INC reg=%d -> model=%d ref=%d\n" reg got want
    end
  done;
  report "INC register"

(* ==== Test 5: JCN pc semantics, exhaustive over the pc and cond code ==== *)
let test_jcn () =
  section "jcn";
  let conds = List.init 16 (fun c -> c) in
  for p = 0 to 4095 do
    List.iter (fun c ->
      List.iter (fun off ->
        List.iter (fun a ->
          List.iter (fun cy ->
            List.iter (fun tp ->
              incr checks;
              let s = mk_state a cy zero_regs p tp zero_rom in
              let s' = execute s (JCN (c, off)) in
              let want = if ref_jcn_cond c a cy tp
                         then ref_page_target p 2 off
                         else ref_next p 2 in
              if pcv s' <> want then begin
                incr fails;
                if !fails <= 5 then
                  Printf.printf "    JCN c=%d off=%d pc=%d acc=%d cy=%b t=%b -> model=%d ref=%d\n"
                    c off p a cy tp (pcv s') want
              end) [false; true]) [false; true]) [0; 1; 15]) [0; 1; 128; 254; 255]) conds
  done;
  report "JCN pc semantics (4096 pcs x 16 conds)"

(* ========= Test 6: ISZ pc + register, exhaustive over the pc ========= *)
let test_isz () =
  section "isz";
  for p = 0 to 4095 do
    for v = 0 to 15 do
      List.iter (fun off ->
        incr checks;
        let regs = List.init 16 (fun i -> if i = 3 then v else 0) in
        let s = mk_state 0 false regs p false zero_rom in
        let s' = execute s (ISZ (3, off)) in
        let v' = (v + 1) mod 16 in
        let want_pc = if v' = 0 then ref_next p 2 else ref_page_target p 2 off in
        if pcv s' <> want_pc || rval s' 3 <> v' then begin
          incr fails;
          if !fails <= 5 then
            Printf.printf "    ISZ pc=%d v=%d off=%d -> model=(pc %d, r3 %d) ref=(pc %d, r3 %d)\n"
              p v off (pcv s') (rval s' 3) want_pc v'
        end) [0; 1; 254; 255]
    done
  done;
  report "ISZ pc + register (all 4096 pcs)"

(* ========= Test 7: JUN/JMS targets and JIN page-relative jump ========= *)
let test_jump () =
  section "jump";
  (* JUN/JMS: every 12-bit target from sampled pcs, and every pc to sampled
     targets; JMS also deposits the return address in the first saved row *)
  List.iter (fun p ->
    for a = 0 to 4095 do
      incr checks;
      let s = mk_state 0 false zero_regs p false zero_rom in
      let s1 = execute s (JUN a) in
      let s2 = execute s (JMS a) in
      if pcv s1 <> a || pcv s2 <> a || stkv1 s2 <> ref_next p 2 then begin
        incr fails;
        if !fails <= 5 then
          Printf.printf "    JUN/JMS a=%d pc=%d -> jun=%d jms=%d ret=%d\n"
            a p (pcv s1) (pcv s2) (stkv1 s2)
      end
    done) [0; 2046; 4094; 4095];
  for p = 0 to 4095 do
    List.iter (fun a ->
      incr checks;
      let s = mk_state 0 false zero_regs p false zero_rom in
      let s1 = execute s (JUN a) in
      let s2 = execute s (JMS a) in
      if pcv s1 <> a || pcv s2 <> a || stkv1 s2 <> ref_next p 2 then begin
        incr fails;
        if !fails <= 5 then
          Printf.printf "    JUN/JMS a=%d pc=%d -> jun=%d jms=%d ret=%d\n"
            a p (pcv s1) (pcv s2) (stkv1 s2)
      end) [0; 255; 256; 2047; 4095]
  done;
  (* JIN: page of pc+1, low byte from the register pair; all 4096 pcs *)
  for p = 0 to 4095 do
    for rh = 0 to 15 do
      for rl = 0 to 15 do
        incr checks;
        let regs = List.init 16 (fun i -> if i = 2 then rh else if i = 3 then rl else 0) in
        let s = mk_state 0 false regs p false zero_rom in
        let s' = execute s (JIN 3) in
        let want = (ref_next p 1) / 256 * 256 + (rh * 16 + rl) in
        if pcv s' <> want then begin
          incr fails;
          if !fails <= 5 then
            Printf.printf "    JIN pc=%d pair=%d -> model=%d ref=%d\n"
              p (rh*16+rl) (pcv s') want
        end
      done
    done
  done;
  report "JUN/JMS/JIN targets (exhaustive pcs)"

(* ========= Test 8: FIN fetches from the page of the next instruction ========= *)
let test_fin () =
  section "fin";
  let romarr = Array.init 4096 (fun i -> (i * 7 + 3) mod 256) in
  let romlist = Array.to_list romarr in
  for p = 0 to 4095 do
    for r0 = 0 to 15 do
      for r1 = 0 to 15 do
        incr checks;
        let regs = List.init 16 (fun i -> if i = 0 then r0 else if i = 1 then r1 else 0) in
        let s = mk_state 0 false regs p false romlist in
        let s' = execute s (FIN 4) in
        let src = (ref_next p 1) / 256 * 256 + (r0 * 16 + r1) in
        let b = romarr.(src) in
        if rval s' 4 <> b / 16 || rval s' 5 <> b mod 16
           || pcv s' <> ref_next p 1 then begin
          incr fails;
          if !fails <= 5 then
            Printf.printf "    FIN pc=%d pair0=%d -> model=(%d,%d,pc %d) ref byte %d at %d\n"
              p (r0*16+r1) (rval s' 4) (rval s' 5) (pcv s') b src
        end
      done
    done
  done;
  report "FIN page-of-next fetch (all 4096 pcs)"

(* ========= Test 9: the JMS/BBL address ring ========= *)
(* Reference: the ring in pointer-relative coordinates (the PC and three
   saved rows).  CALL rotates the return address in and discards the oldest
   row; RET resumes the first saved row and rotates the vacated PC to the
   back, so returns past the ring's depth walk the stale rows. *)
let test_stack () =
  section "stack";
  let scenarios = [ [100; 500; 1000; 2000];
                    [4094; 1; 4095; 256];
                    [7; 7; 7; 7];
                    [0; 4095; 0; 4095; 0; 4095];
                    [1; 2; 3; 4; 5; 6; 7] ] in
  List.iter (fun addrs ->
    let s = ref (mk_state 0 false zero_regs 0 false zero_rom) in
    let rpc = ref 0 and r1 = ref 0 and r2 = ref 0 and r3 = ref 0 in
    let check t =
      incr checks;
      if pcv !s <> !rpc || stkv1 !s <> !r1 || stkv2 !s <> !r2 || stkv3 !s <> !r3
      then begin
        incr fails;
        if !fails <= 5 then
          Printf.printf "    %s -> pc %d/%d rows (%d,%d,%d)/(%d,%d,%d)\n"
            t (pcv !s) !rpc (stkv1 !s) (stkv2 !s) (stkv3 !s) !r1 !r2 !r3
      end in
    List.iter (fun a ->
      s := execute !s (JMS a);
      let ret = (!rpc + 2) mod 4096 in
      r3 := !r2; r2 := !r1; r1 := ret; rpc := a;
      check (Printf.sprintf "JMS %d" a)) addrs;
    for d = 1 to 6 do
      s := execute !s (BBL d);
      let old_pc = !rpc in
      rpc := !r1; r1 := !r2; r2 := !r3; r3 := old_pc;
      incr checks;
      if aval !s <> d then begin
        incr fails;
        if !fails <= 5 then Printf.printf "    BBL %d -> acc=%d\n" d (aval !s)
      end;
      check (Printf.sprintf "BBL %d" d)
    done) scenarios;
  report "JMS/BBL ring (discard + underflow)"

(* ========= Test 10: RAM main memory, full matrix, two patterns ========= *)
let bank_codes = [| 0; 1; 2; 4 |]   (* single-CM-line DCL codes -> banks 0..3 *)

let ram_main_pass value_of =
  let mem = Array.make 1024 0 in
  let s = ref (mk_state 0 false zero_regs 0 false zero_rom) in
  (* write every main character of every bank, then read everything back *)
  for bi = 0 to 3 do
    for src = 0 to 255 do
      let v = value_of bi src in
      s := exec_list [LDM bank_codes.(bi); DCL; FIM (0, src); SRC 1; LDM v; WRM] !s;
      mem.(bi * 256 + src) <- v
    done
  done;
  for bi = 0 to 3 do
    for src = 0 to 255 do
      incr checks;
      s := exec_list [LDM bank_codes.(bi); DCL; FIM (0, src); SRC 1; RDM] !s;
      let want = mem.(bi * 256 + src) in
      if aval !s <> want then begin
        incr fails;
        if !fails <= 5 then
          Printf.printf "    RAM bank %d src %d -> model=%d ref=%d\n"
            bi src (aval !s) want
      end
    done
  done

let test_ram_main () =
  section "ram-main";
  ram_main_pass (fun bi src -> (src + src / 16 + bi * 5) mod 16);
  ram_main_pass (fun bi src -> (src * 3 + src / 16 + bi * 9 + 2) mod 16);
  report "RAM main matrix (2 x 4 banks x 256)"

(* ========= Test 11: RAM status characters, full matrix, two patterns ========= *)
let ram_status_pass value_of =
  let wr_of = [| WR0; WR1; WR2; WR3 |] in
  let rd_of = [| RD0; RD1; RD2; RD3 |] in
  let smem = Array.make 256 0 in
  let s = ref (mk_state 0 false zero_regs 0 false zero_rom) in
  for b = 0 to 3 do
    for chip = 0 to 3 do
      for reg = 0 to 3 do
        for idx = 0 to 3 do
          let v = value_of b chip reg idx in
          let src = (chip * 4 + reg) * 16 in
          s := exec_list [LDM bank_codes.(b); DCL; FIM (0, src); SRC 1; LDM v; wr_of.(idx)] !s;
          smem.(((b * 4 + chip) * 4 + reg) * 4 + idx) <- v
        done
      done
    done
  done;
  for b = 0 to 3 do
    for chip = 0 to 3 do
      for reg = 0 to 3 do
        for idx = 0 to 3 do
          incr checks;
          let src = (chip * 4 + reg) * 16 in
          s := exec_list [LDM bank_codes.(b); DCL; FIM (0, src); SRC 1; rd_of.(idx)] !s;
          let want = smem.(((b * 4 + chip) * 4 + reg) * 4 + idx) in
          if aval !s <> want then begin
            incr fails;
            if !fails <= 5 then
              Printf.printf "    status b%d c%d r%d s%d -> model=%d ref=%d\n"
                b chip reg idx (aval !s) want
          end
        done
      done
    done
  done

let test_ram_status () =
  section "ram-status";
  ram_status_pass (fun b chip reg idx -> (b * 5 + chip * 3 + reg * 7 + idx + 1) mod 16);
  ram_status_pass (fun b chip reg idx -> (b * 11 + chip * 2 + reg * 5 + idx * 3) mod 16);
  report "RAM status matrix (2 x 4x4x4x4)"

(* ========= Test 12: multi-line DCL writes reach every selected bank ========= *)
let test_ram_multibank () =
  section "ram-multibank";
  (* seed each bank with a distinct value, write once through a multi-line
     code, then read every bank back via its single-line code: the selected
     set takes the written value, the rest keep their seeds *)
  let line_sets = [ (3, [1;2]); (5, [1;3]); (6, [2;3]); (7, [1;2;3]) ] in
  List.iter (fun (code, banks) ->
    List.iter (fun src ->
      let s = ref (mk_state 0 false zero_regs 0 false zero_rom) in
      for bi = 0 to 3 do
        s := exec_list [LDM bank_codes.(bi); DCL; FIM (0, src); SRC 1;
                        LDM ((bi + 3) mod 16); WRM] !s
      done;
      s := exec_list [LDM code; DCL; FIM (0, src); SRC 1; LDM 9; WRM] !s;
      for bi = 0 to 3 do
        incr checks;
        s := exec_list [LDM bank_codes.(bi); DCL; FIM (0, src); SRC 1; RDM] !s;
        let want = if List.mem bi banks then 9 else (bi + 3) mod 16 in
        if aval !s <> want then begin
          incr fails;
          if !fails <= 5 then
            Printf.printf "    code %d bank %d src %d -> model=%d ref=%d\n"
              code bi src (aval !s) want
        end
      done) [0; 77; 255]) line_sets;
  report "multi-line DCL writes (codes 3,5,6,7)"

(* ========= Test 13: ADM/SBM memory-operand arithmetic ========= *)
let test_ram_arith () =
  section "ram-arith";
  List.iter (fun (name, op) ->
    for m = 0 to 15 do
      for a = 0 to 15 do
        List.iter (fun cy ->
          incr checks;
          let s0 = mk_state 0 false zero_regs 0 false zero_rom in
          let s1 = exec_list [LDM 0; DCL; FIM (0, 0); SRC 1; LDM m; WRM;
                              (if cy then STC else CLC); LDM a] s0 in
          let s' = execute s1 op in
          let (wa, wc) = ref_alu name a cy m in
          if aval s' <> wa || carry s' <> wc then begin
            incr fails;
            if !fails <= 5 then
              Printf.printf "    %s m=%d a=%d cy=%b -> model=(%d,%b) ref=(%d,%b)\n"
                name m a cy (aval s') (carry s') wa wc
          end) [false; true]
      done
    done) [("ADD", ADM); ("SUB", SBM)];
  report "ADM/SBM vs reference ALU"

(* =================== Test 14: timing, all instructions =================== *)
let sample_instrs =
  [NOP; JCN (0,0); FIM (0,0); SRC 1; FIN 0; JIN 1; JUN 0; JMS 0; INC 0;
   ISZ (0,0); ADD 0; SUB 0; LD 0; XCH 0; BBL 0; LDM 0; WRM; WMP; WRR; WPM;
   WR0; WR1; WR2; WR3; SBM; RDM; RDR; ADM; RD0; RD1; RD2; RD3; CLB; CLC;
   IAC; CMC; CMA; RAL; RAR; TCC; DAC; TCS; STC; DAA; KBP; DCL]

let test_timing () =
  section "timing";
  List.iter (fun i ->
    incr checks;
    let got = cycles i and want = ref_cycles i in
    if got <> want then begin
      incr fails;
      Printf.printf "    cycles %s -> model=%d ref=%d\n" (tag i) got want
    end) sample_instrs;
  report "timing (all 46 instructions)"

(* =================== Test 15: encode/decode round trip =================== *)
let test_roundtrip () =
  section "roundtrip";
  List.iter (fun i ->
    incr checks;
    let (b1,b2) = encode i in
    if tag (decode b1 b2) <> tag i then begin
      incr fails;
      Printf.printf "    roundtrip %s -> %d %d -> %s\n" (tag i) b1 b2 (tag (decode b1 b2))
    end) sample_instrs;
  report "encode/decode round trip"

let () =
  Printf.printf "Differential test: extracted Coq model vs independent reference\n";
  Printf.printf "===============================================================\n";
  let total = ref 0 in
  let run f = f (); total := !total + !fails in
  run test_decode;
  run test_alu;
  run test_daa_decimal;
  run test_inc;
  run test_jcn;
  run test_isz;
  run test_jump;
  run test_fin;
  run test_stack;
  run test_ram_main;
  run test_ram_status;
  run test_ram_multibank;
  run test_ram_arith;
  run test_timing;
  run test_roundtrip;
  Printf.printf "===============================================================\n";
  if !total = 0 then Printf.printf "ALL DIFFERENTIAL TESTS PASSED (model agrees with reference)\n"
  else Printf.printf "TOTAL MISMATCHES: %d\n" !total;
  exit (if !total = 0 then 0 else 1)

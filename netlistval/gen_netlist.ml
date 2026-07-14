(* Netlist-validation vector generator.

   For each suite this program writes a 4096-byte ROM image (hex, one
   byte per line) and the machine-checked model's expected bus-level
   trace over it: one CSV row per machine cycle,

     cycle,addr,x1,x2,x3,cmA3,cmM2,cmX2

   where addr is the fetch address, x1/x2/x3 are the data-bus nibbles
   the CPU drives during X1/X2/X3, and cmA3/cmM2/cmX2 pack
   {cm_rom,cm_ram3..cm_ram0} as a 5-bit mask at the A3/M2/X2 subcycles.
   A field of -1 means the model makes no claim there (the comparator
   skips it).  Everything asserted is exactly what external MCS-4
   hardware observes, so the same expectations apply to a transistor
   netlist simulation or a physical 4004.

   The claims per instruction class:
     every cycle    addr, x1 = low nibble of the byte fetched,
                    cmA3 = CM-ROM plus the DCL-selected CM-RAM lines
     0xEX group     cmM2 = same mask (I/O designation at M2)
     WRR WMP WRM
     WR0-3 WPM      x2 = accumulator
     SRC            x2/x3 = the register pair, cmX2 = mask
     LDM            x2 = the operand *)

open Intel4004_model

let zero_regs = List.init 16 (fun _ -> 0)

(* the CM mask {rom,r3,r2,r1,r0} for the current DCL selection *)
let cm_mask s =
  let lines = dcl_lines (cm_code s) in
  List.fold_left (fun m b -> m lor (1 lsl b)) 16 lines

let is_io b1 = b1 / 16 = 14
let is_acc_emit b1 =
  b1 = 0xE0 || b1 = 0xE1 || b1 = 0xE2 || b1 = 0xE3 ||
  b1 = 0xE4 || b1 = 0xE5 || b1 = 0xE6 || b1 = 0xE7
let is_src b1 = b1 / 16 = 2 && b1 mod 2 = 1
let is_ldm b1 = b1 / 16 = 13

(* run the model over the rom and emit the expected trace *)
let expected_trace oc rom romlist cycles_budget tp =
  let s = ref (mk_state 0 false zero_regs 0 (tp <> 0) romlist) in
  let cyc = ref 0 in
  while !cyc < cycles_budget do
    let p = pcv !s in
    let b1 = rom.(p) in
    let b2 = rom.((p + 1) mod 4096) in
    let i = decode b1 b2 in
    let mc = cycles i / 8 in
    let mask = cm_mask !s in
    (* first machine cycle *)
    let x2, x3 =
      if is_acc_emit b1 then (aval !s, -1)
      else if is_src b1 then
        let r = b1 mod 16 in
        let e = r - r mod 2 in
        (rval !s e, rval !s (e + 1))
      else if is_ldm b1 then (b1 mod 16, -1)
      else (-1, -1)
    in
    Printf.fprintf oc "%d,%d,%d,%d,%d,%d,%d,%d\n"
      !cyc p (b1 mod 16) x2 x3
      mask
      (if is_io b1 then mask else 0)
      (if is_src b1 then mask else 0);
    incr cyc;
    (* second machine cycle: two-word instructions fetch pc+1; FIN
       (one word, two cycles) fetches the indirect address held in
       register pair 0, in the page of pc+1 *)
    if mc = 2 && !cyc < cycles_budget then begin
      let fin = b1 / 16 = 3 && b1 mod 2 = 0 in
      let a2 =
        if fin then
          ((p + 1) mod 4096) / 256 * 256 + rval !s 0 * 16 + rval !s 1
        else (p + 1) mod 4096
      in
      Printf.fprintf oc "%d,%d,%d,%d,%d,%d,%d,%d\n"
        !cyc a2 (if fin then -1 else rom.(a2) mod 16) (-1) (-1) mask 0 0;
      incr cyc
    end;
    s := step !s
  done

let manifest : (string * int * int) list ref = ref []

let write_suite name rom cycles_budget tp =
  let dir = "netlistval/build" in
  (try Sys.mkdir dir 0o755 with Sys_error _ -> ());
  let oc = open_out (Printf.sprintf "%s/%s.hex" dir name) in
  Array.iter (fun b -> Printf.fprintf oc "%02x\n" b) rom;
  close_out oc;
  let romlist = Array.to_list rom in
  let oc = open_out (Printf.sprintf "%s/%s.expected.csv" dir name) in
  expected_trace oc rom romlist cycles_budget tp;
  close_out oc;
  manifest := (name, cycles_budget, tp) :: !manifest;
  Printf.printf "%s: %d cycles, test=%d\n" name cycles_budget tp

(* ---- suite construction helpers ---- *)

let new_rom () = Array.make 4096 0

let emit rom pos bytes =
  List.iteri (fun k b -> rom.(!pos + k) <- b land 0xff) bytes;
  pos := !pos + List.length bytes

let jun_self rom pos =
  (* jump-to-self at the current position *)
  let a = !pos in
  emit rom pos [0x40 lor (a / 256); a land 0xff]

(* ---- suites ---- *)

(* undefined opcodes: 0x00..0x0F and 0xFE/0xFF execute as NOP *)
let suite_undef () =
  let rom = new_rom () in
  let pos = ref 0 in
  emit rom pos [0xD5; 0xE2];                    (* LDM 5; WRR *)
  for b = 0 to 15 do emit rom pos [b] done;
  emit rom pos [0xFE; 0xFF];
  emit rom pos [0xE2];                          (* acc still 5 *)
  jun_self rom pos;
  write_suite "undef" rom 60 1

(* accumulator group: every one-word ALU op over every acc value and
   both carry levels, read back through WRR *)
let suite_alu () =
  let rom = new_rom () in
  let pos = ref 0 in
  let ops = [0xF2; 0xF8; 0xF4; 0xF5; 0xF6; 0xF7; 0xF9; 0xF0; 0xF1;
             0xF3; 0xFB; 0xFC; 0xFA] in
  List.iter (fun op ->
    for v = 0 to 15 do
      List.iter (fun cy ->
        emit rom pos [(if cy = 1 then 0xFA else 0xF1); 0xD0 lor v; op; 0xE2])
        [0; 1]
    done) ops;
  let budget = !pos + 10 in
  jun_self rom pos;
  write_suite "alu" rom budget 1

(* register file: FIM all pairs, SRC dumps, XCH/LD/ADD/SUB/INC, FIN *)
let suite_regs () =
  let rom = new_rom () in
  let pos = ref 0 in
  (* load every pair with a distinct pattern *)
  for p = 0 to 7 do
    emit rom pos [0x20 lor (2 * p); (3 * p + 5) * 16 land 0xf0 lor (13 - p)]
  done;
  (* dump every pair *)
  for p = 0 to 7 do emit rom pos [0x21 lor (2 * p)] done;
  (* exchange, load, arithmetic, increment; probe after each *)
  emit rom pos [0xD7; 0xB3; 0xE2];              (* LDM 7; XCH 3; WRR *)
  emit rom pos [0xA3; 0xE2];                    (* LD 3; WRR *)
  emit rom pos [0x63; 0x23; 0xE2];              (* INC 3; SRC 3: dump pair *)
  emit rom pos [0xF1; 0x85; 0xE2];              (* CLC; ADD 5; WRR *)
  emit rom pos [0xFA; 0x96; 0xE2];              (* STC; SUB 6; WRR *)
  (* FIN through pair 0 pointing at a known byte *)
  emit rom pos [0x20; 0x60];                    (* FIM 0, 0x60 *)
  rom.(0x60) <- 0x9A;
  emit rom pos [0x34];                          (* FIN 4 *)
  emit rom pos [0x25];                          (* SRC 5: dump pair (4,5) *)
  let budget = !pos + 8 in
  jun_self rom pos;
  write_suite "regs" rom budget 1

(* JCN over all sixteen conditions under all flag settings; taken and
   not-taken paths distinguished purely by the fetch trace *)
let suite_branch tp =
  let rom = new_rom () in
  let pos = ref 0 in
  for cond = 0 to 15 do
    List.iter (fun (acc, cy) ->
      emit rom pos [0xD0 lor acc];                    (* LDM acc *)
      emit rom pos [(if cy = 1 then 0xFA else 0xF1)]; (* STC/CLC *)
      let off = (!pos + 4) land 0xff in
      emit rom pos [0x10 lor cond; off];              (* JCN cond off *)
      emit rom pos [0x00; 0x00])                      (* fall-through pad *)
      [(0, 0); (1, 0); (0, 1); (1, 1)]
  done;
  let budget = !pos + 40 in
  jun_self rom pos;
  write_suite (Printf.sprintf "branch_t%d" tp) rom budget tp

(* ISZ loop and JIN/FIN page rule *)
let suite_loops () =
  let rom = new_rom () in
  let pos = ref 0 in
  emit rom pos [0x2E; 0xC0];      (* FIM 14, 0xC0: r14=12, r15=0 *)
  let head = !pos in
  emit rom pos [0x6F];            (* INC 15 *)
  emit rom pos [0x7E; head land 0xff];  (* ISZ 14, head: loops 4 times *)
  emit rom pos [0x2A; 0x00];      (* FIM 10, 0: pair (10,11) = 0,0 *)
  emit rom pos [0x20; 0x80];      (* FIM 0, 0x80 *)
  rom.(0x80) <- 0x77;
  emit rom pos [0x32];            (* FIN 2: loads pair (2,3) from 0x80 *)
  emit rom pos [0x23];            (* SRC 3: dump pair (2,3) = 7,7 *)
  emit rom pos [0x2C; 0x60];      (* FIM 12, 0x60: r12=6, r13=0 *)
  emit rom pos [0x3D];            (* JIN 13: jump to page(pc+1)|0x60 *)
  rom.(0x60) <- 0xD3;             (* LDM 3 *)
  rom.(0x61) <- 0xE2;             (* WRR *)
  rom.(0x62) <- 0x40; rom.(0x63) <- 0x62;   (* JUN self *)
  write_suite "loops" rom 60 1

(* page-boundary and 4095/4096 wraparound behavior *)
let suite_pagewrap () =
  let rom = new_rom () in
  (* island 1: JCN spanning 0x0FE-0x0FF, taken; target is composed in
     the page of pc+2 = page 1 *)
  rom.(0) <- 0xD0;                (* LDM 0: acc = 0 *)
  rom.(1) <- 0x40; rom.(2) <- 0xFE;   (* JUN 0x0FE *)
  rom.(0xFE) <- 0x14; rom.(0xFF) <- 0x10;  (* JCN JZ 0x10 -> 0x110 *)
  rom.(0x110) <- 0x40; rom.(0x111) <- 0x00; rom.(0x112) <- 0x00;
  (* island 2 at 0x110: JUN 4090 *)
  rom.(0x110) <- 0x4F; rom.(0x111) <- 0xFA;   (* JUN 0xFFA *)
  (* island 3 at 4090: set acc nonzero, JCN JNZ at 4094 spanning
     4094-4095; the taken target composes in the page of
     (4094+2) mod 4096 = 0, so control lands at 0x022 *)
  rom.(4090) <- 0xD1;             (* LDM 1 *)
  rom.(4091) <- 0xF1;             (* CLC *)
  rom.(4092) <- 0x00;             (* NOP *)
  rom.(4093) <- 0x00;             (* NOP *)
  rom.(4094) <- 0x1C; rom.(4095) <- 0x22;  (* JCN JNZ 0x22 *)
  rom.(0x22) <- 0xE2;             (* WRR: acc = 1 *)
  rom.(0x23) <- 0x40; rom.(0x24) <- 0x23;  (* JUN self *)
  write_suite "pagewrap" rom 40 1

(* a one-word instruction at 4095: the following fetch wraps to 0 *)
let suite_fetchwrap () =
  let rom = new_rom () in
  rom.(0) <- 0xD2;                (* LDM 2 *)
  rom.(1) <- 0x4F; rom.(2) <- 0xFF;   (* JUN 4095 *)
  rom.(4095) <- 0xF2;             (* IAC at the last byte *)
  rom.(0) <- 0xD2;                (* after wrap: LDM 2 again *)
  rom.(3) <- 0xE2;                (* WRR *)
  rom.(4) <- 0x40; rom.(5) <- 0x04;   (* JUN self *)
  write_suite "fetchwrap" rom 30 1

(* the address ring: five nested calls (overflow discards the oldest),
   then six returns (underflow resumes stale rows); every push and pop
   is visible in the fetch trace *)
let suite_ring () =
  let rom = new_rom () in
  rom.(0) <- 0x51; rom.(1) <- 0x00;        (* JMS 0x100 *)
  rom.(2) <- 0x40; rom.(3) <- 0x02;        (* JUN self (final resume) *)
  rom.(0x100) <- 0x52; rom.(0x101) <- 0x00;  (* JMS 0x200 *)
  rom.(0x102) <- 0xC1;                       (* BBL 1 *)
  rom.(0x200) <- 0x53; rom.(0x201) <- 0x00;  (* JMS 0x300 *)
  rom.(0x202) <- 0xC2;                       (* BBL 2 *)
  rom.(0x300) <- 0x54; rom.(0x301) <- 0x00;  (* JMS 0x400 *)
  rom.(0x302) <- 0xC3;                       (* BBL 3 *)
  rom.(0x400) <- 0x55; rom.(0x401) <- 0x00;  (* JMS 0x500: 5th call *)
  rom.(0x402) <- 0xC4;                       (* BBL 4 *)
  (* six returns walk the ring past its depth *)
  rom.(0x500) <- 0xC5;                       (* BBL 5 *)
  write_suite "ring" rom 40 1

(* DCL: every accumulator value; the CM-RAM masks at A3 and at an I/O
   instruction's M2 follow the line sets *)
let suite_dcl () =
  let rom = new_rom () in
  let pos = ref 0 in
  for v = 0 to 15 do
    emit rom pos [0xD0 lor v; 0xFD; 0xE0]   (* LDM v; DCL; WRM *)
  done;
  emit rom pos [0xD0; 0xFD];                (* restore code 0 *)
  let budget = !pos + 6 in
  jun_self rom pos;
  write_suite "dcl" rom budget 1

(* WPM with no programmer attached: emits the accumulator, changes no
   architectural state *)
let suite_wpm () =
  let rom = new_rom () in
  let pos = ref 0 in
  emit rom pos [0xD9; 0xE3; 0xE2];   (* LDM 9; WPM; WRR *)
  emit rom pos [0xD3; 0xE3; 0xE3; 0xE2];  (* LDM 3; WPM; WPM; WRR *)
  let budget = !pos + 6 in
  jun_self rom pos;
  write_suite "wpm" rom budget 1

(* seeded straight-line random programs over the bus-observable subset,
   with periodic probe blocks *)
let suite_rand seed =
  let rom = new_rom () in
  let pos = ref 0 in
  let st = ref seed in
  let rnd m = st := (!st * 1103515245 + 12345) land 0x3fffffff; !st mod m in
  let safe_ops () =
    match rnd 12 with
    | 0 -> [0xD0 lor rnd 16]                          (* LDM *)
    | 1 -> [0xA0 lor rnd 16]                          (* LD *)
    | 2 -> [0xB0 lor rnd 16]                          (* XCH *)
    | 3 -> [0x60 lor rnd 16]                          (* INC *)
    | 4 -> [0x80 lor rnd 16]                          (* ADD *)
    | 5 -> [0x90 lor rnd 16]                          (* SUB *)
    | 6 -> [0xF0 lor List.nth [0;1;2;3;4;5;6;7;8;9;10;11;12] (rnd 13)]
    | 7 -> [0x20 lor (2 * rnd 8); rnd 256]            (* FIM *)
    | 8 -> [0x21 lor (2 * rnd 8)]                     (* SRC *)
    | 9 -> [0xE0 lor List.nth [0;1;2;3;4;5;6;7] (rnd 8)]  (* I/O writes *)
    | 10 -> [0xFD]                                    (* DCL *)
    | _ -> [0x00]                                     (* NOP *)
  in
  while !pos < 3900 do
    emit rom pos (safe_ops ());
    if rnd 12 = 0 then begin
      emit rom pos [0xE2];                            (* WRR probe *)
      for p = 0 to 7 do emit rom pos [0x21 lor (2 * p)] done
    end
  done;
  let budget = !pos + 8 in
  jun_self rom pos;
  write_suite (Printf.sprintf "rand%d" seed) rom budget 1

let () =
  suite_undef ();
  suite_alu ();
  suite_regs ();
  suite_branch 0;
  suite_branch 1;
  suite_loops ();
  suite_pagewrap ();
  suite_fetchwrap ();
  suite_ring ();
  suite_dcl ();
  suite_wpm ();
  suite_rand 1;
  suite_rand 2;
  suite_rand 3;
  let oc = open_out "netlistval/build/manifest.csv" in
  List.iter (fun (n, c, t) -> Printf.fprintf oc "%s,%d,%d\n" n c t)
    (List.rev !manifest);
  close_out oc

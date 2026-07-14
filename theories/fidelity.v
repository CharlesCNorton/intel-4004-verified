(* ===================================================================== *)
(*  Intel 4004: fidelity closures.                                       *)
(*  Undefined-opcode decoding made a theorem, system-scope RESET,        *)
(*  TEST-pin sampling adequacy, the electrically honest partiality of    *)
(*  multi-line DCL reads, the underflow behavior of the address ring,    *)
(*  the port-driven programming path's read-back caveat for              *)
(*  mask-programmed port directions, the typed bounds of the whole       *)
(*  machine state, correctness theorems for the disassembler and         *)
(*  program validator, and a uniform value-level Hoare rule for the      *)
(*  entire ALU.  The hardware models themselves (multi-bank DCL, the     *)
(*  ring address register, the half-byte WPM latch pair, the port        *)
(*  directions) are the execute semantics of machine.v, with their       *)
(*  headline theorems in behavior.v.                                     *)
(* ===================================================================== *)

From Stdlib Require Import List Arith PeanoNat Bool Lia.
Import ListNotations.
From FourK Require Import machine behavior verification.

(* ==================== Undefined opcodes (modeling convention) ======== *)

(** The whole low opcode group decodes to NOP: bytes 0x00 through 0x0F.
    Together with decode_FE_FF_is_nop this makes the undefined-opcode
    convention a checked statement rather than folklore.  The data sheet
    marks these encodings unused; silicon behavior is not claimed. *)
Theorem decode_low_group_is_nop : forall (b1 b2 : byte),
  wval b1 < 16 -> decode b1 b2 = NOP.
Proof.
  intros b1 b2 Hb.
  unfold decode. cbv zeta.
  rewrite (Nat.div_small (wval b1) 16 Hb).
  reflexivity.
Qed.

(* ==================== System-scope RESET ==================== *)

(* The 4002 data sheet has the system RESET line clear RAM contents and
   output ports as well as the CPU.  reset_state models the CPU scope;
   system_reset models the whole MCS-4 system: everything volatile clears,
   and only the mask-programmed ROM, the mask-time port directions, and
   the externally driven inputs (pins, TEST) survive. *)

Definition system_reset (s : Intel4004State) : Intel4004State :=
  mkState (nib 0) (repeat (nib 0) 16) false (adr 0) (adr 0) (adr 0) (adr 0)
          empty_sys (w3 0) (mkRAMSel (w2 0) (w2 0) (nib 0))
          (repeat (nib 0) 16) (in_ports s) (port_dirs s)
          (nib 0) (rom s) (test_pin s) (adr 0) false latch_init.

Theorem system_reset_specification : forall s, WF s ->
  WF (system_reset s) /\
  acc (system_reset s) = nib 0 /\
  carry (system_reset s) = false /\
  pc (system_reset s) = adr 0 /\
  stk1 (system_reset s) = adr 0 /\
  stk2 (system_reset s) = adr 0 /\
  stk3 (system_reset s) = adr 0 /\
  regs (system_reset s) = repeat (nib 0) 16 /\
  ram_sys (system_reset s) = empty_sys /\
  out_ports (system_reset s) = repeat (nib 0) 16 /\
  rom (system_reset s) = rom s.
Proof.
  intros s HWF. destruct_WF HWF.
  split.
  { unfold WF, system_reset, empty_sys.
    cbn [regs ram_sys out_ports in_ports port_dirs rom].
    repeat split; try assumption; try apply repeat_length.
    apply Forall_repeat. exact empty_bank_WF. }
  repeat split.
Qed.

(** System reset refines CPU reset: on every CPU-visible register the two
    agree; the system line additionally clears the 4002 array and the
    output-port latches. *)
Theorem system_reset_refines_cpu_reset : forall s,
  acc (system_reset s) = acc (reset_state s) /\
  carry (system_reset s) = carry (reset_state s) /\
  pc (system_reset s) = pc (reset_state s) /\
  stk1 (system_reset s) = stk1 (reset_state s) /\
  stk2 (system_reset s) = stk2 (reset_state s) /\
  stk3 (system_reset s) = stk3 (reset_state s) /\
  regs (system_reset s) = regs (reset_state s) /\
  rom (system_reset s) = rom (reset_state s).
Proof. intros s. repeat split. Qed.

(* ==================== TEST-pin sampling adequacy ==================== *)

(** Executing any non-JCN instruction commutes with setting the TEST pin:
    the pin is observable only through JCN's condition, so sampling the
    environment once per instruction (as steps_env does) loses nothing. *)
Theorem test_pin_only_affects_jcn : forall s i b,
  (forall c a, i <> JCN c a) ->
  execute (set_test_pin s b) i = set_test_pin (execute s i) b.
Proof.
  intros s i b Hnjcn.
  destruct i;
    try (exfalso; exact (Hnjcn _ _ eq_refl));
    try reflexivity.
  - (* ISZ *)
    cbn [execute]. cbv zeta.
    change (rval (set_test_pin s b) (wval n)) with (rval s (wval n)).
    destruct (wval (nib (rval s (wval n) + 1)) =? 0); reflexivity.
  - (* WPM *)
    cbn [execute].
    change (prom_enable (set_test_pin s b)) with (prom_enable s).
    change (prom_latch (set_test_pin s b)) with (prom_latch s).
    destruct (prom_enable s); [destruct (pl_expect_low (prom_latch s)) |];
      reflexivity.
Qed.

(* ==================== Multi-line DCL reads: partiality ==================== *)

(* Reads under a multi-line DCL selection put several 4002s on the data
   bus at once; no MCS-4 document defines the electrical outcome.  The
   partial reader ram_read_main_opt is the fidelity claim: defined exactly
   when every selected bank agrees.  The total reader used by execute
   returns nib 0 in the undefined case, as a documented convention. *)

(** An undefined multi-bank read exhibits a disagreeing pair of banks. *)
Lemma agree_read_none_disagree : forall (v0 : nibble) rest,
  agree_read (v0 :: rest) = None ->
  exists x, In x rest /\ wval x <> wval v0.
Proof.
  intros v0 rest H.
  cbn [agree_read] in H.
  destruct (forallb (fun x => wval x =? wval v0) rest) eqn:Ef; [discriminate |].
  clear H.
  induction rest as [|x rest IH]; cbn in Ef; [discriminate |].
  destruct (wval x =? wval v0) eqn:Ex; cbn in Ef.
  - destruct (IH Ef) as (x' & Hin & Hne).
    exists x'. split; [right; exact Hin | exact Hne].
  - exists x. split; [left; reflexivity |].
    apply Nat.eqb_neq. exact Ex.
Qed.

(** A disagreement among the selected banks makes the read undefined. *)
Lemma ram_read_main_opt_none : forall s,
  ram_read_main_opt s = None ->
  exists b b', In b (sel_lines s) /\ In b' (sel_lines s) /\
    wval (read_main_bank (ram_sys s) (sel_ram s) b)
    <> wval (read_main_bank (ram_sys s) (sel_ram s) b').
Proof.
  intros s H.
  unfold ram_read_main_opt in H.
  destruct (sel_lines s) as [|b0 rest] eqn:El.
  - exfalso. exact (sel_lines_nonempty s El).
  - cbn [map] in H.
    destruct (agree_read_none_disagree _ _ H) as (x & Hin & Hne).
    apply in_map_iff in Hin.
    destruct Hin as (b & <- & Hb).
    exists b, b0.
    repeat split.
    + right. exact Hb.
    + left. reflexivity.
    + exact Hne.
Qed.

(** The undefined case reads the documented convention value. *)
Lemma ram_read_main_undefined_convention : forall s,
  ram_read_main_opt s = None -> ram_read_main s = nib 0.
Proof.
  intros s H. unfold ram_read_main. rewrite H. reflexivity.
Qed.

(** The defined case is the fidelity claim: the total reader agrees with
    the partial one. *)
Lemma ram_read_main_defined : forall s v,
  ram_read_main_opt s = Some v -> ram_read_main s = v.
Proof.
  intros s v H. unfold ram_read_main. rewrite H. reflexivity.
Qed.

(* ==================== Address-ring underflow ==================== *)

(* No MCS-4 document defines BBL past the ring's depth; on silicon it
   resumes a stale row.  That is the execute semantics: BBL reads the
   first saved row unconditionally, in lockstep with the explicit
   slots-and-pointer ring (ring_tracks_bbl, ring_underflow_agrees in
   behavior.v). *)

Theorem bbl_reads_stale_row : forall s (d : nibble),
  pc (execute s (BBL d)) = stk1 s.
Proof. reflexivity. Qed.

(** Four consecutive returns rotate the ring fully around: every row
    comes back one byte on, because each return's fetch incremented the
    row it then abandoned. *)
Theorem four_returns_advance_the_ring : forall s (d1 d2 d3 d4 : nibble),
  let s4 := execute (execute (execute (execute s (BBL d1)) (BBL d2))
                       (BBL d3)) (BBL d4) in
  pc s4 = adr (pcv s + 1) /\
  stk1 s4 = adr (wval (stk1 s) + 1) /\
  stk2 s4 = adr (wval (stk2 s) + 1) /\
  stk3 s4 = adr (wval (stk3 s) + 1).
Proof. intros. repeat split. Qed.

(* ==================== Port-direction read-back caveat ==================== *)

(* WRR always writes the 4001's internal output latch, and RDR reads the
   selected port's pins: the latch on an output-configured port
   (wrr_rdr_roundtrip in behavior.v), the environment's drive on an input
   port, whatever WRR left in the latch. *)

Theorem rdr_after_wrr_input_port_reads_environment : forall s k (v : nibble),
  WF s ->
  k < 16 ->
  nth k (port_dirs s) true = false ->
  wval (sel_rom s) = k ->
  acc (execute (drive_rom_port (execute s WRR) k v) RDR) = v.
Proof.
  intros s k v HWF Hk Hdir Hsel.
  apply rdr_reads_driven_input.
  - apply execute_preserves_WF. exact HWF.
  - exact Hk.
  - exact Hdir.
  - exact Hsel.
Qed.

(* ==================== Typed bounds of the whole state ==================== *)

(* Every field of any state, well-formed or not, sits within its wire
   width by construction. *)

Theorem state_bounds_by_construction : forall s,
  aval s < 16 /\
  pcv s < 4096 /\
  wval (stk1 s) < 4096 /\
  wval (stk2 s) < 4096 /\
  wval (stk3 s) < 4096 /\
  (forall r, rval s r < 16) /\
  (forall b c r i,
     wval (get_main (get_regRAM (get_chip (get_bank s b) c) r) i) < 16) /\
  (forall b c r i,
     wval (get_stat (get_regRAM (get_chip (get_bank s b) c) r) i) < 16) /\
  (forall k, wval (nth k (out_ports s) (nib 0)) < 16) /\
  (forall k, wval (nth k (in_ports s) (nib 0)) < 16) /\
  (forall a, wval (fetch_byte s a) < 256) /\
  wval (cm_code s) < 8 /\
  wval (sel_rom s) < 16 /\
  wval (sel_chip (sel_ram s)) < 4 /\
  wval (sel_reg (sel_ram s)) < 4 /\
  wval (sel_char (sel_ram s)) < 16 /\
  wval (prom_addr s) < 4096 /\
  wval (pl_hi (prom_latch s)) < 16.
Proof.
  intro s.
  repeat split; intros;
    first [ apply nib_lt16 | apply byte_lt256 | apply addr12_lt4096
          | apply w2_lt4 | apply w3_lt8 ].
Qed.

(* ==================== Disassembler and validator ==================== *)

Lemma encode_list_length : forall prog,
  length (encode_list prog) = 2 * length prog.
Proof.
  induction prog as [|i rest IH]; cbn [encode_list length].
  - reflexivity.
  - destruct (encode i). cbn [length]. lia.
Qed.

(** The disassembler inverts encode_list at every instruction boundary. *)
Theorem disassemble_encode_list : forall prog k,
  Forall instr_wf prog ->
  k < length prog ->
  disassemble (encode_list prog) (2 * k) = Some (nth k prog NOP, 2 * k + 2).
Proof.
  induction prog as [|i rest IH]; intros k Hwf Hk; [cbn in Hk; lia |].
  pose proof (Forall_inv Hwf) as Hi.
  pose proof (Forall_inv_tail Hwf) as Hrest.
  destruct k as [|k].
  - cbn [encode_list].
    destruct (encode i) as [b1 b2] eqn:Ee.
    unfold disassemble.
    change (2 * 0) with 0.
    cbn [skipn].
    pose proof (decode_encode_id i Hi) as Hd.
    rewrite Ee in Hd.
    rewrite Hd.
    reflexivity.
  - cbn [encode_list].
    destruct (encode i) as [b1 b2].
    unfold disassemble.
    replace (2 * S k) with (S (S (2 * k))) by lia.
    cbn [skipn].
    specialize (IH k Hrest ltac:(cbn [length] in Hk; lia)).
    unfold disassemble in IH.
    destruct (skipn (2 * k) (encode_list rest)) as [|x [|y l]] eqn:Es;
      try discriminate IH.
    injection IH as Hd.
    rewrite Hd.
    cbn [nth].
    reflexivity.
Qed.

(** Programs encode to images the layout validator accepts.  Images are
    lists of byte, bounded by construction, so the validator checks the
    two-byte alignment. *)
Theorem valid_program_encode_list : forall prog,
  valid_program (encode_list prog) = true.
Proof.
  intros prog.
  unfold valid_program.
  rewrite encode_list_length.
  apply Nat.eqb_eq.
  rewrite Nat.mul_comm.
  apply Nat.Div0.mod_mul.
Qed.

(* ==================== Uniform value-level ALU rule ==================== *)

(** One Hoare rule covers the entire ALU at value level: the postcondition
    is the data-sheet reference function itself.  Instantiating i gives the
    exact accumulator and carry for each of the fifteen ALU instructions. *)
Theorem hoare_alu_value : forall i a c rv,
  is_alu i = true ->
  {{ fun s => aval s = a /\ carry s = c /\ alu_reg i s = rv }}
     i
  {{ fun s' => aval s' = fst (alu_ref i a c rv) /\
               carry s' = snd (alu_ref i a c rv) }}.
Proof.
  intros i a c rv Halu.
  unfold hoare_triple.
  intros s HWF (Ha & Hc & Hr).
  split.
  - apply execute_preserves_WF; assumption.
  - pose proof (alu_matches_ref s i Halu) as H.
    rewrite Ha, Hc, Hr in H.
    split.
    + assert (Hf := f_equal fst H). cbn [fst] in Hf. exact Hf.
    + assert (Hs := f_equal snd H). cbn [snd] in Hs. exact Hs.
Qed.

(** Sample instantiation: KBP's exact table through the uniform rule. *)
Corollary hoare_KBP_table : forall a,
  {{ fun s => aval s = a /\ carry s = false /\ alu_reg KBP s = 0 }}
     KBP
  {{ fun s' => aval s' = match a with
                         | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4
                         | _ => 15
                         end }}.
Proof.
  intro a.
  eapply hoare_consequence.
  - intros s H. exact H.
  - apply (hoare_alu_value KBP a false 0). reflexivity.
  - intros s [H _]. cbn [alu_ref fst] in H. exact H.
Qed.

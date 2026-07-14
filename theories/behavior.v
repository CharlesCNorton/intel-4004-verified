(* ===================================================================== *)
(*  Intel 4004: instruction and system behavior.                         *)
(*  Value-level correctness of every instruction, page-boundary and      *)
(*  branch-target arithmetic, frames, timing, PROM programming through   *)
(*  the half-byte 4008/4009 latch pair, register-pair algebra, program   *)
(*  layout, independent data-sheet correspondences, the reactive         *)
(*  environment, the small-step bridge with a looping ROM program,       *)
(*  halting, execution-time analysis, the ALU simulation, the            *)
(*  multi-bank DCL write semantics of the default machine, the           *)
(*  slots-and-pointer ring isomorphism, and the machine-cycle            *)
(*  microarchitecture.                                                   *)
(* ===================================================================== *)

From Stdlib Require Import List Arith PeanoNat Bool NArith Lia.
Import ListNotations.
From FourK Require Import machine.

(* ==================== Reduction toolkit ==================== *)

(** Reduce execute and the state plumbing without touching arithmetic,
    words, or the RAM combinators. *)
Ltac exec_simpl :=
  cbn [execute];
  cbv beta delta [aval pcv cbit pc_bump ring_push ring_pop
      set_reg set_reg_pair
      with_acc with_regs with_carry with_pc with_ram with_cm with_select
      with_out_ports with_in_ports with_rom with_test with_prom_addr
      with_prom_enable with_prom_latch];
  cbn [acc regs carry pc stk1 stk2 stk3 ram_sys cm_code sel_ram out_ports
       in_ports port_dirs sel_rom rom test_pin prom_addr prom_enable
       prom_latch].

(** Case-split every boolean branch surfaced in the goal. *)
Ltac case_branches :=
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         end.

(* ==================== Behavioral correctness theorems ==================== *)

(* NOP preserves all state except incrementing PC. *)
Theorem nop_preserves_state : forall s,
  let s' := execute s NOP in
  acc s' = acc s /\ regs s' = regs s /\ carry s' = carry s /\
  pc s' = adr (pcv s + 1).
Proof. intros s. repeat split. Qed.

(* LDM loads the immediate value into the accumulator. *)
Theorem ldm_loads_immediate : forall s (n : nibble),
  let s' := execute s (LDM n) in
  acc s' = n /\ pc s' = adr (pcv s + 1).
Proof. intros s n. repeat split. Qed.

(* CLB clears both accumulator and carry. *)
Theorem clb_clears : forall s,
  let s' := execute s CLB in
  acc s' = nib 0 /\ carry s' = false /\ pc s' = adr (pcv s + 1).
Proof. intros s. repeat split. Qed.

(* ==================== Arithmetic Correctness ==================== *)

Theorem add_computes_sum : forall s (r : nibble),
  aval (execute s (ADD r)) = (aval s + rval s (wval r) + cbit s) mod 16 /\
  carry (execute s (ADD r)) = (16 <=? aval s + rval s (wval r) + cbit s).
Proof.
  intros s r. split; exec_simpl.
  - apply nib_val.
  - reflexivity.
Qed.

Theorem sub_computes_difference : forall s (r : nibble),
  aval (execute s (SUB r)) = (aval s + 16 - rval s (wval r) - cbit s) mod 16 /\
  carry (execute s (SUB r)) = (16 <=? aval s + 16 - rval s (wval r) - cbit s).
Proof.
  intros s r. split; exec_simpl.
  - apply nib_val.
  - reflexivity.
Qed.

Theorem iac_computes_increment : forall s,
  aval (execute s IAC) = (aval s + 1) mod 16 /\
  carry (execute s IAC) = (16 <=? aval s + 1).
Proof.
  intros s. split; exec_simpl.
  - apply nib_val.
  - reflexivity.
Qed.

Theorem dac_computes_decrement : forall s,
  aval (execute s DAC) = (aval s + 15) mod 16 /\
  carry (execute s DAC) = negb (aval s =? 0).
Proof.
  intros s. split; exec_simpl.
  - apply nib_val.
  - reflexivity.
Qed.

Theorem daa_bcd_adjust_correct : forall s,
  let adjust := orb (carry s) (9 <? aval s) in
  let sum := aval s + (if adjust then 6 else 0) in
  aval (execute s DAA) = sum mod 16 /\
  carry (execute s DAA) = orb (16 <=? sum) (carry s).
Proof.
  intros s. cbv zeta. split; exec_simpl.
  - apply nib_val.
  - reflexivity.
Qed.

Theorem arithmetic_operations_functionally_correct : forall s (r : nibble),
  (aval (execute s (ADD r)) = (aval s + rval s (wval r) + cbit s) mod 16 /\
   carry (execute s (ADD r)) = (16 <=? aval s + rval s (wval r) + cbit s)) /\
  (aval (execute s (SUB r)) = (aval s + 16 - rval s (wval r) - cbit s) mod 16 /\
   carry (execute s (SUB r)) = (16 <=? aval s + 16 - rval s (wval r) - cbit s)) /\
  (aval (execute s IAC) = (aval s + 1) mod 16 /\
   carry (execute s IAC) = (16 <=? aval s + 1)) /\
  (aval (execute s DAC) = (aval s + 15) mod 16 /\
   carry (execute s DAC) = negb (aval s =? 0)).
Proof.
  intros s r.
  split. apply add_computes_sum.
  split. apply sub_computes_difference.
  split. apply iac_computes_increment.
  apply dac_computes_decrement.
Qed.

(* Carry/Link check examples *)
(* SUB sets carry iff the result did not underflow (no borrow occurred). *)
Lemma sub_link_matches_spec : forall s (r : nibble),
  carry (execute s (SUB r)) = (16 <=? aval s + 16 - rval s (wval r) - cbit s).
Proof. intros. exec_simpl. reflexivity. Qed.

(* DAC sets carry iff the accumulator was non-zero. *)
Lemma dac_link_matches_spec : forall s,
  carry (execute s DAC) = negb (aval s =? 0).
Proof. intros. exec_simpl. reflexivity. Qed.

Definition is_bcd_digit (n : nat) : Prop := n <= 9.

(* Without incoming carry, DAA of a BCD digit (<= 9) is a BCD digit. *)
Lemma daa_produces_bcd : forall s,
  is_bcd_digit (aval s) ->
  carry s = false ->
  is_bcd_digit (aval (execute s DAA)).
Proof.
  intros s Hbcd Hcarry.
  unfold is_bcd_digit in *.
  pose proof (daa_bcd_adjust_correct s) as H. cbv zeta in H.
  destruct H as [Ha _].
  rewrite Ha. rewrite Hcarry. cbn [orb].
  destruct (9 <? aval s) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - apply Nat.ltb_ge in E.
    rewrite Nat.add_0_r.
    rewrite Nat.mod_small; [lia |].
    pose proof (aval_lt16 s). lia.
Qed.

(* --- Page-relative control flow (spec-accurate bases) --- *)

Lemma jin_pc_within_page : forall s (r : nibble),
  exists off, off < 256 /\
    pc (execute s (JIN r)) = adr (base_for_next1 s + off).
Proof.
  intros s r. exec_simpl.
  exists (get_reg_pair s (wval r)).
  split.
  - apply get_reg_pair_lt256.
  - unfold base_for_next1, page_base. reflexivity.
Qed.

Lemma fin_reads_from_page_of_next : forall s (r : nibble),
  regs (execute s (FIN r))
  = regs (set_reg_pair s (wval r)
            (wval (fetch_byte s (page_of (wval (pc_inc1 s)) * 256
                                 + get_reg_pair s 0)))).
Proof. intros s r. reflexivity. Qed.

Lemma isz_pc_shape : forall s (r : nibble) (off : byte),
  pc (execute s (ISZ r off)) = adr (pcv s + 2) \/
  pc (execute s (ISZ r off)) = adr (base_for_next2 s + wval off).
Proof.
  intros s r off. cbn [execute]. cbv zeta.
  destruct (wval (nib (rval s (wval r) + 1)) =? 0).
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* ==================== ISZ Loop Verification ========================== *)

(** Whether ISZ takes the branch (loops), from the register value. *)
Definition isz_loops (s : Intel4004State) (r : nat) : bool :=
  negb ((rval s r + 1) mod 16 =? 0).

(** Whether ISZ skips (terminates the loop). *)
Definition isz_terminates (s : Intel4004State) (r : nat) : bool :=
  (rval s r + 1) mod 16 =? 0.

(** Iterations remaining until ISZ terminates. *)
Definition isz_iterations (v : nat) : nat :=
  if v =? 0 then 16 else 16 - v.

Theorem isz_terminates_at_15 : forall s r,
  rval s r = 15 -> isz_terminates s r = true.
Proof.
  intros s r H. unfold isz_terminates. rewrite H. reflexivity.
Qed.

Theorem isz_loops_when_lt_15 : forall s r,
  rval s r < 15 -> isz_loops s r = true.
Proof.
  intros s r H.
  unfold isz_loops.
  rewrite Nat.mod_small by lia.
  destruct (rval s r + 1 =? 0) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - reflexivity.
Qed.

Theorem isz_iterations_decreases : forall v,
  v < 15 ->
  isz_iterations ((v + 1) mod 16) < isz_iterations v.
Proof.
  intros v Hv.
  unfold isz_iterations.
  rewrite Nat.mod_small by lia.
  destruct (v =? 0) eqn:Ev; destruct (v + 1 =? 0) eqn:Ev1.
  - apply Nat.eqb_eq in Ev1. lia.
  - apply Nat.eqb_eq in Ev. rewrite Ev. simpl. lia.
  - apply Nat.eqb_eq in Ev1. lia.
  - lia.
Qed.

Theorem isz_iterations_positive : forall v,
  v < 16 -> isz_iterations v > 0.
Proof.
  intros v Hv. unfold isz_iterations.
  destruct (v =? 0); lia.
Qed.

Theorem isz_iterations_bounded : forall v, isz_iterations v <= 16.
Proof.
  intros v. unfold isz_iterations.
  destruct (v =? 0); lia.
Qed.

(** ISZ branches when the incremented register does not wrap to zero. *)
Theorem isz_branch_taken : forall s (r : nibble) (off : byte),
  isz_loops s (wval r) = true ->
  pc (execute s (ISZ r off)) = adr (base_for_next2 s + wval off).
Proof.
  intros s r off H.
  unfold isz_loops in H. apply negb_true_iff in H.
  cbn [execute]. cbv zeta.
  rewrite nib_val. rewrite H.
  reflexivity.
Qed.

(** ISZ skips when the incremented register wraps to zero. *)
Theorem isz_branch_not_taken : forall s (r : nibble) (off : byte),
  isz_terminates s (wval r) = true ->
  pc (execute s (ISZ r off)) = adr (pcv s + 2).
Proof.
  intros s r off H.
  unfold isz_terminates in H.
  cbn [execute]. cbv zeta.
  rewrite nib_val. rewrite H.
  reflexivity.
Qed.

(** ISZ always increments the register. *)
Theorem isz_increments_reg : forall s (r : nibble) (off : byte),
  length (regs s) = 16 ->
  get_reg (execute s (ISZ r off)) (wval r) = nib (rval s (wval r) + 1).
Proof.
  intros s r off Hlen.
  cbn [execute]. cbv zeta.
  destruct (wval (nib (rval s (wval r) + 1)) =? 0);
    exec_simpl; unfold get_reg; cbn [regs];
    rewrite nth_update_nth_eq by (rewrite Hlen; apply nib_lt16);
    reflexivity.
Qed.

(** ISZ preserves other registers. *)
Theorem isz_preserves_other_reg : forall s (r : nibble) r2 (off : byte),
  wval r <> r2 ->
  get_reg (execute s (ISZ r off)) r2 = get_reg s r2.
Proof.
  intros s r r2 off Hneq.
  cbn [execute]. cbv zeta.
  destruct (wval (nib (rval s (wval r) + 1)) =? 0);
    exec_simpl; unfold get_reg; cbn [regs];
    apply nth_update_nth_neq; lia.
Qed.

(** ISZ preserves the accumulator and carry. *)
Theorem isz_preserves_acc : forall s (r : nibble) (off : byte),
  acc (execute s (ISZ r off)) = acc s.
Proof.
  intros s r off. cbn [execute]. cbv zeta.
  destruct (wval (nib (rval s (wval r) + 1)) =? 0); reflexivity.
Qed.

Theorem isz_preserves_carry : forall s (r : nibble) (off : byte),
  carry (execute s (ISZ r off)) = carry s.
Proof.
  intros s r off. cbn [execute]. cbv zeta.
  destruct (wval (nib (rval s (wval r) + 1)) =? 0); reflexivity.
Qed.

(* --- JCN condition semantics --- *)

(** Whether JCN takes the branch, from the condition code and state. *)
Definition jcn_condition (s : Intel4004State) (cond : nat) : bool :=
  let c1 := cond / 8 in
  let c2 := (cond / 4) mod 2 in
  let c3 := (cond / 2) mod 2 in
  let c4 := cond mod 2 in
  let base := orb (andb (aval s =? 0) (c2 =? 1))
                  (orb (andb (carry s) (c3 =? 1))
                       (andb (negb (test_pin s)) (c4 =? 1))) in
  if c1 =? 1 then negb base else base.

(** Named condition codes per the Intel 4004 manual. *)
Definition JCN_JNT : nat := 1.   (* Jump if TEST = 0 *)
Definition JCN_JC  : nat := 2.   (* Jump if Carry = 1 *)
Definition JCN_JZ  : nat := 4.   (* Jump if Acc = 0 *)
Definition JCN_JT  : nat := 9.   (* Jump if TEST = 1 *)
Definition JCN_JNC : nat := 10.  (* Jump if Carry = 0 *)
Definition JCN_JNZ : nat := 12.  (* Jump if Acc <> 0 *)

Lemma jcn_pc_shape : forall s (cond : nibble) (off : byte),
  pc (execute s (JCN cond off)) = adr (pcv s + 2) \/
  pc (execute s (JCN cond off)) = adr (base_for_next2 s + wval off).
Proof.
  intros s cond off. cbn [execute]. cbv zeta.
  case_branches;
    ((left; reflexivity) || (right; reflexivity)).
Qed.

(** JCN branches when jcn_condition is true. *)
Theorem jcn_branch_taken : forall s (cond : nibble) (off : byte),
  jcn_condition s (wval cond) = true ->
  pc (execute s (JCN cond off)) = adr (base_for_next2 s + wval off).
Proof.
  intros s cond off H.
  unfold jcn_condition in H. cbv zeta in H.
  cbn [execute]. cbv zeta.
  destruct (wval cond / 8 =? 1);
    destruct (orb (andb (aval s =? 0) ((wval cond / 4) mod 2 =? 1))
                  (orb (andb (carry s) ((wval cond / 2) mod 2 =? 1))
                       (andb (negb (test_pin s)) (wval cond mod 2 =? 1))));
    cbn [negb] in *; try discriminate H; reflexivity.
Qed.

(** JCN does not branch when jcn_condition is false. *)
Theorem jcn_branch_not_taken : forall s (cond : nibble) (off : byte),
  jcn_condition s (wval cond) = false ->
  pc (execute s (JCN cond off)) = adr (pcv s + 2).
Proof.
  intros s cond off H.
  unfold jcn_condition in H. cbv zeta in H.
  cbn [execute]. cbv zeta.
  destruct (wval cond / 8 =? 1);
    destruct (orb (andb (aval s =? 0) ((wval cond / 4) mod 2 =? 1))
                  (orb (andb (carry s) ((wval cond / 2) mod 2 =? 1))
                       (andb (negb (test_pin s)) (wval cond mod 2 =? 1))));
    cbn [negb] in *; try discriminate H; reflexivity.
Qed.

(** The named condition codes decode to their documented predicates. *)
Theorem jcn_jz_semantics : forall s,
  jcn_condition s JCN_JZ = (aval s =? 0).
Proof.
  intros s. unfold jcn_condition, JCN_JZ. cbn.
  destruct (carry s); destruct (test_pin s); destruct (aval s =? 0); reflexivity.
Qed.

Theorem jcn_jnz_semantics : forall s,
  jcn_condition s JCN_JNZ = negb (aval s =? 0).
Proof.
  intros s. unfold jcn_condition, JCN_JNZ. cbn.
  destruct (carry s); destruct (test_pin s); destruct (aval s =? 0); reflexivity.
Qed.

Theorem jcn_jc_semantics : forall s,
  jcn_condition s JCN_JC = carry s.
Proof.
  intros s. unfold jcn_condition, JCN_JC. cbn.
  destruct (carry s); destruct (test_pin s); destruct (aval s =? 0); reflexivity.
Qed.

Theorem jcn_jnc_semantics : forall s,
  jcn_condition s JCN_JNC = negb (carry s).
Proof.
  intros s. unfold jcn_condition, JCN_JNC. cbn.
  destruct (carry s); destruct (test_pin s); destruct (aval s =? 0); reflexivity.
Qed.

Theorem jcn_jnt_semantics : forall s,
  jcn_condition s JCN_JNT = negb (test_pin s).
Proof.
  intros s. unfold jcn_condition, JCN_JNT. cbn.
  destruct (carry s); destruct (test_pin s); destruct (aval s =? 0); reflexivity.
Qed.

Theorem jcn_jt_semantics : forall s,
  jcn_condition s JCN_JT = test_pin s.
Proof.
  intros s. unfold jcn_condition, JCN_JT. cbn.
  destruct (carry s); destruct (test_pin s); destruct (aval s =? 0); reflexivity.
Qed.

(** jcn_condition decides the branch. *)
Theorem jcn_condition_decides_branch : forall s (cond : nibble) (off : byte),
  (jcn_condition s (wval cond) = true /\
   pc (execute s (JCN cond off)) = adr (base_for_next2 s + wval off)) \/
  (jcn_condition s (wval cond) = false /\
   pc (execute s (JCN cond off)) = adr (pcv s + 2)).
Proof.
  intros s cond off.
  destruct (jcn_condition s (wval cond)) eqn:E.
  - left. split. reflexivity. apply jcn_branch_taken. exact E.
  - right. split. reflexivity. apply jcn_branch_not_taken. exact E.
Qed.

(* ==================== TEST Pin Modeling ==================== *)

Definition set_test_pin (s : Intel4004State) (v : bool) : Intel4004State :=
  with_test v s.

Lemma set_test_pin_preserves_WF : forall s v,
  WF s -> WF (set_test_pin s v).
Proof.
  intros s v HWF. destruct_WF HWF.
  unfold WF, set_test_pin. exec_simpl.
  repeat split; assumption.
Qed.

Lemma set_test_pin_value : forall s v, test_pin (set_test_pin s v) = v.
Proof. reflexivity. Qed.

Lemma set_test_pin_preserves_acc : forall s v, acc (set_test_pin s v) = acc s.
Proof. reflexivity. Qed.

Lemma set_test_pin_preserves_pc : forall s v, pc (set_test_pin s v) = pc s.
Proof. reflexivity. Qed.

Lemma set_test_pin_preserves_regs : forall s v, regs (set_test_pin s v) = regs s.
Proof. reflexivity. Qed.

Lemma execute_preserves_test_pin : forall s i,
  test_pin (execute s i) = test_pin s.
Proof.
  intros s i.
  destruct i; cbn [execute]; case_branches; reflexivity.
Qed.

Theorem test_pin_external_input : forall s1 s2 i,
  test_pin s1 = test_pin s2 ->
  test_pin (execute s1 i) = test_pin (execute s2 i).
Proof.
  intros s1 s2 i Heq.
  rewrite !execute_preserves_test_pin. exact Heq.
Qed.

Theorem jcn_test_pin_determines_branch : forall s (off : byte),
  (test_pin s = false ->
     pc (execute s (JCN (nib JCN_JNT) off)) = adr (base_for_next2 s + wval off)) /\
  (test_pin s = true ->
     pc (execute s (JCN (nib JCN_JNT) off)) = adr (pcv s + 2)) /\
  (test_pin s = true ->
     pc (execute s (JCN (nib JCN_JT) off)) = adr (base_for_next2 s + wval off)) /\
  (test_pin s = false ->
     pc (execute s (JCN (nib JCN_JT) off)) = adr (pcv s + 2)).
Proof.
  intros s off.
  repeat split; intros Htest.
  - apply jcn_branch_taken.
    rewrite (nib_val_small JCN_JNT) by (unfold JCN_JNT; lia).
    rewrite jcn_jnt_semantics, Htest. reflexivity.
  - apply jcn_branch_not_taken.
    rewrite (nib_val_small JCN_JNT) by (unfold JCN_JNT; lia).
    rewrite jcn_jnt_semantics, Htest. reflexivity.
  - apply jcn_branch_taken.
    rewrite (nib_val_small JCN_JT) by (unfold JCN_JT; lia).
    rewrite jcn_jt_semantics. exact Htest.
  - apply jcn_branch_not_taken.
    rewrite (nib_val_small JCN_JT) by (unfold JCN_JT; lia).
    rewrite jcn_jt_semantics, Htest. reflexivity.
Qed.

(* ==================== RAM Bank Selection (DCL) ==================== *)

(** DCL latches the accumulator's low three bits as the CM-RAM code. *)
Lemma dcl_sets_cm_code : forall s,
  cm_code (execute s DCL) = w3 (aval s).
Proof. reflexivity. Qed.

Lemma dcl_preserves_acc : forall s, acc (execute s DCL) = acc s.
Proof. reflexivity. Qed.

Lemma dcl_preserves_regs : forall s, regs (execute s DCL) = regs s.
Proof. reflexivity. Qed.

Lemma dcl_preserves_carry : forall s, carry (execute s DCL) = carry s.
Proof. reflexivity. Qed.

Lemma dcl_preserves_ram : forall s, ram_sys (execute s DCL) = ram_sys s.
Proof. reflexivity. Qed.

(** The line set selected after DCL, as a function of the accumulator. *)
Theorem dcl_acc_determines_lines : forall s,
  sel_lines (execute s DCL) = dcl_lines (w3 (aval s)).
Proof. reflexivity. Qed.

(** The single-line codes select exactly one bank each. *)
Theorem dcl_acc_determines_bank : forall s,
  (aval s = 0 -> sel_lines (execute s DCL) = [0]) /\
  (aval s = 1 -> sel_lines (execute s DCL) = [1]) /\
  (aval s = 2 -> sel_lines (execute s DCL) = [2]) /\
  (aval s = 4 -> sel_lines (execute s DCL) = [3]).
Proof.
  intros s.
  repeat split; intro Ha;
    rewrite dcl_acc_determines_lines, Ha; reflexivity.
Qed.

(** The multi-line codes select several banks at once. *)
Theorem dcl_multi_line_codes : forall s,
  (aval s = 3 -> sel_lines (execute s DCL) = [1; 2]) /\
  (aval s = 5 -> sel_lines (execute s DCL) = [1; 3]) /\
  (aval s = 6 -> sel_lines (execute s DCL) = [2; 3]) /\
  (aval s = 7 -> sel_lines (execute s DCL) = [1; 2; 3]).
Proof.
  intros s.
  repeat split; intro Ha;
    rewrite dcl_acc_determines_lines, Ha; reflexivity.
Qed.

(** Any CM code is reachable while preserving RAM contents. *)
Theorem bank_selection_complete : forall s (c : word3),
  WF s ->
  exists s', WF s' /\ cm_code s' = c /\ ram_sys s' = ram_sys s.
Proof.
  intros s c HWF.
  exists (with_cm c s).
  split; [| split; reflexivity].
  destruct_WF HWF. unfold WF. exec_simpl.
  repeat split; assumption.
Qed.

(* ==================== Multi-bank DCL write semantics ==================== *)

(* The default machine's WRM writes every bank the DCL latch addresses,
   including under the multi-line codes 3, 5, 6, 7.  These theorems state
   that directly against execute. *)

(** The line set is bounded by the bank count of a well-formed system. *)
Lemma sel_lines_bounded : forall s,
  WF s -> Forall (fun b => b < length (ram_sys s)) (sel_lines s).
Proof.
  intros s HWF. destruct_WF HWF.
  rewrite HsysLen. exact (dcl_lines_bounded (cm_code s)).
Qed.

Lemma sel_lines_nonempty : forall s, sel_lines s <> [].
Proof. intro s. apply dcl_lines_nonempty. Qed.

Lemma sel_lines_NoDup : forall s, NoDup (sel_lines s).
Proof. intro s. apply dcl_lines_NoDup. Qed.

(** Headline: a WRM reaches every bank the DCL code addresses. *)
Theorem dcl_write_reaches_all_selected : forall s b,
  WF s ->
  In b (sel_lines s) ->
  read_main_bank (ram_sys (execute s WRM)) (sel_ram s) b = acc s.
Proof.
  intros s b HWF Hin.
  replace (ram_sys (execute s WRM))
    with (write_main_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s))
    by reflexivity.
  apply write_main_banks_hit.
  - apply sel_lines_NoDup.
  - exact Hin.
  - apply sel_lines_bounded. exact HWF.
  - destruct_WF HWF. exact HsysFor.
Qed.

(** Unselected banks are untouched by the write. *)
Theorem dcl_write_frames_unselected : forall s b,
  ~ In b (sel_lines s) ->
  read_main_bank (ram_sys (execute s WRM)) (sel_ram s) b
  = read_main_bank (ram_sys s) (sel_ram s) b.
Proof.
  intros s b Hnin.
  replace (ram_sys (execute s WRM))
    with (write_main_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s))
    by reflexivity.
  apply read_after_main_banks_other. exact Hnin.
Qed.

(** On a single-line code, WRM writes exactly one bank. *)
Theorem dcl_single_line_writes_one_bank : forall s,
  WF s ->
  (wval (cm_code s) = 0 \/ wval (cm_code s) = 1 \/
   wval (cm_code s) = 2 \/ wval (cm_code s) = 4) ->
  read_main_bank (ram_sys (execute s WRM)) (sel_ram s) (dcl_bank (cm_code s))
    = acc s /\
  (forall b, b <> dcl_bank (cm_code s) ->
     read_main_bank (ram_sys (execute s WRM)) (sel_ram s) b
     = read_main_bank (ram_sys s) (sel_ram s) b).
Proof.
  intros s HWF Hsingle.
  assert (Hlines : sel_lines s = [dcl_bank (cm_code s)]).
  { unfold sel_lines. apply dcl_lines_single. exact Hsingle. }
  split.
  - apply dcl_write_reaches_all_selected; [exact HWF |].
    rewrite Hlines. left. reflexivity.
  - intros b Hne.
    apply dcl_write_frames_unselected.
    rewrite Hlines. intros [Heq | []]. congruence.
Qed.

(** After a WRM, the multi-bank read is defined (the selected banks are
    unanimous) and returns the written value. *)
Theorem dcl_multiwrite_read_defined : forall s,
  WF s ->
  ram_read_main_opt (execute s WRM) = Some (acc s).
Proof.
  intros s HWF.
  unfold ram_read_main_opt.
  replace (sel_lines (execute s WRM)) with (sel_lines s) by reflexivity.
  replace (sel_ram (execute s WRM)) with (sel_ram s) by reflexivity.
  apply agree_read_all.
  - intro Hmap. apply map_eq_nil in Hmap.
    exact (sel_lines_nonempty s Hmap).
  - intros x Hx. apply in_map_iff in Hx.
    destruct Hx as (b & <- & Hb).
    apply dcl_write_reaches_all_selected; assumption.
Qed.

(** RDM after WRM reads back the accumulator, at any DCL code. *)
Theorem wrm_then_rdm_reads_back : forall s,
  WF s ->
  acc (execute (execute s WRM) RDM) = acc s.
Proof.
  intros s HWF.
  replace (acc (execute (execute s WRM) RDM))
    with (ram_read_main (execute s WRM)) by reflexivity.
  unfold ram_read_main.
  rewrite (dcl_multiwrite_read_defined s HWF).
  reflexivity.
Qed.

(** The single-line read is always defined and reads the selected bank. *)
Theorem dcl_read_single_line : forall s,
  (wval (cm_code s) = 0 \/ wval (cm_code s) = 1 \/
   wval (cm_code s) = 2 \/ wval (cm_code s) = 4) ->
  ram_read_main_opt s
  = Some (read_main_bank (ram_sys s) (sel_ram s) (dcl_bank (cm_code s))).
Proof.
  intros s Hsingle.
  unfold ram_read_main_opt, sel_lines.
  rewrite (dcl_lines_single _ Hsingle).
  reflexivity.
Qed.

(* ==================== Multi-bank WMP port writes ==================== *)

(* WMP drives the selected chip's output port in every bank the DCL code
   addresses.  4002 ports are write-only at the ISA level (no instruction
   reads them back), so these are the port-path analogues of the WRM
   theorems, observed through the state. *)

Theorem wmp_writes_selected_ports : forall s b,
  WF s ->
  In b (sel_lines s) ->
  read_port_bank (ram_sys (execute s WMP)) (sel_ram s) b = acc s.
Proof.
  intros s b HWF Hin.
  replace (ram_sys (execute s WMP))
    with (write_port_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s))
    by reflexivity.
  apply write_port_banks_hit.
  - apply sel_lines_NoDup.
  - exact Hin.
  - apply sel_lines_bounded. exact HWF.
  - destruct_WF HWF. exact HsysFor.
Qed.

Theorem wmp_frames_unselected_ports : forall s b,
  ~ In b (sel_lines s) ->
  read_port_bank (ram_sys (execute s WMP)) (sel_ram s) b
  = read_port_bank (ram_sys s) (sel_ram s) b.
Proof.
  intros s b Hnin.
  replace (ram_sys (execute s WMP))
    with (write_port_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s))
    by reflexivity.
  apply read_after_port_banks_other. exact Hnin.
Qed.

(** WMP touches no character: main and status memory read unchanged at
    every address, selected banks included. *)
Theorem wmp_preserves_characters : forall s b c r i,
  WF s ->
  get_main (get_regRAM (get_chip (get_bank (execute s WMP) b) c) r) i
  = get_main (get_regRAM (get_chip (get_bank s b) c) r) i /\
  get_stat (get_regRAM (get_chip (get_bank (execute s WMP) b) c) r) i
  = get_stat (get_regRAM (get_chip (get_bank s b) c) r) i.
Proof.
  intros s b c r i HWF.
  assert (Hcr : chip_regs (get_chip (get_bank (execute s WMP) b) c)
                = chip_regs (get_chip (get_bank s b) c)).
  { unfold get_bank.
    replace (ram_sys (execute s WMP))
      with (write_port_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s))
      by reflexivity.
    apply write_port_banks_chip_regs.
    destruct_WF HWF. exact HsysFor. }
  unfold get_regRAM. rewrite Hcr. split; reflexivity.
Qed.

(* ==================== Status writes read back (WR0-3 / RD0-3) ======== *)

(** The four status characters as indexed instruction families. *)
Definition WRs (idx : nat) : Instruction :=
  match idx with 0 => WR0 | 1 => WR1 | 2 => WR2 | _ => WR3 end.

Definition RDs (idx : nat) : Instruction :=
  match idx with 0 => RD0 | 1 => RD1 | 2 => RD2 | _ => RD3 end.

(** RDs idx loads status character idx into the accumulator. *)
Lemma rds_reads_stat : forall s idx,
  idx < 4 ->
  acc (execute s (RDs idx)) = ram_read_stat s idx.
Proof.
  intros s idx Hidx.
  destruct idx as [|[|[|[|k]]]]; try lia; reflexivity.
Qed.

(** The raw status write leaves the selected banks unanimous at its index. *)
Lemma stat_write_read_defined : forall s idx,
  idx < 4 ->
  WF s ->
  agree_read (map (read_stat_bank
      (write_stat_banks (ram_sys s) (sel_ram s) idx (sel_lines s) (acc s))
      (sel_ram s) idx) (sel_lines s)) = Some (acc s).
Proof.
  intros s idx Hidx HWF.
  apply agree_read_all.
  - intro Hmap. apply map_eq_nil in Hmap.
    exact (sel_lines_nonempty s Hmap).
  - intros x Hx. apply in_map_iff in Hx.
    destruct Hx as (b & <- & Hb).
    apply write_stat_banks_hit; try assumption.
    + apply sel_lines_NoDup.
    + apply sel_lines_bounded. exact HWF.
    + destruct_WF HWF. exact HsysFor.
Qed.

(** After WRs idx, the status read at idx is defined and returns the
    written value, at any DCL code. *)
Theorem wrs_write_defined : forall s idx,
  idx < 4 ->
  WF s ->
  ram_read_stat_opt (execute s (WRs idx)) idx = Some (acc s).
Proof.
  intros s idx Hidx HWF.
  destruct idx as [|[|[|[|k]]]]; try lia; cbn [WRs].
  - exact (stat_write_read_defined s 0 ltac:(lia) HWF).
  - exact (stat_write_read_defined s 1 ltac:(lia) HWF).
  - exact (stat_write_read_defined s 2 ltac:(lia) HWF).
  - exact (stat_write_read_defined s 3 ltac:(lia) HWF).
Qed.

(** RDs after WRs reads back the accumulator, at any DCL code. *)
Theorem wrs_then_rds_reads_back : forall s idx,
  idx < 4 ->
  WF s ->
  acc (execute (execute s (WRs idx)) (RDs idx)) = acc s.
Proof.
  intros s idx Hidx HWF.
  rewrite rds_reads_stat by exact Hidx.
  unfold ram_read_stat.
  rewrite (wrs_write_defined s idx Hidx HWF).
  reflexivity.
Qed.

(* ==================== Memory-operand arithmetic ==================== *)

(** ADM and SBM compute the ALU functions of ADD and SUB with the selected
    RAM character as the operand. *)
Theorem adm_computes_sum : forall s,
  aval (execute s ADM) = (aval s + wval (ram_read_main s) + cbit s) mod 16 /\
  carry (execute s ADM) = (16 <=? aval s + wval (ram_read_main s) + cbit s).
Proof.
  intros s. split; exec_simpl.
  - apply nib_val.
  - reflexivity.
Qed.

Theorem sbm_computes_difference : forall s,
  aval (execute s SBM)
  = (aval s + 16 - wval (ram_read_main s) - cbit s) mod 16 /\
  carry (execute s SBM)
  = (16 <=? aval s + 16 - wval (ram_read_main s) - cbit s).
Proof.
  intros s. split; exec_simpl.
  - apply nib_val.
  - reflexivity.
Qed.

(* ==================== ROM I/O Port Operations ==================== *)

Lemma src_sets_rom_selection : forall s (r : nibble),
  sel_rom (execute s (SRC r)) = nib (get_reg_pair s (wval r) / 16).
Proof. intros s r. reflexivity. Qed.

Lemma wrr_writes_to_selected_port : forall s,
  WF s ->
  nth (wval (sel_rom s)) (out_ports (execute s WRR)) (nib 0) = acc s.
Proof.
  intros s HWF. destruct_WF HWF.
  exec_simpl.
  apply nth_update_nth_eq.
  rewrite HoutLen. apply nib_lt16.
Qed.

Lemma rdr_reads_selected_port : forall s,
  acc (execute s RDR)
  = if nth (wval (sel_rom s)) (port_dirs s) true
    then nth (wval (sel_rom s)) (out_ports s) (nib 0)
    else nth (wval (sel_rom s)) (in_ports s) (nib 0).
Proof. intros s. reflexivity. Qed.

Lemma wrr_preserves_other_ports : forall s n,
  n <> wval (sel_rom s) ->
  nth n (out_ports (execute s WRR)) (nib 0) = nth n (out_ports s) (nib 0).
Proof.
  intros s n Hneq. exec_simpl.
  apply nth_update_nth_neq. exact Hneq.
Qed.

Lemma wrr_preserves_in_ports : forall s,
  in_ports (execute s WRR) = in_ports s.
Proof. reflexivity. Qed.

(** WRR-then-RDR reads back the accumulator on an output-configured port.
    On an input port RDR reads the pins instead (see
    rdr_reads_driven_input and fidelity.v). *)
Theorem wrr_rdr_roundtrip : forall s,
  WF s ->
  nth (wval (sel_rom s)) (port_dirs s) true = true ->
  acc (execute (execute s WRR) RDR) = acc s.
Proof.
  intros s HWF Hdir.
  rewrite rdr_reads_selected_port.
  replace (sel_rom (execute s WRR)) with (sel_rom s) by reflexivity.
  replace (port_dirs (execute s WRR)) with (port_dirs s) by reflexivity.
  rewrite Hdir.
  apply wrr_writes_to_selected_port. exact HWF.
Qed.

Lemma src_wrr_updates_rom_port : forall s (r : nibble),
  WF s ->
  nth (get_reg_pair s (wval r) / 16)
      (out_ports (execute (execute s (SRC r)) WRR)) (nib 0)
  = acc s.
Proof.
  intros s r Hwf.
  assert (HWF1 : WF (execute s (SRC r))) by (apply execute_preserves_WF; exact Hwf).
  assert (Hsel : wval (sel_rom (execute s (SRC r))) = get_reg_pair s (wval r) / 16).
  { exec_simpl. cbv zeta. rewrite nib_val. apply Nat.mod_small.
    apply div16_byte_bound. apply get_reg_pair_lt256. }
  rewrite <- Hsel.
  replace (acc s) with (acc (execute s (SRC r))) by reflexivity.
  apply wrr_writes_to_selected_port. exact HWF1.
Qed.

(* --- Determinism & PC-shape of step --- *)

Theorem step_deterministic : forall s s1 s2,
  s1 = step s -> s2 = step s -> s1 = s2.
Proof. congruence. Qed.

(** PC forms of the simple instructions, definitionally. *)
Lemma pc_shape_nop : forall s, pc (execute s NOP) = adr (pcv s + 1).
Proof. reflexivity. Qed.

Lemma pc_shape_jun : forall s a, pc (execute s (JUN a)) = a.
Proof. reflexivity. Qed.

Lemma pc_shape_jms : forall s a, pc (execute s (JMS a)) = a.
Proof. reflexivity. Qed.

Lemma pc_shape_fim : forall s r d, pc (execute s (FIM r d)) = adr (pcv s + 2).
Proof. reflexivity. Qed.

Lemma pc_shape_bbl : forall s d, pc (execute s (BBL d)) = stk1 s.
Proof. reflexivity. Qed.

Lemma pc_shape_jin : forall s (r : nibble),
  pc (execute s (JIN r))
  = adr (page_of (wval (pc_inc1 s)) * 256 + get_reg_pair s (wval r)).
Proof. reflexivity. Qed.

Lemma page_base_eq_page_times_256 : forall a,
  page_base a = page_of a * 256.
Proof. reflexivity. Qed.

(* ==================== Page Boundary Crossing Behavior ==================== *)

Lemma page_of_bound : forall p, p < 4096 -> page_of p < 16.
Proof.
  intros p Hp. unfold page_of.
  apply Nat.Div0.div_lt_upper_bound. lia.
Qed.

Lemma page_offset_bound_strict : forall p, p mod 256 < 256.
Proof. intros p. apply Nat.mod_upper_bound. lia. Qed.

Lemma page_decomposition : forall p,
  p = page_of p * 256 + p mod 256.
Proof.
  intros p. unfold page_of.
  pose proof (Nat.div_mod p 256 ltac:(lia)). lia.
Qed.

Lemma page_base_offset_decomp : forall p,
  p = page_base p + p mod 256.
Proof.
  intros p. unfold page_base. apply page_decomposition.
Qed.

Lemma same_page_within_offset : forall p off,
  off < 256 ->
  p mod 256 + off < 256 ->
  page_of (p + off) = page_of p.
Proof.
  intros p off Hoff Hno_overflow.
  unfold page_of.
  pose proof (Nat.div_mod p 256 ltac:(lia)) as Hdm.
  assert (Hsum : p + off = p / 256 * 256 + (p mod 256 + off)) by lia.
  rewrite Hsum.
  rewrite Nat.div_add_l by lia.
  rewrite (Nat.div_small (p mod 256 + off) 256) by exact Hno_overflow.
  lia.
Qed.

Lemma page_boundary_cross : forall p,
  p < 4096 ->
  p mod 256 = 255 ->
  page_of ((p + 1) mod 4096) = (page_of p + 1) mod 16.
Proof.
  intros p Hp Hmod.
  unfold page_of.
  pose proof (Nat.div_mod p 256 ltac:(lia)) as Hdm.
  assert (Hpage : p / 256 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hp1 : p + 1 = (p / 256 + 1) * 256) by lia.
  destruct (Nat.eq_dec (p / 256) 15) as [H15 | Hnot15].
  - rewrite H15 in Hp1.
    assert (Hp1' : p + 1 = 4096) by lia.
    rewrite Hp1'.
    rewrite Nat.Div0.mod_same. rewrite H15.
    reflexivity.
  - assert (Hlt : p / 256 + 1 < 16) by lia.
    rewrite Hp1.
    rewrite Nat.mod_small by lia.
    rewrite Nat.div_mul by lia.
    rewrite (Nat.mod_small (p / 256 + 1) 16) by lia.
    reflexivity.
Qed.

Lemma page_boundary_same : forall p,
  p < 4096 ->
  p mod 256 < 255 ->
  page_of ((p + 1) mod 4096) = page_of p.
Proof.
  intros p Hp Hmod.
  assert (Hp1 : p + 1 < 4096 \/ p + 1 = 4096) by lia.
  destruct Hp1 as [Hlt | Heq].
  - rewrite Nat.mod_small by lia.
    apply same_page_within_offset; [lia | lia].
  - exfalso.
    assert (p = 4095) by lia. subst p.
    cbn in Hmod. lia.
Qed.

Lemma page_of_inc2 : forall p,
  p < 4096 ->
  p mod 256 < 254 ->
  page_of ((p + 2) mod 4096) = page_of p.
Proof.
  intros p Hp Hmod.
  assert (Hp2 : p + 2 < 4096 \/ p + 2 >= 4096) by lia.
  destruct Hp2 as [Hlt | Hge].
  - rewrite Nat.mod_small by lia.
    apply same_page_within_offset; [lia | lia].
  - exfalso.
    pose proof (Nat.div_mod p 256 ltac:(lia)) as Hdm.
    assert (p / 256 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
    lia.
Qed.

Lemma pc_inc2_page_cross_characterization : forall s,
  (pcv s mod 256 < 254 ->
     page_of (wval (pc_inc2 s)) = page_of (pcv s)) /\
  (pcv s mod 256 = 254 ->
     page_of (wval (pc_inc2 s)) = (page_of (pcv s) + 1) mod 16) /\
  (pcv s mod 256 = 255 ->
     page_of (wval (pc_inc2 s)) = (page_of (pcv s) + 1) mod 16).
Proof.
  intros s.
  pose proof (pcv_lt4096 s) as Hpc.
  unfold pc_inc2. rewrite adr_val.
  split; [| split]; intro Hmod.
  - apply page_of_inc2; assumption.
  - unfold page_of.
    pose proof (Nat.div_mod (pcv s) 256 ltac:(lia)) as Hdm.
    assert (Hpage : pcv s / 256 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hp2 : pcv s + 2 = (pcv s / 256 + 1) * 256) by lia.
    destruct (Nat.eq_dec (pcv s / 256) 15) as [H15 | Hnot15].
    + rewrite H15 in Hp2.
      assert (Hp2' : pcv s + 2 = 4096) by lia.
      rewrite Hp2'.
      rewrite Nat.Div0.mod_same. rewrite H15. reflexivity.
    + rewrite Hp2.
      rewrite Nat.mod_small by lia.
      rewrite Nat.div_mul by lia.
      rewrite (Nat.mod_small (pcv s / 256 + 1) 16) by lia.
      reflexivity.
  - unfold page_of.
    pose proof (Nat.div_mod (pcv s) 256 ltac:(lia)) as Hdm.
    assert (Hpage : pcv s / 256 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (Hp2 : pcv s + 2 = (pcv s / 256 + 1) * 256 + 1) by lia.
    destruct (Nat.eq_dec (pcv s / 256) 15) as [H15 | Hnot15].
    + rewrite H15 in Hp2.
      assert (Hp2' : pcv s + 2 = 4097) by lia.
      rewrite Hp2'.
      change (4097 mod 4096) with 1.
      rewrite H15. reflexivity.
    + rewrite Hp2.
      rewrite Nat.mod_small by lia.
      rewrite Nat.div_add_l by lia.
      rewrite (Nat.div_small 1 256) by lia.
      rewrite Nat.add_0_r.
      rewrite (Nat.mod_small (pcv s / 256 + 1) 16) by lia.
      reflexivity.
Qed.

(** page_base is idempotent. *)
Lemma page_base_idempotent : forall p,
  page_base (page_base p) = page_base p.
Proof.
  intros p.
  unfold page_base, page_of.
  rewrite Nat.div_mul by lia.
  reflexivity.
Qed.

Lemma page_base_plus_offset_same_page : forall p off,
  off < 256 ->
  page_of (page_base p + off) = page_of p.
Proof.
  intros p off Hoff.
  unfold page_base, page_of.
  rewrite Nat.div_add_l by lia.
  rewrite (Nat.div_small off 256) by exact Hoff.
  lia.
Qed.

Lemma page_base_plus_offset_bound : forall p off,
  p < 4096 ->
  off < 256 ->
  page_base p + off < 4096.
Proof.
  intros p off Hp Hoff.
  unfold page_base, page_of.
  assert (p / 256 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
  lia.
Qed.

(** JCN/ISZ branch targets stay within the page of pc+2. *)
Lemma branch_target_in_page : forall s (off : byte),
  page_of (wval (adr (base_for_next2 s + wval off)))
  = page_of (wval (pc_inc2 s)).
Proof.
  intros s off.
  unfold base_for_next2.
  pose proof (byte_lt256 off) as Hoff.
  assert (Hpc2 : wval (pc_inc2 s) < 4096) by apply addr12_lt4096.
  rewrite adr_val.
  rewrite Nat.mod_small
    by (apply page_base_plus_offset_bound; assumption).
  apply page_base_plus_offset_same_page. exact Hoff.
Qed.

Theorem jcn_branch_stays_in_page : forall s (cond : nibble) (off : byte),
  jcn_condition s (wval cond) = true ->
  page_of (wval (pc (execute s (JCN cond off)))) = page_of (wval (pc_inc2 s)).
Proof.
  intros s cond off Hcond.
  rewrite jcn_branch_taken by exact Hcond.
  apply branch_target_in_page.
Qed.

Theorem isz_branch_stays_in_page : forall s (r : nibble) (off : byte),
  isz_loops s (wval r) = true ->
  page_of (wval (pc (execute s (ISZ r off)))) = page_of (wval (pc_inc2 s)).
Proof.
  intros s r off Hloop.
  rewrite isz_branch_taken by exact Hloop.
  apply branch_target_in_page.
Qed.

Theorem jin_stays_in_page : forall s (r : nibble),
  page_of (wval (pc (execute s (JIN r)))) = page_of (wval (pc_inc1 s)).
Proof.
  intros s r.
  rewrite pc_shape_jin.
  pose proof (get_reg_pair_lt256 s (wval r)) as Hpair.
  pose proof (addr12_lt4096 (pc_inc1 s)) as Hpc1.
  assert (Hpage : page_of (wval (pc_inc1 s)) < 16)
    by (apply page_of_bound; exact Hpc1).
  rewrite adr_val.
  rewrite Nat.mod_small by lia.
  unfold page_of.
  rewrite Nat.div_add_l by lia.
  rewrite (Nat.div_small (get_reg_pair s (wval r)) 256) by exact Hpair.
  lia.
Qed.

(** Full address space wrap: 4096 wraps to 0. *)
Lemma addr_space_wrap : forall n, adr (n + 4096) = adr n.
Proof.
  intros n.
  apply addr12_eq.
  rewrite !adr_val.
  replace (n + 4096) with (n + 1 * 4096) by lia.
  rewrite Nat.Div0.mod_add.
  reflexivity.
Qed.

(** Classifies whether an instruction is a jump/branch. *)
Definition is_jump (i : Instruction) : bool :=
  match i with
  | JCN _ _ | JUN _ | JMS _ | JIN _ | BBL _ | ISZ _ _ => true
  | _ => false
  end.

(** The five PC forms any instruction can produce: sequential advance by
    one or two, a page-relative target, or (for jump instructions only) an
    arbitrary 12-bit target. *)
Lemma execute_pc_shape : forall s i,
  pc (execute s i) = adr (pcv s + 1) \/
  pc (execute s i) = adr (pcv s + 2) \/
  (exists off, off < 256 /\ pc (execute s i) = adr (base_for_next1 s + off)) \/
  (exists off, off < 256 /\ pc (execute s i) = adr (base_for_next2 s + off)) \/
  (is_jump i = true /\ exists a : addr12, pc (execute s i) = a).
Proof.
  intros s i.
  destruct i; cbn [execute is_jump]; cbv zeta; case_branches;
    first
      [ left; reflexivity
      | right; left; reflexivity
      | right; right; left;
        eexists; split;
          [ apply get_reg_pair_lt256
          | unfold base_for_next1, page_base; reflexivity ]
      | right; right; right; left;
        eexists; split;
          [ apply byte_lt256
          | unfold base_for_next2, page_base; reflexivity ]
      | right; right; right; right; split;
          [ reflexivity | eexists; reflexivity ] ].
Qed.

Theorem step_pc_shape : forall s,
  pc (step s) = adr (pcv s + 1) \/
  pc (step s) = adr (pcv s + 2) \/
  (exists off, off < 256 /\ pc (step s) = adr (base_for_next1 s + off)) \/
  (exists off, off < 256 /\ pc (step s) = adr (base_for_next2 s + off)) \/
  (exists a : addr12, pc (step s) = a).
Proof.
  intros s. unfold step.
  destruct (execute_pc_shape s
      (decode (fetch_byte s (pcv s)) (fetch_byte s ((pcv s + 1) mod 4096))))
    as [H|[H|[H|[H|[_ H]]]]].
  - left. exact H.
  - right. left. exact H.
  - right. right. left. exact H.
  - right. right. right. left. exact H.
  - right. right. right. right. exact H.
Qed.

Corollary pc_monotonic_non_jump : forall s i,
  is_jump i = false ->
  pc (execute s i) = adr (pcv s + 1) \/
  pc (execute s i) = adr (pcv s + 2).
Proof.
  intros s i Hjump.
  destruct i; cbn [is_jump] in Hjump; try discriminate Hjump;
    cbn [execute]; case_branches;
    first [left; reflexivity | right; reflexivity].
Qed.

(* --- Frames (no unintended writes) --- *)

(** Classifies instructions that write to the register file. *)
Definition writes_regs (i : Instruction) : bool :=
  match i with
  | XCH _ | INC _ | FIM _ _ | FIN _ | ISZ _ _ => true
  | _ => false
  end.

(** Classifies instructions that write to RAM. *)
Definition writes_ram (i : Instruction) : bool :=
  match i with
  | WRM | WMP | WR0 | WR1 | WR2 | WR3 => true
  | _ => false
  end.

(** Classifies instructions that write to the accumulator. *)
Definition writes_acc (i : Instruction) : bool :=
  match i with
  | LDM _ | LD _ | ADD _ | SUB _ | INC _ | XCH _ | BBL _
  | SBM | RDM | RDR | ADM | RD0 | RD1 | RD2 | RD3
  | CLB | CMA | IAC | DAC | RAL | RAR | TCC | TCS | DAA | KBP => true
  | _ => false
  end.

Lemma execute_regs_frame : forall s i,
  writes_regs i = false ->
  regs (execute s i) = regs s.
Proof.
  intros s i H.
  destruct i; cbn [writes_regs] in H; try discriminate H;
    cbn [execute]; case_branches; reflexivity.
Qed.

Lemma execute_ram_frame : forall s i,
  writes_ram i = false ->
  ram_sys (execute s i) = ram_sys s.
Proof.
  intros s i H.
  destruct i; cbn [writes_ram] in H; try discriminate H;
    cbn [execute]; case_branches; reflexivity.
Qed.

Lemma execute_acc_frame : forall s i,
  writes_acc i = false ->
  acc (execute s i) = acc s.
Proof.
  intros s i H.
  destruct i; cbn [writes_acc] in H; try discriminate H;
    cbn [execute]; case_branches; reflexivity.
Qed.

(** Only WPM writes ROM; every other instruction leaves it unchanged. *)
Lemma execute_rom_frame : forall s i, i <> WPM -> rom (execute s i) = rom s.
Proof.
  intros s i H.
  destruct i; try congruence;
    cbn [execute]; case_branches; reflexivity.
Qed.

(** Only JMS and BBL move the saved rows of the address ring. *)
Definition writes_stack (i : Instruction) : bool :=
  match i with
  | JMS _ | BBL _ => true
  | _ => false
  end.

Lemma execute_stack_frame : forall s i,
  writes_stack i = false ->
  stk1 (execute s i) = stk1 s /\
  stk2 (execute s i) = stk2 s /\
  stk3 (execute s i) = stk3 s.
Proof.
  intros s i H.
  destruct i; cbn [writes_stack] in H; try discriminate H;
    cbn [execute]; case_branches; repeat split; reflexivity.
Qed.

(* --- KBP mapping --- *)

Lemma kbp_map_cases : forall s,
  aval (execute s KBP)
  = match aval s with
    | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4 | _ => 15
    end.
Proof.
  intros s. exec_simpl.
  destruct (wval (acc s)) as [|[|[|[|[|[|[|[|[|k]]]]]]]]];
    apply nib_val_small; lia.
Qed.

Lemma kbp_output_valid : forall s, aval (execute s KBP) < 16.
Proof. intros s. apply aval_lt16. Qed.

Lemma kbp_single_bit_correct : forall s,
  (aval s = 0 -> aval (execute s KBP) = 0) /\
  (aval s = 1 -> aval (execute s KBP) = 1) /\
  (aval s = 2 -> aval (execute s KBP) = 2) /\
  (aval s = 4 -> aval (execute s KBP) = 3) /\
  (aval s = 8 -> aval (execute s KBP) = 4).
Proof.
  intros s.
  repeat split; intro H; rewrite kbp_map_cases; rewrite H; reflexivity.
Qed.

Lemma kbp_multi_bit_returns_15 : forall s,
  aval s <> 0 -> aval s <> 1 -> aval s <> 2 -> aval s <> 4 -> aval s <> 8 ->
  aval (execute s KBP) = 15.
Proof.
  intros s H0 H1 H2 H4 H8.
  rewrite kbp_map_cases.
  destruct (aval s) as [|[|[|[|[|[|[|[|[|k]]]]]]]]]; try contradiction; reflexivity.
Qed.

(* ==================== JMS/BBL: the address ring ==================== *)

(** The exact field motion of CALL: the return address enters the first
    saved row, the older rows shift back, and the oldest is discarded. *)
Theorem jms_ring_motion : forall s (a : addr12),
  pc (execute s (JMS a)) = a /\
  stk1 (execute s (JMS a)) = adr (pcv s + 2) /\
  stk2 (execute s (JMS a)) = stk1 s /\
  stk3 (execute s (JMS a)) = stk2 s.
Proof. intros s a. repeat split. Qed.

(** A fourth nested call overwrites the oldest saved row. *)
Theorem jms_discards_oldest : forall s (a : addr12),
  stk3 (execute s (JMS a)) = stk2 s.
Proof. reflexivity. Qed.

(** The exact field motion of RET: the first saved row resumes as the PC,
    the rows shift forward, and the vacated current row reappears as the
    stale third row holding the address one past the return (the row was
    incremented during the return's own fetch and abandoned without a
    write-back). *)
Theorem bbl_ring_motion : forall s (d : nibble),
  pc (execute s (BBL d)) = stk1 s /\
  stk1 (execute s (BBL d)) = stk2 s /\
  stk2 (execute s (BBL d)) = stk3 s /\
  stk3 (execute s (BBL d)) = adr (pcv s + 1) /\
  acc (execute s (BBL d)) = d.
Proof. intros s d. repeat split. Qed.

(** JMS then BBL returns to the instruction after the JMS, at any ring
    depth: a full ring discards its oldest row, never the return address
    just pushed. *)
Theorem jms_bbl_roundtrip : forall s (a : addr12) (d : nibble),
  pc (execute (execute s (JMS a)) (BBL d)) = adr (pcv s + 2).
Proof. intros s a d. reflexivity. Qed.

(** Returning past the ring's depth resumes stale rows: from a cleared ring
    (e.g. after RESET), one call followed by two returns lands back at
    address 0, the second return reading a stale zero row. *)
Theorem bbl_underflow_from_reset : forall s (a : addr12) (d1 d2 : nibble),
  let s0 := reset_state s in
  pc (execute (execute (execute s0 (JMS a)) (BBL d1)) (BBL d2)) = adr 0.
Proof. intros s a d1 d2. reflexivity. Qed.

Corollary steps_from_init_WF : forall n, WF (steps n init_state).
Proof.
  intros n. apply steps_preserve_WF. apply init_state_WF.
Qed.

(* ===================================================================== *)
(*                         TIMING MODEL                                  *)
(* ===================================================================== *)

(** Instruction timing in clock periods (8 per machine cycle): one-word
    instructions 8, two-word and FIN 16; JCN and ISZ fixed-time. *)
Definition cycles (i : Instruction) : nat :=
  match i with
  | NOP => 8
  | ADD _ | SUB _ | LD _ | XCH _ | LDM _ | INC _ => 8
  | CLB | CLC | IAC | CMC | CMA | RAL | RAR | TCC | DAC | TCS | STC | DAA | KBP | DCL => 8
  | WRM | WMP | WRR | WPM | WR0 | WR1 | WR2 | WR3 => 8
  | SBM | RDM | RDR | ADM | RD0 | RD1 | RD2 | RD3 => 8
  | BBL _ => 8
  | SRC _ | JIN _ => 8
  | FIM _ _ | FIN _ | JUN _ => 16
  | JMS _ => 16
  | JCN _ _ => 16
  | ISZ _ _ => 16
  end.

Lemma max_cycles_per_instruction : forall i, cycles i <= 16.
Proof. intros i. destruct i; cbn; lia. Qed.

Lemma min_cycles_per_instruction : forall i, 8 <= cycles i.
Proof. intros i. destruct i; cbn; lia. Qed.

Theorem timing_preserves_WF : forall s i,
  WF s ->
  cycles i <= 16 /\ WF (execute s i).
Proof.
  intros s i HWF.
  split.
  - apply max_cycles_per_instruction.
  - apply execute_preserves_WF; assumption.
Qed.

(* ===================================================================== *)
(*         WPM PROM PROGRAMMING (the half-byte 4008/4009 protocol)       *)
(* ===================================================================== *)

(* The default WPM is the hardware's: one 4-bit transfer per instruction,
   assembled by the external latch pair, two WPMs per byte, high half
   first.  The programmer's address and write-enable latches load from the
   CPU's ROM output ports (latch_prom below), or directly at spec level
   (arm_prom). *)

(** Arm the external programmer: address and write-enable. *)
Definition arm_prom (s : Intel4004State) (a : addr12) (e : bool) : Intel4004State :=
  with_prom_enable e (with_prom_addr a s).

Lemma arm_prom_fields : forall s a e,
  prom_addr (arm_prom s a e) = a /\
  prom_enable (arm_prom s a e) = e /\
  prom_latch (arm_prom s a e) = prom_latch s /\
  rom (arm_prom s a e) = rom s /\
  regs (arm_prom s a e) = regs s /\
  acc (arm_prom s a e) = acc s.
Proof. intros. repeat split. Qed.

Lemma arm_prom_WF : forall s a e, WF s -> WF (arm_prom s a e).
Proof.
  intros s a e HWF. destruct_WF HWF.
  unfold WF, arm_prom. exec_simpl.
  repeat split; assumption.
Qed.

(** An armed WPM with the latch expecting the high half stages the
    accumulator and writes nothing. *)
Lemma wpm_stage : forall s,
  prom_enable s = true ->
  pl_expect_low (prom_latch s) = false ->
  execute s WPM = pc_bump 1 (with_prom_latch (mkProgLatch true (acc s)) s).
Proof.
  intros s He Hl. cbn [execute].
  rewrite He, Hl. reflexivity.
Qed.

(** An armed WPM with a staged high half commits the assembled byte at the
    programmer's address and returns the latch to its initial state. *)
Lemma wpm_commit : forall s,
  prom_enable s = true ->
  pl_expect_low (prom_latch s) = true ->
  execute s WPM
  = pc_bump 1 (with_prom_latch latch_init
      (with_rom (update_nth (wval (prom_addr s))
                   (byt (wval (pl_hi (prom_latch s)) * 16 + aval s))
                   (rom s)) s)).
Proof.
  intros s He Hl. cbn [execute].
  rewrite He, Hl. reflexivity.
Qed.

(** A disarmed WPM writes nothing and leaves the latch alone. *)
Lemma wpm_disabled_is_nop : forall s,
  prom_enable s = false ->
  execute s WPM = pc_bump 1 s.
Proof.
  intros s He. cbn [execute]. rewrite He. reflexivity.
Qed.

(** One byte through the documented two-transfer protocol: load the high
    half into the accumulator, WPM, load the low half, WPM. *)
Definition wpm_byte (s : Intel4004State) (b : byte) : Intel4004State :=
  execute (with_acc (nib (wval b mod 16))
            (execute (with_acc (nib (wval b / 16)) s) WPM)) WPM.

(** The protocol issues exactly two WPM transfers per byte, as the MCS-4
    manual requires (an even count). *)
Remark wpm_byte_two_transfers : forall s b,
  wpm_byte s b
  = execute (with_acc (nib (wval b mod 16))
              (execute (with_acc (nib (wval b / 16)) s) WPM)) WPM.
Proof. reflexivity. Qed.

(** The armed two-transfer protocol writes exactly the byte and returns the
    latch to its initial state. *)
Lemma wpm_byte_spec : forall s (b : byte),
  prom_enable s = true ->
  prom_latch s = latch_init ->
  rom (wpm_byte s b) = update_nth (wval (prom_addr s)) b (rom s) /\
  prom_latch (wpm_byte s b) = latch_init /\
  prom_addr (wpm_byte s b) = prom_addr s /\
  prom_enable (wpm_byte s b) = true /\
  regs (wpm_byte s b) = regs s /\
  ram_sys (wpm_byte s b) = ram_sys s /\
  out_ports (wpm_byte s b) = out_ports s /\
  in_ports (wpm_byte s b) = in_ports s /\
  port_dirs (wpm_byte s b) = port_dirs s.
Proof.
  intros s b He Hl.
  unfold wpm_byte.
  set (s1 := with_acc (nib (wval b / 16)) s).
  assert (He1 : prom_enable s1 = true) by exact He.
  assert (Hl1 : pl_expect_low (prom_latch s1) = false)
    by (unfold s1; exec_simpl; rewrite Hl; reflexivity).
  rewrite (wpm_stage s1 He1 Hl1).
  set (s2 := pc_bump 1 (with_prom_latch (mkProgLatch true (acc s1)) s1)).
  set (s3 := with_acc (nib (wval b mod 16)) s2).
  assert (He3 : prom_enable s3 = true) by exact He.
  assert (Hl3 : pl_expect_low (prom_latch s3) = true) by reflexivity.
  rewrite (wpm_commit s3 He3 Hl3).
  assert (Hbyte : byt (wval (pl_hi (prom_latch s3)) * 16 + aval s3) = b).
  { replace (pl_hi (prom_latch s3)) with (nib (wval b / 16)) by reflexivity.
    replace (aval s3) with (wval (nib (wval b mod 16))) by reflexivity.
    rewrite nib_val_small
      by (apply div16_byte_bound; apply byte_lt256).
    rewrite nib_val_small by apply mod16_bound.
    pose proof (Nat.div_mod (wval b) 16 ltac:(lia)).
    replace (wval b / 16 * 16 + wval b mod 16) with (wval b) by lia.
    apply byt_wval. }
  rewrite Hbyte.
  repeat split; try reflexivity; exact He.
Qed.

(** Setting the accumulator preserves well-formedness. *)
Lemma with_acc_WF : forall v s, WF s -> WF (with_acc v s).
Proof.
  intros v s H. destruct_WF H.
  unfold WF. exec_simpl. repeat split; assumption.
Qed.

(** The two-transfer protocol preserves well-formedness. *)
Lemma wpm_byte_WF : forall s b, WF s -> WF (wpm_byte s b).
Proof.
  intros s b HWF.
  unfold wpm_byte.
  apply execute_preserves_WF.
  apply with_acc_WF.
  apply execute_preserves_WF.
  apply with_acc_WF.
  exact HWF.
Qed.

(** Program loading: one arm-and-two-transfers per byte, addresses
    ascending. *)
Fixpoint load_program (s : Intel4004State) (base : nat) (bytes : list byte)
  : Intel4004State :=
  match bytes with
  | [] => s
  | b :: rest =>
      load_program (wpm_byte (arm_prom s (adr base) true) b)
                   ((base + 1) mod 4096) rest
  end.

(** Program memory as a pure function of the byte stream. *)
Fixpoint load_rom (r : list byte) (base : nat) (bs : list byte) : list byte :=
  match bs with
  | [] => r
  | b :: rest => load_rom (update_nth (base mod 4096) b r) ((base + 1) mod 4096) rest
  end.

(** The machine-level loader computes the pure image. *)
Lemma load_program_rom : forall bs s base,
  prom_latch s = latch_init ->
  rom (load_program s base bs) = load_rom (rom s) base bs /\
  prom_latch (load_program s base bs) = latch_init.
Proof.
  induction bs as [|b rest IH]; intros s base Hl.
  - split; [reflexivity | exact Hl].
  - cbn [load_program load_rom].
    set (sa := arm_prom s (adr base) true).
    assert (Hea : prom_enable sa = true) by reflexivity.
    assert (Hla : prom_latch sa = latch_init) by exact Hl.
    destruct (wpm_byte_spec sa b Hea Hla)
      as (Hrom & Hlatch & _).
    destruct (IH (wpm_byte sa b) ((base + 1) mod 4096) Hlatch) as [IH1 IH2].
    split; [| exact IH2].
    rewrite IH1. rewrite Hrom.
    replace (wval (prom_addr sa)) with (base mod 4096) by reflexivity.
    replace (rom sa) with (rom s) by reflexivity.
    reflexivity.
Qed.

(** Loading preserves well-formedness. *)
Lemma load_program_preserves_WF : forall bytes s base,
  WF s -> WF (load_program s base bytes).
Proof.
  induction bytes as [|b rest IH]; intros s base HWF; cbn [load_program].
  - exact HWF.
  - apply IH. apply wpm_byte_WF. apply arm_prom_WF. exact HWF.
Qed.

(** The pure image preserves length. *)
Lemma load_rom_length : forall bs r base,
  length (load_rom r base bs) = length r.
Proof.
  induction bs as [|b rest IH]; intros r base; cbn [load_rom].
  - reflexivity.
  - rewrite IH. apply update_nth_length.
Qed.

(** Cells outside the written range are untouched. *)
Lemma load_rom_disjoint : forall bs r base a,
  base + length bs <= 4096 ->
  (a < base \/ base + length bs <= a) ->
  nth a (load_rom r base bs) (byt 0) = nth a r (byt 0).
Proof.
  induction bs as [|b rest IH]; intros r base a Hfit Hdisj.
  - reflexivity.
  - cbn [load_rom]. cbn [length] in Hfit, Hdisj.
    assert (Hbase : base < 4096) by lia.
    rewrite (Nat.mod_small base 4096) by exact Hbase.
    assert (Hb1 : base + 1 <= 4096) by lia.
    destruct (Nat.eq_dec (base + 1) 4096) as [He | Hne].
    + (* the tail is empty *)
      assert (Hrest : length rest = 0) by lia.
      destruct rest; [| cbn in Hrest; lia].
      cbn [load_rom].
      apply nth_update_nth_neq. lia.
    + rewrite (Nat.mod_small (base + 1) 4096) by lia.
      rewrite IH by lia.
      apply nth_update_nth_neq. lia.
Qed.

(** Every loaded byte lands at its address. *)
Lemma load_rom_reads_back : forall bs r base i,
  base + length bs <= 4096 ->
  length r = 4096 ->
  i < length bs ->
  nth (base + i) (load_rom r base bs) (byt 0) = nth i bs (byt 0).
Proof.
  induction bs as [|b rest IH]; intros r base i Hfit Hlen Hi.
  - cbn in Hi. lia.
  - cbn [load_rom]. cbn [length] in Hfit, Hi.
    assert (Hbase : base < 4096) by lia.
    rewrite (Nat.mod_small base 4096) by exact Hbase.
    destruct i as [|i'].
    + rewrite Nat.add_0_r.
      destruct (Nat.eq_dec (base + 1) 4096) as [He | Hne].
      * assert (length rest = 0) by lia.
        destruct rest; [| cbn in H; lia].
        cbn [load_rom nth].
        apply nth_update_nth_eq. lia.
      * rewrite (Nat.mod_small (base + 1) 4096) by lia.
        rewrite load_rom_disjoint
          by (rewrite ?update_nth_length; lia).
        cbn [nth].
        apply nth_update_nth_eq. lia.
    + destruct (Nat.eq_dec (base + 1) 4096) as [He | Hne].
      * exfalso. cbn [length] in Hi. lia.
      * rewrite (Nat.mod_small (base + 1) 4096) by lia.
        replace (base + S i') with (base + 1 + i') by lia.
        cbn [nth].
        apply IH; [lia | rewrite update_nth_length; exact Hlen | lia].
Qed.

(** Headline: load a program image, then fetch it back byte for byte. *)
Theorem load_then_fetch : forall s base bytes,
  WF s ->
  prom_latch s = latch_init ->
  base + length bytes <= 4096 ->
  forall i, i < length bytes ->
  nth (base + i) (rom (load_program s base bytes)) (byt 0)
  = nth i bytes (byt 0).
Proof.
  intros s base bytes HWF Hl Hfit i Hi.
  destruct (load_program_rom bytes s base Hl) as [Hrom _].
  rewrite Hrom.
  apply load_rom_reads_back; [exact Hfit | | exact Hi].
  destruct_WF HWF. exact HromLen.
Qed.

Corollary load_program_fetches_bytes : forall s base bytes,
  WF s ->
  prom_latch s = latch_init ->
  base + length bytes <= 4096 ->
  forall i, i < length bytes ->
  fetch_byte (load_program s base bytes) (base + i) = nth i bytes (byt 0).
Proof.
  intros. unfold fetch_byte. apply load_then_fetch; assumption.
Qed.

(** Loading leaves cells outside the range untouched. *)
Theorem load_program_preserves_other_rom : forall bytes s base a,
  prom_latch s = latch_init ->
  base + length bytes <= 4096 ->
  (a < base \/ base + length bytes <= a) ->
  nth a (rom (load_program s base bytes)) (byt 0) = nth a (rom s) (byt 0).
Proof.
  intros bytes s base a Hl Hfit Hdisj.
  destruct (load_program_rom bytes s base Hl) as [Hrom _].
  rewrite Hrom.
  apply load_rom_disjoint; assumption.
Qed.

(* ---- The programming path driven through the CPU's output ports ---- *)

(* The 4004 drives external hardware only through its ROM output ports.  A
   PROM programmer latches its write address from ports 0..2 (low nibble to
   high) and its write-enable from port 3 (nonzero arms the write); the
   data nibbles arrive on the accumulator with each WPM. *)

(** The programmer latches address and enable from the output ports. *)
Definition latch_prom (s : Intel4004State) : Intel4004State :=
  arm_prom s
    (adr (wval (nth 0 (out_ports s) (nib 0))
          + 16 * wval (nth 1 (out_ports s) (nib 0))
          + 256 * wval (nth 2 (out_ports s) (nib 0))))
    (negb (wval (nth 3 (out_ports s) (nib 0)) =? 0)).

(** Driving the ports and issuing the two WPM transfers writes the
    addressed ROM cell: the programming path runs entirely from
    CPU-visible state. *)
Theorem prom_ports_drive_write : forall s (b : byte),
  prom_latch s = latch_init ->
  wval (nth 3 (out_ports s) (nib 0)) <> 0 ->
  rom (wpm_byte (latch_prom s) b)
  = update_nth (wval (nth 0 (out_ports s) (nib 0))
                + 16 * wval (nth 1 (out_ports s) (nib 0))
                + 256 * wval (nth 2 (out_ports s) (nib 0)))
      b (rom s).
Proof.
  intros s b Hl Hen.
  set (a := wval (nth 0 (out_ports s) (nib 0))
            + 16 * wval (nth 1 (out_ports s) (nib 0))
            + 256 * wval (nth 2 (out_ports s) (nib 0))).
  assert (Ha : a < 4096).
  { unfold a.
    pose proof (nib_lt16 (nth 0 (out_ports s) (nib 0))).
    pose proof (nib_lt16 (nth 1 (out_ports s) (nib 0))).
    pose proof (nib_lt16 (nth 2 (out_ports s) (nib 0))).
    lia. }
  assert (He : prom_enable (latch_prom s) = true).
  { unfold latch_prom, arm_prom. exec_simpl.
    destruct (wval (nth 3 (out_ports s) (nib 0)) =? 0) eqn:E.
    - apply Nat.eqb_eq in E. congruence.
    - reflexivity. }
  assert (Hll : prom_latch (latch_prom s) = latch_init) by exact Hl.
  destruct (wpm_byte_spec (latch_prom s) b He Hll) as (Hrom & _).
  rewrite Hrom.
  replace (wval (prom_addr (latch_prom s))) with (a mod 4096) by reflexivity.
  rewrite (Nat.mod_small a 4096) by exact Ha.
  reflexivity.
Qed.

(* ==================== Register round-trips ==================== *)

Lemma get_reg_set_reg_same : forall s r (v : nibble),
  r < length (regs s) ->
  get_reg (set_reg s r v) r = v.
Proof.
  intros s r v Hr.
  unfold get_reg, set_reg. cbn [regs with_regs].
  apply nth_update_nth_eq. exact Hr.
Qed.

Lemma get_reg_set_reg_diff : forall s r1 r2 (v : nibble),
  r1 <> r2 ->
  get_reg (set_reg s r1 v) r2 = get_reg s r2.
Proof.
  intros s r1 r2 v Hneq.
  unfold get_reg, set_reg. cbn [regs with_regs].
  apply nth_update_nth_neq. lia.
Qed.

(** XCH writes the old accumulator into the register, verbatim. *)
Lemma xch_reg_written : forall s (r : nibble),
  length (regs s) = 16 ->
  get_reg (execute s (XCH r)) (wval r) = acc s.
Proof.
  intros s r Hlen.
  exec_simpl. unfold get_reg. cbn [regs].
  apply nth_update_nth_eq. rewrite Hlen. apply nib_lt16.
Qed.

Lemma xch_reg_other : forall s (r : nibble) r',
  r' <> wval r ->
  get_reg (execute s (XCH r)) r' = get_reg s r'.
Proof.
  intros s r r' Hne.
  exec_simpl. unfold get_reg. cbn [regs].
  apply nth_update_nth_neq. lia.
Qed.

Lemma xch_sets_acc : forall s (r : nibble),
  acc (execute s (XCH r)) = get_reg s (wval r).
Proof. reflexivity. Qed.

(* ==================== Register-pair algebra ==================== *)

Lemma get_reg_pair_split : forall s r,
  r mod 2 = 0 ->
  get_reg_pair s r = rval s r * 16 + rval s (r + 1).
Proof.
  intros s r Heven.
  unfold get_reg_pair.
  rewrite (even_sub_mod r Heven).
  reflexivity.
Qed.

(** Any register index gives the same pair value as its pair base. *)
Lemma get_reg_pair_normalizes : forall s r,
  get_reg_pair s r = get_reg_pair s (r - r mod 2).
Proof.
  intros s r.
  unfold get_reg_pair.
  rewrite (even_sub_mod (r - r mod 2) (pair_base_even r)).
  reflexivity.
Qed.

Lemma reg_pair_addressing_invariant : forall s r,
  r mod 2 = 0 ->
  get_reg_pair s r = get_reg_pair s (r + 1).
Proof.
  intros s r Heven.
  unfold get_reg_pair.
  rewrite (even_sub_mod r Heven).
  rewrite (succ_even_odd r Heven).
  replace (r + 1 - 1) with r by lia.
  reflexivity.
Qed.

Lemma odd_reg_same_pair_as_predecessor : forall s r,
  r mod 2 = 1 ->
  get_reg_pair s r = get_reg_pair s (r - 1).
Proof.
  intros s r Hodd.
  unfold get_reg_pair.
  rewrite (odd_sub_mod r Hodd).
  assert (Hpred : (r - 1) mod 2 = 0).
  { pose proof (Nat.div_mod r 2 ltac:(lia)) as Hdm.
    replace (r - 1) with (2 * (r / 2)) by lia.
    rewrite Nat.mul_comm. apply Nat.Div0.mod_mul. }
  rewrite (even_sub_mod (r - 1) Hpred).
  reflexivity.
Qed.

Lemma set_reg_pair_get_pair : forall s r v,
  length (regs s) = 16 ->
  r < 16 ->
  r mod 2 = 0 ->
  v < 256 ->
  get_reg_pair (set_reg_pair s r v) r = v.
Proof.
  intros s r v Hlen Hr Heven Hv.
  assert (Hr1 : r + 1 < 16).
  { destruct (Nat.eq_dec r 15) as [-> | Hne]; [cbn in Heven; discriminate | ].
    assert (r <= 14) by lia.
    destruct (Nat.eq_dec r 14) as [-> | Hne2]; [lia |].
    lia. }
  unfold get_reg_pair, set_reg_pair.
  rewrite (even_sub_mod r Heven).
  unfold rval, get_reg. cbn [regs with_regs].
  rewrite nth_update_nth_eq
    by (rewrite update_nth_length, Hlen; lia).
  rewrite nth_update_nth_neq by lia.
  rewrite nth_update_nth_eq by (rewrite Hlen; lia).
  rewrite nib_val_small by (apply div16_byte_bound; exact Hv).
  rewrite nib_val_small by apply mod16_bound.
  pose proof (Nat.div_mod v 16 ltac:(lia)).
  lia.
Qed.

Lemma set_reg_pair_get_components : forall s r v,
  length (regs s) = 16 ->
  r < 16 ->
  r mod 2 = 0 ->
  v < 256 ->
  get_reg (set_reg_pair s r v) r = nib (v / 16) /\
  get_reg (set_reg_pair s r v) (r + 1) = nib (v mod 16).
Proof.
  intros s r v Hlen Hr Heven Hv.
  assert (Hr1 : r + 1 < 16).
  { destruct (Nat.eq_dec r 15) as [-> | Hne]; [cbn in Heven; discriminate | lia]. }
  unfold set_reg_pair.
  rewrite (even_sub_mod r Heven).
  unfold get_reg. cbn [regs with_regs].
  split.
  - rewrite nth_update_nth_neq by lia.
    apply nth_update_nth_eq. rewrite Hlen. lia.
  - apply nth_update_nth_eq.
    rewrite update_nth_length, Hlen. lia.
Qed.

Lemma set_reg_pair_preserves_other_regs : forall s r v r',
  r' <> r - r mod 2 ->
  r' <> (r - r mod 2) + 1 ->
  get_reg (set_reg_pair s r v) r' = get_reg s r'.
Proof.
  intros s r v r' H1 H2.
  unfold set_reg_pair, get_reg. cbn [regs with_regs].
  rewrite nth_update_nth_neq by lia.
  rewrite nth_update_nth_neq by lia.
  reflexivity.
Qed.

(** FIM loads its immediate byte into the register pair. *)
Theorem fim_operates_on_pairs : forall s (r : nibble) (d : byte),
  length (regs s) = 16 ->
  wval r mod 2 = 0 ->
  get_reg_pair (execute s (FIM r d)) (wval r) = wval d.
Proof.
  intros s r d Hlen Heven.
  cbn [execute].
  replace (get_reg_pair (pc_bump 2 (set_reg_pair s (wval r) (wval d))) (wval r))
    with (get_reg_pair (set_reg_pair s (wval r) (wval d)) (wval r))
    by reflexivity.
  apply set_reg_pair_get_pair;
    [exact Hlen | apply nib_lt16 | exact Heven | apply byte_lt256].
Qed.

Corollary fim_loads_byte_into_pair : forall s pair_idx (d : byte),
  length (regs s) = 16 ->
  pair_idx < 8 ->
  get_reg_pair (execute s (FIM (nib (2 * pair_idx)) d)) (2 * pair_idx) = wval d.
Proof.
  intros s pair_idx d Hlen Hpair.
  assert (Hv : wval (nib (2 * pair_idx)) = 2 * pair_idx)
    by (apply nib_val_small; lia).
  pose proof (fim_operates_on_pairs s (nib (2 * pair_idx)) d Hlen) as H.
  rewrite Hv in H.
  apply H.
  rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
Qed.

(** SRC decomposes the pair value into the port and RAM address latches. *)
Theorem src_uses_pair_value : forall s (r : nibble),
  let v := get_reg_pair s (wval r) in
  wval (sel_rom (execute s (SRC r))) = v / 16 /\
  wval (sel_chip (sel_ram (execute s (SRC r)))) = v / 16 / 4 /\
  wval (sel_reg (sel_ram (execute s (SRC r)))) = (v / 16) mod 4 /\
  wval (sel_char (sel_ram (execute s (SRC r)))) = v mod 16.
Proof.
  intros s r. cbv zeta.
  pose proof (get_reg_pair_lt256 s (wval r)) as Hv.
  assert (Hhi : get_reg_pair s (wval r) / 16 < 16)
    by (apply div16_byte_bound; exact Hv).
  exec_simpl. cbv zeta.
  repeat split.
  - apply nib_val_small. exact Hhi.
  - apply w2_val_small. apply Nat.Div0.div_lt_upper_bound. exact Hhi.
  - apply w2_val_small. apply Nat.mod_upper_bound. lia.
  - apply nib_val_small. apply mod16_bound.
Qed.

(** FIN loads the ROM byte addressed by pair 0 into the target pair
    (stated in page 0, where the page rule is trivial). *)
Theorem fin_operates_on_pairs : forall s (r : nibble),
  length (regs s) = 16 ->
  wval r mod 2 = 0 ->
  page_of (wval (pc_inc1 s)) = 0 ->
  get_reg_pair (execute s (FIN r)) (wval r)
  = wval (fetch_byte s (get_reg_pair s 0)).
Proof.
  intros s r Hlen Heven Hpage.
  cbn [execute].
  rewrite Hpage. cbn [Nat.mul].
  replace (get_reg_pair
             (pc_bump 1 (set_reg_pair s (wval r)
                (wval (fetch_byte s (0 + get_reg_pair s 0))))) (wval r))
    with (get_reg_pair
            (set_reg_pair s (wval r)
               (wval (fetch_byte s (0 + get_reg_pair s 0)))) (wval r))
    by reflexivity.
  rewrite Nat.add_0_l.
  apply set_reg_pair_get_pair;
    [exact Hlen | apply nib_lt16 | exact Heven | apply byte_lt256].
Qed.

Theorem jin_uses_pair_for_jump : forall s (r : nibble),
  pc (execute s (JIN r))
  = adr (page_of (wval (pc_inc1 s)) * 256 + get_reg_pair s (wval r)).
Proof. reflexivity. Qed.

(** The 16 registers form exactly 8 pairs. *)
Theorem register_pairs_partition : forall r,
  r < 16 ->
  exists pair_idx,
    pair_idx < 8 /\
    ((r = 2 * pair_idx /\ r mod 2 = 0) \/
     (r = 2 * pair_idx + 1 /\ r mod 2 = 1)).
Proof.
  intros r Hr.
  exists (r / 2).
  pose proof (mod2_cases r) as Hm.
  pose proof (Nat.div_mod r 2 ltac:(lia)) as Hdm.
  split.
  - apply Nat.Div0.div_lt_upper_bound; lia.
  - destruct Hm as [He | Ho]; [left | right]; lia.
Qed.

(** Initial state has every pair at 0. *)
Lemma get_reg_pair_init_state : forall r,
  r < 16 -> get_reg_pair init_state r = 0.
Proof.
  intros r Hr.
  unfold get_reg_pair, rval, get_reg, init_state, init_state_dirs.
  cbn [regs].
  nibble_cases r.
Qed.

(* ==================== Program layout ==================== *)

(** Instruction length in ROM bytes. *)
Definition instr_bytes (i : Instruction) : nat :=
  match i with
  | JCN _ _ | FIM _ _ | JUN _ | JMS _ | ISZ _ _ => 2
  | _ => 1
  end.

(** Machine cycles per the data sheet: 2 for two-word instructions and FIN,
    1 otherwise. *)
Definition machine_cycles (i : Instruction) : nat :=
  match i with
  | JCN _ _ | FIM _ _ | JUN _ | JMS _ | ISZ _ _ => 2
  | FIN _ => 2
  | _ => 1
  end.

(** The cycle table equals 8 clock periods times the machine-cycle count. *)
Theorem cycles_eq_machine : forall i,
  cycles i = 8 * machine_cycles i.
Proof. intros i. destruct i; reflexivity. Qed.

Lemma machine_cycles_one_or_two : forall i,
  machine_cycles i = 1 \/ machine_cycles i = 2.
Proof.
  intros i. destruct i; cbn; ((left; reflexivity) || (right; reflexivity)).
Qed.

Lemma two_word_is_two_cycle : forall i,
  instr_bytes i = 2 -> machine_cycles i = 2.
Proof.
  intros i H. destruct i; cbn in *; try discriminate; reflexivity.
Qed.

(** Every non-jump instruction advances the program counter by exactly its
    length in bytes. *)
Theorem nonjump_pc_advances_by_bytes : forall s i,
  is_jump i = false ->
  pc (execute s i) = adr (pcv s + instr_bytes i).
Proof.
  intros s i H.
  destruct i; cbn [is_jump] in H; try discriminate H;
    cbn [execute instr_bytes]; case_branches; reflexivity.
Qed.

Fixpoint encode_list (prog : list Instruction) : list byte :=
  match prog with
  | [] => []
  | i :: rest => let '(b1, b2) := encode i in
                 b1 :: b2 :: encode_list rest
  end.

Fixpoint decode_list (bytes : list byte) : list Instruction :=
  match bytes with
  | [] => []
  | b1 :: b2 :: rest => decode b1 b2 :: decode_list rest
  | _ => []
  end.

Corollary encode_decode_list_id : forall prog,
  Forall instr_wf prog ->
  decode_list (encode_list prog) = prog.
Proof.
  induction prog as [|i rest IH]; intros Hall.
  - reflexivity.
  - cbn [encode_list]. inversion Hall; subst.
    destruct (encode i) as [b1 b2] eqn:E.
    cbn [decode_list].
    assert (Hdec : decode b1 b2 = i).
    { pose proof (decode_encode_id i H1) as H.
      rewrite E in H. exact H. }
    rewrite Hdec.
    rewrite IH; auto.
Qed.

(* Disassembly of a two-byte instruction stream (see encode_list), and a
   byte-level layout check on program images; their correctness theorems
   live in fidelity.v.  Images are lists of byte, bounded by construction,
   so only the two-byte alignment is checkable. *)

Definition disassemble (romv : list byte) (addr : nat) : option (Instruction * nat) :=
  match skipn addr romv with
  | b1 :: b2 :: _ => Some (decode b1 b2, addr + 2)
  | _ => None
  end.

Definition valid_program (bytes : list byte) : bool :=
  length bytes mod 2 =? 0.

(* ===================================================================== *)
(*         INDEPENDENT SPECIFICATIONS AND CORRESPONDENCE                  *)
(* ===================================================================== *)

(* -------- DAA against decimal arithmetic -------- *)

(* DAA decimal correctness: for raw = x+y+cin with acc = raw mod 16 and
   carry = (raw >= 16), DAA yields (raw mod 10, raw / 10). *)
Theorem daa_decimal_correct : forall s x y cin,
  x <= 9 -> y <= 9 -> cin <= 1 ->
  aval s = (x + y + cin) mod 16 ->
  carry s = (16 <=? x + y + cin) ->
  aval (execute s DAA) = (x + y + cin) mod 10 /\
  (if carry (execute s DAA) then 1 else 0) = (x + y + cin) / 10.
Proof.
  intros s x y cin Hx Hy Hcin Hacc Hcarry.
  pose proof (daa_bcd_adjust_correct s) as H. cbv zeta in H.
  destruct H as [Ha Hc].
  rewrite Ha, Hc, Hacc, Hcarry.
  remember (x + y + cin) as raw eqn:Hr.
  assert (Hraw : raw <= 19) by lia.
  clear Hr Hacc Hcarry Ha Hc Hx Hy Hcin.
  do 20 (destruct raw as [|raw]; [split; reflexivity |]).
  lia.
Qed.

(* -------- ADD against the 4-bit adder identity -------- *)

(* 4-bit adder identity: acc + reg + carry_in = 16*carry_out + acc_out. *)
Theorem add_value_correct : forall s (r : nibble),
  aval s + rval s (wval r) + cbit s
  = 16 * (if carry (execute s (ADD r)) then 1 else 0)
    + aval (execute s (ADD r)).
Proof.
  intros s r.
  destruct (add_computes_sum s r) as [Hacc Hcar].
  rewrite Hacc, Hcar.
  pose proof (aval_lt16 s).
  pose proof (rval_lt16 s (wval r)).
  set (sum := aval s + rval s (wval r) + cbit s) in *.
  assert (Hsum : sum < 32) by (unfold sum, cbit; destruct (carry s); lia).
  pose proof (Nat.Div0.div_mod sum 16) as Hdm.
  pose proof (Nat.mod_upper_bound sum 16 ltac:(lia)) as Hub.
  destruct (16 <=? sum) eqn:E;
    [apply Nat.leb_le in E | apply Nat.leb_gt in E].
  - assert (sum / 16 = 1) by lia. lia.
  - assert (sum / 16 = 0) by lia. lia.
Qed.

(* -------- Undefined opcodes decode to NOP -------- *)

Lemma decode_FE_FF_is_nop : forall b2,
  decode (byt 254) b2 = NOP /\ decode (byt 255) b2 = NOP.
Proof. intro b2. split; reflexivity. Qed.

(* ===================================================================== *)
(*         PARTIAL ACCESSORS, STATE BUNDLE, PROGRAM LOGIC                 *)
(* ===================================================================== *)

(* Register read as a total option: Some in range, None past the file end. *)
Definition get_reg_checked (s : Intel4004State) (r : nat) : option nibble :=
  if r <? length (regs s) then Some (nth r (regs s) (nib 0)) else None.

Lemma get_reg_checked_in : forall s r,
  r < length (regs s) -> get_reg_checked s r = Some (get_reg s r).
Proof.
  intros s r H. unfold get_reg_checked, get_reg.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma get_reg_checked_oob : forall s r,
  length (regs s) <= r -> get_reg_checked s r = None.
Proof.
  intros s r H. unfold get_reg_checked.
  apply Nat.ltb_ge in H. rewrite H. reflexivity.
Qed.

(* ROM fetch as a total option: Some in range, None past the ROM end. *)
Definition fetch_byte_checked (s : Intel4004State) (a : nat) : option byte :=
  if a <? length (rom s) then Some (nth a (rom s) (byt 0)) else None.

Lemma fetch_byte_checked_in : forall s a,
  a < length (rom s) -> fetch_byte_checked s a = Some (fetch_byte s a).
Proof.
  intros s a H. unfold fetch_byte_checked, fetch_byte.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma fetch_byte_checked_oob : forall s a,
  length (rom s) <= a -> fetch_byte_checked s a = None.
Proof.
  intros s a H. unfold fetch_byte_checked.
  apply Nat.ltb_ge in H. rewrite H. reflexivity.
Qed.

(* A state bundled with its well-formedness proof. *)
Record WFState : Type := mkWFState {
  wf_st  : Intel4004State;
  wf_prf : WF wf_st
}.

(* Stepping a bundled state carries the invariant by construction. *)
Definition wf_step (ws : WFState) : WFState :=
  mkWFState (step (wf_st ws)) (step_preserves_WF (wf_st ws) (wf_prf ws)).

Definition wf_steps (n : nat) (ws : WFState) : WFState :=
  mkWFState (steps n (wf_st ws)) (steps_preserve_WF n (wf_st ws) (wf_prf ws)).

Lemma wf_step_projects : forall ws, wf_st (wf_step ws) = step (wf_st ws).
Proof. intros ws. reflexivity. Qed.

Lemma wf_steps_projects : forall n ws, wf_st (wf_steps n ws) = steps n (wf_st ws).
Proof. intros n ws. reflexivity. Qed.

(* Every well-formed instruction has a two-byte encoding that decodes to it. *)
Theorem decode_surjective_on_wf : forall i,
  instr_wf i -> exists b1 b2, decode b1 b2 = i.
Proof.
  intros i Hwf. destruct (encode i) as [b1 b2] eqn:E.
  exists b1, b2.
  pose proof (decode_encode_id i Hwf) as Hd. rewrite E in Hd. exact Hd.
Qed.

(* decode is not injective, so encode-after-decode is not the identity. *)
Lemma encode_decode_not_identity : encode (decode (byt 0) (byt 5)) <> (byt 0, byt 5).
Proof.
  intro H.
  apply (f_equal snd) in H.
  apply (f_equal (@wval 8)) in H.
  cbn in H. discriminate.
Qed.

(* ===================================================================== *)
(*            SEPARATION FRAME, PROGRESS, TIMING EXTENSION               *)
(* ===================================================================== *)

(* The 4004 has no hardware interrupt mechanism; external MCS-4 interrupt
   logic is outside the processor model and is not represented. *)

(* Points-to for a main RAM cell at (bank, chip, reg, char). *)
Definition ram_main_is (b c r i : nat) (v : nibble) (s : Intel4004State) : Prop :=
  get_main (get_regRAM (get_chip (get_bank s b) c) r) i = v.

(* WRM writes only the selected banks; reads in any other bank are
   unchanged. *)
Lemma wrm_frames_other_bank : forall s b c r i,
  ~ In b (sel_lines s) ->
  get_main (get_regRAM (get_chip (get_bank (execute s WRM) b) c) r) i
  = get_main (get_regRAM (get_chip (get_bank s b) c) r) i.
Proof.
  intros s b c r i Hb.
  assert (Hbank : get_bank (execute s WRM) b = get_bank s b).
  { unfold get_bank.
    replace (ram_sys (execute s WRM))
      with (write_main_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s))
      by reflexivity.
    apply write_main_banks_other. exact Hb. }
  rewrite Hbank. reflexivity.
Qed.

(* Cell-level separation frame: WRM preserves a points-to in an unselected
   bank. *)
Corollary ram_main_is_frame_bank : forall s b c r i v,
  ~ In b (sel_lines s) ->
  ram_main_is b c r i v s -> ram_main_is b c r i v (execute s WRM).
Proof.
  intros s b c r i v Hb H. unfold ram_main_is in *.
  rewrite wrm_frames_other_bank by exact Hb. exact H.
Qed.

(* Progress: from any well-formed state, step yields a well-formed state
   with a bounded PC. *)
Theorem progress : forall s, WF s ->
  WF (step s) /\ pcv (step s) < 4096.
Proof.
  intros s HWF. split.
  - apply step_preserves_WF; exact HWF.
  - apply pcv_lt4096.
Qed.

(* Timing with w extra clock periods per instruction. The 4004 itself has no
   wait-state mechanism (there is no READY pin), so instruction timing is
   fully deterministic and w = 0 is the hardware; w models hypothetical
   external clock stretching only. *)
Definition cycles_with_waits (w : nat) (i : Instruction) : nat :=
  cycles i + w.

Lemma cycles_with_waits_zero : forall i, cycles_with_waits 0 i = cycles i.
Proof. intros i. unfold cycles_with_waits. lia. Qed.

Lemma cycles_with_waits_mono : forall w i, cycles i <= cycles_with_waits w i.
Proof. intros w i. unfold cycles_with_waits. lia. Qed.

(* ---- Fixed-width bounds, by construction ---- *)

(* The machine's quantities are dependent fixed-width words; the bound
   lemmas are aval_lt16, rval_lt16, pcv_lt4096, get_reg_pair_lt256,
   fetch_byte_lt256, and wbound at every width (machine.v). *)

Theorem nibble_view_cannot_overflow : forall x : nibble, wval x < 16.
Proof. exact nib_lt16. Qed.

Corollary acc_view_never_illegal : forall s, aval s < 16.
Proof. exact aval_lt16. Qed.

Corollary reg_view_never_illegal : forall s r, rval s r < 16.
Proof. exact rval_lt16. Qed.

Theorem get_reg_checked_is_typed : forall s r,
  r < length (regs s) ->
  get_reg_checked s r = Some (get_reg s r) /\ rval s r < 16.
Proof.
  intros s r Hr.
  split; [apply get_reg_checked_in; exact Hr | apply rval_lt16].
Qed.

(* ===================================================================== *)
(*                 INSTRUCTION LENGTH AND FETCH FIDELITY                 *)
(* ===================================================================== *)

(** The instruction currently addressed by the program counter. *)
Definition instr_at (s : Intel4004State) : Instruction :=
  decode (fetch_byte s (pcv s)) (fetch_byte s ((pcv s + 1) mod 4096)).

Lemma step_is_instr_at : forall s, step s = execute s (instr_at s).
Proof. reflexivity. Qed.

(** When a decoded instruction occupies a single byte, the second fetched
    byte does not affect the decode. *)
Lemma decode_1byte_ignores_b2 : forall b1 b2 b2',
  instr_bytes (decode b1 b2) = 1 -> decode b1 b2' = decode b1 b2.
Proof.
  intros b1 b2 b2' H. unfold decode in *. cbv zeta in *.
  destruct (wval b1 / 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]]]];
    repeat match goal with
           | |- context [if ?c then _ else _] => destruct c
           | H : context [if ?c then _ else _] |- _ => destruct c
           end;
    cbn [instr_bytes] in H; (reflexivity || discriminate).
Qed.

(** A single-byte instruction at the program counter is independent of the
    byte at PC+1. *)
Theorem step_fetch_is_length_faithful : forall s b2',
  instr_bytes (instr_at s) = 1 ->
  decode (fetch_byte s (pcv s)) b2' = instr_at s.
Proof.
  intros s b2' H. unfold instr_at in *.
  apply decode_1byte_ignores_b2. exact H.
Qed.

(* ===================================================================== *)
(*                       EXTERNAL INPUT ENVIRONMENT                      *)
(* ===================================================================== *)

(* The processor reacts to external inputs the program does not itself
   produce: the TEST pin, sampled each machine cycle, and the 4001 ROM
   input ports, driven by external devices and read by RDR.  An environment
   supplies the TEST level at each cycle; the driven machine samples it
   before every fetch-decode-execute, so execution is an open reactive
   system. *)

Definition Env := nat -> bool.

(** One driven step: sample the environment's TEST level, then execute. *)
Definition step_env (e : Env) (t : nat) (s : Intel4004State) : Intel4004State :=
  step (set_test_pin s (e t)).

(** Iterated driven stepping from cycle t. *)
Fixpoint steps_env (e : Env) (t n : nat) (s : Intel4004State) : Intel4004State :=
  match n with
  | 0 => s
  | S k => steps_env e (S t) k (step_env e t s)
  end.

Lemma step_env_preserves_WF : forall e t s, WF s -> WF (step_env e t s).
Proof.
  intros e t s HWF. unfold step_env.
  apply step_preserves_WF. apply set_test_pin_preserves_WF. exact HWF.
Qed.

Lemma steps_env_preserves_WF : forall e n t s, WF s -> WF (steps_env e t n s).
Proof.
  intros e n. induction n; intros t s HWF; simpl.
  - exact HWF.
  - apply IHn. apply step_env_preserves_WF. exact HWF.
Qed.

Lemma step_env_samples_test : forall (e : Env) t s,
  test_pin (set_test_pin s (e t)) = e t.
Proof. intros. apply set_test_pin_value. Qed.

(** The external TEST level controls a JNT branch: with TEST low the branch
    is taken, with TEST high control falls through.  The machine is open. *)
Theorem test_input_controls_branch : forall s (off : byte),
  pc (execute (set_test_pin s false) (JCN (nib JCN_JNT) off))
    = adr (base_for_next2 s + wval off) /\
  pc (execute (set_test_pin s true) (JCN (nib JCN_JNT) off))
    = adr (pcv s + 2).
Proof.
  intros s off.
  destruct (jcn_test_pin_determines_branch (set_test_pin s false) off)
    as [Hf _].
  destruct (jcn_test_pin_determines_branch (set_test_pin s true) off)
    as [_ [Ht _]].
  split.
  - replace (base_for_next2 s)
      with (base_for_next2 (set_test_pin s false)) by reflexivity.
    apply Hf. reflexivity.
  - replace (pcv s) with (pcv (set_test_pin s true)) by reflexivity.
    apply Ht. reflexivity.
Qed.

(** An external device drives ROM input port k to value v. *)
Definition drive_rom_port (s : Intel4004State) (k : nat) (v : nibble)
  : Intel4004State :=
  with_in_ports (update_nth k v (in_ports s)) s.

Lemma drive_rom_port_WF : forall s k v, WF s -> WF (drive_rom_port s k v).
Proof.
  intros s k v HWF. destruct_WF HWF.
  unfold WF, drive_rom_port. exec_simpl.
  rewrite update_nth_length.
  repeat split; assumption.
Qed.

Lemma drive_rom_port_out_frame : forall s k v,
  out_ports (drive_rom_port s k v) = out_ports s.
Proof. reflexivity. Qed.

(** RDR reads back the value an external device drove onto the selected
    input port. *)
Theorem rdr_reads_driven_input : forall s k (v : nibble),
  WF s ->
  k < 16 ->
  nth k (port_dirs s) true = false ->
  wval (sel_rom s) = k ->
  acc (execute (drive_rom_port s k v) RDR) = v.
Proof.
  intros s k v HWF Hk Hdir Hsel.
  destruct_WF HWF.
  rewrite rdr_reads_selected_port.
  replace (wval (sel_rom (drive_rom_port s k v))) with k
    by (symmetry; exact Hsel).
  replace (port_dirs (drive_rom_port s k v)) with (port_dirs s) by reflexivity.
  rewrite Hdir.
  replace (in_ports (drive_rom_port s k v))
    with (update_nth k v (in_ports s)) by reflexivity.
  apply nth_update_nth_eq. rewrite HinLen. exact Hk.
Qed.

(* ===================================================================== *)
(*            SMALL-STEP MACHINE TRACKS BIG-STEP EXECUTION               *)
(* ===================================================================== *)

(* The program logic runs over exec_program, a fold of execute over an
   instruction list; the fetch-decode-execute machine runs over steps,
   which read bytes from ROM.  code_at a prog holds when ROM, walked by the
   machine's own two-byte fetch and variable instruction length, decodes
   prog as a packed instruction stream from address a.  A one-byte
   instruction ignores the following byte, so tight packing decodes
   correctly. *)

Fixpoint code_at (s : Intel4004State) (a : nat) (prog : list Instruction) : Prop :=
  match prog with
  | [] => True
  | i :: rest =>
      decode (fetch_byte s a) (fetch_byte s ((a + 1) mod 4096)) = i /\
      code_at s ((a + instr_bytes i) mod 4096) rest
  end.

(** code_at depends only on ROM, so a ROM-preserving step keeps it. *)
Lemma code_at_rom_invariant : forall prog s s' a,
  rom s' = rom s -> code_at s a prog -> code_at s' a prog.
Proof.
  induction prog as [|i rest IH]; intros s s' a Hrom H.
  - exact I.
  - destruct H as [Hd Hrest]. split.
    + unfold fetch_byte in *. rewrite Hrom. exact Hd.
    + apply (IH s s'); [exact Hrom | exact Hrest].
Qed.

(** The instruction ROM decodes at the head of a stream is well-formed. *)
Lemma code_at_head_wf : forall s i rest a,
  code_at s a (i :: rest) -> instr_wf i.
Proof.
  intros s i rest a [Hd _].
  rewrite <- Hd. apply decode_instr_wf.
Qed.

(** For a straight-line program (no jumps, no ROM writes) held in ROM at
    the program counter, running one small step per instruction reproduces
    the big-step exec_program semantics exactly. *)
Theorem steps_tracks_exec_program : forall prog s,
  Forall (fun i => is_jump i = false /\ i <> WPM) prog ->
  code_at s (pcv s) prog ->
  steps (length prog) s = exec_program prog s.
Proof.
  induction prog as [|i rest IH]; intros s Hall Hcode.
  - reflexivity.
  - assert (Hhead := Forall_inv Hall).
    assert (Hall' := Forall_inv_tail Hall).
    destruct Hhead as [Hnj Hnwpm].
    destruct Hcode as [Hd Hrest].
    assert (Hstep : step s = execute s i).
    { unfold step. rewrite Hd. reflexivity. }
    replace (steps (length (i :: rest)) s)
      with (steps (length rest) (step s)) by reflexivity.
    replace (exec_program (i :: rest) s)
      with (exec_program rest (execute s i)) by reflexivity.
    rewrite Hstep.
    apply IH.
    + exact Hall'.
    + assert (Hpc : pc (execute s i) = adr (pcv s + instr_bytes i))
        by (apply nonjump_pc_advances_by_bytes; exact Hnj).
      assert (Hpcv : pcv (execute s i) = (pcv s + instr_bytes i) mod 4096).
      { unfold pcv at 1. rewrite Hpc. apply adr_val. }
      assert (Hrom : rom (execute s i) = rom s)
        by (apply execute_rom_frame; exact Hnwpm).
      rewrite Hpcv.
      apply (code_at_rom_invariant rest s (execute s i));
        [exact Hrom | exact Hrest].
Qed.

(* A concrete program in ROM, run by the actual machine.  LDM 5 encodes to
   the byte 213 and IAC to 242, each one byte; packed they occupy addresses
   0 and 1. *)

Definition demo_rom : list byte := byt 213 :: byt 242 :: repeat (byt 0) 4094.

Definition demo_state : Intel4004State := with_rom demo_rom init_state.

Lemma demo_state_WF : WF demo_state.
Proof.
  pose proof init_state_WF as H. destruct_WF H.
  unfold WF, demo_state. exec_simpl.
  repeat split; try assumption.
Qed.

(** ROM decodes the packed program at the program counter. *)
Lemma demo_code : code_at demo_state 0 [LDM (nib 5); IAC].
Proof. repeat split; vm_compute; reflexivity. Qed.

(** Placing the program in ROM and running the fetch-decode-execute machine
    for two steps leaves 6 in the accumulator, matching the big-step
    result. *)
Theorem demo_runs_on_machine : aval (steps 2 demo_state) = 6.
Proof. vm_compute. reflexivity. Qed.

(* ===================================================================== *)
(*                         HALTING AND STASIS                            *)
(* ===================================================================== *)

(* The 4004 has no halt instruction; a program stops by branching to
   itself.  A halted state is a fixed point of the step relation. *)

Definition halted (s : Intel4004State) : Prop := step s = s.

Definition halts_within (n : nat) (s : Intel4004State) : Prop :=
  exists k, k <= n /\ halted (steps k s).

Lemma halted_steps_fixed : forall n s, halted s -> steps n s = s.
Proof.
  intros n s H. induction n; simpl.
  - reflexivity.
  - unfold halted in H. rewrite H. exact IHn.
Qed.

(** A jump-to-self at the program counter is a halted state. *)
Lemma jun_self_halted : forall s, instr_at s = JUN (pc s) -> halted s.
Proof.
  intros s H. unfold halted.
  rewrite step_is_instr_at, H.
  destruct s; reflexivity.
Qed.

Theorem self_loop_halts_within_0 : forall s,
  instr_at s = JUN (pc s) -> halts_within 0 s.
Proof.
  intros s H. exists 0. split; [lia | apply jun_self_halted; exact H].
Qed.

Theorem halted_confines_pc : forall n s, halted s -> pc (steps n s) = pc s.
Proof. intros n s H. rewrite halted_steps_fixed by exact H. reflexivity. Qed.

(* ===================================================================== *)
(*        ACCUMULATOR/CARRY SIMULATION AGAINST AN INDEPENDENT ALU        *)
(* ===================================================================== *)

(** The accumulator/carry instructions. *)
Definition is_alu (i : Instruction) : bool :=
  match i with
  | ADD _ | SUB _ | IAC | DAC | CMA | RAL | RAR | TCC | TCS
  | CLB | CLC | STC | CMC | DAA | KBP => true
  | _ => false
  end.

(** The register value an ALU instruction consumes. *)
Definition alu_reg (i : Instruction) (s : Intel4004State) : nat :=
  match i with ADD r | SUB r => rval s (wval r) | _ => 0 end.

(* An accumulator/carry reference written directly from the MCS-4 data
   sheet, independent of execute. *)
Definition alu_ref (i : Instruction) (a : nat) (c : bool) (r : nat) : nat * bool :=
  let b := fun x : bool => if x then 1 else 0 in
  match i with
  | ADD _ => let t := a + r + b c in (t mod 16, 16 <=? t)
  | SUB _ => let t := a + 16 - r - b c in (t mod 16, 16 <=? t)
  | IAC   => let t := a + 1 in (t mod 16, 16 <=? t)
  | DAC   => ((a + 15) mod 16, negb (a =? 0))
  | CMA   => ((15 - a) mod 16, c)
  | RAL   => ((a * 2 + b c) mod 16, 8 <=? a)
  | RAR   => ((a / 2 + (if c then 8 else 0)) mod 16, a mod 2 =? 1)
  | TCC   => (b c, false)
  | TCS   => ((if c then 10 else 9), false)
  | CLB   => (0, false)
  | CLC   => (a, false)
  | STC   => (a, true)
  | CMC   => (a, negb c)
  | DAA   => let adj := orb c (9 <? a) in
             let t := a + (if adj then 6 else 0) in
             (t mod 16, orb (16 <=? t) c)
  | KBP   => ((match a with 0=>0|1=>1|2=>2|4=>3|8=>4|_=>15 end), c)
  | _     => (a, c)
  end.

(** The machine's accumulator/carry result on every ALU instruction equals
    the independent data-sheet reference. *)
Theorem alu_matches_ref : forall s i,
  is_alu i = true ->
  (aval (execute s i), carry (execute s i))
  = alu_ref i (aval s) (carry s) (alu_reg i s).
Proof.
  intros s i Halu.
  destruct i; try discriminate Halu;
    exec_simpl; cbn [alu_ref alu_reg]; cbv zeta;
    try reflexivity;
    try (rewrite nib_val; reflexivity);
    try (destruct (carry s); reflexivity);
    try (rewrite nib_val; destruct (carry s); reflexivity).
  (* KBP *)
  destruct (wval (acc s)) as [|[|[|[|[|[|[|[|[|k]]]]]]]]]; reflexivity.
Qed.

(** The machine is a sound transition system: every well-formed step stays
    well-formed, keeps the program counter in range, and costs at most two
    machine cycles. *)
Theorem intel4004_transition_sound : forall s i,
  WF s ->
  WF (execute s i) /\ pcv (execute s i) < 4096 /\ cycles i <= 16.
Proof.
  intros s i HWF. split; [| split].
  - apply execute_preserves_WF; assumption.
  - apply pcv_lt4096.
  - apply max_cycles_per_instruction.
Qed.

(* ===================================================================== *)
(*      THE SLOTS-AND-POINTER RING: ISOMORPHISM WITH THE MACHINE         *)
(* ===================================================================== *)

(* The 4004's program counter and three-level stack are physically one ring
   of four 12-bit dynamic registers with a 2-bit pointer selecting the row
   that acts as the PC.  The machine state stores this ring in
   pointer-relative coordinates (pc, stk1, stk2, stk3), because the pointer
   is not architecturally observable.  This module models the ring with its
   explicit pointer and proves the two presentations move in lockstep:
   every machine state realizes a pointered ring at every pointer value,
   JMS tracks CALL, BBL tracks RET, and underflow resumes the stale row in
   both. *)

Record Ring := mkRing {
  ring_slots : list addr12;   (* exactly 4 rows *)
  ring_ptr   : nat            (* 0..3: the row acting as the PC *)
}.

Definition ring_wf (rg : Ring) : Prop :=
  length (ring_slots rg) = 4 /\ ring_ptr rg < 4.

Definition ring_pc (rg : Ring) : addr12 :=
  nth (ring_ptr rg) (ring_slots rg) (adr 0).

(** CALL: deposit the return address in the current row, advance, and load
    the target into the new current row. *)
Definition ring_call (rg : Ring) (ret target : addr12) : Ring :=
  let p := ring_ptr rg in
  let p' := (p + 1) mod 4 in
  mkRing (update_nth p' target (update_nth p ret (ring_slots rg))) p'.

(** RET: the current row is left holding its fetch-incremented value and
    the pointer backs up; that row resumes as the PC. *)
Definition ring_ret (rg : Ring) : Ring :=
  mkRing (update_nth (ring_ptr rg)
            (adr (wval (nth (ring_ptr rg) (ring_slots rg) (adr 0)) + 1))
            (ring_slots rg))
         ((ring_ptr rg + 3) mod 4).

(** Correspondence: the machine's pointer-relative rows are the ring's rows
    read backwards from the pointer. *)
Definition ring_matches (rg : Ring) (s : Intel4004State) : Prop :=
  ring_wf rg /\
  ring_pc rg = pc s /\
  nth ((ring_ptr rg + 3) mod 4) (ring_slots rg) (adr 0) = stk1 s /\
  nth ((ring_ptr rg + 2) mod 4) (ring_slots rg) (adr 0) = stk2 s /\
  nth ((ring_ptr rg + 1) mod 4) (ring_slots rg) (adr 0) = stk3 s.

(** Every machine state realizes a pointered ring. *)
Theorem rotating_ring_complete : forall s,
  exists rg, ring_matches rg s.
Proof.
  intro s.
  exists (mkRing [pc s; stk3 s; stk2 s; stk1 s] 0).
  unfold ring_matches, ring_wf, ring_pc. cbn.
  repeat split; reflexivity || lia.
Qed.

(** JMS tracks CALL at every pointer value. *)
Theorem ring_tracks_jms : forall rg s (a : addr12),
  ring_matches rg s ->
  ring_matches (ring_call rg (adr (pcv s + 2)) a) (execute s (JMS a)).
Proof.
  intros rg s a H.
  destruct rg as [slots ptr].
  destruct H as [[Hlen Hptr] [Hpc [H1 [H2 H3]]]].
  cbn [ring_slots ring_ptr] in *.
  destruct slots as [|q0 [|q1 [|q2 [|q3 [|junk rest]]]]];
    cbn [length] in Hlen; try lia.
  destruct ptr as [|[|[|[|junkp]]]]; try lia;
    unfold ring_matches, ring_wf, ring_pc, ring_call;
    cbn in *; repeat split; (congruence || lia).
Qed.

(** BBL tracks RET at every pointer value, including underflow. *)
Theorem ring_tracks_bbl : forall rg s (d : nibble),
  ring_matches rg s ->
  ring_matches (ring_ret rg) (execute s (BBL d)).
Proof.
  intros rg s d H.
  destruct rg as [slots ptr].
  destruct H as [[Hlen Hptr] [Hpc [H1 [H2 H3]]]].
  cbn [ring_slots ring_ptr] in *.
  destruct slots as [|q0 [|q1 [|q2 [|q3 [|junk rest]]]]];
    cbn [length] in Hlen; try lia.
  destruct ptr as [|[|[|[|junkp]]]]; try lia;
    unfold ring_matches, ring_wf, ring_pc, ring_ret;
    cbn in *; subst; repeat split; (reflexivity || lia).
Qed.

(** Underflow has a definite hardware meaning: RET on the ring resumes the
    stale row one position behind the pointer (untouched by the write-back
    to the vacated row), and the machine's BBL agrees. *)
Theorem ring_underflow_resumes_stale : forall rg,
  ring_pc (ring_ret rg)
  = nth ((ring_ptr rg + 3) mod 4) (ring_slots rg) (adr 0).
Proof.
  intros rg. unfold ring_pc, ring_ret. cbn [ring_slots ring_ptr].
  apply nth_update_nth_neq.
  remember (ring_ptr rg) as n eqn:En.
  intro Heq.
  pose proof (Nat.mod_upper_bound (n + 3) 4 ltac:(lia)) as Hub.
  destruct n as [|[|[|[|k]]]]; cbn in Heq, Hub; lia.
Qed.

Corollary ring_underflow_agrees : forall rg s (d : nibble),
  ring_matches rg s ->
  ring_pc (ring_ret rg) = pc (execute s (BBL d)).
Proof.
  intros rg s d H.
  destruct (ring_tracks_bbl rg s d H) as [_ [Hpc _]].
  exact Hpc.
Qed.

(* ===================================================================== *)
(*                  MACHINE-CYCLE MICROARCHITECTURE                      *)
(* ===================================================================== *)

(* The 4004 executes each machine cycle as A1-A3 (address out), M1-M2
   (byte fetch), X1-X3 (execute): one-word one-cycle instructions complete
   inside their single cycle, and the two-cycle instructions (the two-word
   opcodes and FIN) spend a first cycle banking the first byte.  This
   module models execution at that granularity and proves the microcycle
   machine refines the ISA step.  Gate-level equivalence remains open. *)

(** Whether the first instruction byte announces a two-machine-cycle
    instruction: the two-word opcodes, and FIN (one word, two cycles). *)
Definition two_cycle_b1 (b1 : byte) : bool :=
  match wval b1 / 16 with
  | 1 | 4 | 5 | 7 => true
  | 2 | 3 => (wval b1 mod 16) mod 2 =? 0
  | _ => false
  end.

Lemma two_cycle_b1_correct : forall b1 b2,
  machine_cycles (decode b1 b2) = if two_cycle_b1 b1 then 2 else 1.
Proof.
  intros b1 b2. unfold two_cycle_b1, decode. cbv zeta.
  destruct (wval b1 / 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]]]];
  try destruct ((wval b1 mod 16) mod 2 =? 0);
  try (destruct (wval b1 mod 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|m]]]]]]]]]]]]]]]);
  reflexivity.
Qed.

Inductive MPhase := MFetch | MExec (b1 : byte).

Record MC := mkMC { mc_state : Intel4004State; mc_phase : MPhase }.

(** One machine cycle.  From a fetch boundary, a one-cycle instruction
    completes; a two-cycle instruction banks its first byte.  The second
    cycle fetches at PC+1 and executes. *)
Definition mc_step (m : MC) : MC :=
  match mc_phase m with
  | MFetch =>
      let s := mc_state m in
      let b1 := fetch_byte s (pcv s) in
      if two_cycle_b1 b1
      then mkMC s (MExec b1)
      else mkMC (step s) MFetch
  | MExec b1 =>
      let s := mc_state m in
      mkMC (execute s (decode b1 (fetch_byte s ((pcv s + 1) mod 4096)))) MFetch
  end.

Fixpoint mc_run (n : nat) (m : MC) : MC :=
  match n with
  | 0 => m
  | S k => mc_run k (mc_step m)
  end.

Lemma mc_run_add : forall a b m, mc_run (a + b) m = mc_run b (mc_run a m).
Proof.
  induction a as [|a IH]; intros b m; simpl.
  - reflexivity.
  - apply IH.
Qed.

(** Machine cycles of the instruction at the PC. *)
Definition mcycles_at (s : Intel4004State) : nat := machine_cycles (instr_at s).

(** Headline: from a fetch boundary, running exactly the instruction's
    machine-cycle count of microcycles is the ISA step. *)
Theorem microcycle_refines_step : forall s,
  mc_run (mcycles_at s) (mkMC s MFetch) = mkMC (step s) MFetch.
Proof.
  intros s. unfold mcycles_at, instr_at.
  rewrite (two_cycle_b1_correct (fetch_byte s (pcv s))
             (fetch_byte s ((pcv s + 1) mod 4096))).
  destruct (two_cycle_b1 (fetch_byte s (pcv s))) eqn:E.
  - cbn [mc_run mc_step mc_phase mc_state].
    rewrite E.
    cbn [mc_run mc_step mc_phase mc_state].
    unfold step. reflexivity.
  - cbn [mc_run mc_step mc_phase mc_state].
    rewrite E.
    unfold step. reflexivity.
Qed.

(** Composing runs of the machine. *)
Lemma steps_add : forall m n s, steps (m + n) s = steps n (steps m s).
Proof.
  induction m as [|m IH]; intros n s; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma steps_snoc : forall n s, steps (S n) s = step (steps n s).
Proof.
  intros n s.
  replace (S n) with (n + 1) by lia.
  rewrite steps_add. reflexivity.
Qed.

(** Total microcycles of an n-instruction run. *)
Fixpoint mc_time (n : nat) (s : Intel4004State) : nat :=
  match n with
  | 0 => 0
  | S k => mcycles_at s + mc_time k (step s)
  end.

(** The microcycle machine refines whole ISA runs. *)
Theorem microcycle_refines_steps : forall n s,
  mc_run (mc_time n s) (mkMC s MFetch) = mkMC (steps n s) MFetch.
Proof.
  induction n as [|n IH]; intros s.
  - reflexivity.
  - cbn [mc_time steps].
    rewrite mc_run_add.
    rewrite microcycle_refines_step.
    apply IH.
Qed.

(* ===================================================================== *)
(*                    EXECUTION-TIME ANALYSIS                            *)
(* ===================================================================== *)

(** Pure per-program cost in clock periods. *)
Fixpoint list_cycles (prog : list Instruction) : nat :=
  match prog with
  | [] => 0
  | i :: rest => 8 * machine_cycles i + list_cycles rest
  end.

(** WCET/BCET bounds for any straight-line fragment. *)
Theorem straightline_time_bounds : forall prog,
  8 * length prog <= list_cycles prog <= 16 * length prog.
Proof.
  induction prog as [|i rest IH]; simpl.
  - lia.
  - pose proof (machine_cycles_one_or_two i). lia.
Qed.

(** Clock periods consumed by n fetch-decode-execute machine steps. *)
Fixpoint run_cycles (n : nat) (s : Intel4004State) : nat :=
  match n with
  | 0 => 0
  | S k => cycles (instr_at s) + run_cycles k (step s)
  end.

Lemma run_cycles_add : forall m n s,
  run_cycles (m + n) s = run_cycles m s + run_cycles n (steps m s).
Proof.
  induction m as [|m IH]; intros n s; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(** Universal machine-time bounds: every step costs one or two machine
    cycles, 8 to 16 clock periods. *)
Theorem machine_time_bounds : forall n s,
  8 * n <= run_cycles n s <= 16 * n.
Proof.
  induction n as [|n IH]; intros s; simpl.
  - lia.
  - specialize (IH (step s)).
    pose proof (max_cycles_per_instruction (instr_at s)).
    pose proof (min_cycles_per_instruction (instr_at s)).
    lia.
Qed.

(** For straight-line code held in ROM at the PC, the machine's execution
    time is exactly the pure per-instruction sum: WCET = BCET. *)
Theorem machine_time_straightline : forall prog s,
  Forall (fun i => is_jump i = false /\ i <> WPM) prog ->
  code_at s (pcv s) prog ->
  run_cycles (length prog) s = list_cycles prog.
Proof.
  induction prog as [|i rest IH]; intros s Hall Hcode; simpl.
  - reflexivity.
  - destruct Hcode as [Hd Hrest].
    assert (Hstep : step s = execute s i)
      by (unfold step; rewrite Hd; reflexivity).
    assert (Hinstr : instr_at s = i) by (unfold instr_at; exact Hd).
    rewrite Hinstr, Hstep.
    rewrite (cycles_eq_machine i).
    f_equal.
    apply IH.
    + exact (Forall_inv_tail Hall).
    + destruct (Forall_inv Hall) as [Hnj Hnwpm].
      assert (Hpc : pc (execute s i) = adr (pcv s + instr_bytes i))
        by (apply nonjump_pc_advances_by_bytes; exact Hnj).
      assert (Hpcv : pcv (execute s i) = (pcv s + instr_bytes i) mod 4096).
      { unfold pcv at 1. rewrite Hpc. apply adr_val. }
      assert (Hrom : rom (execute s i) = rom s)
        by (apply execute_rom_frame; exact Hnwpm).
      rewrite Hpcv.
      apply (code_at_rom_invariant rest s (execute s i));
        [exact Hrom | exact Hrest].
Qed.

(* ===================================================================== *)
(*  The looping program:                                                 *)
(*    0: LDM 0        (0xD0)         acc := 0                            *)
(*    1: XCH 0        (0xB0)         R0 := 0                             *)
(*    2: ISZ 0, 2     (0x70 0x02)    R0 := R0+1; if R0 <> 0 goto 2       *)
(*    4: JUN 4        (0x40 0x04)    halt (jump to self)                 *)
(* ===================================================================== *)

Definition loop_rom : list byte :=
  byt 208 :: byt 176 :: byt 112 :: byt 2 :: byt 64 :: byt 4 :: repeat (byt 0) 4090.

Definition loop_start : Intel4004State := with_rom loop_rom init_state.

(** The machine state at the k-th visit to the loop head: R0 holds k. *)
Definition loop_at (k : nat) : Intel4004State :=
  with_regs (update_nth 0 (nib k) (repeat (nib 0) 16))
    (with_pc (adr 2) loop_start).

(** The exit state: R0 wrapped to zero, control fell through to the halt. *)
Definition loop_done : Intel4004State :=
  with_regs (update_nth 0 (nib 0) (repeat (nib 0) 16))
    (with_pc (adr 4) loop_start).

(** Entering the loop: two straight-line instructions establish R0 = 0. *)
Lemma loop_enter : steps 2 loop_start = loop_at 0.
Proof. vm_compute. reflexivity. Qed.

(** One trip around the loop increments R0 and branches back to the head. *)
Lemma loop_iterate : forall k, k <= 14 -> step (loop_at k) = loop_at (S k).
Proof.
  intros k Hk.
  do 15 (destruct k as [|k]; [vm_compute; reflexivity|]).
  lia.
Qed.

(** The PC-indexed loop invariant, by induction on the iteration count. *)
Lemma loop_invariant : forall k, k <= 15 -> steps (2 + k) loop_start = loop_at k.
Proof.
  induction k as [|k IH]; intros Hk.
  - rewrite Nat.add_0_r. apply loop_enter.
  - replace (2 + S k) with (S (2 + k)) by lia.
    rewrite steps_snoc.
    rewrite IH by lia.
    apply loop_iterate. lia.
Qed.

(** The sixteenth increment wraps R0 to zero and control exits the loop. *)
Lemma loop_exit : step (loop_at 15) = loop_done.
Proof. vm_compute. reflexivity. Qed.

(** Headline: the machine, fetching from ROM, runs the loop for exactly
    sixteen iterations and reaches the exit with R0 = 0. *)
Theorem iszloop_runs_on_machine : steps 18 loop_start = loop_done.
Proof.
  change 18 with (S (2 + 15)).
  rewrite steps_snoc.
  rewrite loop_invariant by lia.
  apply loop_exit.
Qed.

(** The exit is a jump-to-self, so the machine is halted there. *)
Lemma loop_done_halted : halted loop_done.
Proof.
  apply jun_self_halted. vm_compute. reflexivity.
Qed.

(** The result is confined forever after. *)
Theorem iszloop_confined_forever : forall n,
  18 <= n -> steps n loop_start = loop_done.
Proof.
  intros n Hn.
  replace n with (18 + (n - 18)) by lia.
  rewrite steps_add.
  rewrite iszloop_runs_on_machine.
  apply halted_steps_fixed. apply loop_done_halted.
Qed.

Corollary iszloop_result :
  rval (steps 18 loop_start) 0 = 0 /\ pc (steps 18 loop_start) = adr 4.
Proof.
  rewrite iszloop_runs_on_machine. split; reflexivity.
Qed.

(** Exact end-to-end time of the looping ROM program: LDM and XCH cost one
    machine cycle each, the sixteen ISZ trips cost two machine cycles each:
    8 + 8 + 16*16 = 272 clock periods. *)
Theorem iszloop_machine_time : run_cycles 18 loop_start = 272.
Proof. vm_compute. reflexivity. Qed.

(** Microcycle time is the WCET module's clock-period cost divided by the
    eight clock periods per machine cycle. *)
Theorem run_cycles_is_mc_time : forall n s,
  run_cycles n s = 8 * mc_time n s.
Proof.
  induction n as [|n IH]; intros s; simpl.
  - reflexivity.
  - rewrite IH. unfold mcycles_at.
    rewrite (cycles_eq_machine (instr_at s)). lia.
Qed.


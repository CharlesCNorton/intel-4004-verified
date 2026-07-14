(* ===================================================================== *)
(*  Intel 4004: control flow.                                            *)
(*  The general PC-indexed simulation method for arbitrary branching     *)
(*  control-flow graphs over the fetch-decode-execute machine, a         *)
(*  measured variant that reaches an exit, and a compiler for a source   *)
(*  language with assignment, sequencing, if, and while, refined all     *)
(*  the way into a packed ROM image proven to run correctly on the       *)
(*  machine.  Loop reasoning is closed at both levels: the machine       *)
(*  level by the simulation theorems, the source level by an invariant   *)
(*  rule for while.                                                      *)
(* ===================================================================== *)

From Stdlib Require Import List Arith PeanoNat Bool Lia.
Import ListNotations.
From FourK Require Import machine behavior verification.

(* ==================== Address arithmetic ==================== *)

(** Composing 12-bit normalizations. *)
Lemma adr_add_l : forall x y,
  adr (wval (adr x) + y) = adr (x + y).
Proof.
  intros x y.
  apply addr12_eq.
  rewrite !adr_val.
  apply Nat.Div0.add_mod_idemp_l.
Qed.

(* ==================== Byte images held in ROM ==================== *)

(** bs is held byte for byte in ROM starting at base. *)
Definition rom_holds (s : Intel4004State) (base : nat) (bs : list byte) : Prop :=
  forall j, j < length bs -> fetch_byte s (base + j) = nth j bs (byt 0).

Lemma rom_holds_app_l : forall s base b1 b2,
  rom_holds s base (b1 ++ b2) -> rom_holds s base b1.
Proof.
  intros s base b1 b2 H j Hj.
  assert (Hj2 : j < length (b1 ++ b2)) by (rewrite length_app; lia).
  specialize (H j Hj2).
  rewrite app_nth1 in H by exact Hj.
  exact H.
Qed.

Lemma rom_holds_app_r : forall s base b1 b2,
  rom_holds s base (b1 ++ b2) -> rom_holds s (base + length b1) b2.
Proof.
  intros s base b1 b2 H j Hj.
  assert (Hj2 : length b1 + j < length (b1 ++ b2)) by (rewrite length_app; lia).
  specialize (H (length b1 + j) Hj2).
  rewrite app_nth2 in H by lia.
  replace (length b1 + j - length b1) with j in H by lia.
  replace (base + (length b1 + j)) with (base + length b1 + j) in H by lia.
  exact H.
Qed.

(** rom_holds depends only on the ROM. *)
Lemma rom_holds_eq : forall s s' base bs,
  rom s' = rom s -> rom_holds s base bs -> rom_holds s' base bs.
Proof.
  intros s s' base bs Hrom H j Hj.
  unfold fetch_byte. rewrite Hrom.
  apply (H j Hj).
Qed.

(* ==================== Flat code segments ==================== *)

(** Program counter after a straight-line run of one-byte instructions. *)
Lemma exec_flat_pc : forall prog s,
  Forall (fun i => is_jump i = false) prog ->
  Forall (fun i => instr_bytes i = 1) prog ->
  pc (exec_program prog s) = adr (pcv s + length prog).
Proof.
  induction prog as [|i rest IH]; intros s Hnj H1b; cbn [exec_program length].
  - rewrite Nat.add_0_r. symmetry. apply adr_wval.
  - pose proof (Forall_inv Hnj) as Hnji.
    pose proof (Forall_inv H1b) as H1bi.
    cbv beta in Hnji, H1bi.
    assert (Hstep : pc (execute s i) = adr (pcv s + 1)).
    { rewrite (nonjump_pc_advances_by_bytes s i Hnji).
      rewrite H1bi. reflexivity. }
    rewrite IH; [| exact (Forall_inv_tail Hnj) | exact (Forall_inv_tail H1b)].
    unfold pcv at 1. rewrite Hstep.
    rewrite adr_add_l. f_equal. lia.
Qed.

(** Straight-line non-WPM code preserves the ROM. *)
Lemma exec_flat_rom : forall prog s,
  Forall (fun i => i <> WPM) prog ->
  rom (exec_program prog s) = rom s.
Proof.
  induction prog as [|i rest IH]; intros s H; cbn [exec_program].
  - reflexivity.
  - rewrite IH by exact (Forall_inv_tail H).
    apply execute_rom_frame. exact (Forall_inv H).
Qed.

(** Ring-pure code preserves the saved rows. *)
Lemma exec_flat_stack : forall prog s,
  Forall (fun i => writes_stack i = false) prog ->
  stk1 (exec_program prog s) = stk1 s /\
  stk2 (exec_program prog s) = stk2 s /\
  stk3 (exec_program prog s) = stk3 s.
Proof.
  induction prog as [|i rest IH]; intros s H; cbn [exec_program].
  - repeat split; reflexivity.
  - pose proof (Forall_inv H) as Hi. cbv beta in Hi.
    destruct (execute_stack_frame s i Hi) as (E1 & E2 & E3).
    destruct (IH (execute s i) (Forall_inv_tail H)) as (F1 & F2 & F3).
    rewrite F1, F2, F3, E1, E2, E3.
    repeat split; reflexivity.
Qed.

(** RAM-pure code preserves the RAM system. *)
Lemma exec_flat_ram : forall prog s,
  Forall (fun i => writes_ram i = false) prog ->
  ram_sys (exec_program prog s) = ram_sys s.
Proof.
  induction prog as [|i rest IH]; intros s H; cbn [exec_program].
  - reflexivity.
  - rewrite IH by exact (Forall_inv_tail H).
    apply execute_ram_frame. exact (Forall_inv H).
Qed.

(** Register- and accumulator-pure segments. *)
Lemma exec_flat_regs : forall prog s,
  Forall (fun i => writes_regs i = false) prog ->
  regs (exec_program prog s) = regs s.
Proof.
  induction prog as [|i rest IH]; intros s H; cbn [exec_program].
  - reflexivity.
  - rewrite IH by exact (Forall_inv_tail H).
    apply execute_regs_frame. exact (Forall_inv H).
Qed.

Lemma exec_flat_acc : forall prog s,
  Forall (fun i => writes_acc i = false) prog ->
  acc (exec_program prog s) = acc s.
Proof.
  induction prog as [|i rest IH]; intros s H; cbn [exec_program].
  - reflexivity.
  - rewrite IH by exact (Forall_inv_tail H).
    apply execute_acc_frame. exact (Forall_inv H).
Qed.

(** Running an assembled straight-line segment: the machine reproduces the
    big-step run, stays well-formed, lands just past the segment, and
    leaves ROM, ring rows, and RAM untouched. *)
Lemma run_segment : forall prog s base,
  WF s -> pcv s = base ->
  base + length prog <= 4096 ->
  Forall (fun i => (is_jump i = false /\ i <> WPM) /\ instr_bytes i = 1) prog ->
  Forall instr_wf prog ->
  Forall (fun i => writes_ram i = false /\ writes_stack i = false) prog ->
  rom_holds s base (assemble prog) ->
  steps (length prog) s = exec_program prog s /\
  WF (exec_program prog s) /\
  pc (exec_program prog s) = adr (base + length prog) /\
  rom (exec_program prog s) = rom s /\
  (stk1 (exec_program prog s) = stk1 s /\
   stk2 (exec_program prog s) = stk2 s /\
   stk3 (exec_program prog s) = stk3 s) /\
  ram_sys (exec_program prog s) = ram_sys s.
Proof.
  intros prog s base HWF Hpc Hfit Hflat Hwf Hpure Hrom.
  assert (H1b : Forall (fun i => instr_bytes i = 1) prog).
  { eapply Forall_impl; [|exact Hflat]. intros a [_ Hb]. exact Hb. }
  assert (Hnj : Forall (fun i => is_jump i = false) prog).
  { eapply Forall_impl; [|exact Hflat]. intros a [[Ha _] _]. exact Ha. }
  assert (Hsl : Forall (fun i => is_jump i = false /\ i <> WPM) prog).
  { eapply Forall_impl; [|exact Hflat]. intros a [Ha _]. exact Ha. }
  assert (Hnw : Forall (fun i => i <> WPM) prog).
  { eapply Forall_impl; [|exact Hflat]. intros a [[_ Ha] _]. exact Ha. }
  assert (Hram : Forall (fun i => writes_ram i = false) prog).
  { eapply Forall_impl; [|exact Hpure]. intros a [Ha _]. exact Ha. }
  assert (Hstk : Forall (fun i => writes_stack i = false) prog).
  { eapply Forall_impl; [|exact Hpure]. intros a [_ Ha]. exact Ha. }
  assert (HlenA : length (assemble prog) = length prog)
    by (apply assemble_length_1byte; exact H1b).
  assert (Hcode : code_at s base prog).
  { apply code_at_assembled_1byte; try assumption.
    intros j Hj. apply Hrom. rewrite HlenA. exact Hj. }
  assert (Hsteps : steps (length prog) s = exec_program prog s).
  { apply steps_tracks_exec_program; [exact Hsl |].
    rewrite Hpc. exact Hcode. }
  split; [exact Hsteps |].
  split; [apply exec_program_preserves_WF; exact HWF |].
  split.
  { rewrite exec_flat_pc by assumption. rewrite Hpc. reflexivity. }
  split; [apply exec_flat_rom; exact Hnw |].
  split; [apply exec_flat_stack; exact Hstk | apply exec_flat_ram; exact Hram].
Qed.

(* ==================== Jump-step lemmas ==================== *)

(** One machine step executes the decode of the fetched bytes. *)
Lemma step_at : forall s b1 b2,
  fetch_byte s (pcv s) = b1 ->
  fetch_byte s ((pcv s + 1) mod 4096) = b2 ->
  step s = execute s (decode b1 b2).
Proof.
  intros s b1 b2 H1 H2. unfold step. rewrite H1, H2. reflexivity.
Qed.

(** Byte 20 followed by a target byte decodes as JCN JZ. *)
Lemma decode_jcn_jz_bytes : forall t, decode (byt 20) t = JCN (nib 4) t.
Proof. intros t. reflexivity. Qed.

(** JUN's two-byte encoding decodes back for any 12-bit target. *)
Lemma decode_jun_bytes : forall a : addr12,
  decode (byt (64 + wval a / 256)) (byt (wval a mod 256)) = JUN a.
Proof.
  intros a.
  pose proof (decode_encode_id (JUN a) I) as H.
  cbn [encode] in H.
  exact H.
Qed.

(** In page 0, a taken JCN lands exactly on its target byte. *)
Lemma jcn_taken_target_page0 : forall s (off : byte),
  pcv s + 2 < 256 ->
  adr (base_for_next2 s + wval off) = adr (wval off).
Proof.
  intros s off Hpc.
  unfold base_for_next2, pc_inc2, page_base, page_of.
  rewrite adr_val.
  rewrite (Nat.mod_small (pcv s + 2) 4096) by lia.
  rewrite (Nat.div_small (pcv s + 2) 256) by lia.
  reflexivity.
Qed.

(** JCN JZ, taken: with a zero accumulator in page 0, control moves to the
    target byte. *)
Lemma exec_jcn_jz_taken : forall s (off : byte),
  aval s = 0 -> pcv s + 2 < 256 ->
  pc (execute s (JCN (nib 4) off)) = adr (wval off).
Proof.
  intros s off Hz Hpc.
  rewrite jcn_branch_taken.
  - apply jcn_taken_target_page0. exact Hpc.
  - rewrite (nib_val_small 4) by lia.
    change 4 with JCN_JZ.
    rewrite jcn_jz_semantics, Hz. reflexivity.
Qed.

(** JCN JZ, not taken: with a nonzero accumulator control falls through. *)
Lemma exec_jcn_jz_not_taken : forall s (off : byte),
  aval s <> 0 ->
  pc (execute s (JCN (nib 4) off)) = adr (pcv s + 2).
Proof.
  intros s off Hnz.
  rewrite jcn_branch_not_taken.
  - reflexivity.
  - rewrite (nib_val_small 4) by lia.
    change 4 with JCN_JZ.
    rewrite jcn_jz_semantics.
    apply Nat.eqb_neq. exact Hnz.
Qed.

(* ==================== Page-boundary NOP padding ==================== *)

(* A JCN at q branches within the page of q+2, so a compiled conditional
   skip (JCN over a 2-byte JUN, landing at q+4) is page-safe exactly when
   q+2 and q+4 share a page.  The generator pads with NOPs until the JCN
   site q satisfies q mod 256 < 252, which guarantees it; long-range
   control transfers are absolute 12-bit JUNs and need no page reasoning. *)

Definition padlen (q : nat) : nat :=
  if q mod 256 <? 252 then 0 else 256 - q mod 256.

Lemma padlen_le_4 : forall q, padlen q <= 4.
Proof.
  intro q. unfold padlen.
  destruct (q mod 256 <? 252) eqn:E; [lia |].
  apply Nat.ltb_ge in E.
  pose proof (Nat.mod_upper_bound q 256 ltac:(lia)). lia.
Qed.

Lemma padlen_safe : forall q, (q + padlen q) mod 256 < 252.
Proof.
  intro q. unfold padlen.
  destruct (q mod 256 <? 252) eqn:E.
  - rewrite Nat.add_0_r. apply Nat.ltb_lt. exact E.
  - apply Nat.ltb_ge in E.
    pose proof (Nat.mod_upper_bound q 256 ltac:(lia)) as Hub.
    pose proof (Nat.div_mod q 256 ltac:(lia)) as Hdm.
    replace (q + (256 - q mod 256)) with ((q / 256 + 1) * 256) by lia.
    rewrite Nat.Div0.mod_mul. lia.
Qed.

Lemma mod256_add2_small : forall q,
  q mod 256 < 252 -> (q + 2) mod 256 < 254.
Proof.
  intros q Hq.
  pose proof (Nat.div_mod q 256 ltac:(lia)) as Hdm.
  replace (q + 2) with (q mod 256 + 2 + q / 256 * 256) by lia.
  rewrite Nat.Div0.mod_add.
  rewrite Nat.mod_small by lia.
  lia.
Qed.

(** The padding bytes are NOPs. *)
Lemma assemble_repeat_nop : forall n,
  assemble (repeat NOP n) = repeat (byt 0) n.
Proof.
  induction n as [|n IH]; [reflexivity |].
  cbn [repeat assemble encode instr_bytes Nat.eqb app].
  f_equal. exact IH.
Qed.

Lemma repeat_nop_flat : forall n,
  Forall (fun i => (is_jump i = false /\ i <> WPM) /\ instr_bytes i = 1)
         (repeat NOP n).
Proof.
  intro n. apply Forall_repeat.
  repeat split; try reflexivity; discriminate.
Qed.

(** Running an n-NOP pad: n steps advance the PC by n and preserve
    everything else. *)
Lemma run_pad : forall n s base,
  WF s -> pcv s = base -> base + n <= 4096 ->
  rom_holds s base (repeat (byt 0) n) ->
  steps n s = exec_program (repeat NOP n) s /\
  WF (exec_program (repeat NOP n) s) /\
  pc (exec_program (repeat NOP n) s) = adr (base + n) /\
  regs (exec_program (repeat NOP n) s) = regs s /\
  acc (exec_program (repeat NOP n) s) = acc s /\
  rom (exec_program (repeat NOP n) s) = rom s /\
  (stk1 (exec_program (repeat NOP n) s) = stk1 s /\
   stk2 (exec_program (repeat NOP n) s) = stk2 s /\
   stk3 (exec_program (repeat NOP n) s) = stk3 s) /\
  ram_sys (exec_program (repeat NOP n) s) = ram_sys s.
Proof.
  intros n s base HWF Hpc Hfit Hrom.
  assert (Hflat := repeat_nop_flat n).
  assert (Hwf : Forall instr_wf (repeat NOP n))
    by (apply Forall_repeat; exact I).
  assert (Hpure : Forall (fun i => writes_ram i = false /\ writes_stack i = false)
                  (repeat NOP n))
    by (apply Forall_repeat; split; reflexivity).
  assert (Hrom' : rom_holds s base (assemble (repeat NOP n)))
    by (rewrite assemble_repeat_nop; exact Hrom).
  assert (Hlen : length (repeat NOP n) = n) by apply repeat_length.
  pose proof (run_segment (repeat NOP n) s base HWF Hpc
                ltac:(rewrite Hlen; exact Hfit) Hflat Hwf Hpure Hrom')
    as (Hsteps & HWF' & Hpc' & Hrom'' & Hstk & Hram).
  rewrite Hlen in Hsteps, Hpc'.
  split; [exact Hsteps |].
  split; [exact HWF' |].
  split; [exact Hpc' |].
  split.
  { apply exec_flat_regs. apply Forall_repeat. reflexivity. }
  split.
  { apply exec_flat_acc. apply Forall_repeat. reflexivity. }
  split; [exact Hrom'' |].
  split; [exact Hstk | exact Hram].
Qed.

(* ==================== The page-local conditional skip ==================== *)

(** The compiled skip: a JCN at q whose target byte is (q+4) mod 256 lands
    exactly at q+4, provided q+2 and q+4 share a page (guaranteed by the
    generator's padding) and q+4 is a ROM address. *)
Lemma jcn_taken_target_local : forall s,
  (pcv s + 2) mod 256 < 254 ->
  pcv s + 4 < 4096 ->
  adr (base_for_next2 s + wval (byt ((pcv s + 4) mod 256))) = adr (pcv s + 4).
Proof.
  intros s Hmod Hfit.
  f_equal.
  unfold base_for_next2, pc_inc2, page_base, page_of.
  rewrite adr_val.
  rewrite (Nat.mod_small (pcv s + 2) 4096) by lia.
  rewrite byt_val.
  rewrite (Nat.Div0.mod_mod (pcv s + 4) 256).
  pose proof (Nat.div_mod (pcv s + 2) 256 ltac:(lia)) as Hdm.
  assert (Hm4 : (pcv s + 4) mod 256 = (pcv s + 2) mod 256 + 2).
  { replace (pcv s + 4)
      with ((pcv s + 2) mod 256 + 2 + (pcv s + 2) / 256 * 256) by lia.
    rewrite Nat.Div0.mod_add.
    apply Nat.mod_small. lia. }
  rewrite Hm4. lia.
Qed.

Lemma exec_jcn_jz_taken_local : forall s,
  aval s = 0 ->
  (pcv s + 2) mod 256 < 254 ->
  pcv s + 4 < 4096 ->
  pc (execute s (JCN (nib 4) (byt ((pcv s + 4) mod 256)))) = adr (pcv s + 4).
Proof.
  intros s Hz Hmod Hfit.
  rewrite jcn_branch_taken.
  - apply jcn_taken_target_local; assumption.
  - rewrite (nib_val_small 4) by lia.
    change 4 with JCN_JZ.
    rewrite jcn_jz_semantics, Hz. reflexivity.
Qed.

(* ===================================================================== *)
(*   PC-INDEXED SIMULATION FOR ARBITRARY CONTROL-FLOW GRAPHS             *)
(* ===================================================================== *)

(* A control-flow graph over ROM is a finite domain D of program-counter
   values with an invariant family I indexed by them.  If every step from
   an invariant node lands on an invariant node, the family confines
   execution forever; this generalizes the straight-line bridge to
   arbitrary branching and is exactly the method used concretely for the
   ISZ counting loop. *)

Theorem pc_indexed_simulation :
  forall (D : list addr12) (I : addr12 -> Intel4004State -> Prop),
  (forall p s, In p D -> I p s -> pc s = p) ->
  (forall p s, In p D -> I p s ->
     exists q, In q D /\ I q (step s)) ->
  forall n p s, In p D -> I p s ->
  exists q, In q D /\ pc (steps n s) = q /\ I q (steps n s).
Proof.
  intros D I Hat Hstep n.
  induction n as [|n IH]; intros p s Hin HI.
  - exists p. repeat split; [exact Hin | apply (Hat p s Hin HI) | exact HI].
  - destruct (Hstep p s Hin HI) as (q & Hq & HIq).
    exact (IH q (step s) Hq HIq).
Qed.

(** The measured variant: if every step inside the family either strictly
    decreases a measure or exits into Q, the machine reaches Q within
    measure-plus-one steps. *)
Theorem pc_indexed_reaches :
  forall (D : list addr12) (I : addr12 -> Intel4004State -> Prop)
         (m : Intel4004State -> nat) (Q : Intel4004State -> Prop),
  (forall p s, In p D -> I p s ->
     (exists q, In q D /\ I q (step s) /\ m (step s) < m s)
     \/ Q (step s)) ->
  forall k p s, In p D -> I p s -> m s <= k ->
  exists n, n <= k + 1 /\ Q (steps n s).
Proof.
  intros D I m Q Hstep.
  induction k as [|k IH]; intros p s Hin HI Hm.
  - destruct (Hstep p s Hin HI) as [(q & _ & _ & Hlt) | HQ].
    + lia.
    + exists 1. split; [lia | exact HQ].
  - destruct (Hstep p s Hin HI) as [(q & Hq & HIq & Hlt) | HQ].
    + destruct (IH q (step s) Hq HIq ltac:(lia)) as (n & Hn & HQn).
      exists (S n). split; [lia | exact HQn].
    + exists 1. split; [lia | exact HQ].
Qed.

(* ===================================================================== *)
(*   A SOURCE LANGUAGE WITH CONTROL FLOW, COMPILED TO A ROM IMAGE        *)
(* ===================================================================== *)

(* Statements over the expression language of the verified compiler:
   assignment, sequencing, if, and while.  Conditions are expressions,
   tested against zero. *)

Inductive CStmt : Type :=
  | CAssign (r : nat) (e : Expr)
  | CSeq (a b : CStmt)
  | CIf (e : Expr) (t g : CStmt)
  | CWhile (e : Expr) (b : CStmt).

(** Environment update. *)
Definition updenv (env : nat -> nat) (r v : nat) : nat -> nat :=
  fun q => if q =? r then v else env q.

(** Fuel-indexed big-step semantics: None means the fuel ran out (a while
    loop that has not yet terminated), Some the final register
    environment. *)
Fixpoint csem (fuel : nat) (st : CStmt) (env : nat -> nat)
  : option (nat -> nat) :=
  match fuel with
  | 0 => None
  | S f =>
      match st with
      | CAssign r e => Some (updenv env r (eval env e))
      | CSeq a b =>
          match csem f a env with
          | Some env1 => csem f b env1
          | None => None
          end
      | CIf e t g =>
          if eval env e =? 0 then csem f g env else csem f t env
      | CWhile e b =>
          if eval env e =? 0 then Some env
          else match csem f b env with
               | Some env1 => csem f (CWhile e b) env1
               | None => None
               end
      end
  end.

(** Definitional unfolding equations for csem at successor fuel. *)
Lemma csem_S_assign : forall f r e env,
  csem (S f) (CAssign r e) env = Some (updenv env r (eval env e)).
Proof. reflexivity. Qed.

Lemma csem_S_seq : forall f a b env,
  csem (S f) (CSeq a b) env =
  match csem f a env with
  | Some env1 => csem f b env1
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma csem_S_if : forall f e t g env,
  csem (S f) (CIf e t g) env =
  if eval env e =? 0 then csem f g env else csem f t env.
Proof. reflexivity. Qed.

Lemma csem_S_while : forall f e b env,
  csem (S f) (CWhile e b) env =
  if eval env e =? 0 then Some env
  else match csem f b env with
       | Some env1 => csem f (CWhile e b) env1
       | None => None
       end.
Proof. reflexivity. Qed.

(** Well-formed statements: targets in the low registers, expressions
    well-formed with at most eight scratch registers. *)
Fixpoint cstmt_wf (st : CStmt) : Prop :=
  match st with
  | CAssign r e => r < 8 /\ expr_wf e /\ need e <= 8
  | CSeq a b => cstmt_wf a /\ cstmt_wf b
  | CIf e t g => expr_wf e /\ need e <= 8 /\ cstmt_wf t /\ cstmt_wf g
  | CWhile e b => expr_wf e /\ need e <= 8 /\ cstmt_wf b
  end.

(** Byte length of an expression block. *)
Definition elen (e : Expr) : nat := length (compile_expr e 8).

Lemma elen_ge_1 : forall e, 1 <= elen e.
Proof.
  intro e. unfold elen.
  destruct e; cbn [compile_expr]; rewrite ?length_app; cbn [length]; lia.
Qed.

(** Byte size of the compiled statement, at a placement address (padding
    before each conditional skip makes size address-dependent). *)
Fixpoint csize (st : CStmt) (base : nat) : nat :=
  match st with
  | CAssign r e => elen e + 1
  | CSeq a b => csize a base + csize b (base + csize a base)
  | CIf e t g =>
      let pad := padlen (base + elen e) in
      let q := base + elen e + pad in
      let pg := q + 4 in
      let pgj := pg + csize g pg in
      let pt := pgj + 2 in
      elen e + pad + 6 + csize g pg + csize t pt
  | CWhile e b =>
      let pad := padlen (base + elen e) in
      let q := base + elen e + pad in
      let pb := q + 6 in
      elen e + pad + 8 + csize b pb
  end.

Lemma csize_ge_2 : forall st base, 2 <= csize st base.
Proof.
  induction st as [r e | a IHa b IHb | e t IHt g IHg | e b IHb];
    intro base0; cbn [csize]; cbv zeta.
  - pose proof (elen_ge_1 e). lia.
  - pose proof (IHa base0). lia.
  - lia.
  - lia.
Qed.

(* Code generation at a base address.  Conditionals compile page-free: the
   JCN skips forward 4 bytes over an absolute JUN (NOP padding keeps that
   skip inside one page), and every long-range control transfer is an
   absolute 12-bit JUN, so images may span pages and sit anywhere in ROM.
     CIf:    expr; pad; JCN JZ ->q+4; JUN ->then; else; JUN ->end; then
     CWhile: expr; pad; JCN JZ ->q+4; JUN ->body; JUN ->end;
             body; JUN ->head                                            *)
Fixpoint cgen (st : CStmt) (base : nat) : list byte :=
  match st with
  | CAssign r e => assemble (compile_stmt (SAssign r e))
  | CSeq a b => cgen a base ++ cgen b (base + csize a base)
  | CIf e t g =>
      let pad := padlen (base + elen e) in
      let q := base + elen e + pad in
      let pg := q + 4 in
      let pgj := pg + csize g pg in
      let pt := pgj + 2 in
      let pend := pt + csize t pt in
      assemble (compile_expr e 8)
        ++ repeat (byt 0) pad
        ++ [byt 20; byt (pg mod 256)]
        ++ [byt (64 + pt / 256); byt (pt mod 256)]
        ++ cgen g pg
        ++ [byt (64 + pend / 256); byt (pend mod 256)]
        ++ cgen t pt
  | CWhile e b =>
      let pad := padlen (base + elen e) in
      let q := base + elen e + pad in
      let pb := q + 6 in
      let pj := pb + csize b pb in
      let pend := pj + 2 in
      assemble (compile_expr e 8)
        ++ repeat (byt 0) pad
        ++ [byt 20; byt ((q + 4) mod 256)]
        ++ [byt (64 + pb / 256); byt (pb mod 256)]
        ++ [byt (64 + pend / 256); byt (pend mod 256)]
        ++ cgen b pb
        ++ [byt (64 + base / 256); byt (base mod 256)]
  end.

(* ==================== Static facts about generated code ==================== *)

(** Generated code lengths follow csize. *)
Lemma cgen_length : forall st base, length (cgen st base) = csize st base.
Proof.
  induction st as [r e | a IHa b IHb | e t IHt g IHg | e b IHb];
    intros base; cbn [cgen csize]; cbv zeta.
  - rewrite assemble_length_1byte.
    + cbn [compile_stmt]. rewrite length_app. cbn [length]. unfold elen. lia.
    + eapply Forall_impl; [|apply (compile_stmt_flat (SAssign r e))].
      intros i [_ Hb]. exact Hb.
  - rewrite length_app, IHa, IHb. reflexivity.
  - rewrite !length_app, repeat_length.
    rewrite assemble_length_1byte.
    + cbn [length]. rewrite IHt, IHg. unfold elen. lia.
    + eapply Forall_impl; [|apply (compile_expr_flat e 8)].
      intros i [_ Hb]. exact Hb.
  - rewrite !length_app, repeat_length.
    rewrite assemble_length_1byte.
    + cbn [length]. rewrite IHb. unfold elen. lia.
    + eapply Forall_impl; [|apply (compile_expr_flat e 8)].
      intros i [_ Hb]. exact Hb.
Qed.

(* ==================== Running an expression block ==================== *)

(** Running a compiled expression block held in ROM: some number of steps
    computes the expression into the accumulator, preserves the low
    registers, and moves the program counter just past the block. *)
Lemma run_expr_block : forall e s base,
  WF s -> pcv s = base -> expr_wf e -> need e <= 8 ->
  base + elen e <= 4096 ->
  rom_holds s base (assemble (compile_expr e 8)) ->
  WF (steps (elen e) s) /\
  pc (steps (elen e) s) = adr (base + elen e) /\
  aval (steps (elen e) s) = eval (fun r => rval s r) e /\
  (forall r, r < 8 -> get_reg (steps (elen e) s) r = get_reg s r) /\
  rom (steps (elen e) s) = rom s /\
  (stk1 (steps (elen e) s) = stk1 s /\
   stk2 (steps (elen e) s) = stk2 s /\
   stk3 (steps (elen e) s) = stk3 s) /\
  ram_sys (steps (elen e) s) = ram_sys s.
Proof.
  intros e s base HWF Hpc He Hn Hfit Hrom.
  assert (Hwfp : Forall instr_wf (compile_expr e 8))
    by (apply compile_expr_instr_wf).
  pose proof (run_segment (compile_expr e 8) s base HWF Hpc
                Hfit (compile_expr_flat e 8) Hwfp (compile_expr_pure e 8) Hrom)
    as (Hsteps & HWF' & Hpc' & Hrom' & Hstk' & Hram').
  destruct (compile_expr_correct e 8 s HWF He ltac:(lia) ltac:(lia))
    as (_ & Hacc & Hfr).
  unfold elen. rewrite Hsteps.
  split; [assumption |].
  split; [assumption |].
  split; [assumption |].
  split.
  { intros r Hr. apply Hfr. lia. }
  split; [assumption |].
  split; assumption.
Qed.

(* ==================== The main refinement ==================== *)

(** Machine correctness of generated code: whenever the source semantics
    terminates on some fuel, some number of machine steps runs the compiled
    bytes from ROM to the block exit with the final environment in the low
    registers, preserving ROM, the ring rows, and RAM. *)
Lemma cgen_correct : forall fuel st env env' s base,
  WF s ->
  cstmt_wf st ->
  base + csize st base < 4096 ->
  rom_holds s base (cgen st base) ->
  pcv s = base ->
  (forall r, r < 8 -> env r = rval s r) ->
  csem fuel st env = Some env' ->
  exists n,
    WF (steps n s) /\
    pcv (steps n s) = base + csize st base /\
    (forall r, r < 8 -> rval (steps n s) r = env' r) /\
    rom (steps n s) = rom s /\
    (stk1 (steps n s) = stk1 s /\
     stk2 (steps n s) = stk2 s /\
     stk3 (steps n s) = stk3 s) /\
    ram_sys (steps n s) = ram_sys s.
Proof.
  induction fuel as [|f IH];
    intros st env env' s base HWF Hwf Hfit Hrom Hpc Henv Hsem;
    [discriminate Hsem |].
  destruct st as [r e | a b | e t g | e b].

  - (* CAssign *)
    rewrite csem_S_assign in Hsem. injection Hsem as <-.
    cbn [cstmt_wf] in Hwf. destruct Hwf as (Hr & He & Hn).
    cbn [csize] in Hfit.
    set (prog := compile_stmt (SAssign r e)).
    assert (Hlenp : length prog = elen e + 1).
    { unfold prog. cbn [compile_stmt]. rewrite length_app. cbn [length].
      unfold elen. lia. }
    assert (Hswf : stmt_wf (SAssign r e)) by (cbn [stmt_wf]; auto).
    assert (Hwfp : Forall instr_wf prog)
      by (apply compile_stmt_instr_wf).
    pose proof (run_segment prog s base HWF Hpc
                  ltac:(rewrite Hlenp; lia)
                  (compile_stmt_flat (SAssign r e)) Hwfp
                  (compile_assign_pure r e) Hrom)
      as (Hsteps & HWF' & Hpc' & Hrom' & Hstk' & Hram').
    exists (length prog).
    rewrite Hsteps.
    destruct (compile_stmt_correct (SAssign r e) s HWF Hswf) as (_ & Hsem').
    fold prog in Hsem'.
    split; [exact HWF' |].
    split.
    { unfold pcv. rewrite Hpc'. rewrite adr_val.
      rewrite Nat.mod_small by (rewrite Hlenp; cbn [csize]; lia).
      rewrite Hlenp. cbn [csize]. lia. }
    split.
    { intros q Hq.
      rewrite (Hsem' q Hq). cbn [sem_stmt].
      unfold updenv.
      destruct (q =? r) eqn:Eq.
      - apply eval_ext; [exact He |].
        intros p Hp. symmetry. apply Henv. exact Hp.
      - symmetry. apply Henv. exact Hq. }
    split; [exact Hrom' |].
    split; [exact Hstk' | exact Hram'].

  - (* CSeq *)
    rewrite csem_S_seq in Hsem.
    destruct (csem f a env) as [env1|] eqn:Ea; [| discriminate Hsem].
    cbn [cstmt_wf] in Hwf. destruct Hwf as [Hwa Hwb].
    cbn [csize] in Hfit.
    cbn [cgen] in Hrom.
    pose proof (rom_holds_app_l _ _ _ _ Hrom) as Hrom_a.
    pose proof (rom_holds_app_r _ _ _ _ Hrom) as Hrom_b.
    rewrite cgen_length in Hrom_b.
    destruct (IH a env env1 s base HWF Hwa ltac:(lia) Hrom_a Hpc Henv Ea)
      as (n1 & HWF1 & Hpc1 & Hreg1 & Hrom1 & Hstk1 & Hram1).
    set (s1 := steps n1 s) in *.
    assert (Hrom_b1 : rom_holds s1 (base + csize a base)
                        (cgen b (base + csize a base)))
      by (apply (rom_holds_eq s s1); assumption).
    assert (Henv1 : forall r, r < 8 -> env1 r = rval s1 r)
      by (intros r Hr; symmetry; apply Hreg1; exact Hr).
    destruct (IH b env1 env' s1 (base + csize a base) HWF1 Hwb ltac:(lia)
                Hrom_b1 Hpc1 Henv1 Hsem)
      as (n2 & HWF2 & Hpc2 & Hreg2 & Hrom2 & Hstk2 & Hram2).
    exists (n1 + n2).
    rewrite steps_add. fold s1.
    split; [exact HWF2 |].
    split; [rewrite Hpc2; cbn [csize]; lia |].
    split; [exact Hreg2 |].
    split; [rewrite Hrom2; exact Hrom1 |].
    destruct Hstk1 as (Ha1 & Ha2 & Ha3).
    destruct Hstk2 as (Hb1 & Hb2 & Hb3).
    split; [| rewrite Hram2; exact Hram1].
    rewrite Hb1, Hb2, Hb3. auto.

  - (* CIf *)
    rewrite csem_S_if in Hsem.
    cbn [cstmt_wf] in Hwf. destruct Hwf as (He & Hn & Hwt & Hwg).
    cbn [csize] in Hfit. cbv zeta in Hfit.
    cbn [cgen] in Hrom. cbv zeta in Hrom.
    set (pe := base + elen e) in *.
    set (pad := padlen pe) in *.
    set (q := pe + pad) in *.
    set (pg := q + 4) in *.
    set (pgj := pg + csize g pg) in *.
    set (pt := pgj + 2) in *.
    set (pend := pt + csize t pt) in *.
    (* decompose the image *)
    pose proof (rom_holds_app_l _ _ _ _ Hrom) as Hrom_e.
    pose proof (rom_holds_app_r _ _ _ _ Hrom) as Hrest.
    rewrite assemble_length_1byte in Hrest
      by (eapply Forall_impl; [|apply (compile_expr_flat e 8)];
          intros i [_ Hb]; exact Hb).
    fold (elen e) in Hrest. fold pe in Hrest.
    pose proof (rom_holds_app_l _ _ _ _ Hrest) as Hrom_pad.
    pose proof (rom_holds_app_r _ _ _ _ Hrest) as Hrest2.
    rewrite repeat_length in Hrest2. fold q in Hrest2.
    pose proof (rom_holds_app_l _ _ _ _ Hrest2) as Hrom_jcn.
    pose proof (rom_holds_app_r _ _ _ _ Hrest2) as Hrest3.
    cbn [length] in Hrest3.
    pose proof (rom_holds_app_l _ _ _ _ Hrest3) as Hrom_jun_t.
    pose proof (rom_holds_app_r _ _ _ _ Hrest3) as Hrest4.
    cbn [length] in Hrest4.
    replace (q + 2 + 2) with pg in Hrest4 by (unfold pg; lia).
    pose proof (rom_holds_app_l _ _ _ _ Hrest4) as Hrom_g.
    pose proof (rom_holds_app_r _ _ _ _ Hrest4) as Hrest5.
    rewrite cgen_length in Hrest5. fold pgj in Hrest5.
    pose proof (rom_holds_app_l _ _ _ _ Hrest5) as Hrom_jun_end.
    pose proof (rom_holds_app_r _ _ _ _ Hrest5) as Hrom_t.
    cbn [length] in Hrom_t. fold pt in Hrom_t.
    (* run the expression block *)
    pose proof (run_expr_block e s base HWF Hpc He Hn
                  ltac:(unfold pend, pt, pgj, pg, q, pad, pe in *; lia) Hrom_e)
      as (HWF1 & Hpc1 & Hacc1 & Hreg1 & Hrom1 & Hstk1 & Hram1).
    set (s1 := steps (elen e) s) in *.
    assert (Hpc1' : pcv s1 = pe).
    { unfold pcv. rewrite Hpc1. rewrite adr_val.
      apply Nat.mod_small. unfold pend, pt, pgj, pg, q, pad, pe in *. lia. }
    (* run the padding *)
    assert (Hrom_pad1 : rom_holds s1 pe (repeat (byt 0) pad))
      by (apply (rom_holds_eq s s1); assumption).
    pose proof (run_pad pad s1 pe HWF1 Hpc1'
                  ltac:(unfold pend, pt, pgj, pg, q, pad, pe in *; lia) Hrom_pad1)
      as (Hsteps_p & HWFp & Hpcp & Hregsp & Haccp & Hromp & Hstkp & Hramp).
    set (s1' := exec_program (repeat NOP pad) s1) in *.
    assert (Hpcq : pcv s1' = q).
    { unfold pcv. rewrite Hpcp. rewrite adr_val.
      apply Nat.mod_small. unfold pend, pt, pgj, pg, q, pad, pe in *. lia. }
    assert (Hacc1' : aval s1' = eval env e).
    { unfold aval. rewrite Haccp.
      change (wval (acc s1)) with (aval s1).
      rewrite Hacc1.
      apply eval_ext; [exact He |].
      intros z Hz. symmetry. apply Henv. exact Hz. }
    assert (Hreg1' : forall z, z < 8 -> get_reg s1' z = get_reg s z).
    { intros z Hz. unfold get_reg. rewrite Hregsp.
      exact (Hreg1 z Hz). }
    assert (Hrom1' : rom s1' = rom s) by (rewrite Hromp; exact Hrom1).
    (* the JCN skip *)
    assert (Hf1 : fetch_byte s1' (pcv s1') = byt 20).
    { specialize (Hrom_jcn 0 ltac:(cbn [length]; lia)).
      rewrite Nat.add_0_r in Hrom_jcn. cbn [nth] in Hrom_jcn.
      rewrite Hpcq.
      unfold fetch_byte in *. rewrite Hrom1'. exact Hrom_jcn. }
    assert (Hf2 : fetch_byte s1' ((pcv s1' + 1) mod 4096) = byt (pg mod 256)).
    { specialize (Hrom_jcn 1 ltac:(cbn [length]; lia)).
      cbn [nth] in Hrom_jcn.
      rewrite Hpcq.
      rewrite (Nat.mod_small (q + 1) 4096)
        by (unfold pend, pt, pgj, pg, q, pad, pe in *; lia).
      unfold fetch_byte in *. rewrite Hrom1'. exact Hrom_jcn. }
    assert (Hstep1 : step s1' = execute s1' (JCN (nib 4) (byt (pg mod 256)))).
    { rewrite (step_at s1' (byt 20) (byt (pg mod 256)) Hf1 Hf2).
      rewrite decode_jcn_jz_bytes. reflexivity. }
    assert (HWF2 : WF (execute s1' (JCN (nib 4) (byt (pg mod 256)))))
      by (apply execute_preserves_WF; exact HWFp).
    set (s2 := execute s1' (JCN (nib 4) (byt (pg mod 256)))) in *.
    assert (Hregs2 : regs s2 = regs s1')
      by (apply execute_regs_frame; reflexivity).
    assert (Hrom2 : rom s2 = rom s).
    { unfold s2.
      rewrite (execute_rom_frame s1' (JCN (nib 4) (byt (pg mod 256))))
        by discriminate.
      exact Hrom1'. }
    assert (Hstk2 : stk1 s2 = stk1 s1' /\ stk2 s2 = stk2 s1' /\ stk3 s2 = stk3 s1')
      by (apply execute_stack_frame; reflexivity).
    assert (Hram2 : ram_sys s2 = ram_sys s1')
      by (apply execute_ram_frame; reflexivity).
    assert (Henv2 : forall z, z < 8 -> env z = rval s2 z).
    { intros z Hz. unfold rval, get_reg. rewrite Hregs2.
      rewrite (Henv z Hz). unfold rval. f_equal.
      symmetry. exact (Hreg1' z Hz). }
    destruct (eval env e =? 0) eqn:Ez.
    + (* condition zero: skip lands on the else block at pg *)
      apply Nat.eqb_eq in Ez.
      assert (Hpc2 : pcv s2 = pg).
      { unfold pcv, s2.
        replace (byt (pg mod 256)) with (byt ((pcv s1' + 4) mod 256))
          by (rewrite Hpcq; unfold pg; reflexivity).
        rewrite exec_jcn_jz_taken_local.
        - rewrite adr_val. rewrite Hpcq.
          replace (q + 4) with pg by (unfold pg; lia).
          apply Nat.mod_small.
          unfold pend, pt, pgj, pg, q, pad, pe in *. lia.
        - rewrite Hacc1'. exact Ez.
        - rewrite Hpcq.
          apply mod256_add2_small.
          replace q with (pe + padlen pe) by reflexivity.
          apply padlen_safe.
        - rewrite Hpcq. unfold pend, pt, pgj, pg, q, pad, pe in *. lia. }
      assert (Hrom_g2 : rom_holds s2 pg (cgen g pg))
        by (apply (rom_holds_eq s s2); assumption).
      destruct (IH g env env' s2 pg HWF2 Hwg
                  ltac:(unfold pend, pt, pgj, pg, q, pad, pe in *; lia)
                  Hrom_g2 Hpc2 Henv2 Hsem)
        as (n3 & HWF3 & Hpc3 & Hreg3 & Hrom3 & Hstk3 & Hram3).
      set (s3 := steps n3 s2) in *.
      assert (Hpc3' : pcv s3 = pgj) by exact Hpc3.
      assert (Hrom3' : rom s3 = rom s) by (rewrite Hrom3; exact Hrom2).
      assert (Hpend : pend < 4096)
        by (unfold pend, pt, pgj, pg, q, pad, pe in *; lia).
      (* the JUN past the then block *)
      assert (Hg1 : fetch_byte s3 (pcv s3) = byt (64 + pend / 256)).
      { specialize (Hrom_jun_end 0 ltac:(cbn [length]; lia)).
        rewrite Nat.add_0_r in Hrom_jun_end. cbn [nth] in Hrom_jun_end.
        rewrite Hpc3'.
        unfold fetch_byte in *. rewrite Hrom3'. exact Hrom_jun_end. }
      assert (Hg2 : fetch_byte s3 ((pcv s3 + 1) mod 4096) = byt (pend mod 256)).
      { specialize (Hrom_jun_end 1 ltac:(cbn [length]; lia)).
        cbn [nth] in Hrom_jun_end.
        rewrite Hpc3'.
        rewrite (Nat.mod_small (pgj + 1) 4096)
          by (unfold pend, pt, pgj, pg, q, pad, pe in *; lia).
        unfold fetch_byte in *. rewrite Hrom3'. exact Hrom_jun_end. }
      assert (Hstep3 : step s3 = execute s3 (JUN (adr pend))).
      { rewrite (step_at s3 _ _ Hg1 Hg2).
        replace (byt (64 + pend / 256))
          with (byt (64 + wval (adr pend) / 256))
          by (rewrite adr_val_small by exact Hpend; reflexivity).
        replace (byt (pend mod 256))
          with (byt (wval (adr pend) mod 256))
          by (rewrite adr_val_small by exact Hpend; reflexivity).
        rewrite decode_jun_bytes. reflexivity. }
      set (s4 := execute s3 (JUN (adr pend))) in *.
      assert (HWF4 : WF s4) by (apply execute_preserves_WF; exact HWF3).
      assert (Hregs4 : regs s4 = regs s3)
        by (apply execute_regs_frame; reflexivity).
      exists (elen e + (pad + (1 + (n3 + 1)))).
      rewrite steps_add. fold s1.
      rewrite steps_add. rewrite Hsteps_p. fold s1'.
      replace (steps (1 + (n3 + 1)) s1') with (steps (n3 + 1) (step s1'))
        by (rewrite (steps_add 1 (n3 + 1) s1'); reflexivity).
      rewrite Hstep1. fold s2.
      rewrite steps_add. fold s3.
      replace (steps 1 s3) with (step s3) by reflexivity.
      rewrite Hstep3. fold s4.
      split; [exact HWF4 |].
      split.
      { unfold s4, pcv. rewrite pc_shape_jun.
        rewrite adr_val_small by exact Hpend.
        unfold pend, pt, pgj, pg, q, pad, pe. cbn [csize]. cbv zeta. lia. }
      split.
      { intros z Hz. unfold rval, get_reg. rewrite Hregs4.
        exact (Hreg3 z Hz). }
      split.
      { unfold s4.
        rewrite (execute_rom_frame s3 (JUN (adr pend))) by discriminate.
        exact Hrom3'. }
      destruct Hstkp as (Hp1 & Hp2 & Hp3).
      destruct Hstk1 as (Hs11 & Hs12 & Hs13).
      destruct Hstk2 as (Hs21 & Hs22 & Hs23).
      destruct Hstk3 as (Hs31 & Hs32 & Hs33).
      destruct (execute_stack_frame s3 (JUN (adr pend)) ltac:(reflexivity))
        as (Hs41 & Hs42 & Hs43).
      split.
      { unfold s4.
        rewrite Hs41, Hs42, Hs43, Hs31, Hs32, Hs33, Hs21, Hs22, Hs23,
                Hp1, Hp2, Hp3, Hs11, Hs12, Hs13.
        auto. }
      { unfold s4.
        rewrite (execute_ram_frame s3 (JUN (adr pend))) by reflexivity.
        rewrite Hram3, Hram2, Hramp. exact Hram1. }
    + (* condition nonzero: fall through the skip, JUN to the then block *)
      apply Nat.eqb_neq in Ez.
      assert (Hpc2 : pcv s2 = q + 2).
      { unfold pcv, s2.
        rewrite exec_jcn_jz_not_taken by (rewrite Hacc1'; exact Ez).
        rewrite adr_val. rewrite Hpcq.
        apply Nat.mod_small.
        unfold pend, pt, pgj, pg, q, pad, pe in *. lia. }
      assert (Hpt4096 : pt < 4096)
        by (unfold pend, pt, pgj, pg, q, pad, pe in *; lia).
      assert (Hg1 : fetch_byte s2 (pcv s2) = byt (64 + pt / 256)).
      { specialize (Hrom_jun_t 0 ltac:(cbn [length]; lia)).
        rewrite Nat.add_0_r in Hrom_jun_t. cbn [nth] in Hrom_jun_t.
        rewrite Hpc2.
        unfold fetch_byte in *. rewrite Hrom2. exact Hrom_jun_t. }
      assert (Hg2 : fetch_byte s2 ((pcv s2 + 1) mod 4096) = byt (pt mod 256)).
      { specialize (Hrom_jun_t 1 ltac:(cbn [length]; lia)).
        cbn [nth] in Hrom_jun_t.
        rewrite Hpc2.
        rewrite (Nat.mod_small (q + 2 + 1) 4096)
          by (unfold pend, pt, pgj, pg, q, pad, pe in *; lia).
        unfold fetch_byte in *. rewrite Hrom2. exact Hrom_jun_t. }
      assert (Hstep2 : step s2 = execute s2 (JUN (adr pt))).
      { rewrite (step_at s2 _ _ Hg1 Hg2).
        replace (byt (64 + pt / 256))
          with (byt (64 + wval (adr pt) / 256))
          by (rewrite adr_val_small by exact Hpt4096; reflexivity).
        replace (byt (pt mod 256))
          with (byt (wval (adr pt) mod 256))
          by (rewrite adr_val_small by exact Hpt4096; reflexivity).
        rewrite decode_jun_bytes. reflexivity. }
      set (s3 := execute s2 (JUN (adr pt))) in *.
      assert (HWF3 : WF s3) by (apply execute_preserves_WF; exact HWF2).
      assert (Hpc3 : pcv s3 = pt).
      { unfold pcv, s3. rewrite pc_shape_jun.
        apply adr_val_small. exact Hpt4096. }
      assert (Hregs3 : regs s3 = regs s2)
        by (apply execute_regs_frame; reflexivity).
      assert (Hrom3 : rom s3 = rom s).
      { unfold s3.
        rewrite (execute_rom_frame s2 (JUN (adr pt))) by discriminate.
        exact Hrom2. }
      assert (Hrom_t3 : rom_holds s3 pt (cgen t pt))
        by (apply (rom_holds_eq s s3); assumption).
      assert (Henv3 : forall z, z < 8 -> env z = rval s3 z).
      { intros z Hz. unfold rval, get_reg. rewrite Hregs3.
        exact (Henv2 z Hz). }
      destruct (IH t env env' s3 pt HWF3 Hwt
                  ltac:(unfold pend, pt, pgj, pg, q, pad, pe in *; lia)
                  Hrom_t3 Hpc3 Henv3 Hsem)
        as (n4 & HWF4 & Hpc4 & Hreg4 & Hrom4 & Hstk4 & Hram4).
      exists (elen e + (pad + (1 + (1 + n4)))).
      rewrite steps_add. fold s1.
      rewrite steps_add. rewrite Hsteps_p. fold s1'.
      replace (steps (1 + (1 + n4)) s1') with (steps (1 + n4) (step s1'))
        by (rewrite (steps_add 1 (1 + n4) s1'); reflexivity).
      rewrite Hstep1. fold s2.
      replace (steps (1 + n4) s2) with (steps n4 (step s2))
        by (rewrite (steps_add 1 n4 s2); reflexivity).
      rewrite Hstep2. fold s3.
      split; [exact HWF4 |].
      split.
      { rewrite Hpc4.
        unfold pend, pt, pgj, pg, q, pad, pe. cbn [csize]. cbv zeta. lia. }
      split; [exact Hreg4 |].
      split; [rewrite Hrom4; exact Hrom3 |].
      destruct Hstkp as (Hp1 & Hp2 & Hp3).
      destruct Hstk1 as (Hs11 & Hs12 & Hs13).
      destruct Hstk2 as (Hs21 & Hs22 & Hs23).
      destruct (execute_stack_frame s2 (JUN (adr pt)) ltac:(reflexivity))
        as (Hs31 & Hs32 & Hs33).
      destruct Hstk4 as (Hs41 & Hs42 & Hs43).
      split.
      { rewrite Hs41, Hs42, Hs43. unfold s3.
        rewrite Hs31, Hs32, Hs33, Hs21, Hs22, Hs23, Hp1, Hp2, Hp3,
                Hs11, Hs12, Hs13.
        auto. }
      { rewrite Hram4. unfold s3.
        rewrite (execute_ram_frame s2 (JUN (adr pt))) by reflexivity.
        rewrite Hram2, Hramp. exact Hram1. }

  - (* CWhile *)
    rewrite csem_S_while in Hsem.
    cbn [cstmt_wf] in Hwf. destruct Hwf as (He & Hn & Hwb).
    cbn [csize] in Hfit. cbv zeta in Hfit.
    cbn [cgen] in Hrom. cbv zeta in Hrom.
    set (pe := base + elen e) in *.
    set (pad := padlen pe) in *.
    set (q := pe + pad) in *.
    set (pb := q + 6) in *.
    set (pj := pb + csize b pb) in *.
    set (pend := pj + 2) in *.
    (* decompose the image *)
    pose proof (rom_holds_app_l _ _ _ _ Hrom) as Hrom_e.
    pose proof (rom_holds_app_r _ _ _ _ Hrom) as Hrest.
    rewrite assemble_length_1byte in Hrest
      by (eapply Forall_impl; [|apply (compile_expr_flat e 8)];
          intros i [_ Hb]; exact Hb).
    fold (elen e) in Hrest. fold pe in Hrest.
    pose proof (rom_holds_app_l _ _ _ _ Hrest) as Hrom_pad.
    pose proof (rom_holds_app_r _ _ _ _ Hrest) as Hrest2.
    rewrite repeat_length in Hrest2. fold q in Hrest2.
    pose proof (rom_holds_app_l _ _ _ _ Hrest2) as Hrom_jcn.
    pose proof (rom_holds_app_r _ _ _ _ Hrest2) as Hrest3.
    cbn [length] in Hrest3.
    pose proof (rom_holds_app_l _ _ _ _ Hrest3) as Hrom_jun_b.
    pose proof (rom_holds_app_r _ _ _ _ Hrest3) as Hrest4.
    cbn [length] in Hrest4.
    pose proof (rom_holds_app_l _ _ _ _ Hrest4) as Hrom_jun_end.
    pose proof (rom_holds_app_r _ _ _ _ Hrest4) as Hrest5.
    cbn [length] in Hrest5.
    replace (q + 2 + 2 + 2) with pb in Hrest5 by (unfold pb; lia).
    replace (q + 2 + 2) with (q + 4) in Hrom_jun_end by lia.
    pose proof (rom_holds_app_l _ _ _ _ Hrest5) as Hrom_b.
    pose proof (rom_holds_app_r _ _ _ _ Hrest5) as Hrom_jun_back.
    rewrite cgen_length in Hrom_jun_back. fold pj in Hrom_jun_back.
    (* run the expression block *)
    pose proof (run_expr_block e s base HWF Hpc He Hn
                  ltac:(unfold pend, pj, pb, q, pad, pe in *; lia) Hrom_e)
      as (HWF1 & Hpc1 & Hacc1 & Hreg1 & Hrom1 & Hstk1 & Hram1).
    set (s1 := steps (elen e) s) in *.
    assert (Hpc1' : pcv s1 = pe).
    { unfold pcv. rewrite Hpc1. rewrite adr_val.
      apply Nat.mod_small. unfold pend, pj, pb, q, pad, pe in *. lia. }
    (* run the padding *)
    assert (Hrom_pad1 : rom_holds s1 pe (repeat (byt 0) pad))
      by (apply (rom_holds_eq s s1); assumption).
    pose proof (run_pad pad s1 pe HWF1 Hpc1'
                  ltac:(unfold pend, pj, pb, q, pad, pe in *; lia) Hrom_pad1)
      as (Hsteps_p & HWFp & Hpcp & Hregsp & Haccp & Hromp & Hstkp & Hramp).
    set (s1' := exec_program (repeat NOP pad) s1) in *.
    assert (Hpcq : pcv s1' = q).
    { unfold pcv. rewrite Hpcp. rewrite adr_val.
      apply Nat.mod_small. unfold pend, pj, pb, q, pad, pe in *. lia. }
    assert (Hacc1' : aval s1' = eval env e).
    { unfold aval. rewrite Haccp.
      change (wval (acc s1)) with (aval s1).
      rewrite Hacc1.
      apply eval_ext; [exact He |].
      intros z Hz. symmetry. apply Henv. exact Hz. }
    assert (Hreg1' : forall z, z < 8 -> get_reg s1' z = get_reg s z).
    { intros z Hz. unfold get_reg. rewrite Hregsp.
      exact (Hreg1 z Hz). }
    assert (Hrom1' : rom s1' = rom s) by (rewrite Hromp; exact Hrom1).
    (* the JCN skip *)
    assert (Hf1 : fetch_byte s1' (pcv s1') = byt 20).
    { specialize (Hrom_jcn 0 ltac:(cbn [length]; lia)).
      rewrite Nat.add_0_r in Hrom_jcn. cbn [nth] in Hrom_jcn.
      rewrite Hpcq.
      unfold fetch_byte in *. rewrite Hrom1'. exact Hrom_jcn. }
    assert (Hf2 : fetch_byte s1' ((pcv s1' + 1) mod 4096)
                  = byt ((q + 4) mod 256)).
    { specialize (Hrom_jcn 1 ltac:(cbn [length]; lia)).
      cbn [nth] in Hrom_jcn.
      rewrite Hpcq.
      rewrite (Nat.mod_small (q + 1) 4096)
        by (unfold pend, pj, pb, q, pad, pe in *; lia).
      unfold fetch_byte in *. rewrite Hrom1'. exact Hrom_jcn. }
    assert (Hstep1 : step s1'
                     = execute s1' (JCN (nib 4) (byt ((q + 4) mod 256)))).
    { rewrite (step_at s1' (byt 20) (byt ((q + 4) mod 256)) Hf1 Hf2).
      rewrite decode_jcn_jz_bytes. reflexivity. }
    assert (HWF2 : WF (execute s1' (JCN (nib 4) (byt ((q + 4) mod 256)))))
      by (apply execute_preserves_WF; exact HWFp).
    set (s2 := execute s1' (JCN (nib 4) (byt ((q + 4) mod 256)))) in *.
    assert (Hregs2 : regs s2 = regs s1')
      by (apply execute_regs_frame; reflexivity).
    assert (Hrom2 : rom s2 = rom s).
    { unfold s2.
      rewrite (execute_rom_frame s1' (JCN (nib 4) (byt ((q + 4) mod 256))))
        by discriminate.
      exact Hrom1'. }
    assert (Hstk2 : stk1 s2 = stk1 s1' /\ stk2 s2 = stk2 s1' /\ stk3 s2 = stk3 s1')
      by (apply execute_stack_frame; reflexivity).
    assert (Hram2 : ram_sys s2 = ram_sys s1')
      by (apply execute_ram_frame; reflexivity).
    assert (Henv2 : forall z, z < 8 -> env z = rval s2 z).
    { intros z Hz. unfold rval, get_reg. rewrite Hregs2.
      rewrite (Henv z Hz). unfold rval. f_equal.
      symmetry. exact (Hreg1' z Hz). }
    destruct (eval env e =? 0) eqn:Ez.
    + (* loop exits: skip to the JUN past the loop *)
      apply Nat.eqb_eq in Ez.
      injection Hsem as <-.
      assert (Hpc2 : pcv s2 = q + 4).
      { unfold pcv, s2.
        replace (byt ((q + 4) mod 256)) with (byt ((pcv s1' + 4) mod 256))
          by (rewrite Hpcq; reflexivity).
        rewrite exec_jcn_jz_taken_local.
        - rewrite adr_val. rewrite Hpcq.
          apply Nat.mod_small.
          unfold pend, pj, pb, q, pad, pe in *. lia.
        - rewrite Hacc1'. exact Ez.
        - rewrite Hpcq.
          apply mod256_add2_small.
          replace q with (pe + padlen pe) by reflexivity.
          apply padlen_safe.
        - rewrite Hpcq. unfold pend, pj, pb, q, pad, pe in *. lia. }
      assert (Hpend : pend < 4096)
        by (unfold pend, pj, pb, q, pad, pe in *; lia).
      assert (Hg1 : fetch_byte s2 (pcv s2) = byt (64 + pend / 256)).
      { specialize (Hrom_jun_end 0 ltac:(cbn [length]; lia)).
        rewrite Nat.add_0_r in Hrom_jun_end. cbn [nth] in Hrom_jun_end.
        rewrite Hpc2.
        unfold fetch_byte in *. rewrite Hrom2. exact Hrom_jun_end. }
      assert (Hg2 : fetch_byte s2 ((pcv s2 + 1) mod 4096) = byt (pend mod 256)).
      { specialize (Hrom_jun_end 1 ltac:(cbn [length]; lia)).
        cbn [nth] in Hrom_jun_end.
        rewrite Hpc2.
        rewrite (Nat.mod_small (q + 4 + 1) 4096)
          by (unfold pend, pj, pb, q, pad, pe in *; lia).
        unfold fetch_byte in *. rewrite Hrom2. exact Hrom_jun_end. }
      assert (Hstep2 : step s2 = execute s2 (JUN (adr pend))).
      { rewrite (step_at s2 _ _ Hg1 Hg2).
        replace (byt (64 + pend / 256))
          with (byt (64 + wval (adr pend) / 256))
          by (rewrite adr_val_small by exact Hpend; reflexivity).
        replace (byt (pend mod 256))
          with (byt (wval (adr pend) mod 256))
          by (rewrite adr_val_small by exact Hpend; reflexivity).
        rewrite decode_jun_bytes. reflexivity. }
      set (s3 := execute s2 (JUN (adr pend))) in *.
      assert (HWF3 : WF s3) by (apply execute_preserves_WF; exact HWF2).
      assert (Hregs3 : regs s3 = regs s2)
        by (apply execute_regs_frame; reflexivity).
      exists (elen e + (pad + (1 + 1))).
      rewrite steps_add. fold s1.
      rewrite steps_add. rewrite Hsteps_p. fold s1'.
      replace (steps (1 + 1) s1') with (steps 1 (step s1'))
        by (rewrite (steps_add 1 1 s1'); reflexivity).
      rewrite Hstep1. fold s2.
      replace (steps 1 s2) with (step s2) by reflexivity.
      rewrite Hstep2. fold s3.
      split; [exact HWF3 |].
      split.
      { unfold s3, pcv. rewrite pc_shape_jun.
        rewrite adr_val_small by exact Hpend.
        unfold pend, pj, pb, q, pad, pe. cbn [csize]. cbv zeta. lia. }
      split.
      { intros z Hz. unfold rval, get_reg. rewrite Hregs3, Hregs2.
        rewrite (Henv z Hz). unfold rval. f_equal.
        exact (Hreg1' z Hz). }
      split.
      { unfold s3.
        rewrite (execute_rom_frame s2 (JUN (adr pend))) by discriminate.
        exact Hrom2. }
      destruct Hstkp as (Hp1 & Hp2 & Hp3).
      destruct Hstk1 as (Hs11 & Hs12 & Hs13).
      destruct Hstk2 as (Hs21 & Hs22 & Hs23).
      destruct (execute_stack_frame s2 (JUN (adr pend)) ltac:(reflexivity))
        as (Hs31 & Hs32 & Hs33).
      split.
      { unfold s3.
        rewrite Hs31, Hs32, Hs33, Hs21, Hs22, Hs23, Hp1, Hp2, Hp3,
                Hs11, Hs12, Hs13.
        auto. }
      { unfold s3.
        rewrite (execute_ram_frame s2 (JUN (adr pend))) by reflexivity.
        rewrite Hram2, Hramp. exact Hram1. }
    + (* loop continues: body, jump back to the head, repeat *)
      apply Nat.eqb_neq in Ez.
      destruct (csem f b env) as [env1|] eqn:Eb; [| discriminate Hsem].
      assert (Hpc2 : pcv s2 = q + 2).
      { unfold pcv, s2.
        rewrite exec_jcn_jz_not_taken by (rewrite Hacc1'; exact Ez).
        rewrite adr_val. rewrite Hpcq.
        apply Nat.mod_small.
        unfold pend, pj, pb, q, pad, pe in *. lia. }
      assert (Hpb4096 : pb < 4096)
        by (unfold pend, pj, pb, q, pad, pe in *; lia).
      assert (Hg1 : fetch_byte s2 (pcv s2) = byt (64 + pb / 256)).
      { specialize (Hrom_jun_b 0 ltac:(cbn [length]; lia)).
        rewrite Nat.add_0_r in Hrom_jun_b. cbn [nth] in Hrom_jun_b.
        rewrite Hpc2.
        unfold fetch_byte in *. rewrite Hrom2. exact Hrom_jun_b. }
      assert (Hg2 : fetch_byte s2 ((pcv s2 + 1) mod 4096) = byt (pb mod 256)).
      { specialize (Hrom_jun_b 1 ltac:(cbn [length]; lia)).
        cbn [nth] in Hrom_jun_b.
        rewrite Hpc2.
        rewrite (Nat.mod_small (q + 2 + 1) 4096)
          by (unfold pend, pj, pb, q, pad, pe in *; lia).
        unfold fetch_byte in *. rewrite Hrom2. exact Hrom_jun_b. }
      assert (Hstep2 : step s2 = execute s2 (JUN (adr pb))).
      { rewrite (step_at s2 _ _ Hg1 Hg2).
        replace (byt (64 + pb / 256))
          with (byt (64 + wval (adr pb) / 256))
          by (rewrite adr_val_small by exact Hpb4096; reflexivity).
        replace (byt (pb mod 256))
          with (byt (wval (adr pb) mod 256))
          by (rewrite adr_val_small by exact Hpb4096; reflexivity).
        rewrite decode_jun_bytes. reflexivity. }
      set (s3 := execute s2 (JUN (adr pb))) in *.
      assert (HWF3 : WF s3) by (apply execute_preserves_WF; exact HWF2).
      assert (Hpc3 : pcv s3 = pb).
      { unfold pcv, s3. rewrite pc_shape_jun.
        apply adr_val_small. exact Hpb4096. }
      assert (Hregs3 : regs s3 = regs s2)
        by (apply execute_regs_frame; reflexivity).
      assert (Hrom3 : rom s3 = rom s).
      { unfold s3.
        rewrite (execute_rom_frame s2 (JUN (adr pb))) by discriminate.
        exact Hrom2. }
      assert (Hrom_b3 : rom_holds s3 pb (cgen b pb))
        by (apply (rom_holds_eq s s3); assumption).
      assert (Henv3 : forall z, z < 8 -> env z = rval s3 z).
      { intros z Hz. unfold rval, get_reg. rewrite Hregs3.
        exact (Henv2 z Hz). }
      destruct (IH b env env1 s3 pb HWF3 Hwb
                  ltac:(unfold pend, pj, pb, q, pad, pe in *; lia)
                  Hrom_b3 Hpc3 Henv3 Eb)
        as (n4 & HWF4 & Hpc4 & Hreg4 & Hrom4 & Hstk4 & Hram4).
      set (s4 := steps n4 s3) in *.
      assert (Hpc4' : pcv s4 = pj) by exact Hpc4.
      assert (Hrom4' : rom s4 = rom s) by (rewrite Hrom4; exact Hrom3).
      assert (Hbase4096 : base < 4096)
        by (unfold pend, pj, pb, q, pad, pe in *; lia).
      (* the JUN back to the head *)
      assert (Hg3 : fetch_byte s4 (pcv s4) = byt (64 + base / 256)).
      { specialize (Hrom_jun_back 0 ltac:(cbn [length]; lia)).
        rewrite Nat.add_0_r in Hrom_jun_back. cbn [nth] in Hrom_jun_back.
        rewrite Hpc4'.
        unfold fetch_byte in *. rewrite Hrom4'. exact Hrom_jun_back. }
      assert (Hg4 : fetch_byte s4 ((pcv s4 + 1) mod 4096) = byt (base mod 256)).
      { specialize (Hrom_jun_back 1 ltac:(cbn [length]; lia)).
        cbn [nth] in Hrom_jun_back.
        rewrite Hpc4'.
        rewrite (Nat.mod_small (pj + 1) 4096)
          by (unfold pend, pj, pb, q, pad, pe in *; lia).
        unfold fetch_byte in *. rewrite Hrom4'. exact Hrom_jun_back. }
      assert (Hstep4 : step s4 = execute s4 (JUN (adr base))).
      { rewrite (step_at s4 _ _ Hg3 Hg4).
        replace (byt (64 + base / 256))
          with (byt (64 + wval (adr base) / 256))
          by (rewrite adr_val_small by exact Hbase4096; reflexivity).
        replace (byt (base mod 256))
          with (byt (wval (adr base) mod 256))
          by (rewrite adr_val_small by exact Hbase4096; reflexivity).
        rewrite decode_jun_bytes. reflexivity. }
      set (s5 := execute s4 (JUN (adr base))) in *.
      assert (HWF5 : WF s5) by (apply execute_preserves_WF; exact HWF4).
      assert (Hpc5 : pcv s5 = base).
      { unfold pcv, s5. rewrite pc_shape_jun.
        apply adr_val_small. exact Hbase4096. }
      assert (Hregs5 : regs s5 = regs s4)
        by (apply execute_regs_frame; reflexivity).
      assert (Hrom5 : rom s5 = rom s).
      { unfold s5.
        rewrite (execute_rom_frame s4 (JUN (adr base))) by discriminate.
        exact Hrom4'. }
      assert (Hrom_w5 : rom_holds s5 base (cgen (CWhile e b) base)).
      { apply (rom_holds_eq s s5); [exact Hrom5 |].
        cbn [cgen]. cbv zeta.
        fold pe. fold pad. fold q. fold pb. fold pj. fold pend.
        exact Hrom. }
      assert (Henv5 : forall z, z < 8 -> env1 z = rval s5 z).
      { intros z Hz. unfold rval, get_reg. rewrite Hregs5.
        symmetry. exact (Hreg4 z Hz). }
      destruct (IH (CWhile e b) env1 env' s5 base HWF5
                  ltac:(cbn [cstmt_wf]; auto)
                  ltac:(cbn [csize]; cbv zeta;
                        fold pe; fold pad; fold q; fold pb; exact Hfit)
                  Hrom_w5 Hpc5 Henv5 Hsem)
        as (n6 & HWF6 & Hpc6 & Hreg6 & Hrom6 & Hstk6 & Hram6).
      exists (elen e + (pad + (1 + (1 + (n4 + (1 + n6)))))).
      rewrite steps_add. fold s1.
      rewrite steps_add. rewrite Hsteps_p. fold s1'.
      replace (steps (1 + (1 + (n4 + (1 + n6)))) s1')
        with (steps (1 + (n4 + (1 + n6))) (step s1'))
        by (rewrite (steps_add 1 (1 + (n4 + (1 + n6))) s1'); reflexivity).
      rewrite Hstep1. fold s2.
      replace (steps (1 + (n4 + (1 + n6))) s2)
        with (steps (n4 + (1 + n6)) (step s2))
        by (rewrite (steps_add 1 (n4 + (1 + n6)) s2); reflexivity).
      rewrite Hstep2. fold s3.
      rewrite steps_add. fold s4.
      replace (steps (1 + n6) s4) with (steps n6 (step s4))
        by (rewrite (steps_add 1 n6 s4); reflexivity).
      rewrite Hstep4. fold s5.
      split; [exact HWF6 |].
      split; [exact Hpc6 |].
      split; [exact Hreg6 |].
      split; [rewrite Hrom6; exact Hrom5 |].
      destruct Hstkp as (Hp1 & Hp2 & Hp3).
      destruct Hstk1 as (Hs11 & Hs12 & Hs13).
      destruct Hstk2 as (Hs21 & Hs22 & Hs23).
      destruct (execute_stack_frame s2 (JUN (adr pb)) ltac:(reflexivity))
        as (Hs31 & Hs32 & Hs33).
      destruct Hstk4 as (Hs41 & Hs42 & Hs43).
      destruct (execute_stack_frame s4 (JUN (adr base)) ltac:(reflexivity))
        as (Hs51 & Hs52 & Hs53).
      destruct Hstk6 as (Hs61 & Hs62 & Hs63).
      split.
      { rewrite Hs61, Hs62, Hs63. unfold s5.
        rewrite Hs51, Hs52, Hs53, Hs41, Hs42, Hs43. unfold s3.
        rewrite Hs31, Hs32, Hs33, Hs21, Hs22, Hs23, Hp1, Hp2, Hp3,
                Hs11, Hs12, Hs13.
        auto. }
      { rewrite Hram6. unfold s5.
        rewrite (execute_ram_frame s4 (JUN (adr base))) by reflexivity.
        rewrite Hram4. unfold s3.
        rewrite (execute_ram_frame s2 (JUN (adr pb))) by reflexivity.
        rewrite Hram2, Hramp. exact Hram1. }
Qed.

(* ==================== End-to-end: power-on to result ==================== *)

(** Headline: place the generated bytes at address 0 of a ROM image, power
    on, and run the fetch-decode-execute machine: whenever the source
    semantics terminates, the machine reaches the block exit with the final
    environment in the low registers. *)
Theorem compiled_cstmt_runs_on_machine : forall fuel st env' regsv,
  cstmt_wf st ->
  csize st 0 < 4096 ->
  length regsv = 16 ->
  csem fuel st (fun r => rval (init_with (rom_of (cgen st 0)) regsv) r)
    = Some env' ->
  exists n,
    pcv (steps n (init_with (rom_of (cgen st 0)) regsv)) = csize st 0 /\
    forall r, r < 8 ->
      rval (steps n (init_with (rom_of (cgen st 0)) regsv)) r = env' r.
Proof.
  intros fuel st env' regsv Hwf Hfit HlenR Hsem.
  set (s0 := init_with (rom_of (cgen st 0)) regsv).
  assert (Hlen : length (cgen st 0) = csize st 0) by apply cgen_length.
  assert (HWF0 : WF s0).
  { apply init_with_WF; [exact HlenR |].
    apply rom_of_length. lia. }
  assert (Hrom0 : rom_holds s0 0 (cgen st 0)).
  { intros j Hj.
    replace (0 + j) with j by lia.
    unfold fetch_byte.
    change (rom s0) with (rom_of (cgen st 0)).
    apply rom_of_nth. exact Hj. }
  assert (Hpc0 : pcv s0 = 0) by reflexivity.
  destruct (cgen_correct fuel st _ env' s0 0 HWF0 Hwf ltac:(lia) Hrom0 Hpc0
              ltac:(intros r Hr; reflexivity) Hsem)
    as (n & _ & Hpc & Hreg & _).
  exists n. split.
  - rewrite Hpc. lia.
  - exact Hreg.
Qed.

(* ==================== Source-level while rule ==================== *)

(** Partial-correctness triples over the source semantics. *)
Definition csem_triple (P : (nat -> nat) -> Prop) (st : CStmt)
                       (Q : (nat -> nat) -> Prop) : Prop :=
  forall fuel env env', P env -> csem fuel st env = Some env' -> Q env'.

(** The while rule: an invariant preserved by the body under a true guard
    holds at exit together with the negated guard.  With
    pc_indexed_simulation and pc_indexed_reaches this closes loop reasoning
    at the source and machine levels respectively. *)
Theorem cwhile_rule : forall (I : (nat -> nat) -> Prop) e b,
  csem_triple (fun env => I env /\ eval env e <> 0) b I ->
  csem_triple I (CWhile e b) (fun env => I env /\ eval env e = 0).
Proof.
  intros I e b Hbody.
  unfold csem_triple.
  intros fuel.
  induction fuel as [|f IHf]; intros env env' HI Hsem; [discriminate Hsem |].
  rewrite csem_S_while in Hsem.
  destruct (eval env e =? 0) eqn:Ez.
  - injection Hsem as <-.
    split; [exact HI | apply Nat.eqb_eq; exact Ez].
  - destruct (csem f b env) as [env1|] eqn:Eb; [| discriminate Hsem].
    apply (IHf env1 env').
    + apply (Hbody f env env1); [| exact Eb].
      split; [exact HI | apply Nat.eqb_neq; exact Ez].
    + exact Hsem.
Qed.

(* ==================== A concrete looping program ==================== *)

(* R0 := 3; while R0 <> 0 do R0 := R0 - 1.
   Layout at base 0 (17 bytes; no padding needed at this address):
     0: LDM 3          (0xD3)
     1: XCH 0          (0xB0)
     2: LD 0           (0xA0)   <- loop head
     3: JCN JZ 7       (0x14 0x07)  ; R0 = 0 -> the exit island
     5: JUN 9          (0x40 0x09)  ; R0 <> 0 -> the body
     7: JUN 17         (0x40 0x11)  ; exit past the loop
     9: LDM 1          (0xD1)
    10: XCH 8          (0xB8)
    11: LD 0           (0xA0)
    12: CLC            (0xF1)
    13: SUB 8          (0x98)
    14: XCH 0          (0xB0)
    15: JUN 2          (0x40 0x02)  ; back to the head
    17:                             <- exit                               *)
Definition demo_prog : CStmt :=
  CSeq (CAssign 0 (EConst 3))
       (CWhile (EReg 0) (CAssign 0 (ESub (EReg 0) (EConst 1)))).

(** The source semantics drives R0 to zero. *)
Example cwhile_demo_sem :
  match csem 10 demo_prog (fun _ => 0) with
  | Some env' => env' 0 = 0
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** The machine, fetching the generated bytes from ROM, computes the loop:
    35 steps after power-on, R0 holds zero and control sits at the exit. *)
Example cwhile_demo_machine :
  rval (steps 35 (init_with (rom_of (cgen demo_prog 0)) (repeat (nib 0) 16))) 0 = 0
  /\ pcv (steps 35 (init_with (rom_of (cgen demo_prog 0)) (repeat (nib 0) 16))) = 17.
Proof. split; vm_compute; reflexivity. Qed.

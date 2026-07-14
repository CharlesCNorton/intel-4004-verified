(* ===================================================================== *)
(*  Intel 4004: program verification.                                    *)
(*  Hoare logic with frame rules, program-level triples, weakest         *)
(*  preconditions and verification conditions, verified example          *)
(*  programs, value-level instruction specifications, separation logic   *)
(*  over the RAM hierarchy, multi-digit BCD arithmetic, and a verified   *)
(*  compiler refined into a ROM image running on the machine.            *)
(* ===================================================================== *)

From Stdlib Require Import List Arith PeanoNat Bool NArith Lia.
Import ListNotations.
From FourK Require Import machine behavior.

(* ===================================================================== *)
(*                         HOARE LOGIC LAYER                             *)
(* ===================================================================== *)

(* ==================== Hoare Triple Definition ======================= *)

Definition hoare_triple (P Q : Intel4004State -> Prop) (i : Instruction) : Prop :=
  forall s, WF s -> P s ->
    let s' := execute s i in
    WF s' /\ Q s'.

Notation "{{ P }} i {{ Q }}" := (hoare_triple P Q i) (at level 90, i at next level).

(** Open a Hoare-triple goal: the well-formedness half is discharged by the
    unconditional preservation theorem. *)
Ltac hoare_start :=
  unfold hoare_triple; intros ?s ?HWF ?Hpre;
  split; [ apply execute_preserves_WF; assumption | ];
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         end.

(* ==================== Structural Rules =========================== *)

Lemma hoare_consequence : forall P P' Q Q' i,
  (forall s, P' s -> P s) ->
  {{ P }} i {{ Q }} ->
  (forall s, Q s -> Q' s) ->
  {{ P' }} i {{ Q' }}.
Proof.
  intros P P' Q Q' i Hpre Htriple Hpost.
  unfold hoare_triple in *.
  intros s HWF HP'.
  specialize (Htriple s HWF (Hpre s HP')).
  destruct Htriple as [HWF' HQ].
  split; auto.
Qed.

Lemma hoare_conj : forall P P' Q Q' i,
  {{ P }} i {{ Q }} ->
  {{ P' }} i {{ Q' }} ->
  {{ fun s => P s /\ P' s }} i {{ fun s => Q s /\ Q' s }}.
Proof.
  intros P P' Q Q' i H1 H2.
  unfold hoare_triple in *.
  intros s HWF [HP HP'].
  specialize (H1 s HWF HP).
  specialize (H2 s HWF HP').
  destruct H1 as [HWF1 HQ].
  destruct H2 as [HWF2 HQ'].
  split; auto.
Qed.

Lemma hoare_disj : forall P1 P2 Q1 Q2 i,
  {{ P1 }} i {{ Q1 }} ->
  {{ P2 }} i {{ Q2 }} ->
  {{ fun s => P1 s \/ P2 s }} i {{ fun s => Q1 s \/ Q2 s }}.
Proof.
  intros P1 P2 Q1 Q2 i H1 H2.
  unfold hoare_triple in *.
  intros s HWF [HP1 | HP2].
  - specialize (H1 s HWF HP1).
    destruct H1 as [HWF' HQ1].
    split; auto.
  - specialize (H2 s HWF HP2).
    destruct H2 as [HWF' HQ2].
    split; auto.
Qed.

Lemma hoare_exists : forall A (P Q : A -> Intel4004State -> Prop) i,
  (forall x, {{ P x }} i {{ Q x }}) ->
  {{ fun s => exists x, P x s }} i {{ fun s => exists x, Q x s }}.
Proof.
  intros A P Q i H.
  unfold hoare_triple in *.
  intros s HWF [x HP].
  specialize (H x s HWF HP).
  destruct H as [HWF' HQ].
  split; auto.
  exists x. exact HQ.
Qed.

Lemma hoare_frame_regs : forall P Q i R,
  {{ P }} i {{ Q }} ->
  writes_regs i = false ->
  (forall s1 s2, regs s1 = regs s2 -> R s1 -> R s2) ->
  {{ fun s => P s /\ R s }} i {{ fun s => Q s /\ R s }}.
Proof.
  intros P Q i R Htriple Hwrites Hindep.
  unfold hoare_triple in *.
  intros s HWF [HP HR].
  specialize (Htriple s HWF HP).
  destruct Htriple as [HWF' HQ].
  split; auto.
  split; auto.
  apply (Hindep s (execute s i)).
  - symmetry. apply execute_regs_frame. exact Hwrites.
  - exact HR.
Qed.

Lemma hoare_frame_ram : forall P Q i R,
  {{ P }} i {{ Q }} ->
  writes_ram i = false ->
  (forall s1 s2, ram_sys s1 = ram_sys s2 -> R s1 -> R s2) ->
  {{ fun s => P s /\ R s }} i {{ fun s => Q s /\ R s }}.
Proof.
  intros P Q i R Htriple Hwrites Hindep.
  unfold hoare_triple in *.
  intros s HWF [HP HR].
  specialize (Htriple s HWF HP).
  destruct Htriple as [HWF' HQ].
  split; auto.
  split; auto.
  apply (Hindep s (execute s i)).
  - symmetry. apply execute_ram_frame. exact Hwrites.
  - exact HR.
Qed.

Lemma hoare_frame_acc : forall P Q i R,
  {{ P }} i {{ Q }} ->
  writes_acc i = false ->
  (forall s1 s2, acc s1 = acc s2 -> R s1 -> R s2) ->
  {{ fun s => P s /\ R s }} i {{ fun s => Q s /\ R s }}.
Proof.
  intros P Q i R Htriple Hwrites Hindep.
  unfold hoare_triple in *.
  intros s HWF [HP HR].
  specialize (Htriple s HWF HP).
  destruct Htriple as [HWF' HQ].
  split; auto.
  split; auto.
  apply (Hindep s (execute s i)).
  - symmetry. apply execute_acc_frame. exact Hwrites.
  - exact HR.
Qed.

(* ==================== Accumulator Instructions =================== *)

(** LDM leaves exactly the immediate in the accumulator. *)
Lemma hoare_LDM : forall n : nibble,
  {{ fun _ => True }}
     LDM n
  {{ fun s => acc s = n }}.
Proof. intros n. hoare_start. reflexivity. Qed.

Lemma hoare_LDM_frame : forall (n : nibble) r (v : nibble),
  {{ fun s => get_reg s r = v }}
     LDM n
  {{ fun s => acc s = n /\ get_reg s r = v }}.
Proof.
  intros n r v. hoare_start.
  split; [reflexivity | exact Hpre].
Qed.

Lemma hoare_LD : forall (r : nibble) (v : nibble),
  {{ fun s => get_reg s (wval r) = v }}
     LD r
  {{ fun s => acc s = v }}.
Proof. intros r v. hoare_start. exact Hpre. Qed.

Lemma hoare_CLB :
  {{ fun _ => True }}
     CLB
  {{ fun s => acc s = nib 0 /\ carry s = false }}.
Proof. hoare_start. split; reflexivity. Qed.

Lemma hoare_CLC : forall a : nibble,
  {{ fun s => acc s = a }}
     CLC
  {{ fun s => acc s = a /\ carry s = false }}.
Proof.
  intros a. hoare_start.
  split; [exact Hpre | reflexivity].
Qed.

Lemma hoare_STC : forall a : nibble,
  {{ fun s => acc s = a }}
     STC
  {{ fun s => acc s = a /\ carry s = true }}.
Proof.
  intros a. hoare_start.
  split; [exact Hpre | reflexivity].
Qed.

Lemma hoare_CMC : forall (a : nibble) (c : bool),
  {{ fun s => acc s = a /\ carry s = c }}
     CMC
  {{ fun s => acc s = a /\ carry s = negb c }}.
Proof.
  intros a c. hoare_start.
  split; [assumption | exec_simpl; congruence].
Qed.

Lemma hoare_CMA_value : forall a,
  {{ fun s => aval s = a }}
     CMA
  {{ fun s => aval s = 15 - a }}.
Proof.
  intros a. hoare_start.
  unfold aval in Hpre |- *. exec_simpl.
  rewrite Hpre.
  rewrite nib_val_small by lia. reflexivity.
Qed.

(** CMA is an involution on the accumulator value. *)
Lemma hoare_CMA_involution_proof : forall a,
  a < 16 -> 15 - (15 - a) = a.
Proof. intros a Ha. lia. Qed.

Lemma hoare_IAC_value : forall a,
  {{ fun s => aval s = a }}
     IAC
  {{ fun s => aval s = (a + 1) mod 16 /\ carry s = (16 <=? a + 1) }}.
Proof.
  intros a. hoare_start.
  destruct (iac_computes_increment s) as [Ha Hc].
  rewrite Hpre in Ha, Hc.
  split; assumption.
Qed.

Lemma hoare_DAC_value : forall a,
  {{ fun s => aval s = a }}
     DAC
  {{ fun s => aval s = (a + 15) mod 16 /\ carry s = negb (a =? 0) }}.
Proof.
  intros a. hoare_start.
  destruct (dac_computes_decrement s) as [Ha Hc].
  rewrite Hpre in Ha, Hc.
  split; assumption.
Qed.

Lemma hoare_DAA_value : forall a c,
  {{ fun s => aval s = a /\ carry s = c }}
     DAA
  {{ fun s => aval s = (a + (if orb c (9 <? a) then 6 else 0)) mod 16 /\
              carry s = orb (16 <=? (a + (if orb c (9 <? a) then 6 else 0))) c }}.
Proof.
  intros a c. hoare_start.
  pose proof (daa_bcd_adjust_correct s) as Hd. cbv zeta in Hd.
  destruct Hd as [Ha Hc].
  match goal with
  | Hacc : aval s = a, Hcar : carry s = c |- _ =>
      rewrite Hacc, Hcar in Ha, Hc
  end.
  split; assumption.
Qed.

Lemma hoare_TCC_value : forall c,
  {{ fun s => carry s = c }}
     TCC
  {{ fun s => aval s = (if c then 1 else 0) /\ carry s = false }}.
Proof.
  intros c. hoare_start.
  exec_simpl. rewrite Hpre.
  split; [| reflexivity].
  destruct c; reflexivity.
Qed.

Lemma hoare_KBP_value : forall a,
  {{ fun s => aval s = a }}
     KBP
  {{ fun s => aval s = match a with
                       | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4
                       | _ => 15
                       end }}.
Proof.
  intros a. hoare_start.
  rewrite kbp_map_cases. rewrite Hpre. reflexivity.
Qed.

(* ==================== Register Instructions ====================== *)

Lemma hoare_INC_value : forall (r : nibble) v,
  {{ fun s => length (regs s) = 16 /\ rval s (wval r) = v }}
     INC r
  {{ fun s => rval s (wval r) = (v + 1) mod 16 }}.
Proof.
  intros r v. hoare_start.
  match goal with
  | Hlen : length (regs s) = 16, Hv : rval s (wval r) = v |- _ =>
      unfold rval at 1; unfold get_reg at 1;
      exec_simpl; cbn [regs];
      rewrite nth_update_nth_eq by (rewrite Hlen; apply nib_lt16);
      rewrite nib_val; rewrite Hv; reflexivity
  end.
Qed.

Lemma hoare_INC_preserves_other : forall (r : nibble) r2 (v : nibble),
  wval r <> r2 ->
  {{ fun s => get_reg s r2 = v }}
     INC r
  {{ fun s => get_reg s r2 = v }}.
Proof.
  intros r r2 v Hneq. hoare_start.
  exec_simpl. unfold get_reg in *. cbn [regs].
  rewrite nth_update_nth_neq by lia.
  assumption.
Qed.

Lemma hoare_ADD_value : forall (r : nibble) a v c,
  {{ fun s => aval s = a /\ rval s (wval r) = v /\ carry s = c }}
     ADD r
  {{ fun s => aval s = (a + v + (if c then 1 else 0)) mod 16 /\
              carry s = (16 <=? a + v + (if c then 1 else 0)) }}.
Proof.
  intros r a v c. hoare_start.
  destruct (add_computes_sum s r) as [Ha Hc].
  unfold cbit in Ha, Hc.
  match goal with
  | H1 : aval s = a, H2 : rval s (wval r) = v, H3 : carry s = c |- _ =>
      rewrite H1, H2, H3 in Ha, Hc
  end.
  split; assumption.
Qed.

Lemma hoare_SUB_value : forall (r : nibble) a v c,
  {{ fun s => aval s = a /\ rval s (wval r) = v /\ carry s = c }}
     SUB r
  {{ fun s => aval s = (a + 16 - v - (if c then 1 else 0)) mod 16 /\
              carry s = (16 <=? a + 16 - v - (if c then 1 else 0)) }}.
Proof.
  intros r a v c. hoare_start.
  destruct (sub_computes_difference s r) as [Ha Hc].
  unfold cbit in Ha, Hc.
  match goal with
  | H1 : aval s = a, H2 : rval s (wval r) = v, H3 : carry s = c |- _ =>
      rewrite H1, H2, H3 in Ha, Hc
  end.
  split; assumption.
Qed.

Lemma hoare_XCH_swaps : forall (r : nibble) (a v : nibble),
  {{ fun s => length (regs s) = 16 /\ acc s = a /\ get_reg s (wval r) = v }}
     XCH r
  {{ fun s => acc s = v /\ get_reg s (wval r) = a }}.
Proof.
  intros r a v. hoare_start.
  match goal with
  | Hlen : length (regs s) = 16, Hacc : acc s = a,
    Hreg : get_reg s (wval r) = v |- _ =>
      split;
      [ rewrite xch_sets_acc; exact Hreg
      | rewrite xch_reg_written by exact Hlen; exact Hacc ]
  end.
Qed.

Lemma hoare_FIM : forall (r : nibble) (d : byte),
  wval r mod 2 = 0 ->
  {{ fun s => length (regs s) = 16 }}
     FIM r d
  {{ fun s => get_reg_pair s (wval r) = wval d }}.
Proof.
  intros r d Heven. hoare_start.
  apply fim_operates_on_pairs; assumption.
Qed.

Lemma hoare_SRC : forall (r : nibble) p,
  {{ fun s => get_reg_pair s (wval r) = p }}
     SRC r
  {{ fun s => wval (sel_rom s) = p / 16 /\
              wval (sel_chip (sel_ram s)) = p / 16 / 4 /\
              wval (sel_reg (sel_ram s)) = (p / 16) mod 4 /\
              wval (sel_char (sel_ram s)) = p mod 16 }}.
Proof.
  intros r p. hoare_start.
  pose proof (src_uses_pair_value s r) as H. cbv zeta in H.
  rewrite Hpre in H.
  exact H.
Qed.

(* ==================== ISZ Loop Hoare Rules ======================== *)

(** Hoare rule for ISZ when the loop continues. *)
Lemma hoare_ISZ_loop : forall (r : nibble) (off : byte) v,
  v < 15 ->
  {{ fun s => length (regs s) = 16 /\ rval s (wval r) = v }}
     ISZ r off
  {{ fun s => rval s (wval r) = v + 1 }}.
Proof.
  intros r off v Hv. hoare_start.
  match goal with
  | Hlen : length (regs s) = 16, Hval : rval s (wval r) = v |- _ =>
      unfold rval;
      rewrite (isz_increments_reg s r off Hlen);
      rewrite nib_val; rewrite Hval;
      apply Nat.mod_small; lia
  end.
Qed.

(** Hoare rule for ISZ when the loop terminates. *)
Lemma hoare_ISZ_terminate : forall (r : nibble) (off : byte) p0,
  {{ fun s => length (regs s) = 16 /\ rval s (wval r) = 15 /\ pcv s = p0 }}
     ISZ r off
  {{ fun s => rval s (wval r) = 0 /\ pc s = adr (p0 + 2) }}.
Proof.
  intros r off p0. hoare_start.
  match goal with
  | Hlen : length (regs s) = 16, Hval : rval s (wval r) = 15,
    Hpc : pcv s = p0 |- _ =>
      split;
      [ unfold rval;
        rewrite (isz_increments_reg s r off Hlen);
        rewrite nib_val; rewrite Hval; reflexivity
      | rewrite isz_branch_not_taken
          by (apply isz_terminates_at_15; exact Hval);
        rewrite Hpc; reflexivity ]
  end.
Qed.

Lemma hoare_ISZ_preserves_acc : forall (r : nibble) (off : byte) (a : nibble),
  {{ fun s => acc s = a }}
     ISZ r off
  {{ fun s => acc s = a }}.
Proof.
  intros r off a. hoare_start.
  rewrite isz_preserves_acc. exact Hpre.
Qed.

(* ==================== JCN Conditional Branch Hoare Rules ========= *)

(** JCN taken: the postcondition names the concrete target computed from
    the pre-state program counter p0. *)
Lemma hoare_JCN_taken : forall (cond : nibble) (off : byte) (P : Intel4004State -> Prop) p0,
  (forall s, P s -> jcn_condition s (wval cond) = true) ->
  {{ fun s => P s /\ pcv s = p0 }}
     JCN cond off
  {{ fun s' => pc s' = adr (page_base ((p0 + 2) mod 4096) + wval off) }}.
Proof.
  intros cond off P p0 Hcond.
  hoare_start.
  match goal with
  | HP : P s, Hp : pcv s = p0 |- _ =>
      rewrite (jcn_branch_taken s cond off (Hcond s HP));
      unfold base_for_next2, pc_inc2;
      rewrite adr_val; rewrite Hp; reflexivity
  end.
Qed.

(** JCN not taken: fall-through to p0+2. *)
Lemma hoare_JCN_not_taken : forall (cond : nibble) (off : byte) (P : Intel4004State -> Prop) p0,
  (forall s, P s -> jcn_condition s (wval cond) = false) ->
  {{ fun s => P s /\ pcv s = p0 }}
     JCN cond off
  {{ fun s' => pc s' = adr (p0 + 2) }}.
Proof.
  intros cond off P p0 Hcond.
  hoare_start.
  match goal with
  | HP : P s, Hp : pcv s = p0 |- _ =>
      rewrite (jcn_branch_not_taken s cond off (Hcond s HP));
      rewrite Hp; reflexivity
  end.
Qed.

(** JCN_JZ jumps to the page-relative target when the accumulator is zero. *)
Lemma hoare_JCN_JZ_taken : forall (off : byte) p0,
  {{ fun s => aval s = 0 /\ pcv s = p0 }}
     JCN (nib JCN_JZ) off
  {{ fun s' => pc s' = adr (page_base ((p0 + 2) mod 4096) + wval off) }}.
Proof.
  intros off p0.
  apply hoare_JCN_taken.
  intros s Ha.
  rewrite (nib_val_small JCN_JZ) by (unfold JCN_JZ; lia).
  rewrite jcn_jz_semantics, Ha. reflexivity.
Qed.

(** JCN_JZ falls through when the accumulator is non-zero. *)
Lemma hoare_JCN_JZ_not_taken : forall (off : byte) p0 v,
  v <> 0 ->
  {{ fun s => aval s = v /\ pcv s = p0 }}
     JCN (nib JCN_JZ) off
  {{ fun s' => pc s' = adr (p0 + 2) }}.
Proof.
  intros off p0 v Hneq.
  apply hoare_JCN_not_taken.
  intros s Ha.
  rewrite (nib_val_small JCN_JZ) by (unfold JCN_JZ; lia).
  rewrite jcn_jz_semantics, Ha.
  destruct v; [contradiction | reflexivity].
Qed.

(** JCN_JC jumps when carry is set. *)
Lemma hoare_JCN_JC_taken : forall (off : byte) p0,
  {{ fun s => carry s = true /\ pcv s = p0 }}
     JCN (nib JCN_JC) off
  {{ fun s' => pc s' = adr (page_base ((p0 + 2) mod 4096) + wval off) }}.
Proof.
  intros off p0.
  apply hoare_JCN_taken.
  intros s Hc.
  rewrite (nib_val_small JCN_JC) by (unfold JCN_JC; lia).
  rewrite jcn_jc_semantics. exact Hc.
Qed.

(** JCN_JNC jumps when carry is clear. *)
Lemma hoare_JCN_JNC_taken : forall (off : byte) p0,
  {{ fun s => carry s = false /\ pcv s = p0 }}
     JCN (nib JCN_JNC) off
  {{ fun s' => pc s' = adr (page_base ((p0 + 2) mod 4096) + wval off) }}.
Proof.
  intros off p0.
  apply hoare_JCN_taken.
  intros s Hc.
  rewrite (nib_val_small JCN_JNC) by (unfold JCN_JNC; lia).
  rewrite jcn_jnc_semantics, Hc. reflexivity.
Qed.

(* ==================== Control Flow =============================== *)

Lemma hoare_NOP :
  {{ fun _ => True }}
     NOP
  {{ fun _ => True }}.
Proof. hoare_start. exact I. Qed.

Lemma hoare_NOP_preserves : forall (a : nibble) r (v : nibble) (c : bool),
  {{ fun s => acc s = a /\ get_reg s r = v /\ carry s = c }}
     NOP
  {{ fun s => acc s = a /\ get_reg s r = v /\ carry s = c }}.
Proof.
  intros a r v c. hoare_start.
  repeat split; assumption.
Qed.

Lemma hoare_JUN : forall a : addr12,
  {{ fun _ => True }}
     JUN a
  {{ fun s => pc s = a }}.
Proof. intros a. hoare_start. reflexivity. Qed.

(** JMS: control moves to the target and the return address enters the
    first saved row of the address ring. *)
Lemma hoare_JMS : forall (a : addr12) p0,
  {{ fun s => pcv s = p0 }}
     JMS a
  {{ fun s => pc s = a /\ stk1 s = adr (p0 + 2) }}.
Proof.
  intros a p0. hoare_start.
  split.
  - reflexivity.
  - unfold pcv in Hpre. exec_simpl. rewrite Hpre. reflexivity.
Qed.

(** BBL: control resumes at the first saved row and the accumulator takes
    the immediate, exactly (typed operand). *)
Lemma hoare_BBL : forall (d : nibble) (ra : addr12),
  {{ fun s => stk1 s = ra }}
     BBL d
  {{ fun s => acc s = d /\ pc s = ra }}.
Proof.
  intros d ra. hoare_start.
  split; [reflexivity | exact Hpre].
Qed.

(* ==================== RAM/ROM Operations ========================= *)

Lemma hoare_RDM_value : forall v : nibble,
  {{ fun s => ram_read_main s = v }}
     RDM
  {{ fun s => acc s = v }}.
Proof. intros v. hoare_start. exact Hpre. Qed.

(** WRM followed by unanimity: the written value reads back through the
    selected banks (any DCL code). *)
Lemma hoare_WRM_writes : forall v : nibble,
  {{ fun s => acc s = v }}
     WRM
  {{ fun s => ram_read_main_opt s = Some v }}.
Proof.
  intros v.
  unfold hoare_triple. intros s HWF Hpre.
  split; [apply execute_preserves_WF; exact HWF |].
  rewrite <- Hpre.
  apply dcl_multiwrite_read_defined. exact HWF.
Qed.

Lemma hoare_DCL : forall a,
  {{ fun s => aval s = a }}
     DCL
  {{ fun s => cm_code s = w3 a }}.
Proof.
  intros a. hoare_start.
  rewrite dcl_sets_cm_code. rewrite Hpre. reflexivity.
Qed.

(* ============ The remaining instructions: pairs, ports, PROM ========= *)

(** FIN loads the ROM byte addressed by pair 0, fetched from the page of
    the next instruction, into the target pair. *)
Lemma hoare_FIN : forall (r : nibble) (v : byte),
  wval r mod 2 = 0 ->
  {{ fun s => length (regs s) = 16 /\
              fetch_byte s (page_of (wval (pc_inc1 s)) * 256
                            + get_reg_pair s 0) = v }}
     FIN r
  {{ fun s => get_reg_pair s (wval r) = wval v }}.
Proof.
  intros r v Heven. hoare_start.
  match goal with
  | Hlen : length (regs s) = 16, Hf : fetch_byte s _ = v |- _ =>
      cbn [execute];
      replace (get_reg_pair
                 (pc_bump 1 (set_reg_pair s (wval r)
                    (wval (fetch_byte s (page_of (wval (pc_inc1 s)) * 256
                                         + get_reg_pair s 0))))) (wval r))
        with (get_reg_pair
                (set_reg_pair s (wval r)
                   (wval (fetch_byte s (page_of (wval (pc_inc1 s)) * 256
                                        + get_reg_pair s 0)))) (wval r))
        by reflexivity;
      rewrite Hf;
      apply set_reg_pair_get_pair;
        [exact Hlen | apply nib_lt16 | exact Heven | apply byte_lt256]
  end.
Qed.

(** JIN jumps within the page of the next instruction, low byte from the
    register pair. *)
Lemma hoare_JIN : forall (r : nibble) p p0,
  {{ fun s => get_reg_pair s (wval r) = p /\ pcv s = p0 }}
     JIN r
  {{ fun s' => pc s' = adr (page_of ((p0 + 1) mod 4096) * 256 + p) }}.
Proof.
  intros r p p0. hoare_start.
  match goal with
  | Hp : get_reg_pair s (wval r) = p, H0 : pcv s = p0 |- _ =>
      rewrite pc_shape_jin;
      unfold pc_inc1; rewrite adr_val; rewrite H0, Hp; reflexivity
  end.
Qed.

(** WRR writes the accumulator into the selected output-port latch. *)
Lemma hoare_WRR : forall (v : nibble) k,
  {{ fun s => acc s = v /\ wval (sel_rom s) = k }}
     WRR
  {{ fun s' => nth k (out_ports s') (nib 0) = v }}.
Proof.
  intros v k.
  unfold hoare_triple. intros s HWF [Hacc Hsel].
  split; [apply execute_preserves_WF; exact HWF |].
  rewrite <- Hsel, <- Hacc.
  apply wrr_writes_to_selected_port. exact HWF.
Qed.

(** RDR reads the selected port's pins: the latch on an output port, the
    external drive on an input port. *)
Lemma hoare_RDR : forall v : nibble,
  {{ fun s => (if nth (wval (sel_rom s)) (port_dirs s) true
               then nth (wval (sel_rom s)) (out_ports s) (nib 0)
               else nth (wval (sel_rom s)) (in_ports s) (nib 0)) = v }}
     RDR
  {{ fun s' => acc s' = v }}.
Proof.
  intros v. hoare_start.
  rewrite rdr_reads_selected_port. exact Hpre.
Qed.

(** WMP drives the selected chip's port in every bank the DCL code
    addresses. *)
Lemma hoare_WMP : forall (v : nibble) b,
  {{ fun s => acc s = v /\ In b (sel_lines s) }}
     WMP
  {{ fun s' => read_port_bank (ram_sys s') (sel_ram s') b = v }}.
Proof.
  intros v b.
  unfold hoare_triple. intros s HWF [Hacc Hin].
  split; [apply execute_preserves_WF; exact HWF |].
  replace (sel_ram (execute s WMP)) with (sel_ram s) by reflexivity.
  rewrite <- Hacc.
  apply wmp_writes_selected_ports; assumption.
Qed.

(** An armed WPM with the latch expecting the high half stages the
    accumulator; ROM is untouched. *)
Lemma hoare_WPM_stage : forall (v : nibble) (romv : list byte),
  {{ fun s => acc s = v /\ rom s = romv /\
              prom_enable s = true /\ pl_expect_low (prom_latch s) = false }}
     WPM
  {{ fun s' => prom_latch s' = mkProgLatch true v /\ rom s' = romv }}.
Proof.
  intros v romv.
  unfold hoare_triple. intros s HWF (Hacc & Hrom & He & Hl).
  split; [apply execute_preserves_WF; exact HWF |].
  rewrite (wpm_stage s He Hl).
  split.
  - rewrite Hacc. reflexivity.
  - exact Hrom.
Qed.

(** An armed WPM with a staged high half commits the assembled byte at the
    programmer's address and returns the latch to its initial state. *)
Lemma hoare_WPM_commit : forall (hi lo : nibble) (a : addr12) (romv : list byte),
  {{ fun s => acc s = lo /\ prom_enable s = true /\
              prom_latch s = mkProgLatch true hi /\
              prom_addr s = a /\ rom s = romv }}
     WPM
  {{ fun s' => rom s' = update_nth (wval a) (byt (wval hi * 16 + wval lo)) romv /\
               prom_latch s' = latch_init }}.
Proof.
  intros hi lo a romv.
  unfold hoare_triple. intros s HWF (Hacc & He & Hl & Ha & Hr).
  split; [apply execute_preserves_WF; exact HWF |].
  assert (Hexp : pl_expect_low (prom_latch s) = true)
    by (rewrite Hl; reflexivity).
  rewrite (wpm_commit s He Hexp).
  split.
  - replace (rom (pc_bump 1 (with_prom_latch latch_init
               (with_rom (update_nth (wval (prom_addr s))
                  (byt (wval (pl_hi (prom_latch s)) * 16 + aval s)) (rom s)) s))))
      with (update_nth (wval (prom_addr s))
              (byt (wval (pl_hi (prom_latch s)) * 16 + aval s)) (rom s))
      by reflexivity.
    rewrite Hl, Ha, Hr. unfold aval. rewrite Hacc. reflexivity.
  - reflexivity.
Qed.

(** A disarmed WPM is a no-op on ROM and the staging latch. *)
Lemma hoare_WPM_disabled : forall (romv : list byte) (pl : ProgLatch),
  {{ fun s => prom_enable s = false /\ rom s = romv /\ prom_latch s = pl }}
     WPM
  {{ fun s' => rom s' = romv /\ prom_latch s' = pl }}.
Proof.
  intros romv pl.
  unfold hoare_triple. intros s HWF (He & Hr & Hl).
  split; [apply execute_preserves_WF; exact HWF |].
  rewrite (wpm_disabled_is_nop s He).
  split; [exact Hr | exact Hl].
Qed.

(** WRs idx writes the accumulator into status character idx of every
    selected bank: the status read at idx becomes defined with that value. *)
Lemma hoare_WRs_writes : forall idx (v : nibble),
  idx < 4 ->
  {{ fun s => acc s = v }}
     WRs idx
  {{ fun s' => ram_read_stat_opt s' idx = Some v }}.
Proof.
  intros idx v Hidx.
  unfold hoare_triple. intros s HWF Hacc.
  split; [apply execute_preserves_WF; exact HWF |].
  rewrite <- Hacc.
  apply wrs_write_defined; assumption.
Qed.

Corollary hoare_WR0_writes : forall v : nibble,
  {{ fun s => acc s = v }} WR0 {{ fun s' => ram_read_stat_opt s' 0 = Some v }}.
Proof. intro v. exact (hoare_WRs_writes 0 v ltac:(lia)). Qed.

Corollary hoare_WR1_writes : forall v : nibble,
  {{ fun s => acc s = v }} WR1 {{ fun s' => ram_read_stat_opt s' 1 = Some v }}.
Proof. intro v. exact (hoare_WRs_writes 1 v ltac:(lia)). Qed.

Corollary hoare_WR2_writes : forall v : nibble,
  {{ fun s => acc s = v }} WR2 {{ fun s' => ram_read_stat_opt s' 2 = Some v }}.
Proof. intro v. exact (hoare_WRs_writes 2 v ltac:(lia)). Qed.

Corollary hoare_WR3_writes : forall v : nibble,
  {{ fun s => acc s = v }} WR3 {{ fun s' => ram_read_stat_opt s' 3 = Some v }}.
Proof. intro v. exact (hoare_WRs_writes 3 v ltac:(lia)). Qed.

(** RDs idx loads status character idx into the accumulator. *)
Lemma hoare_RDs_value : forall idx (v : nibble),
  idx < 4 ->
  {{ fun s => ram_read_stat s idx = v }}
     RDs idx
  {{ fun s' => acc s' = v }}.
Proof.
  intros idx v Hidx.
  unfold hoare_triple. intros s HWF Hpre.
  split; [apply execute_preserves_WF; exact HWF |].
  rewrite rds_reads_stat by exact Hidx. exact Hpre.
Qed.

Corollary hoare_RD0_value : forall v : nibble,
  {{ fun s => ram_read_stat s 0 = v }} RD0 {{ fun s' => acc s' = v }}.
Proof. intro v. exact (hoare_RDs_value 0 v ltac:(lia)). Qed.

Corollary hoare_RD1_value : forall v : nibble,
  {{ fun s => ram_read_stat s 1 = v }} RD1 {{ fun s' => acc s' = v }}.
Proof. intro v. exact (hoare_RDs_value 1 v ltac:(lia)). Qed.

Corollary hoare_RD2_value : forall v : nibble,
  {{ fun s => ram_read_stat s 2 = v }} RD2 {{ fun s' => acc s' = v }}.
Proof. intro v. exact (hoare_RDs_value 2 v ltac:(lia)). Qed.

Corollary hoare_RD3_value : forall v : nibble,
  {{ fun s => ram_read_stat s 3 = v }} RD3 {{ fun s' => acc s' = v }}.
Proof. intro v. exact (hoare_RDs_value 3 v ltac:(lia)). Qed.

(** ADM: add the selected RAM character with carry. *)
Lemma hoare_ADM_value : forall a m c,
  {{ fun s => aval s = a /\ wval (ram_read_main s) = m /\ carry s = c }}
     ADM
  {{ fun s' => aval s' = (a + m + (if c then 1 else 0)) mod 16 /\
               carry s' = (16 <=? a + m + (if c then 1 else 0)) }}.
Proof.
  intros a m c. hoare_start.
  destruct (adm_computes_sum s) as [Ha Hc].
  unfold cbit in Ha, Hc.
  match goal with
  | H1 : aval s = a, H2 : wval (ram_read_main s) = m, H3 : carry s = c |- _ =>
      rewrite H1, H2, H3 in Ha, Hc
  end.
  split; assumption.
Qed.

(** SBM: subtract the selected RAM character with borrow. *)
Lemma hoare_SBM_value : forall a m c,
  {{ fun s => aval s = a /\ wval (ram_read_main s) = m /\ carry s = c }}
     SBM
  {{ fun s' => aval s' = (a + 16 - m - (if c then 1 else 0)) mod 16 /\
               carry s' = (16 <=? a + 16 - m - (if c then 1 else 0)) }}.
Proof.
  intros a m c. hoare_start.
  destruct (sbm_computes_difference s) as [Ha Hc].
  unfold cbit in Ha, Hc.
  match goal with
  | H1 : aval s = a, H2 : wval (ram_read_main s) = m, H3 : carry s = c |- _ =>
      rewrite H1, H2, H3 in Ha, Hc
  end.
  split; assumption.
Qed.

(* ==================== Program-Level Hoare Logic ================== *)

Definition hoare_prog (P Q : Intel4004State -> Prop) (prog : list Instruction) : Prop :=
  forall s, WF s -> P s ->
    let s' := exec_program prog s in
    WF s' /\ Q s'.

Notation "{{| P |}} prog {{| Q |}}" := (hoare_prog P Q prog) (at level 90).

Lemma hoare_single : forall P Q i,
  {{ P }} i {{ Q }} ->
  {{| P |}} [i] {{| Q |}}.
Proof.
  intros P Q i H.
  unfold hoare_prog, hoare_triple in *.
  intros s HWF HP. simpl. apply H; auto.
Qed.

Lemma hoare_prog_seq : forall P Q R prog1 prog2,
  {{| P |}} prog1 {{| Q |}} ->
  {{| Q |}} prog2 {{| R |}} ->
  {{| P |}} prog1 ++ prog2 {{| R |}}.
Proof.
  intros P Q R prog1 prog2 H1 H2.
  unfold hoare_prog in *.
  intros s HWF HP.
  rewrite exec_program_app.
  assert (Hmid := H1 s HWF HP).
  destruct Hmid as [HWF' HQ].
  apply H2; auto.
Qed.

Lemma hoare_prog_consequence : forall P P' Q Q' prog,
  (forall s, P' s -> P s) ->
  {{| P |}} prog {{| Q |}} ->
  (forall s, Q s -> Q' s) ->
  {{| P' |}} prog {{| Q' |}}.
Proof.
  intros P P' Q Q' prog Hpre Hprog Hpost.
  unfold hoare_prog in *.
  intros s HWF HP'.
  specialize (Hprog s HWF (Hpre s HP')).
  destruct Hprog as [HWF' HQ].
  split; auto.
Qed.

Fixpoint wp (prog : list Instruction) (Q : Intel4004State -> Prop) : Intel4004State -> Prop :=
  match prog with
  | [] => Q
  | i :: rest => fun s =>
      WF s ->
      let s' := execute s i in
      WF s' /\ wp rest Q s'
  end.

Theorem wp_soundness : forall prog Q,
  {{| wp prog Q |}} prog {{| Q |}}.
Proof.
  induction prog; intros Q.
  - unfold hoare_prog, wp. intros s HWF HQ. simpl. split; auto.
  - unfold hoare_prog, wp. intros s HWF Hwp.
    specialize (Hwp HWF).
    destruct Hwp as [HWF' Hwp'].
    simpl. fold exec_program.
    apply IHprog; auto.
Qed.

(* Bounded repetition of a program body (total-function analogue of while). *)
Fixpoint repeat_prog (n : nat) (body : list Instruction) : list Instruction :=
  match n with
  | 0 => []
  | S k => body ++ repeat_prog k body
  end.

(* Loop-invariant rule: an Inv-preserving body preserves Inv over any
   iteration count. *)
Lemma hoare_prog_repeat : forall (Inv : Intel4004State -> Prop) body n,
  {{| Inv |}} body {{| Inv |}} ->
  {{| Inv |}} repeat_prog n body {{| Inv |}}.
Proof.
  intros Inv body n Hbody. induction n; simpl.
  - unfold hoare_prog. intros s HWF HI. simpl. split; assumption.
  - apply hoare_prog_seq with (Q := Inv); [exact Hbody | exact IHn].
Qed.

(* Verification condition for a straight-line program against a
   postcondition. *)
Definition vc (P : Intel4004State -> Prop) (prog : list Instruction)
              (Q : Intel4004State -> Prop) : Prop :=
  forall s, WF s -> P s -> wp prog Q s.

(* Discharging the verification condition establishes the program triple. *)
Theorem vc_sound : forall P prog Q,
  vc P prog Q -> {{| P |}} prog {{| Q |}}.
Proof.
  intros P prog Q Hvc. unfold hoare_prog, vc in *. intros s HWF HP.
  pose proof (wp_soundness prog Q) as Hwp. unfold hoare_prog in Hwp.
  apply Hwp; [exact HWF | apply Hvc; assumption].
Qed.

(* ==================== Example Verifications ====================== *)

Example ex_load_5 :
  {{| fun _ => True |}}
      [LDM (nib 5)]
  {{| fun s => acc s = nib 5 |}}.
Proof.
  apply hoare_single. apply hoare_LDM.
Qed.

Example ex_clear :
  {{| fun _ => True |}}
      [CLB]
  {{| fun s => acc s = nib 0 /\ carry s = false |}}.
Proof.
  apply hoare_single. apply hoare_CLB.
Qed.

Example ex_ldm_iac :
  {{| fun _ => True |}}
      [LDM (nib 5); IAC]
  {{| fun s => aval s = 6 |}}.
Proof.
  unfold hoare_prog. intros s HWF _.
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - reflexivity.
Qed.

Example ex_CMA_involution : forall a,
  a < 16 ->
  {{| fun s => aval s = a |}}
      [CMA; CMA]
  {{| fun s => aval s = a |}}.
Proof.
  intros a Ha.
  unfold hoare_prog. intros s HWF Hacc.
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - unfold aval in Hacc |- *.
    exec_simpl.
    rewrite nib_val. rewrite nib_val.
    rewrite (Nat.mod_small (15 - wval (acc s)) 16)
      by (pose proof (nib_lt16 (acc s)); lia).
    rewrite Hacc.
    rewrite Nat.mod_small by lia.
    lia.
Qed.

(** Copying a register through the accumulator. *)
Lemma copy_reg : forall (src dst : nibble) (v : nibble),
  wval src <> wval dst ->
  {{| fun s => length (regs s) = 16 /\ get_reg s (wval src) = v |}}
      [LD src; XCH dst]
  {{| fun s => get_reg s (wval src) = v /\ get_reg s (wval dst) = v |}}.
Proof.
  intros src dst v Hneq.
  unfold hoare_prog. intros s HWF [Hlen Hreg].
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - set (s1 := execute s (LD src)).
    assert (Hlen1 : length (regs s1) = 16) by exact Hlen.
    assert (Hacc1 : acc s1 = v) by exact Hreg.
    assert (Hreg1 : get_reg s1 (wval src) = v) by exact Hreg.
    split.
    + rewrite xch_reg_other by lia. exact Hreg1.
    + rewrite xch_reg_written by exact Hlen1. exact Hacc1.
Qed.

(** Zeroing a register. *)
Lemma zero_reg : forall r : nibble,
  {{| fun s => length (regs s) = 16 |}}
      [CLB; XCH r]
  {{| fun s => get_reg s (wval r) = nib 0 |}}.
Proof.
  intros r.
  unfold hoare_prog. intros s HWF Hlen.
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - set (s1 := execute s CLB).
    assert (Hlen1 : length (regs s1) = 16) by exact Hlen.
    assert (Hacc1 : acc s1 = nib 0) by reflexivity.
    rewrite xch_reg_written by exact Hlen1. exact Hacc1.
Qed.

(** JMS then BBL: the return lands after the call, at any ring depth. *)
Example ex_jms_bbl_roundtrip : forall (a : addr12) (d : nibble) p0,
  {{| fun s => pcv s = p0 |}}
      [JMS a; BBL d]
  {{| fun s => pc s = adr (p0 + 2) /\ acc s = d |}}.
Proof.
  intros a d p0.
  unfold hoare_prog. intros s HWF Hpc.
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - split.
    + rewrite jms_bbl_roundtrip. rewrite Hpc. reflexivity.
    + reflexivity.
Qed.

(** Nested calls and returns through the ring: two JMS/BBL pairs restore
    the sequential flow. *)
Example ex_stack_discipline : forall (a1 a2 : addr12) (d1 d2 : nibble) p0,
  p0 + 4 < 4096 ->
  {{| fun s => pcv s = p0 |}}
      [JMS a1; BBL d1; JMS a2; BBL d2]
  {{| fun s => pc s = adr (p0 + 4) |}}.
Proof.
  intros a1 a2 d1 d2 p0 Hfit.
  unfold hoare_prog. intros s HWF Hpc.
  cbn [exec_program].
  split.
  - repeat apply execute_preserves_WF. exact HWF.
  - set (s2 := execute (execute s (JMS a1)) (BBL d1)).
    assert (Hpc2 : pc s2 = adr (p0 + 2)).
    { unfold s2. rewrite jms_bbl_roundtrip. rewrite Hpc. reflexivity. }
    replace (pc (execute (execute s2 (JMS a2)) (BBL d2)))
      with (adr (pcv s2 + 2)) by (rewrite jms_bbl_roundtrip; reflexivity).
    unfold pcv. rewrite Hpc2.
    rewrite adr_val.
    rewrite Nat.mod_small by lia.
    replace (p0 + 2 + 2) with (p0 + 4) by lia.
    reflexivity.
Qed.

(** RAM round trip: select, write, read back (any DCL code). *)
Example ram_write_read_roundtrip : forall (r : nibble) (v : nibble),
  {{| fun s => acc s = v |}}
      [SRC r; WRM; RDM]
  {{| fun s => acc s = v |}}.
Proof.
  intros r v.
  unfold hoare_prog. intros s HWF Hacc.
  cbn [exec_program].
  split.
  - repeat apply execute_preserves_WF. exact HWF.
  - set (s1 := execute s (SRC r)).
    assert (HWF1 : WF s1) by (apply execute_preserves_WF; exact HWF).
    assert (Hacc1 : acc s1 = v) by exact Hacc.
    rewrite <- Hacc1.
    apply wrm_then_rdm_reads_back. exact HWF1.
Qed.

(** Doubling the accumulator by rotate-left with clear carry. *)
Example double_accumulator : forall v,
  v < 8 ->
  {{| fun s => aval s = v /\ carry s = false |}}
      [RAL]
  {{| fun s => aval s = 2 * v /\ carry s = false |}}.
Proof.
  intros v Hv.
  unfold hoare_prog. intros s HWF [Hacc Hcarry].
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. exact HWF.
  - unfold aval in Hacc |- *. exec_simpl. rewrite Hacc, Hcarry.
    split.
    + rewrite nib_val. rewrite Nat.add_0_r.
      rewrite Nat.mod_small by lia. lia.
    + destruct (8 <=? v) eqn:E; [apply Nat.leb_le in E; lia | reflexivity].
Qed.

(** Halving the accumulator by rotate-right with clear carry. *)
Example halve_accumulator : forall v,
  {{| fun s => aval s = v /\ carry s = false |}}
      [RAR]
  {{| fun s => aval s = v / 2 |}}.
Proof.
  intros v.
  unfold hoare_prog. intros s HWF [Hacc Hcarry].
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. exact HWF.
  - assert (Hv16 : v < 16) by (rewrite <- Hacc; apply aval_lt16).
    unfold aval in Hacc |- *. exec_simpl. rewrite Hacc, Hcarry.
    rewrite nib_val. rewrite Nat.add_0_r.
    apply Nat.mod_small.
    apply Nat.Div0.div_lt_upper_bound. lia.
Qed.

(** Extracting bit zero of the accumulator. *)
Example test_bit_zero : forall v,
  v < 16 ->
  {{| fun s => aval s = v |}}
      [RAR; TCC]
  {{| fun s => aval s = (if v mod 2 =? 1 then 1 else 0) /\ carry s = false |}}.
Proof.
  intros v Hv.
  unfold hoare_prog. intros s HWF Hacc.
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - set (s1 := execute s RAR).
    assert (Hc1 : carry s1 = (aval s mod 2 =? 1)) by reflexivity.
    split.
    + assert (Ha : aval (execute s1 TCC) = cbit s1).
      { unfold aval, cbit. exec_simpl.
        destruct (carry s1); reflexivity. }
      rewrite Ha. unfold cbit. rewrite Hc1, Hacc.
      destruct (v mod 2 =? 1); reflexivity.
    + reflexivity.
Qed.

(** Comparison by subtraction: 7 - 3 leaves no borrow (carry set). *)
Example max_of_two_concrete :
  {{| fun s => get_reg s 0 = nib 7 /\ get_reg s 1 = nib 3 /\ carry s = false |}}
      [LD (nib 0); SUB (nib 1)]
  {{| fun s => carry s = true |}}.
Proof.
  unfold hoare_prog. intros s HWF [Hr0 [Hr1 Hcarry]].
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - set (s1 := execute s (LD (nib 0))).
    assert (Hacc1 : acc s1 = nib 7).
    { unfold s1. rewrite <- Hr0. reflexivity. }
    assert (Hreg1 : get_reg s1 1 = nib 3) by exact Hr1.
    assert (Hcar1 : carry s1 = false) by exact Hcarry.
    destruct (sub_computes_difference s1 (nib 1)) as [_ Hc].
    rewrite Hc.
    unfold aval, rval, cbit.
    rewrite Hacc1, Hcar1.
    replace (wval (nib 1)) with 1 by reflexivity.
    rewrite Hreg1.
    reflexivity.
Qed.

(** Addition: 5 + 7 = 12. *)
Example add_two_nibbles :
  {{| fun s => get_reg s 0 = nib 5 /\ get_reg s 1 = nib 7 /\ carry s = false |}}
      [LD (nib 0); ADD (nib 1)]
  {{| fun s => aval s = 12 |}}.
Proof.
  unfold hoare_prog. intros s HWF [Hr0 [Hr1 Hcarry]].
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - set (s1 := execute s (LD (nib 0))).
    assert (Hacc1 : acc s1 = nib 5).
    { unfold s1. rewrite <- Hr0. reflexivity. }
    assert (Hreg1 : get_reg s1 1 = nib 7) by exact Hr1.
    assert (Hcar1 : carry s1 = false) by exact Hcarry.
    destruct (add_computes_sum s1 (nib 1)) as [Ha _].
    rewrite Ha.
    unfold aval, rval, cbit.
    rewrite Hacc1, Hcar1.
    replace (wval (nib 1)) with 1 by reflexivity.
    rewrite Hreg1.
    reflexivity.
Qed.

(* ===================================================================== *)
(*                    END-TO-END PROGRAM VERIFICATION                    *)
(* ===================================================================== *)

(*
   Verified Program: ISZ Counting Loop

   This program counts from 0 to 15 in register R0, then exits when R0
   wraps back to 0.

   Assembly:
        LDM 0       ; acc = 0
        XCH 0       ; R0 = 0, acc = old R0
   LOOP:
        INC 0       ; R0 = R0 + 1
        ISZ 0,LOOP  ; if R0 != 0, goto LOOP
*)

Definition count_loop_init : list Instruction :=
  [LDM (nib 0); XCH (nib 0)].

Definition count_loop_body : Instruction :=
  INC (nib 0).

Theorem count_loop_init_correct :
  {{| fun s => length (regs s) = 16 |}}
      count_loop_init
  {{| fun s => rval s 0 = 0 |}}.
Proof.
  unfold count_loop_init, hoare_prog.
  intros s HWF Hlen.
  cbn [exec_program].
  split.
  - apply execute_preserves_WF. apply execute_preserves_WF. exact HWF.
  - set (s1 := execute s (LDM (nib 0))).
    assert (Hlen1 : length (regs s1) = 16) by exact Hlen.
    assert (Hx := xch_reg_written s1 (nib 0) Hlen1).
    replace (wval (nib 0)) with 0 in Hx by reflexivity.
    unfold rval. rewrite Hx. reflexivity.
Qed.

Lemma count_loop_body_increments : forall s v,
  length (regs s) = 16 ->
  rval s 0 = v ->
  rval (execute s count_loop_body) 0 = (v + 1) mod 16.
Proof.
  intros s v Hlen Hv.
  unfold count_loop_body, rval.
  exec_simpl. unfold get_reg. cbn [regs].
  replace (wval (nib 0)) with 0 by reflexivity.
  rewrite nth_update_nth_eq by (rewrite Hlen; lia).
  rewrite nib_val.
  rewrite Hv.
  reflexivity.
Qed.

Fixpoint iterate_body (n : nat) (s : Intel4004State) : Intel4004State :=
  match n with
  | 0 => s
  | S n' => iterate_body n' (execute s count_loop_body)
  end.

Lemma iterate_body_preserves_WF : forall n s,
  WF s -> WF (iterate_body n s).
Proof.
  induction n; intros s HWF.
  - exact HWF.
  - cbn [iterate_body]. apply IHn. apply execute_preserves_WF. exact HWF.
Qed.

Lemma iterate_body_preserves_len : forall n s,
  length (regs s) = 16 -> length (regs (iterate_body n s)) = 16.
Proof.
  induction n; intros s Hlen.
  - exact Hlen.
  - cbn [iterate_body]. apply IHn.
    unfold count_loop_body. exec_simpl.
    rewrite update_nth_length. exact Hlen.
Qed.

Lemma iterate_body_register_gen : forall n s v,
  length (regs s) = 16 ->
  rval s 0 = v ->
  v < 16 ->
  n + v <= 16 ->
  rval (iterate_body n s) 0 = (v + n) mod 16.
Proof.
  induction n; intros s v Hlen Hreg Hv Hbound.
  - cbn [iterate_body]. rewrite Hreg.
    replace (v + 0) with v by lia.
    symmetry. apply Nat.mod_small. lia.
  - cbn [iterate_body].
    assert (Hlen' : length (regs (execute s count_loop_body)) = 16).
    { unfold count_loop_body. exec_simpl.
      rewrite update_nth_length. exact Hlen. }
    assert (Hreg' : rval (execute s count_loop_body) 0 = (v + 1) mod 16)
      by (apply count_loop_body_increments; assumption).
    destruct (Nat.eq_dec v 15) as [Hv15 | Hv15].
    + subst v.
      assert (Hn0 : n = 0) by lia. subst n.
      simpl. exact Hreg'.
    + assert (Hsmall : (v + 1) mod 16 = v + 1) by (apply Nat.mod_small; lia).
      rewrite Hsmall in Hreg'.
      rewrite (IHn (execute s count_loop_body) (v + 1) Hlen' Hreg')
        by lia.
      replace (v + 1 + n) with (v + S n) by lia.
      reflexivity.
Qed.

Theorem count_loop_16_iterations : forall s,
  length (regs s) = 16 ->
  rval s 0 = 0 ->
  rval (iterate_body 16 s) 0 = 0.
Proof.
  intros s Hlen Hreg.
  rewrite (iterate_body_register_gen 16 s 0 Hlen Hreg) by lia.
  reflexivity.
Qed.

Theorem count_loop_terminates : forall s,
  WF s ->
  rval s 0 = 0 ->
  WF (iterate_body 16 s) /\ rval (iterate_body 16 s) 0 = 0.
Proof.
  intros s HWF Hreg.
  split.
  - apply iterate_body_preserves_WF. exact HWF.
  - apply count_loop_16_iterations; [destruct_WF HWF; assumption | exact Hreg].
Qed.

(* ==================== BCD digit addition ========================== *)

(* Binary add then decimal adjust yields the decimal sum digit and carry. *)
Definition bcd_add_digits : list Instruction :=
  [CLC; LD (nib 1); ADD (nib 2); DAA].

Theorem bcd_add_digits_correct : forall s x y,
  x <= 9 -> y <= 9 ->
  rval s 1 = x -> rval s 2 = y ->
  let s' := exec_program bcd_add_digits s in
  aval s' = (x + y) mod 10 /\
  (if carry s' then 1 else 0) = (x + y) / 10.
Proof.
  intros s x y Hx Hy H1 H2. cbv zeta.
  unfold bcd_add_digits. cbn [exec_program].
  set (s1 := execute s CLC).
  assert (Hc1 : carry s1 = false) by reflexivity.
  assert (Hg1 : rval s1 1 = x) by exact H1.
  assert (Hg2 : rval s1 2 = y) by exact H2.
  set (s2 := execute s1 (LD (nib 1))).
  assert (Ha2 : aval s2 = x).
  { unfold s2, aval. exec_simpl.
    replace (wval (nib 1)) with 1 by reflexivity.
    exact Hg1. }
  assert (Hc2 : carry s2 = false) by exact Hc1.
  assert (Hg2' : rval s2 2 = y) by exact Hg2.
  set (s3 := execute s2 (ADD (nib 2))).
  assert (Ha3 : aval s3 = (x + y + 0) mod 16).
  { unfold s3.
    destruct (add_computes_sum s2 (nib 2)) as [HA _].
    rewrite HA.
    unfold cbit. rewrite Hc2, Ha2.
    replace (wval (nib 2)) with 2 by reflexivity.
    rewrite Hg2'. reflexivity. }
  assert (Hc3 : carry s3 = (16 <=? x + y + 0)).
  { unfold s3.
    destruct (add_computes_sum s2 (nib 2)) as [_ HC].
    rewrite HC.
    unfold cbit. rewrite Hc2, Ha2.
    replace (wval (nib 2)) with 2 by reflexivity.
    rewrite Hg2'. reflexivity. }
  pose proof (daa_decimal_correct s3 x y 0 Hx Hy ltac:(lia) Ha3 Hc3) as Hfin.
  replace (x + y + 0) with (x + y) in Hfin by lia.
  exact Hfin.
Qed.

(* Minimal verified compiler over a source accumulator-expression language. *)
Inductive SrcExpr : Type :=
  | SConst : nibble -> SrcExpr
  | SReg   : nibble -> SrcExpr.

Definition src_eval (s : Intel4004State) (e : SrcExpr) : nibble :=
  match e with
  | SConst n => n
  | SReg r => get_reg s (wval r)
  end.

Definition compile (e : SrcExpr) : list Instruction :=
  match e with
  | SConst n => [LDM n]
  | SReg r => [LD r]
  end.

(* Refinement: compiled code leaves the source value in the accumulator. *)
Theorem compile_correct : forall s e,
  acc (exec_program (compile e) s) = src_eval s e.
Proof. intros s e. destruct e; reflexivity. Qed.

(* ===================================================================== *)
(*             SEPARATION LOGIC OVER THE RAM HIERARCHY                   *)
(* ===================================================================== *)

(* Heaps are partial maps from (bank, chip, register, character) addresses
   to nibbles; assertions are heap predicates with an honest separating
   conjunction, and a state realizes an assertion when the RAM agrees with
   some satisfying heap on its whole domain.  The small-footprint WRM and
   RDM rules are stated for single-line DCL codes, where the machine
   addresses exactly one cell; the multi-line write semantics is covered by
   the bank-set theorems of behavior.v. *)

Definition Addr4 : Type := (nat * nat * nat * nat)%type.

Definition addr4_eq_dec : forall a b : Addr4, {a = b} + {a <> b}.
Proof. repeat decide equality. Defined.

Definition Heap := Addr4 -> option nibble.

Definition hempty : Heap := fun _ => None.

Definition hsingle (a : Addr4) (v : nibble) : Heap :=
  fun a' => if addr4_eq_dec a' a then Some v else None.

Definition hdisj (h1 h2 : Heap) : Prop :=
  forall a, h1 a = None \/ h2 a = None.

Definition hunion (h1 h2 : Heap) : Heap :=
  fun a => match h1 a with Some v => Some v | None => h2 a end.

Definition Assertion := Heap -> Prop.

Definition emp : Assertion := fun h => forall a, h a = None.

Definition pts (a : Addr4) (v : nibble) : Assertion :=
  fun h => forall a', h a' = hsingle a v a'.

Definition star (P Q : Assertion) : Assertion :=
  fun h => exists h1 h2,
    hdisj h1 h2 /\ (forall a, h a = hunion h1 h2 a) /\ P h1 /\ Q h2.

Notation "P ** Q" := (star P Q) (at level 80, right associativity).
Notation "a |-> v" := (pts a v) (at level 70).

(* ---------------- Heap algebra ---------------- *)

Lemma hdisj_comm : forall h1 h2, hdisj h1 h2 -> hdisj h2 h1.
Proof. intros h1 h2 H a. destruct (H a); auto. Qed.

Lemma hunion_comm_pt : forall h1 h2 a,
  hdisj h1 h2 -> hunion h1 h2 a = hunion h2 h1 a.
Proof.
  intros h1 h2 a Hd. unfold hunion.
  destruct (Hd a) as [E|E]; rewrite E.
  - destruct (h2 a); reflexivity.
  - destruct (h1 a); reflexivity.
Qed.

(** Separating conjunction is commutative. *)
Lemma star_comm : forall P Q h, (P ** Q) h <-> (Q ** P) h.
Proof.
  assert (F : forall P Q h, (P ** Q) h -> (Q ** P) h).
  { intros P Q h (h1 & h2 & Hd & Hu & HP & HQ).
    exists h2, h1.
    split; [apply hdisj_comm; exact Hd|].
    split; [|split; assumption].
    intro a. rewrite Hu. apply hunion_comm_pt. exact Hd. }
  intros P Q h. split; apply F.
Qed.

Lemma hunion_none : forall h1 h2 a,
  hunion h1 h2 a = None -> h1 a = None /\ h2 a = None.
Proof.
  intros h1 h2 a H. unfold hunion in H.
  destruct (h1 a) eqn:E1; [discriminate | auto].
Qed.

(** Separating conjunction is associative. *)
Lemma star_assoc : forall P Q R h,
  (P ** (Q ** R)) h <-> ((P ** Q) ** R) h.
Proof.
  intros P Q R h; split.
  - intros (h1 & h23 & Hd & Hu & HP & (h2 & h3 & Hd23 & Hu23 & HQ & HR)).
    assert (Hd12 : hdisj h1 h2).
    { intro a. destruct (Hd a) as [E|E]; [auto|].
      rewrite Hu23 in E. destruct (hunion_none _ _ _ E); auto. }
    assert (Hd13 : hdisj h1 h3).
    { intro a. destruct (Hd a) as [E|E]; [auto|].
      rewrite Hu23 in E. destruct (hunion_none _ _ _ E); auto. }
    exists (hunion h1 h2), h3.
    repeat split; auto.
    + intro a. unfold hunion.
      destruct (h1 a) eqn:E1.
      * destruct (Hd13 a) as [E|E]; [congruence | auto].
      * destruct (Hd23 a) as [E|E]; auto.
    + intro a. rewrite Hu. unfold hunion.
      destruct (h1 a) eqn:E1; [reflexivity|].
      rewrite Hu23. unfold hunion. reflexivity.
    + exists h1, h2. repeat split; auto.
  - intros (h12 & h3 & Hd & Hu & (h1 & h2 & Hd12 & Hu12 & HP & HQ) & HR).
    assert (Hd23 : hdisj h2 h3).
    { intro a. destruct (Hd a) as [E|E]; [|auto].
      rewrite Hu12 in E. destruct (hunion_none _ _ _ E); auto. }
    assert (Hd13 : hdisj h1 h3).
    { intro a. destruct (Hd a) as [E|E]; [|auto].
      rewrite Hu12 in E. destruct (hunion_none _ _ _ E); auto. }
    exists h1, (hunion h2 h3).
    repeat split; auto.
    + intro a. unfold hunion.
      destruct (h1 a) eqn:E1; [|auto].
      destruct (Hd12 a) as [E|E]; [congruence|].
      rewrite E. destruct (Hd13 a) as [E'|E']; [congruence | auto].
    + intro a. rewrite Hu. unfold hunion. rewrite Hu12. unfold hunion.
      destruct (h1 a) eqn:E1; [reflexivity|].
      destruct (h2 a) eqn:E2; reflexivity.
    + exists h2, h3. repeat split; auto.
Qed.

(** The same cell cannot be owned twice. *)
Lemma pts_star_pts_absurd : forall a v w h,
  ~ ((a |-> v) ** (a |-> w)) h.
Proof.
  intros a v w h (h1 & h2 & Hd & _ & H1 & H2).
  destruct (Hd a) as [E|E];
    [rewrite H1 in E | rewrite H2 in E];
    unfold hsingle in E;
    destruct (addr4_eq_dec a a); congruence.
Qed.

(* ---------------- States realizing assertions ---------------- *)

(** RAM contents at a hierarchy address. *)
Definition ram_at (s : Intel4004State) (a : Addr4) : nibble :=
  let '(b, c, r, i) := a in
  get_main (get_regRAM (get_chip (get_bank s b) c) r) i.

(** A state realizes an assertion when some satisfying heap agrees with the
    RAM everywhere the heap is defined. *)
Definition holds (s : Intel4004State) (P : Assertion) : Prop :=
  exists h, P h /\ forall a v, h a = Some v -> ram_at s a = v.

(** Single-line DCL selection: the machine addresses exactly one cell. *)
Definition single_line (s : Intel4004State) : Prop :=
  wval (cm_code s) = 0 \/ wval (cm_code s) = 1 \/
  wval (cm_code s) = 2 \/ wval (cm_code s) = 4.

(** The currently selected cell as a hierarchy address. *)
Definition sel_addr (s : Intel4004State) : Addr4 :=
  (dcl_bank (cm_code s),
   wval (sel_chip (sel_ram s)),
   wval (sel_reg (sel_ram s)),
   wval (sel_char (sel_ram s))).

Lemma ram_read_main_is_ram_at : forall s,
  single_line s ->
  ram_read_main s = ram_at s (sel_addr s).
Proof.
  intros s Hs.
  unfold ram_read_main.
  rewrite (dcl_read_single_line s Hs).
  reflexivity.
Qed.

(** WRM writes the selected cell (single-line). *)
Lemma wrm_ram_at_write : forall s,
  WF s ->
  single_line s ->
  ram_at (execute s WRM) (sel_addr s) = acc s.
Proof.
  intros s HWF Hs.
  replace (ram_at (execute s WRM) (sel_addr s))
    with (read_main_bank (ram_sys (execute s WRM)) (sel_ram s)
            (dcl_bank (cm_code s)))
    by reflexivity.
  apply dcl_write_reaches_all_selected; [exact HWF |].
  unfold sel_lines.
  rewrite (dcl_lines_single _ Hs).
  left. reflexivity.
Qed.

(** WRM leaves every other cell alone (single-line). *)
Lemma wrm_ram_at_frame : forall s b' c' r' i',
  WF s ->
  single_line s ->
  (b', c', r', i') <> sel_addr s ->
  ram_at (execute s WRM) (b', c', r', i') = ram_at s (b', c', r', i').
Proof.
  intros s b' c' r' i' HWF Hs Hne.
  destruct_WF HWF.
  set (k := dcl_bank (cm_code s)) in *.
  assert (Hlines : sel_lines s = [k])
    by (unfold sel_lines, k; apply dcl_lines_single; exact Hs).
  destruct (Nat.eq_dec b' k) as [-> | Hbne].
  2:{ apply wrm_frames_other_bank.
      rewrite Hlines. intros [Heq | []]. congruence. }
  (* the selected bank, but a different chip, register, or character *)
  assert (Hk4 : k < 4) by (unfold k; apply dcl_bank_lt_4).
  assert (Hklen : k < length (ram_sys s))
    by (rewrite HsysLen; unfold NBANKS; lia).
  assert (Hram : ram_sys (execute s WRM)
                 = write_main_bank (ram_sys s) (sel_ram s) k (acc s)).
  { replace (ram_sys (execute s WRM))
      with (write_main_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s))
      by reflexivity.
    rewrite Hlines. reflexivity. }
  unfold ram_at, get_bank.
  rewrite Hram.
  rewrite (write_main_bank_bank (ram_sys s) (sel_ram s) k (acc s) Hklen).
  assert (HWFbk : WF_bank (get_bank_sys (ram_sys s) k))
    by (apply WF_bank_from_sys; assumption).
  assert (HWFch : WF_chip (get_chip (get_bank_sys (ram_sys s) k)
                             (wval (sel_chip (sel_ram s)))))
    by (apply WF_chip_from_bank; exact HWFbk).
  destruct (Nat.eq_dec c' (wval (sel_chip (sel_ram s)))) as [-> | Hcne].
  2:{ rewrite get_chip_upd_chip_in_bank_neq by congruence. reflexivity. }
  rewrite get_chip_upd_chip_in_bank
    by (destruct HWFbk as [Hl _]; rewrite Hl;
        pose proof (w2_lt4 (sel_chip (sel_ram s))); unfold NCHIPS; lia).
  destruct (Nat.eq_dec r' (wval (sel_reg (sel_ram s)))) as [-> | Hrne].
  2:{ rewrite get_regRAM_upd_reg_in_chip_neq by congruence. reflexivity. }
  rewrite get_regRAM_upd_reg_in_chip
    by (destruct HWFch as [Hl _]; rewrite Hl;
        pose proof (w2_lt4 (sel_reg (sel_ram s))); unfold NREGS; lia).
  apply get_main_upd_main_in_reg_neq.
  intro Heq. apply Hne. unfold sel_addr, k. congruence.
Qed.

(* ---------------- Small-footprint rules with frames ---------------- *)

(** {sel |-> w ** R} WRM {sel |-> acc ** R}: the single-line write owns
    exactly the selected cell; an arbitrary disjoint frame survives
    untouched. *)
Theorem wrm_sep_frame : forall s (R : Assertion) (w : nibble),
  WF s ->
  single_line s ->
  holds s ((sel_addr s |-> w) ** R) ->
  holds (execute s WRM) ((sel_addr s |-> acc s) ** R).
Proof.
  intros s R w HWF Hs (h & (h1 & h2 & Hd & Hu & Hpts & HR) & Hagree).
  assert (Hh2sel : h2 (sel_addr s) = None).
  { destruct (Hd (sel_addr s)) as [E|E]; [|exact E].
    rewrite Hpts in E. unfold hsingle in E.
    destruct (addr4_eq_dec (sel_addr s) (sel_addr s)); congruence. }
  exists (hunion (hsingle (sel_addr s) (acc s)) h2).
  split.
  - exists (hsingle (sel_addr s) (acc s)), h2.
    repeat split; auto.
    + intro a. unfold hsingle.
      destruct (addr4_eq_dec a (sel_addr s)) as [->|]; [right; exact Hh2sel |].
      left; reflexivity.
  - intros [[[b' c'] r'] i'] v Hav.
    unfold hunion, hsingle in Hav.
    destruct (addr4_eq_dec (b', c', r', i') (sel_addr s)) as [Heq|Hne].
    + injection Hav as <-. rewrite Heq. apply wrm_ram_at_write; assumption.
    + rewrite wrm_ram_at_frame by assumption.
      apply Hagree. rewrite Hu. unfold hunion.
      rewrite Hpts. unfold hsingle.
      destruct (addr4_eq_dec (b', c', r', i') (sel_addr s)); [contradiction|].
      exact Hav.
Qed.

(** RDM reads through a points-to on the selected cell (single-line). *)
Theorem rdm_sep : forall s (R : Assertion) (v : nibble),
  single_line s ->
  holds s ((sel_addr s |-> v) ** R) ->
  acc (execute s RDM) = v.
Proof.
  intros s R v Hs (h & (h1 & h2 & Hd & Hu & Hpts & HR) & Hagree).
  replace (acc (execute s RDM)) with (ram_read_main s) by reflexivity.
  rewrite (ram_read_main_is_ram_at s Hs).
  apply Hagree. rewrite Hu. unfold hunion.
  rewrite Hpts. unfold hsingle.
  destruct (addr4_eq_dec (sel_addr s) (sel_addr s)); [reflexivity | congruence].
Qed.

(* ===================================================================== *)
(*            MULTI-BYTE BCD ARITHMETIC WITH CARRY PROPAGATION           *)
(* ===================================================================== *)

(* The addend digits sit little-endian in registers 2..7, the augend digits
   in registers 8..13, and the generated program chains CLC with one
   LD/ADD/DAA/XCH block per digit, the decimal carry flowing through the
   carry/link flag.  Correctness is proven against a pure decimal
   digit-adder, which itself is proven to compute digit-list values. *)

(* ---------------- The pure decimal reference ---------------- *)

(** Value of a little-endian decimal digit list. *)
Fixpoint dval (ds : list nat) : nat :=
  match ds with
  | [] => 0
  | d :: rest => d + 10 * dval rest
  end.

(** Decimal ripple adder over digit lists. *)
Fixpoint bcd_sum (xs ys : list nat) (c : nat) : list nat * nat :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      let '(rest, cout) := bcd_sum xs' ys' ((x + y + c) / 10) in
      ((x + y + c) mod 10 :: rest, cout)
  | _, _ => ([], c)
  end.

(** The ripple adder computes digit-list addition. *)
Theorem bcd_sum_correct : forall xs ys c,
  length ys = length xs ->
  Forall (fun d => d <= 9) xs -> Forall (fun d => d <= 9) ys -> c <= 1 ->
  dval (fst (bcd_sum xs ys c)) + snd (bcd_sum xs ys c) * 10 ^ length xs
  = dval xs + dval ys + c.
Proof.
  induction xs as [|x xs' IH]; intros ys c Hlen Hxs Hys Hc.
  - destruct ys; [simpl; lia | simpl in Hlen; discriminate].
  - destruct ys as [|y ys']; [simpl in Hlen; discriminate|].
    inversion Hxs as [|? ? Hx9 Hxs']; subst.
    inversion Hys as [|? ? Hy9 Hys']; subst.
    simpl in Hlen. injection Hlen as Hlen.
    assert (Hc' : (x + y + c) / 10 <= 1).
    { assert ((x + y + c) / 10 < 2);
        [apply Nat.Div0.div_lt_upper_bound; lia | lia]. }
    specialize (IH ys' ((x + y + c) / 10) Hlen Hxs' Hys' Hc').
    cbn [bcd_sum].
    destruct (bcd_sum xs' ys' ((x + y + c) / 10)) as [rest cout] eqn:Erec.
    cbn [fst snd] in IH.
    cbn [fst snd dval length Nat.pow].
    pose proof (Nat.div_mod_eq (x + y + c) 10) as Hdm.
    nia.
Qed.

(** The decimal carry never exceeds one for bounded digits. *)
Lemma bcd_sum_carry_le1 : forall xs ys c,
  Forall (fun d => d <= 9) xs -> Forall (fun d => d <= 9) ys -> c <= 1 ->
  snd (bcd_sum xs ys c) <= 1.
Proof.
  induction xs as [|x xs' IH]; intros ys c Hxs Hys Hc.
  - simpl. exact Hc.
  - destruct ys as [|y ys']; [simpl; exact Hc|].
    inversion Hxs as [|? ? Hx9 Hxs']; subst.
    inversion Hys as [|? ? Hy9 Hys']; subst.
    cbn [bcd_sum].
    assert (Hc' : (x + y + c) / 10 <= 1).
    { assert ((x + y + c) / 10 < 2);
        [apply Nat.Div0.div_lt_upper_bound; lia | lia]. }
    specialize (IH ys' ((x + y + c) / 10) Hxs' Hys' Hc').
    destruct (bcd_sum xs' ys' ((x + y + c) / 10)) as [rest cout] eqn:Erec.
    cbn [snd] in *. exact IH.
Qed.

(* ---------------- The generated 4004 program ---------------- *)

Fixpoint bcd_blocks (i n : nat) : list Instruction :=
  match n with
  | 0 => []
  | S k => [LD (nib (2 + i)); ADD (nib (8 + i)); DAA; XCH (nib (2 + i))]
             ++ bcd_blocks (S i) k
  end.

Definition bcd_add_prog (n : nat) : list Instruction :=
  CLC :: bcd_blocks 0 n.

(** One digit block: from digit x in register 2+i, digit y in register 8+i,
    and decimal carry-in c on the carry flag, LD/ADD/DAA/XCH leaves the
    decimal sum digit in register 2+i and the decimal carry-out on the
    carry flag, touching no other register. *)
Lemma bcd_block_step : forall s i x y c,
  WF s -> i <= 5 ->
  rval s (2 + i) = x -> rval s (8 + i) = y ->
  x <= 9 -> y <= 9 ->
  cbit s = c -> c <= 1 ->
  let s4 := exec_program [LD (nib (2 + i)); ADD (nib (8 + i)); DAA;
                          XCH (nib (2 + i))] s in
  WF s4 /\
  rval s4 (2 + i) = (x + y + c) mod 10 /\
  cbit s4 = (x + y + c) / 10 /\
  (forall r', r' <> 2 + i -> get_reg s4 r' = get_reg s r').
Proof.
  intros s i x y c HWF Hi Hx Hy Hx9 Hy9 Hc Hc1.
  cbv zeta. cbn [exec_program].
  assert (Hlen : length (regs s) = 16) by (destruct_WF HWF; assumption).
  assert (Hv2 : wval (nib (2 + i)) = 2 + i) by (apply nib_val_small; lia).
  assert (Hv8 : wval (nib (8 + i)) = 8 + i) by (apply nib_val_small; lia).
  set (s1 := execute s (LD (nib (2 + i)))).
  assert (Ha1 : aval s1 = x).
  { unfold s1, aval. exec_simpl. rewrite Hv2. exact Hx. }
  assert (Hc1' : carry s1 = carry s) by reflexivity.
  assert (Hr1y : rval s1 (8 + i) = y) by exact Hy.
  set (s2 := execute s1 (ADD (nib (8 + i)))).
  assert (Ha2 : aval s2 = (x + y + c) mod 16).
  { unfold s2.
    destruct (add_computes_sum s1 (nib (8 + i))) as [HA _].
    rewrite HA. rewrite Hv8, Ha1, Hr1y.
    replace (cbit s1) with c by (rewrite <- Hc; reflexivity).
    reflexivity. }
  assert (Hcy2 : carry s2 = (16 <=? x + y + c)).
  { unfold s2.
    destruct (add_computes_sum s1 (nib (8 + i))) as [_ HC].
    rewrite HC. rewrite Hv8, Ha1, Hr1y.
    replace (cbit s1) with c by (rewrite <- Hc; reflexivity).
    reflexivity. }
  set (s3 := execute s2 DAA).
  assert (Hda : aval s3 = (x + y + c) mod 10 /\
                (if carry s3 then 1 else 0) = (x + y + c) / 10).
  { unfold s3. apply daa_decimal_correct; assumption. }
  destruct Hda as [Hda Hdc].
  assert (Hlen3 : length (regs s3) = 16) by exact Hlen.
  split; [| split; [| split]].
  - repeat apply execute_preserves_WF. exact HWF.
  - assert (Hxw := xch_reg_written s3 (nib (2 + i)) Hlen3).
    rewrite Hv2 in Hxw.
    unfold rval. rewrite Hxw.
    unfold aval in Hda. exact Hda.
  - unfold cbit.
    replace (carry (execute s3 (XCH (nib (2 + i))))) with (carry s3)
      by reflexivity.
    exact Hdc.
  - intros r' Hne.
    rewrite xch_reg_other by (rewrite Hv2; lia).
    reflexivity.
Qed.

(** The chained blocks compute the ripple adder over the register file. *)
Lemma bcd_blocks_correct : forall xs ys i s c,
  WF s ->
  i + length xs <= 6 ->
  length ys = length xs ->
  Forall (fun d => d <= 9) xs -> Forall (fun d => d <= 9) ys ->
  (forall j, j < length xs -> rval s (2 + i + j) = nth j xs 0) ->
  (forall j, j < length xs -> rval s (8 + i + j) = nth j ys 0) ->
  cbit s = c -> c <= 1 ->
  let s' := exec_program (bcd_blocks i (length xs)) s in
  WF s' /\
  (forall j, j < length xs ->
     rval s' (2 + i + j) = nth j (fst (bcd_sum xs ys c)) 0) /\
  cbit s' = snd (bcd_sum xs ys c) /\
  (forall r', (forall j, j < length xs -> r' <> 2 + i + j) ->
     get_reg s' r' = get_reg s r').
Proof.
  induction xs as [|x xs' IH]; intros ys i s c HWF Hbound Hlen Hxs Hys Hxr Hyr Hc Hc1.
  - cbv zeta. cbn [bcd_blocks length exec_program].
    split; [exact HWF|].
    split; [intros j Hj; lia|].
    split; [exact Hc|].
    intros r' _. reflexivity.
  - destruct ys as [|y ys']; [simpl in Hlen; discriminate|].
    pose proof (Forall_inv Hxs) as Hx9.
    pose proof (Forall_inv_tail Hxs) as Hxs'.
    pose proof (Forall_inv Hys) as Hy9.
    pose proof (Forall_inv_tail Hys) as Hys'.
    cbv beta in Hx9, Hy9.
    simpl in Hlen. injection Hlen as Hlen.
    cbv zeta. cbn [bcd_blocks length].
    rewrite exec_program_app.
    (* the head block *)
    assert (Hi5 : i <= 5) by (cbn [length] in Hbound; lia).
    assert (H0len : 0 < length (x :: xs')) by (cbn; lia).
    assert (Hx0 : rval s (2 + i) = x).
    { specialize (Hxr 0 H0len). rewrite Nat.add_0_r in Hxr. exact Hxr. }
    assert (Hy0 : rval s (8 + i) = y).
    { specialize (Hyr 0 H0len). rewrite Nat.add_0_r in Hyr. exact Hyr. }
    pose proof (bcd_block_step s i x y c HWF Hi5 Hx0 Hy0 Hx9 Hy9 Hc Hc1) as Hblk.
    cbv zeta in Hblk.
    destruct Hblk as (HWF4 & Hdig & Hcy4 & Hframe4).
    (* keep the block's result state abstract *)
    revert HWF4 Hdig Hcy4 Hframe4.
    generalize (exec_program [LD (nib (2 + i)); ADD (nib (8 + i)); DAA;
                              XCH (nib (2 + i))] s) as s4.
    intros s4 HWF4 Hdig Hcy4 Hframe4.
    assert (Hc' : (x + y + c) / 10 <= 1).
    { assert ((x + y + c) / 10 < 2);
        [apply Nat.Div0.div_lt_upper_bound; lia | lia]. }
    (* the remaining blocks via the induction hypothesis at S i *)
    assert (HSb : S i + length xs' <= 6) by (cbn [length] in Hbound; lia).
    pose proof (IH ys' (S i) s4 ((x + y + c) / 10) HWF4 HSb Hlen Hxs' Hys') as IH'.
    assert (Hxr' : forall j, j < length xs' ->
              rval s4 (2 + S i + j) = nth j xs' 0).
    { intros j Hj.
      unfold rval. rewrite Hframe4 by lia.
      replace (2 + S i + j) with (2 + i + S j) by lia.
      apply (Hxr (S j)). cbn. lia. }
    assert (Hyr' : forall j, j < length xs' ->
              rval s4 (8 + S i + j) = nth j ys' 0).
    { intros j Hj.
      unfold rval. rewrite Hframe4 by lia.
      replace (8 + S i + j) with (8 + i + S j) by lia.
      apply (Hyr (S j)). cbn. lia. }
    specialize (IH' Hxr' Hyr' Hcy4 Hc').
    cbv zeta in IH'.
    destruct IH' as (HWF' & Hdig' & Hcy' & Hframe').
    assert (Efst : fst (bcd_sum (x :: xs') (y :: ys') c)
                 = (x + y + c) mod 10 :: fst (bcd_sum xs' ys' ((x + y + c) / 10))).
    { cbn [bcd_sum].
      destruct (bcd_sum xs' ys' ((x + y + c) / 10)); reflexivity. }
    assert (Esnd : snd (bcd_sum (x :: xs') (y :: ys') c)
                 = snd (bcd_sum xs' ys' ((x + y + c) / 10))).
    { cbn [bcd_sum].
      destruct (bcd_sum xs' ys' ((x + y + c) / 10)); reflexivity. }
    rewrite Efst, Esnd.
    split; [exact HWF' | split; [| split]].
    + intros j Hj. destruct j as [|j].
      * rewrite Nat.add_0_r.
        unfold rval.
        rewrite Hframe' by (intros j' Hj'; lia).
        cbn [nth].
        unfold rval in Hdig.
        exact Hdig.
      * replace (2 + i + S j) with (2 + S i + j) by lia.
        cbn [nth].
        assert (Hj' : j < length xs') by (cbn [length] in Hj; lia).
        exact (Hdig' j Hj').
    + exact Hcy'.
    + intros r' Hr'.
      assert (Hr0 : r' <> 2 + i).
      { specialize (Hr' 0). rewrite Nat.add_0_r in Hr'. apply Hr'. cbn. lia. }
      rewrite Hframe'.
      * apply Hframe4. exact Hr0.
      * intros j Hj.
        replace (2 + S i + j) with (2 + i + S j) by lia.
        apply Hr'. cbn. lia.
Qed.

(** Headline: the generated n-digit program (n <= 6) computes decimal
    addition of the register-file digit strings, decimal carry included. *)
Theorem bcd_add_prog_correct : forall xs ys s,
  WF s ->
  length xs <= 6 ->
  length ys = length xs ->
  Forall (fun d => d <= 9) xs -> Forall (fun d => d <= 9) ys ->
  (forall j, j < length xs -> rval s (2 + j) = nth j xs 0) ->
  (forall j, j < length xs -> rval s (8 + j) = nth j ys 0) ->
  let s' := exec_program (bcd_add_prog (length xs)) s in
  WF s' /\
  (forall j, j < length xs ->
     rval s' (2 + j) = nth j (fst (bcd_sum xs ys 0)) 0) /\
  cbit s' = snd (bcd_sum xs ys 0).
Proof.
  intros xs ys s HWF Hn Hlen Hxs Hys Hxr Hyr.
  cbv zeta. unfold bcd_add_prog.
  change (exec_program (CLC :: bcd_blocks 0 (length xs)) s)
    with (exec_program (bcd_blocks 0 (length xs)) (execute s CLC)).
  set (s0 := execute s CLC).
  assert (HWF0 : WF s0) by (apply execute_preserves_WF; exact HWF).
  assert (Hc0 : cbit s0 = 0) by reflexivity.
  assert (Hxr0 : forall j, j < length xs -> rval s0 (2 + 0 + j) = nth j xs 0).
  { intros j Hj. replace (2 + 0 + j) with (2 + j) by lia. apply Hxr. exact Hj. }
  assert (Hyr0 : forall j, j < length xs -> rval s0 (8 + 0 + j) = nth j ys 0).
  { intros j Hj. replace (8 + 0 + j) with (8 + j) by lia. apply Hyr. exact Hj. }
  assert (Hb6 : 0 + length xs <= 6) by lia.
  assert (Hle1 : 0 <= 1) by lia.
  pose proof (bcd_blocks_correct xs ys 0 s0 0 HWF0 Hb6 Hlen Hxs Hys
                Hxr0 Hyr0 Hc0 Hle1) as H.
  cbv zeta in H.
  destruct H as (HWF' & Hdig & Hcy & _).
  split; [exact HWF' | split; [| exact Hcy]].
  intros j Hj.
  specialize (Hdig j Hj).
  replace (2 + j) with (2 + 0 + j) by lia.
  exact Hdig.
Qed.

(** Decimal reading of the machine result. *)
Corollary bcd_add_prog_value : forall xs ys,
  length ys = length xs ->
  Forall (fun d => d <= 9) xs -> Forall (fun d => d <= 9) ys ->
  dval (fst (bcd_sum xs ys 0)) + snd (bcd_sum xs ys 0) * 10 ^ length xs
  = dval xs + dval ys.
Proof.
  intros xs ys Hlen Hxs Hys.
  pose proof (bcd_sum_correct xs ys 0 Hlen Hxs Hys ltac:(lia)). lia.
Qed.

(* ===================================================================== *)
(*     A VERIFIED COMPILER, REFINED INTO A ROM IMAGE ON THE MACHINE      *)
(* ===================================================================== *)

(* Binary add/subtract expressions over constants and the low registers,
   compiled with a scratch-register discipline (operands stashed in
   registers 8..15), and statement sequences of register assignments.
   Refinement is carried all the way into hardware terms: compiled
   programs are assembled into a packed byte image, loaded into ROM, and
   proven to run correctly on the fetch-decode-execute machine via the
   small-step bridge. *)

(* ---------------- Source language ---------------- *)

Inductive Expr :=
  | EConst (n : nat)
  | EReg (r : nat)
  | EAdd (e1 e2 : Expr)
  | ESub (e1 e2 : Expr).

(** Source semantics: 4-bit modular arithmetic over a register environment. *)
Fixpoint eval (env : nat -> nat) (e : Expr) : nat :=
  match e with
  | EConst n => n mod 16
  | EReg r => env r
  | EAdd e1 e2 => (eval env e1 + eval env e2) mod 16
  | ESub e1 e2 => (eval env e1 + 16 - eval env e2) mod 16
  end.

(** Well-formed sources read only the low registers 0..7. *)
Fixpoint expr_wf (e : Expr) : Prop :=
  match e with
  | EConst n => n < 16
  | EReg r => r < 8
  | EAdd e1 e2 | ESub e1 e2 => expr_wf e1 /\ expr_wf e2
  end.

(** Scratch registers needed: one per held right operand. *)
Fixpoint need (e : Expr) : nat :=
  match e with
  | EConst _ | EReg _ => 0
  | EAdd e1 e2 | ESub e1 e2 => Nat.max (need e2) (S (need e1))
  end.

(** Compilation with scratch base t: evaluate the right operand, stash it at
    t, evaluate the left operand with scratch above t, then combine.  CLC
    pins the carry so ADD adds exactly and SUB subtracts without borrow (on
    real silicon the incoming carry is the borrow). *)
Fixpoint compile_expr (e : Expr) (t : nat) : list Instruction :=
  match e with
  | EConst n => [LDM (nib n)]
  | EReg r => [LD (nib r)]
  | EAdd e1 e2 =>
      compile_expr e2 t ++ [XCH (nib t)] ++ compile_expr e1 (S t)
        ++ [CLC; ADD (nib t)]
  | ESub e1 e2 =>
      compile_expr e2 t ++ [XCH (nib t)] ++ compile_expr e1 (S t)
        ++ [CLC; SUB (nib t)]
  end.

(* ---------------- Expression correctness ---------------- *)

Lemma eval_bound : forall e s,
  expr_wf e -> eval (fun q => rval s q) e < 16.
Proof.
  induction e; intros s Hwf; cbn [eval expr_wf] in *.
  - apply Nat.mod_upper_bound; lia.
  - apply rval_lt16.
  - apply Nat.mod_upper_bound; lia.
  - apply Nat.mod_upper_bound; lia.
Qed.

Lemma eval_ext : forall e env1 env2,
  expr_wf e -> (forall r, r < 8 -> env1 r = env2 r) ->
  eval env1 e = eval env2 e.
Proof.
  induction e; intros env1 env2 Hwf Hext; cbn [eval expr_wf] in *.
  - reflexivity.
  - apply Hext. exact Hwf.
  - destruct Hwf. rewrite (IHe1 env1 env2), (IHe2 env1 env2); auto.
  - destruct Hwf. rewrite (IHe1 env1 env2), (IHe2 env1 env2); auto.
Qed.

Lemma compile_expr_correct : forall e t s,
  WF s -> expr_wf e -> 8 <= t -> t + need e <= 16 ->
  WF (exec_program (compile_expr e t) s) /\
  aval (exec_program (compile_expr e t) s) = eval (fun q => rval s q) e /\
  (forall r, r < t ->
     get_reg (exec_program (compile_expr e t) s) r = get_reg s r).
Proof.
  induction e; intros t s HWF Hwf Ht Hneed.

  - (* EConst *)
    cbn [compile_expr exec_program]. cbn [expr_wf] in Hwf.
    split; [apply execute_preserves_WF; exact HWF |].
    split.
    + unfold aval. exec_simpl. apply nib_val.
    + intros r Hr. reflexivity.

  - (* EReg *)
    cbn [compile_expr exec_program]. cbn [expr_wf] in Hwf.
    split; [apply execute_preserves_WF; exact HWF |].
    split.
    + unfold aval. exec_simpl.
      rewrite nib_val_small by lia. reflexivity.
    + intros r' Hr'. reflexivity.

  - (* EAdd *)
    cbn [expr_wf] in Hwf. destruct Hwf as [Hwf1 Hwf2].
    cbn [need] in Hneed.
    assert (Ht15 : t < 16) by lia.
    assert (Hvt : wval (nib t) = t) by (apply nib_val_small; lia).
    cbn [compile_expr].
    rewrite !exec_program_app.
    assert (Hn2 : t + need e2 <= 16) by lia.
    assert (Hn1 : S t + need e1 <= 16) by lia.
    destruct (IHe2 t s HWF Hwf2 Ht Hn2) as (HWF1 & Hacc1 & Hfr1).
    set (env := fun r : nat => rval s r) in *.
    set (s1 := exec_program (compile_expr e2 t) s) in *.
    change (exec_program [XCH (nib t)] s1) with (execute s1 (XCH (nib t))).
    set (s2 := execute s1 (XCH (nib t))) in *.
    assert (HWF2s : WF s2) by (apply execute_preserves_WF; exact HWF1).
    assert (Hlen1 : length (regs s1) = 16) by (destruct_WF HWF1; assumption).
    assert (Hregt : rval s2 t = eval env e2).
    { assert (Hx := xch_reg_written s1 (nib t) Hlen1).
      rewrite Hvt in Hx.
      unfold rval, s2. rewrite Hx.
      unfold aval in Hacc1. exact Hacc1. }
    assert (Henv2 : forall q, q < 8 -> rval s2 q = env q).
    { intros q Hq. unfold rval, s2.
      rewrite xch_reg_other by (rewrite Hvt; lia).
      unfold env, rval. f_equal. apply Hfr1. lia. }
    assert (HtS : 8 <= S t) by lia.
    destruct (IHe1 (S t) s2 HWF2s Hwf1 HtS Hn1) as (HWF3 & Hacc3 & Hfr3).
    set (s3 := exec_program (compile_expr e1 (S t)) s2) in *.
    change (exec_program [CLC; ADD (nib t)] s3)
      with (execute (execute s3 CLC) (ADD (nib t))).
    assert (HWFc : WF (execute s3 CLC))
      by (apply execute_preserves_WF; exact HWF3).
    split; [apply execute_preserves_WF; exact HWFc |].
    assert (Hacc_final :
      aval (execute (execute s3 CLC) (ADD (nib t)))
      = (eval env e1 + eval env e2) mod 16).
    { destruct (add_computes_sum (execute s3 CLC) (nib t)) as [HA _].
      rewrite HA.
      replace (cbit (execute s3 CLC)) with 0 by reflexivity.
      replace (aval (execute s3 CLC)) with (aval s3) by reflexivity.
      replace (rval (execute s3 CLC) (wval (nib t))) with (rval s3 (wval (nib t)))
        by reflexivity.
      rewrite Hvt.
      rewrite Hacc3.
      rewrite (eval_ext e1 (fun q => rval s2 q) env Hwf1 Henv2).
      unfold rval at 1. rewrite Hfr3 by lia.
      fold (rval s2 t). rewrite Hregt.
      rewrite Nat.add_0_r. reflexivity. }
    split.
    + rewrite Hacc_final. cbn [eval]. reflexivity.
    + intros r Hr.
      replace (get_reg (execute (execute s3 CLC) (ADD (nib t))) r)
        with (get_reg s3 r) by reflexivity.
      rewrite Hfr3 by lia.
      unfold s2. rewrite xch_reg_other by (rewrite Hvt; lia).
      apply Hfr1. exact Hr.

  - (* ESub *)
    cbn [expr_wf] in Hwf. destruct Hwf as [Hwf1 Hwf2].
    cbn [need] in Hneed.
    assert (Ht15 : t < 16) by lia.
    assert (Hvt : wval (nib t) = t) by (apply nib_val_small; lia).
    cbn [compile_expr].
    rewrite !exec_program_app.
    assert (Hn2 : t + need e2 <= 16) by lia.
    assert (Hn1 : S t + need e1 <= 16) by lia.
    destruct (IHe2 t s HWF Hwf2 Ht Hn2) as (HWF1 & Hacc1 & Hfr1).
    set (env := fun r : nat => rval s r) in *.
    set (s1 := exec_program (compile_expr e2 t) s) in *.
    change (exec_program [XCH (nib t)] s1) with (execute s1 (XCH (nib t))).
    set (s2 := execute s1 (XCH (nib t))) in *.
    assert (HWF2s : WF s2) by (apply execute_preserves_WF; exact HWF1).
    assert (Hlen1 : length (regs s1) = 16) by (destruct_WF HWF1; assumption).
    assert (Hregt : rval s2 t = eval env e2).
    { assert (Hx := xch_reg_written s1 (nib t) Hlen1).
      rewrite Hvt in Hx.
      unfold rval, s2. rewrite Hx.
      unfold aval in Hacc1. exact Hacc1. }
    assert (Henv2 : forall q, q < 8 -> rval s2 q = env q).
    { intros q Hq. unfold rval, s2.
      rewrite xch_reg_other by (rewrite Hvt; lia).
      unfold env, rval. f_equal. apply Hfr1. lia. }
    assert (HtS : 8 <= S t) by lia.
    destruct (IHe1 (S t) s2 HWF2s Hwf1 HtS Hn1) as (HWF3 & Hacc3 & Hfr3).
    set (s3 := exec_program (compile_expr e1 (S t)) s2) in *.
    change (exec_program [CLC; SUB (nib t)] s3)
      with (execute (execute s3 CLC) (SUB (nib t))).
    assert (HWFc : WF (execute s3 CLC))
      by (apply execute_preserves_WF; exact HWF3).
    split; [apply execute_preserves_WF; exact HWFc |].
    assert (Hacc_final :
      aval (execute (execute s3 CLC) (SUB (nib t)))
      = (eval env e1 + 16 - eval env e2) mod 16).
    { destruct (sub_computes_difference (execute s3 CLC) (nib t)) as [HA _].
      rewrite HA.
      replace (cbit (execute s3 CLC)) with 0 by reflexivity.
      replace (aval (execute s3 CLC)) with (aval s3) by reflexivity.
      replace (rval (execute s3 CLC) (wval (nib t))) with (rval s3 (wval (nib t)))
        by reflexivity.
      rewrite Hvt.
      rewrite Hacc3.
      rewrite (eval_ext e1 (fun q => rval s2 q) env Hwf1 Henv2).
      unfold rval at 1. rewrite Hfr3 by lia.
      fold (rval s2 t). rewrite Hregt.
      rewrite Nat.sub_0_r. reflexivity. }
    split.
    + rewrite Hacc_final. cbn [eval]. reflexivity.
    + intros r Hr.
      replace (get_reg (execute (execute s3 CLC) (SUB (nib t))) r)
        with (get_reg s3 r) by reflexivity.
      rewrite Hfr3 by lia.
      unfold s2. rewrite xch_reg_other by (rewrite Hvt; lia).
      apply Hfr1. exact Hr.
Qed.

(* ---------------- Statements ---------------- *)

Inductive Stmt :=
  | SAssign (r : nat) (e : Expr)
  | SSeq (a b : Stmt).

Fixpoint stmt_wf (st : Stmt) : Prop :=
  match st with
  | SAssign r e => r < 8 /\ expr_wf e /\ need e <= 8
  | SSeq a b => stmt_wf a /\ stmt_wf b
  end.

Fixpoint compile_stmt (st : Stmt) : list Instruction :=
  match st with
  | SAssign r e => compile_expr e 8 ++ [XCH (nib r)]
  | SSeq a b => compile_stmt a ++ compile_stmt b
  end.

(** Source semantics of statements over register environments. *)
Fixpoint sem_stmt (env : nat -> nat) (st : Stmt) : nat -> nat :=
  match st with
  | SAssign r e => fun r' => if r' =? r then eval env e else env r'
  | SSeq a b => sem_stmt (sem_stmt env a) b
  end.

Lemma sem_stmt_ext : forall st env1 env2,
  stmt_wf st -> (forall r, r < 8 -> env1 r = env2 r) ->
  forall r, r < 8 -> sem_stmt env1 st r = sem_stmt env2 st r.
Proof.
  induction st as [r0 e | a IHa b IHb];
    intros env1 env2 Hwf Hext r Hr; cbn [sem_stmt stmt_wf] in *.
  - destruct Hwf as (Hr8 & Hewf & _).
    destruct (r =? r0).
    + apply eval_ext; assumption.
    + apply Hext. exact Hr.
  - destruct Hwf as [Hwa Hwb].
    apply IHb; [exact Hwb | | exact Hr].
    intros q Hq. apply IHa; assumption.
Qed.

Theorem compile_stmt_correct : forall st s,
  WF s -> stmt_wf st ->
  WF (exec_program (compile_stmt st) s) /\
  (forall r, r < 8 ->
     rval (exec_program (compile_stmt st) s) r
     = sem_stmt (fun q => rval s q) st r).
Proof.
  induction st as [r0 e | a IHa b IHb];
    intros s HWF Hwf; cbn [compile_stmt stmt_wf] in *.
  - destruct Hwf as (Hr8 & Hewf & Hneed8).
    rewrite exec_program_app.
    assert (H8 : 8 <= 8) by lia.
    assert (H16 : 8 + need e <= 16) by lia.
    destruct (compile_expr_correct e 8 s HWF Hewf H8 H16)
      as (HWF1 & Hacc1 & Hfr1).
    set (s1 := exec_program (compile_expr e 8) s) in *.
    change (exec_program [XCH (nib r0)] s1) with (execute s1 (XCH (nib r0))).
    assert (Hlen1 : length (regs s1) = 16) by (destruct_WF HWF1; assumption).
    assert (Hvr : wval (nib r0) = r0) by (apply nib_val_small; lia).
    split.
    + apply execute_preserves_WF. exact HWF1.
    + intros r Hr. cbn [sem_stmt].
      destruct (Nat.eq_dec r r0) as [->|Hne].
      * rewrite Nat.eqb_refl.
        assert (Hx := xch_reg_written s1 (nib r0) Hlen1).
        rewrite Hvr in Hx.
        unfold rval. rewrite Hx.
        unfold aval in Hacc1. exact Hacc1.
      * replace (r =? r0) with false
          by (symmetry; apply Nat.eqb_neq; exact Hne).
        unfold rval.
        rewrite xch_reg_other by (rewrite Hvr; lia).
        f_equal. apply Hfr1. lia.
  - destruct Hwf as [Hwa Hwb].
    rewrite exec_program_app.
    destruct (IHa s HWF Hwa) as (HWF1 & Hsem1).
    set (s1 := exec_program (compile_stmt a) s) in *.
    destruct (IHb s1 HWF1 Hwb) as (HWF2 & Hsem2).
    split; [exact HWF2|].
    intros r Hr. cbn [sem_stmt].
    rewrite Hsem2 by exact Hr.
    apply sem_stmt_ext; [exact Hwb | | exact Hr].
    intros q Hq. apply Hsem1. exact Hq.
Qed.

(* ---------------- Static facts about compiled code ---------------- *)

Lemma compile_expr_flat : forall e t,
  Forall (fun i => (is_jump i = false /\ i <> WPM) /\ instr_bytes i = 1)
         (compile_expr e t).
Proof.
  induction e; intros t; cbn [compile_expr].
  - repeat constructor; try reflexivity; discriminate.
  - repeat constructor; try reflexivity; discriminate.
  - rewrite !Forall_app.
    repeat split; [apply IHe2 | | apply IHe1 | ];
      repeat constructor; try reflexivity; discriminate.
  - rewrite !Forall_app.
    repeat split; [apply IHe2 | | apply IHe1 | ];
      repeat constructor; try reflexivity; discriminate.
Qed.

(** Compiled expressions never touch RAM or the address ring. *)
Lemma compile_expr_pure : forall e t,
  Forall (fun i => writes_ram i = false /\ writes_stack i = false)
         (compile_expr e t).
Proof.
  induction e; intros t; cbn [compile_expr].
  - repeat constructor.
  - repeat constructor.
  - rewrite !Forall_app.
    repeat split; [apply IHe2 | | apply IHe1 | ]; repeat constructor.
  - rewrite !Forall_app.
    repeat split; [apply IHe2 | | apply IHe1 | ]; repeat constructor.
Qed.

(** Every compiled instruction is well-formed (none takes a register
    pair, so no parity conditions arise). *)
Lemma compile_expr_instr_wf : forall e t,
  Forall instr_wf (compile_expr e t).
Proof.
  induction e; intros t; cbn [compile_expr].
  - repeat constructor.
  - repeat constructor.
  - rewrite !Forall_app. repeat split;
      [apply IHe2 | repeat constructor | apply IHe1 | repeat constructor].
  - rewrite !Forall_app. repeat split;
      [apply IHe2 | repeat constructor | apply IHe1 | repeat constructor].
Qed.

Lemma compile_stmt_flat : forall st,
  Forall (fun i => (is_jump i = false /\ i <> WPM) /\ instr_bytes i = 1)
         (compile_stmt st).
Proof.
  induction st as [r e | a IHa b IHb]; cbn [compile_stmt].
  - rewrite Forall_app. split.
    + apply compile_expr_flat.
    + repeat constructor; try reflexivity; discriminate.
  - rewrite Forall_app. split; assumption.
Qed.

Lemma compile_assign_pure : forall r e,
  Forall (fun i => writes_ram i = false /\ writes_stack i = false)
         (compile_stmt (SAssign r e)).
Proof.
  intros r e. cbn [compile_stmt].
  rewrite Forall_app. split; [apply compile_expr_pure | repeat constructor].
Qed.

Lemma compile_stmt_instr_wf : forall st,
  Forall instr_wf (compile_stmt st).
Proof.
  induction st as [r e | a IHa b IHb]; cbn [compile_stmt].
  - rewrite Forall_app. split.
    + apply compile_expr_instr_wf.
    + repeat constructor.
  - rewrite Forall_app. split; assumption.
Qed.

(* ---------------- Packed assembly into a ROM image ---------------- *)

(** Packed assembler: one byte for one-byte instructions, two otherwise. *)
Fixpoint assemble (prog : list Instruction) : list byte :=
  match prog with
  | [] => []
  | i :: rest =>
      let '(b1, b2) := encode i in
      (if instr_bytes i =? 1 then [b1] else [b1; b2]) ++ assemble rest
  end.

Lemma assemble_length_1byte : forall prog,
  Forall (fun i => instr_bytes i = 1) prog ->
  length (assemble prog) = length prog.
Proof.
  induction prog as [|i rest IH]; intros H; [reflexivity|].
  pose proof (Forall_inv H) as Hi.
  cbn [assemble].
  destruct (encode i) as [b1 b2].
  rewrite Hi. cbn [Nat.eqb app length].
  f_equal. apply IH. exact (Forall_inv_tail H).
Qed.

(** Packed one-byte code in ROM decodes as the instruction stream. *)
Lemma code_at_assembled_1byte : forall prog s base,
  Forall instr_wf prog ->
  Forall (fun i => instr_bytes i = 1) prog ->
  base + length prog <= 4096 ->
  (forall j, j < length prog ->
     fetch_byte s (base + j) = nth j (assemble prog) (byt 0)) ->
  code_at s base prog.
Proof.
  induction prog as [|i rest IH]; intros s base Hwf H1 Hb Hfetch.
  - exact I.
  - pose proof (Forall_inv Hwf) as Hwfi.
    pose proof (Forall_inv H1) as H1i.
    pose proof (Forall_inv_tail Hwf) as Hwf'.
    pose proof (Forall_inv_tail H1) as H1'.
    assert (Hass : assemble (i :: rest) = fst (encode i) :: assemble rest).
    { cbn [assemble]. destruct (encode i) as [b1 b2].
      rewrite H1i. reflexivity. }
    cbn [code_at].
    split.
    + assert (H0l : 0 < length (i :: rest)) by (cbn [length]; lia).
      pose proof (Hfetch 0 H0l) as Hf0.
      rewrite Nat.add_0_r in Hf0. rewrite Hass in Hf0. cbn [nth] in Hf0.
      rewrite Hf0.
      assert (Hdec : decode (fst (encode i)) (snd (encode i)) = i).
      { pose proof (decode_encode_id i Hwfi) as Hd.
        destruct (encode i) as [b1 b2]. exact Hd. }
      transitivity (decode (fst (encode i)) (snd (encode i))); [| exact Hdec].
      apply decode_1byte_ignores_b2.
      rewrite Hdec. exact H1i.
    + rewrite H1i.
      destruct rest as [|i2 rest'].
      * cbn [code_at]. exact I.
      * assert (Hb1 : base + 1 < 4096) by (cbn [length] in Hb; lia).
        rewrite (Nat.mod_small (base + 1) 4096) by exact Hb1.
        apply IH; try assumption.
        -- cbn [length] in *. lia.
        -- intros j Hj.
           assert (HSj : S j < length (i :: i2 :: rest'))
             by (cbn [length] in *; lia).
           pose proof (Hfetch (S j) HSj) as Hf.
           replace (base + 1 + j) with (base + S j) by lia.
           rewrite Hf. rewrite Hass. cbn [nth]. reflexivity.
Qed.

(* ---------------- ROM images and the machine ---------------- *)

Definition rom_of (bytes : list byte) : list byte :=
  bytes ++ repeat (byt 0) (4096 - length bytes).

Lemma rom_of_length : forall bytes,
  length bytes <= 4096 -> length (rom_of bytes) = 4096.
Proof.
  intros bytes H. unfold rom_of.
  rewrite length_app, repeat_length. lia.
Qed.

Lemma rom_of_nth : forall bytes j,
  j < length bytes -> nth j (rom_of bytes) (byt 0) = nth j bytes (byt 0).
Proof. intros bytes j H. unfold rom_of. apply app_nth1. exact H. Qed.

(** Power-on state with a given ROM image and register file. *)
Definition init_with (romv : list byte) (regsv : list nibble) : Intel4004State :=
  with_regs regsv (with_rom romv init_state).

Lemma init_with_WF : forall romv regsv,
  length regsv = 16 ->
  length romv = 4096 ->
  WF (init_with romv regsv).
Proof.
  intros romv regsv H1 H2.
  pose proof init_state_WF as H. destruct_WF H.
  unfold WF, init_with. exec_simpl.
  repeat split; assumption.
Qed.

(** Headline: assemble the compiled statement, place it at address 0 of
    ROM, power on, and run the fetch-decode-execute machine for exactly one
    step per instruction: the low registers finish holding the source
    semantics. *)
Theorem compiled_stmt_runs_on_machine : forall st regsv,
  stmt_wf st ->
  length (compile_stmt st) <= 4096 ->
  length regsv = 16 ->
  forall r, r < 8 ->
    rval (steps (length (compile_stmt st))
            (init_with (rom_of (assemble (compile_stmt st))) regsv)) r
    = sem_stmt
        (fun q => rval (init_with (rom_of (assemble (compile_stmt st))) regsv) q)
        st r.
Proof.
  intros st regsv Hwf Hlen4k HlenR r Hr.
  set (prog := compile_stmt st) in *.
  set (s0 := init_with (rom_of (assemble prog)) regsv) in *.
  pose proof (compile_stmt_flat st) as Hflat. fold prog in Hflat.
  pose proof (compile_stmt_instr_wf st) as Hwfp. fold prog in Hwfp.
  assert (H1b : Forall (fun i => instr_bytes i = 1) prog).
  { eapply Forall_impl; [|exact Hflat]. intros a [_ Hb]. exact Hb. }
  assert (Hsl : Forall (fun i => is_jump i = false /\ i <> WPM) prog).
  { eapply Forall_impl; [|exact Hflat]. intros a [Ha _]. exact Ha. }
  assert (HlenA : length (assemble prog) = length prog)
    by (apply assemble_length_1byte; exact H1b).
  assert (HWF0 : WF s0).
  { apply init_with_WF; [exact HlenR |].
    apply rom_of_length. lia. }
  assert (Hfetch0 : forall j, j < length prog ->
            fetch_byte s0 (0 + j) = nth j (assemble prog) (byt 0)).
  { intros j Hj.
    replace (0 + j) with j by lia.
    unfold fetch_byte.
    change (rom s0) with (rom_of (assemble prog)).
    apply rom_of_nth. lia. }
  assert (Hcode : code_at s0 0 prog)
    by (apply code_at_assembled_1byte;
        [exact Hwfp | exact H1b | lia | exact Hfetch0]).
  assert (Hsteps : steps (length prog) s0 = exec_program prog s0).
  { apply steps_tracks_exec_program; [exact Hsl |].
    replace (pcv s0) with 0 by reflexivity. exact Hcode. }
  rewrite Hsteps.
  destruct (compile_stmt_correct st s0 HWF0 Hwf) as [_ Hsem].
  fold prog in Hsem.
  apply Hsem. exact Hr.
Qed.

(** A concrete program through the whole chain: R0 := (9 + 8) - 3, machine
    result computed by the fetch-decode-execute machine over the assembled
    ROM image.  (9 + 8) mod 16 = 1, then (1 + 16 - 3) mod 16 = 14. *)
Example compiled_demo :
  rval
    (steps
       (length (compile_stmt (SAssign 0 (ESub (EAdd (EConst 9) (EConst 8)) (EConst 3)))))
       (init_with
          (rom_of (assemble (compile_stmt
             (SAssign 0 (ESub (EAdd (EConst 9) (EConst 8)) (EConst 3))))))
          (repeat (nib 0) 16))) 0 = 14.
Proof. vm_compute. reflexivity. Qed.


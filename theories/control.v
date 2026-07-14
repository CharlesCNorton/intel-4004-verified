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

(** Byte size of the compiled statement. *)
Fixpoint csize (st : CStmt) : nat :=
  match st with
  | CAssign r e => elen e + 1
  | CSeq a b => csize a + csize b
  | CIf e t g => elen e + 2 + csize t + 2 + csize g
  | CWhile e b => elen e + 2 + csize b + 2
  end.

(* Code generation, placed at a base address.  The whole image must live
   in page 0 (enforced by the correctness theorem's fit hypothesis), so a
   JCN target is its absolute low byte.
     CIf:    expr; JCN JZ ->else; then; JUN ->end; else
     CWhile: expr; JCN JZ ->end;  body; JUN ->head                       *)
Fixpoint cgen (st : CStmt) (base : nat) : list byte :=
  match st with
  | CAssign r e => assemble (compile_stmt (SAssign r e))
  | CSeq a b => cgen a base ++ cgen b (base + csize a)
  | CIf e t g =>
      let pe := base + elen e in
      let pt := pe + 2 in
      let pj := pt + csize t in
      let pg := pj + 2 in
      let pend := pg + csize g in
      assemble (compile_expr e 8)
        ++ [byt 20; byt pg]
        ++ cgen t pt
        ++ [byt (64 + pend / 256); byt (pend mod 256)]
        ++ cgen g pg
  | CWhile e b =>
      let pe := base + elen e in
      let pb := pe + 2 in
      let pj := pb + csize b in
      assemble (compile_expr e 8)
        ++ [byt 20; byt (pj + 2)]
        ++ cgen b pb
        ++ [byt (64 + base / 256); byt (base mod 256)]
  end.

(* ==================== Static facts about generated code ==================== *)

(** Generated code lengths follow csize. *)
Lemma cgen_length : forall st base, length (cgen st base) = csize st.
Proof.
  induction st as [r e | a IHa b IHb | e t IHt g IHg | e b IHb];
    intros base; cbn [cgen csize].
  - rewrite assemble_length_1byte.
    + cbn [compile_stmt]. rewrite length_app. cbn [length]. unfold elen. lia.
    + eapply Forall_impl; [|apply (compile_stmt_flat (SAssign r e))].
      intros i [_ Hb]. exact Hb.
  - rewrite length_app, IHa, IHb. reflexivity.
  - rewrite !length_app.
    rewrite assemble_length_1byte.
    + cbn [length]. rewrite IHt, IHg. unfold elen. lia.
    + eapply Forall_impl; [|apply (compile_expr_flat e 8)].
      intros i [_ Hb]. exact Hb.
  - rewrite !length_app.
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
  base + csize st <= 254 ->
  rom_holds s base (cgen st base) ->
  pcv s = base ->
  (forall r, r < 8 -> env r = rval s r) ->
  csem fuel st env = Some env' ->
  exists n,
    WF (steps n s) /\
    pcv (steps n s) = base + csize st /\
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
    assert (Hrom_b1 : rom_holds s1 (base + csize a) (cgen b (base + csize a)))
      by (apply (rom_holds_eq s s1); assumption).
    assert (Henv1 : forall r, r < 8 -> env1 r = rval s1 r)
      by (intros r Hr; symmetry; apply Hreg1; exact Hr).
    destruct (IH b env1 env' s1 (base + csize a) HWF1 Hwb ltac:(lia)
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
    cbn [csize] in Hfit.
    cbn [cgen] in Hrom. cbv zeta in Hrom.
    set (pe := base + elen e) in *.
    set (pt := pe + 2) in *.
    set (pj := pt + csize t) in *.
    set (pg := pj + 2) in *.
    set (pend := pg + csize g) in *.
    (* decompose the image *)
    pose proof (rom_holds_app_l _ _ _ _ Hrom) as Hrom_e.
    pose proof (rom_holds_app_r _ _ _ _ Hrom) as Hrom_rest.
    rewrite assemble_length_1byte in Hrom_rest
      by (eapply Forall_impl; [|apply (compile_expr_flat e 8)];
          intros i [_ Hb]; exact Hb).
    fold (elen e) in Hrom_rest. fold pe in Hrom_rest.
    pose proof (rom_holds_app_l _ _ _ _ Hrom_rest) as Hrom_jcn.
    pose proof (rom_holds_app_r _ _ _ _ Hrom_rest) as Hrom_rest2.
    cbn [length] in Hrom_rest2. fold pt in Hrom_rest2.
    pose proof (rom_holds_app_l _ _ _ _ Hrom_rest2) as Hrom_t.
    pose proof (rom_holds_app_r _ _ _ _ Hrom_rest2) as Hrom_rest3.
    rewrite cgen_length in Hrom_rest3. fold pj in Hrom_rest3.
    pose proof (rom_holds_app_l _ _ _ _ Hrom_rest3) as Hrom_jun.
    pose proof (rom_holds_app_r _ _ _ _ Hrom_rest3) as Hrom_g.
    cbn [length] in Hrom_g. fold pg in Hrom_g.
    (* run the expression block *)
    pose proof (run_expr_block e s base HWF Hpc He Hn
                  ltac:(unfold pe in *; lia) Hrom_e)
      as (HWF1 & Hpc1 & Hacc1 & Hreg1 & Hrom1 & Hstk1 & Hram1).
    set (s1 := steps (elen e) s) in *.
    assert (Hpc1' : pcv s1 = pe).
    { unfold pcv. rewrite Hpc1. rewrite adr_val.
      apply Nat.mod_small. unfold pe in *. lia. }
    assert (Hacc1' : aval s1 = eval env e).
    { rewrite Hacc1. apply eval_ext; [exact He |].
      intros q Hq. symmetry. apply Henv. exact Hq. }
    (* the JCN step *)
    assert (Hf1 : fetch_byte s1 (pcv s1) = byt 20).
    { specialize (Hrom_jcn 0 ltac:(cbn [length]; lia)).
      rewrite Nat.add_0_r in Hrom_jcn. cbn [nth] in Hrom_jcn.
      rewrite Hpc1'.
      unfold fetch_byte in *. rewrite Hrom1. exact Hrom_jcn. }
    assert (Hf2 : fetch_byte s1 ((pcv s1 + 1) mod 4096) = byt pg).
    { specialize (Hrom_jcn 1 ltac:(cbn [length]; lia)).
      cbn [nth] in Hrom_jcn.
      rewrite Hpc1'.
      rewrite (Nat.mod_small (pe + 1) 4096)
        by (unfold pend, pg, pj, pt, pe in *; lia).
      unfold fetch_byte in *. rewrite Hrom1. exact Hrom_jcn. }
    assert (Hstep1 : step s1 = execute s1 (JCN (nib 4) (byt pg))).
    { rewrite (step_at s1 (byt 20) (byt pg) Hf1 Hf2).
      rewrite decode_jcn_jz_bytes. reflexivity. }
    assert (HWF2 : WF (execute s1 (JCN (nib 4) (byt pg))))
      by (apply execute_preserves_WF; exact HWF1).
    set (s2 := execute s1 (JCN (nib 4) (byt pg))) in *.
    assert (Hregs2 : regs s2 = regs s1)
      by (apply execute_regs_frame; reflexivity).
    assert (Hrom2 : rom s2 = rom s1)
      by (apply execute_rom_frame; discriminate).
    assert (Hstk2 : stk1 s2 = stk1 s1 /\ stk2 s2 = stk2 s1 /\ stk3 s2 = stk3 s1)
      by (apply execute_stack_frame; reflexivity).
    assert (Hram2 : ram_sys s2 = ram_sys s1)
      by (apply execute_ram_frame; reflexivity).
    assert (Hreg2 : forall q, q < 8 -> rval s2 q = rval s q).
    { intros q Hq. unfold rval, get_reg. rewrite Hregs2.
      f_equal. apply (Hreg1 q Hq). }
    destruct (eval env e =? 0) eqn:Ez.
    + (* condition zero: branch to the else block *)
      apply Nat.eqb_eq in Ez.
      assert (Hpc2 : pcv s2 = pg).
      { unfold pcv, s2. rewrite exec_jcn_jz_taken.
        - rewrite byt_val_small
            by (unfold pend, pg, pj, pt, pe in *; lia).
          rewrite adr_val.
          apply Nat.mod_small. unfold pend, pg, pj, pt, pe in *. lia.
        - rewrite Hacc1'. exact Ez.
        - rewrite Hpc1'. unfold pend, pg, pj, pt, pe in *. lia. }
      assert (Hrom_g2 : rom_holds s2 pg (cgen g pg)).
      { apply (rom_holds_eq s s2); [| exact Hrom_g].
        rewrite Hrom2. exact Hrom1. }
      assert (Henv2 : forall q, q < 8 -> env q = rval s2 q).
      { intros q Hq. rewrite (Hreg2 q Hq). apply Henv. exact Hq. }
      destruct (IH g env env' s2 pg HWF2 Hwg
                  ltac:(unfold pend, pg, pj, pt, pe in *; lia)
                  Hrom_g2 Hpc2 Henv2 Hsem)
        as (n3 & HWF3 & Hpc3 & Hreg3 & Hrom3 & Hstk3 & Hram3).
      exists (elen e + (1 + n3)).
      rewrite steps_add. fold s1.
      replace (steps (1 + n3) s1) with (steps n3 (step s1))
        by (rewrite (steps_add 1 n3 s1); reflexivity).
      rewrite Hstep1. fold s2.
      split; [exact HWF3 |].
      split.
      { rewrite Hpc3. unfold pend, pg, pj, pt, pe. cbn [csize]. lia. }
      split; [exact Hreg3 |].
      split.
      { rewrite Hrom3. rewrite Hrom2. exact Hrom1. }
      destruct Hstk1 as (Hs11 & Hs12 & Hs13).
      destruct Hstk2 as (Hs21 & Hs22 & Hs23).
      destruct Hstk3 as (Hs31 & Hs32 & Hs33).
      split; [| rewrite Hram3; rewrite Hram2; exact Hram1].
      rewrite Hs31, Hs32, Hs33, Hs21, Hs22, Hs23. auto.
    + (* condition nonzero: fall through to the then block, then JUN past *)
      apply Nat.eqb_neq in Ez.
      assert (Hpc2 : pcv s2 = pt).
      { unfold pcv, s2.
        rewrite exec_jcn_jz_not_taken by (rewrite Hacc1'; exact Ez).
        rewrite adr_val. rewrite Hpc1'.
        unfold pt. apply Nat.mod_small.
        unfold pend, pg, pj, pt, pe in *. lia. }
      assert (Hrom_t2 : rom_holds s2 pt (cgen t pt)).
      { apply (rom_holds_eq s s2); [| exact Hrom_t].
        rewrite Hrom2. exact Hrom1. }
      assert (Henv2 : forall q, q < 8 -> env q = rval s2 q).
      { intros q Hq. rewrite (Hreg2 q Hq). apply Henv. exact Hq. }
      destruct (IH t env env' s2 pt HWF2 Hwt
                  ltac:(unfold pend, pg, pj, pt, pe in *; lia)
                  Hrom_t2 Hpc2 Henv2 Hsem)
        as (n3 & HWF3 & Hpc3 & Hreg3 & Hrom3 & Hstk3 & Hram3).
      set (s3 := steps n3 s2) in *.
      assert (Hpc3' : pcv s3 = pj) by (rewrite Hpc3; unfold pj; lia).
      assert (Hrom3' : rom s3 = rom s).
      { rewrite Hrom3. rewrite Hrom2. exact Hrom1. }
      (* the JUN step *)
      assert (Hg1 : fetch_byte s3 (pcv s3) = byt (64 + pend / 256)).
      { specialize (Hrom_jun 0 ltac:(cbn [length]; lia)).
        rewrite Nat.add_0_r in Hrom_jun. cbn [nth] in Hrom_jun.
        rewrite Hpc3'.
        unfold fetch_byte in *. rewrite Hrom3'. exact Hrom_jun. }
      assert (Hg2 : fetch_byte s3 ((pcv s3 + 1) mod 4096) = byt (pend mod 256)).
      { specialize (Hrom_jun 1 ltac:(cbn [length]; lia)).
        cbn [nth] in Hrom_jun.
        rewrite Hpc3'.
        rewrite (Nat.mod_small (pj + 1) 4096)
          by (unfold pend, pg, pj, pt, pe in *; lia).
        unfold fetch_byte in *. rewrite Hrom3'. exact Hrom_jun. }
      assert (Hpend : pend < 4096) by (unfold pend, pg, pj, pt, pe in *; lia).
      assert (Hstep3 : step s3 = execute s3 (JUN (adr pend))).
      { rewrite (step_at s3 _ _ Hg1 Hg2).
        replace (byt (64 + pend / 256))
          with (byt (64 + wval (adr pend) / 256))
          by (rewrite adr_val_small by exact Hpend; reflexivity).
        replace (byt (pend mod 256))
          with (byt (wval (adr pend) mod 256))
          by (rewrite adr_val_small by exact Hpend; reflexivity).
        rewrite decode_jun_bytes.
        reflexivity. }
      set (s4 := execute s3 (JUN (adr pend))).
      assert (HWF4 : WF s4)
        by (apply execute_preserves_WF; exact HWF3).
      exists (elen e + (1 + (n3 + 1))).
      rewrite steps_add. fold s1.
      replace (steps (1 + (n3 + 1)) s1) with (steps (n3 + 1) (step s1))
        by (rewrite (steps_add 1 (n3 + 1) s1); reflexivity).
      rewrite Hstep1. fold s2.
      rewrite steps_add. fold s3.
      replace (steps 1 s3) with (step s3) by reflexivity.
      rewrite Hstep3. fold s4.
      assert (Hregs4 : regs s4 = regs s3)
        by (apply execute_regs_frame; reflexivity).
      split; [exact HWF4 |].
      split.
      { unfold s4, pcv. rewrite pc_shape_jun.
        rewrite adr_val_small by exact Hpend.
        unfold pend, pg, pj, pt, pe. cbn [csize]. lia. }
      split.
      { intros q Hq. unfold rval, get_reg. rewrite Hregs4.
        apply (Hreg3 q Hq). }
      split.
      { unfold s4. rewrite (execute_rom_frame s3 (JUN (adr pend))) by discriminate.
        exact Hrom3'. }
      destruct Hstk1 as (Hs11 & Hs12 & Hs13).
      destruct Hstk2 as (Hs21 & Hs22 & Hs23).
      destruct Hstk3 as (Hs31 & Hs32 & Hs33).
      destruct (execute_stack_frame s3 (JUN (adr pend)) ltac:(reflexivity))
        as (Hs41 & Hs42 & Hs43).
      split; [| unfold s4;
                rewrite (execute_ram_frame s3 (JUN (adr pend)))
                  by reflexivity;
                rewrite Hram3; rewrite Hram2; exact Hram1].
      unfold s4.
      rewrite Hs41, Hs42, Hs43, Hs31, Hs32, Hs33, Hs21, Hs22, Hs23. auto.

  - (* CWhile *)
    rewrite csem_S_while in Hsem.
    cbn [cstmt_wf] in Hwf. destruct Hwf as (He & Hn & Hwb).
    cbn [csize] in Hfit.
    cbn [cgen] in Hrom. cbv zeta in Hrom.
    set (pe := base + elen e) in *.
    set (pb := pe + 2) in *.
    set (pj := pb + csize b) in *.
    pose proof (rom_holds_app_l _ _ _ _ Hrom) as Hrom_e.
    pose proof (rom_holds_app_r _ _ _ _ Hrom) as Hrom_rest.
    rewrite assemble_length_1byte in Hrom_rest
      by (eapply Forall_impl; [|apply (compile_expr_flat e 8)];
          intros i [_ Hb]; exact Hb).
    fold (elen e) in Hrom_rest. fold pe in Hrom_rest.
    pose proof (rom_holds_app_l _ _ _ _ Hrom_rest) as Hrom_jcn.
    pose proof (rom_holds_app_r _ _ _ _ Hrom_rest) as Hrom_rest2.
    cbn [length] in Hrom_rest2. fold pb in Hrom_rest2.
    pose proof (rom_holds_app_l _ _ _ _ Hrom_rest2) as Hrom_b.
    pose proof (rom_holds_app_r _ _ _ _ Hrom_rest2) as Hrom_jun.
    rewrite cgen_length in Hrom_jun. fold pj in Hrom_jun.
    (* run the expression block *)
    pose proof (run_expr_block e s base HWF Hpc He Hn
                  ltac:(unfold pe in *; lia) Hrom_e)
      as (HWF1 & Hpc1 & Hacc1 & Hreg1 & Hrom1 & Hstk1 & Hram1).
    set (s1 := steps (elen e) s) in *.
    assert (Hpc1' : pcv s1 = pe).
    { unfold pcv. rewrite Hpc1. rewrite adr_val.
      apply Nat.mod_small. unfold pe in *. lia. }
    assert (Hacc1' : aval s1 = eval env e).
    { rewrite Hacc1. apply eval_ext; [exact He |].
      intros q Hq. symmetry. apply Henv. exact Hq. }
    assert (Hf1 : fetch_byte s1 (pcv s1) = byt 20).
    { specialize (Hrom_jcn 0 ltac:(cbn [length]; lia)).
      rewrite Nat.add_0_r in Hrom_jcn. cbn [nth] in Hrom_jcn.
      rewrite Hpc1'.
      unfold fetch_byte in *. rewrite Hrom1. exact Hrom_jcn. }
    assert (Hf2 : fetch_byte s1 ((pcv s1 + 1) mod 4096) = byt (pj + 2)).
    { specialize (Hrom_jcn 1 ltac:(cbn [length]; lia)).
      cbn [nth] in Hrom_jcn.
      rewrite Hpc1'.
      rewrite (Nat.mod_small (pe + 1) 4096) by (unfold pj, pb, pe in *; lia).
      unfold fetch_byte in *. rewrite Hrom1. exact Hrom_jcn. }
    assert (Hstep1 : step s1 = execute s1 (JCN (nib 4) (byt (pj + 2)))).
    { rewrite (step_at s1 (byt 20) (byt (pj + 2)) Hf1 Hf2).
      rewrite decode_jcn_jz_bytes. reflexivity. }
    assert (HWF2 : WF (execute s1 (JCN (nib 4) (byt (pj + 2)))))
      by (apply execute_preserves_WF; exact HWF1).
    set (s2 := execute s1 (JCN (nib 4) (byt (pj + 2)))) in *.
    assert (Hregs2 : regs s2 = regs s1)
      by (apply execute_regs_frame; reflexivity).
    assert (Hrom2 : rom s2 = rom s1)
      by (apply execute_rom_frame; discriminate).
    assert (Hstk2 : stk1 s2 = stk1 s1 /\ stk2 s2 = stk2 s1 /\ stk3 s2 = stk3 s1)
      by (apply execute_stack_frame; reflexivity).
    assert (Hram2 : ram_sys s2 = ram_sys s1)
      by (apply execute_ram_frame; reflexivity).
    assert (Hreg2 : forall q, q < 8 -> rval s2 q = rval s q).
    { intros q Hq. unfold rval, get_reg. rewrite Hregs2.
      f_equal. apply (Hreg1 q Hq). }
    destruct (eval env e =? 0) eqn:Ez.
    + (* loop exits: branch past the body *)
      apply Nat.eqb_eq in Ez.
      injection Hsem as <-.
      assert (Hpc2 : pcv s2 = pj + 2).
      { unfold pcv, s2. rewrite exec_jcn_jz_taken.
        - rewrite byt_val_small by (unfold pj, pb, pe in *; lia).
          rewrite adr_val.
          apply Nat.mod_small. unfold pj, pb, pe in *. lia.
        - rewrite Hacc1'. exact Ez.
        - rewrite Hpc1'. unfold pj, pb, pe in *. lia. }
      exists (elen e + 1).
      rewrite steps_add. fold s1.
      replace (steps 1 s1) with (step s1) by reflexivity.
      rewrite Hstep1. fold s2.
      split; [exact HWF2 |].
      split.
      { rewrite Hpc2. unfold pj, pb, pe. cbn [csize]. lia. }
      split.
      { intros q Hq. rewrite (Hreg2 q Hq). symmetry. apply Henv. exact Hq. }
      split.
      { rewrite Hrom2. exact Hrom1. }
      destruct Hstk1 as (Hs11 & Hs12 & Hs13).
      destruct Hstk2 as (Hs21 & Hs22 & Hs23).
      split; [| rewrite Hram2; exact Hram1].
      rewrite Hs21, Hs22, Hs23. auto.
    + (* loop continues: body, jump back to the head, repeat *)
      apply Nat.eqb_neq in Ez.
      destruct (csem f b env) as [env1|] eqn:Eb; [| discriminate Hsem].
      assert (Hpc2 : pcv s2 = pb).
      { unfold pcv, s2.
        rewrite exec_jcn_jz_not_taken by (rewrite Hacc1'; exact Ez).
        rewrite adr_val. rewrite Hpc1'.
        unfold pb. apply Nat.mod_small.
        unfold pj, pb, pe in *. lia. }
      assert (Hrom_b2 : rom_holds s2 pb (cgen b pb)).
      { apply (rom_holds_eq s s2); [| exact Hrom_b].
        rewrite Hrom2. exact Hrom1. }
      assert (Henv2 : forall q, q < 8 -> env q = rval s2 q).
      { intros q Hq. rewrite (Hreg2 q Hq). apply Henv. exact Hq. }
      destruct (IH b env env1 s2 pb HWF2 Hwb
                  ltac:(unfold pj, pb, pe in *; lia)
                  Hrom_b2 Hpc2 Henv2 Eb)
        as (n3 & HWF3 & Hpc3 & Hreg3 & Hrom3 & Hstk3 & Hram3).
      set (s3 := steps n3 s2) in *.
      assert (Hpc3' : pcv s3 = pj) by (rewrite Hpc3; unfold pj; lia).
      assert (Hrom3' : rom s3 = rom s).
      { rewrite Hrom3. rewrite Hrom2. exact Hrom1. }
      assert (Hbase : base < 4096) by lia.
      assert (Hg1 : fetch_byte s3 (pcv s3) = byt (64 + base / 256)).
      { specialize (Hrom_jun 0 ltac:(cbn [length]; lia)).
        rewrite Nat.add_0_r in Hrom_jun. cbn [nth] in Hrom_jun.
        rewrite Hpc3'.
        unfold fetch_byte in *. rewrite Hrom3'. exact Hrom_jun. }
      assert (Hg2 : fetch_byte s3 ((pcv s3 + 1) mod 4096) = byt (base mod 256)).
      { specialize (Hrom_jun 1 ltac:(cbn [length]; lia)).
        cbn [nth] in Hrom_jun.
        rewrite Hpc3'.
        rewrite (Nat.mod_small (pj + 1) 4096)
          by (unfold pj, pb, pe in *; lia).
        unfold fetch_byte in *. rewrite Hrom3'. exact Hrom_jun. }
      assert (Hstep3 : step s3 = execute s3 (JUN (adr base))).
      { rewrite (step_at s3 _ _ Hg1 Hg2).
        replace (byt (64 + base / 256))
          with (byt (64 + wval (adr base) / 256))
          by (rewrite adr_val_small by exact Hbase; reflexivity).
        replace (byt (base mod 256))
          with (byt (wval (adr base) mod 256))
          by (rewrite adr_val_small by exact Hbase; reflexivity).
        rewrite decode_jun_bytes.
        reflexivity. }
      set (s4 := execute s3 (JUN (adr base))) in *.
      assert (HWF4 : WF s4)
        by (apply execute_preserves_WF; exact HWF3).
      assert (Hregs4 : regs s4 = regs s3)
        by (apply execute_regs_frame; reflexivity).
      assert (Hpc4 : pcv s4 = base).
      { unfold pcv, s4. rewrite pc_shape_jun.
        apply adr_val_small. exact Hbase. }
      assert (Hrom4 : rom s4 = rom s).
      { unfold s4. rewrite (execute_rom_frame s3 (JUN (adr base))) by discriminate.
        exact Hrom3'. }
      assert (Hrom_w4 : rom_holds s4 base (cgen (CWhile e b) base)).
      { apply (rom_holds_eq s s4); [exact Hrom4 |].
        cbn [cgen]. cbv zeta. fold (elen e). fold pe pb pj. exact Hrom. }
      assert (Henv4 : forall q, q < 8 -> env1 q = rval s4 q).
      { intros q Hq. unfold rval, get_reg. rewrite Hregs4.
        symmetry. apply (Hreg3 q Hq). }
      destruct (IH (CWhile e b) env1 env' s4 base HWF4
                  ltac:(cbn [cstmt_wf]; auto)
                  ltac:(cbn [csize]; unfold pj, pb, pe in *; lia)
                  Hrom_w4 Hpc4 Henv4 Hsem)
        as (n5 & HWF5 & Hpc5 & Hreg5 & Hrom5 & Hstk5 & Hram5).
      exists (elen e + (1 + (n3 + (1 + n5)))).
      rewrite steps_add. fold s1.
      replace (steps (1 + (n3 + (1 + n5))) s1)
        with (steps (n3 + (1 + n5)) (step s1))
        by (rewrite (steps_add 1 (n3 + (1 + n5)) s1); reflexivity).
      rewrite Hstep1. fold s2.
      rewrite steps_add. fold s3.
      replace (steps (1 + n5) s3) with (steps n5 (step s3))
        by (rewrite (steps_add 1 n5 s3); reflexivity).
      rewrite Hstep3. fold s4.
      split; [exact HWF5 |].
      split; [rewrite Hpc5; cbn [csize]; reflexivity |].
      split; [exact Hreg5 |].
      split; [rewrite Hrom5; exact Hrom4 |].
      destruct Hstk1 as (Hs11 & Hs12 & Hs13).
      destruct Hstk2 as (Hs21 & Hs22 & Hs23).
      destruct Hstk3 as (Hs31 & Hs32 & Hs33).
      destruct Hstk5 as (Hs51 & Hs52 & Hs53).
      destruct (execute_stack_frame s3 (JUN (adr base)) ltac:(reflexivity))
        as (Hs41 & Hs42 & Hs43).
      split;
        [| rewrite Hram5; unfold s4;
           rewrite (execute_ram_frame s3 (JUN (adr base))) by reflexivity;
           rewrite Hram3; rewrite Hram2; exact Hram1].
      rewrite Hs51, Hs52, Hs53. unfold s4.
      rewrite Hs41, Hs42, Hs43, Hs31, Hs32, Hs33, Hs21, Hs22, Hs23. auto.
Qed.

(* ==================== End-to-end: power-on to result ==================== *)

(** Headline: place the generated bytes at address 0 of a ROM image, power
    on, and run the fetch-decode-execute machine: whenever the source
    semantics terminates, the machine reaches the block exit with the final
    environment in the low registers. *)
Theorem compiled_cstmt_runs_on_machine : forall fuel st env' regsv,
  cstmt_wf st ->
  csize st <= 254 ->
  length regsv = 16 ->
  csem fuel st (fun r => rval (init_with (rom_of (cgen st 0)) regsv) r)
    = Some env' ->
  exists n,
    pcv (steps n (init_with (rom_of (cgen st 0)) regsv)) = csize st /\
    forall r, r < 8 ->
      rval (steps n (init_with (rom_of (cgen st 0)) regsv)) r = env' r.
Proof.
  intros fuel st env' regsv Hwf Hfit HlenR Hsem.
  set (s0 := init_with (rom_of (cgen st 0)) regsv).
  assert (Hlen : length (cgen st 0) = csize st) by apply cgen_length.
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
   Layout at base 0 (13 bytes, page 0):
     0: LDM 3          (0xD3)
     1: XCH 0          (0xB0)
     2: LD 0           (0xA0)   <- loop head
     3: JCN JZ 13      (0x14 0x0D)
     5: LDM 1          (0xD1)
     6: XCH 8          (0xB8)
     7: LD 0           (0xA0)
     8: CLC            (0xF1)
     9: SUB 8          (0x98)
    10: XCH 0          (0xB0)
    11: JUN 2          (0x40 0x02)
    13:                          <- exit                                  *)
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
    31 steps after power-on, R0 holds zero and control sits at the exit. *)
Example cwhile_demo_machine :
  rval (steps 31 (init_with (rom_of (cgen demo_prog 0)) (repeat (nib 0) 16))) 0 = 0
  /\ pcv (steps 31 (init_with (rom_of (cgen demo_prog 0)) (repeat (nib 0) 16))) = 13.
Proof. split; vm_compute; reflexivity. Qed.

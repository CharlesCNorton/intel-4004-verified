(*******************************************************************************)
(*                                                                             *)
(*        Intel 4004 Microprocessor: Formal Verification in Coq                *)
(*                                                                             *)
(*    Complete formalization of the world's first commercial microprocessor.  *)
(*    All 46 instructions modeled with proven preservation of well-formedness.*)
(*    Includes MCS-4 RAM/ROM I/O system, Hoare logic layer, and program       *)
(*    verification infrastructure.                                            *)
(*                                                                             *)
(*    On that cold January night of 1971, the world's first                   *)
(*     microprocessor was born!                                               *)
(*    — Federico Faggin, Silicon (2021)                                        *)
(*                                                                             *)
(*    Author: Charles Norton                                                   *)
(*    Date: October 2025; revised July 2026                                    *)
(*                                                                             *)
(*******************************************************************************)

(* Behavioral reference: Intel MCS-4 Assembly Language Programming Manual (1973) and 4004 data sheet. *)

(* ======================= Imports and Setup ========================== *)

From Stdlib Require Import List Arith PeanoNat Bool NArith Lia Eqdep_dec.
Import ListNotations.

(* ===================== Fixed-width machine words ===================== *)

(* The machine's quantities are dependent fixed-width words: a w-bit word is
   a natural number packaged with a proof that it is below 2^w.  Bounds hold
   by construction, so the well-formedness invariant carries no value bounds,
   only structural facts (list lengths).  The bound is a boolean equation, so
   word equality reduces to value equality without axioms (UIP on bool), and
   extraction erases the proof: a word extracts to a bare integer. *)

Definition word (w : nat) : Set := { n : nat | (n <? 2 ^ w) = true }.

(** The numeric value carried by a word. *)
Definition wval {w : nat} (x : word w) : nat := proj1_sig x.

(** 2^w is positive for every width. *)
Lemma pow2_pos : forall w, 0 < 2 ^ w.
Proof. intro w. induction w; simpl; lia. Qed.

(** Every word is below its width bound. *)
Lemma wbound : forall w (x : word w), wval x < 2 ^ w.
Proof. intros w [v h]. cbn. apply Nat.ltb_lt. exact h. Qed.

(** Truncating constructor: any natural number, reduced mod 2^w. *)
Lemma mkw_ok : forall w n, (n mod 2 ^ w <? 2 ^ w) = true.
Proof.
  intros w n. apply Nat.ltb_lt. apply Nat.mod_upper_bound.
  pose proof (pow2_pos w). lia.
Qed.

(** Canonicalize a boolean-equation proof: on a computed-true boolean this
    reduces to eq_refl, so words built from closed values carry literally
    identical proofs and full-state equalities are decided by vm_compute. *)
Definition bcanon {b : bool} (p : b = true) : b = true :=
  match b as b0 return b0 = true -> b0 = true with
  | true => fun _ => eq_refl
  | false => fun q => q
  end p.

Definition mkw {w : nat} (n : nat) : word w :=
  exist _ (n mod 2 ^ w) (bcanon (mkw_ok w n)).

(** Words with equal values are equal: the bound proof is a boolean equation,
    unique by decidability of bool (no axioms). *)
Lemma word_eq : forall w (x y : word w), wval x = wval y -> x = y.
Proof.
  intros w [xv xh] [yv yh]. cbn. intro E. subst yv.
  assert (Hp : xh = yh) by (apply UIP_dec; apply Bool.bool_dec).
  subst yh. reflexivity.
Qed.

(** The value of a truncated word. *)
Lemma wval_mkw : forall w n, wval (@mkw w n) = n mod 2 ^ w.
Proof. reflexivity. Qed.

(** Truncation is the identity below the bound. *)
Lemma wval_mkw_small : forall w n, n < 2 ^ w -> wval (@mkw w n) = n.
Proof. intros w n H. cbn. apply Nat.mod_small. exact H. Qed.

(** Rebuilding a word from its value is the identity. *)
Lemma mkw_wval : forall w (x : word w), mkw (wval x) = x.
Proof.
  intros w x. apply word_eq. apply wval_mkw_small. apply wbound.
Qed.

(* ---- The machine's widths ---- *)

Definition nibble := word 4.   (* 4-bit data:      0..15   *)
Definition byte   := word 8.   (* 8-bit ROM datum: 0..255  *)
Definition addr12 := word 12.  (* 12-bit address:  0..4095 *)
Definition word2  := word 2.   (* 2-bit index:     0..3    *)
Definition word3  := word 3.   (* 3-bit CM code:   0..7    *)

Definition nib (n : nat) : nibble := mkw n.
Definition byt (n : nat) : byte   := mkw n.
Definition adr (n : nat) : addr12 := mkw n.
Definition w2  (n : nat) : word2  := mkw n.
Definition w3  (n : nat) : word3  := mkw n.

(** Width bounds in decimal form. *)
Lemma nib_lt16 : forall x : nibble, wval x < 16.
Proof. intro x. exact (wbound 4 x). Qed.

Lemma byte_lt256 : forall x : byte, wval x < 256.
Proof. intro x. exact (wbound 8 x). Qed.

Lemma addr12_lt4096 : forall x : addr12, wval x < 4096.
Proof. intro x. exact (wbound 12 x). Qed.

Lemma w2_lt4 : forall x : word2, wval x < 4.
Proof. intro x. exact (wbound 2 x). Qed.

Lemma w3_lt8 : forall x : word3, wval x < 8.
Proof. intro x. exact (wbound 3 x). Qed.

(** Constructor values in decimal form. *)
Lemma nib_val : forall n, wval (nib n) = n mod 16.
Proof. reflexivity. Qed.

Lemma byt_val : forall n, wval (byt n) = n mod 256.
Proof. reflexivity. Qed.

Lemma adr_val : forall n, wval (adr n) = n mod 4096.
Proof. reflexivity. Qed.

Lemma w2_val : forall n, wval (w2 n) = n mod 4.
Proof. reflexivity. Qed.

Lemma w3_val : forall n, wval (w3 n) = n mod 8.
Proof. reflexivity. Qed.

Lemma nib_val_small : forall n, n < 16 -> wval (nib n) = n.
Proof. intros n H. apply (wval_mkw_small 4 n H). Qed.

Lemma byt_val_small : forall n, n < 256 -> wval (byt n) = n.
Proof. intros n H. apply (wval_mkw_small 8 n H). Qed.

Lemma adr_val_small : forall n, n < 4096 -> wval (adr n) = n.
Proof. intros n H. apply (wval_mkw_small 12 n H). Qed.

Lemma w2_val_small : forall n, n < 4 -> wval (w2 n) = n.
Proof. intros n H. apply (wval_mkw_small 2 n H). Qed.

Lemma w3_val_small : forall n, n < 8 -> wval (w3 n) = n.
Proof. intros n H. apply (wval_mkw_small 3 n H). Qed.

(** Word equality specialized to each width (value determines the word). *)
Lemma nib_eq : forall x y : nibble, wval x = wval y -> x = y.
Proof. intros x y. apply (word_eq 4). Qed.

Lemma byte_eq : forall x y : byte, wval x = wval y -> x = y.
Proof. intros x y. apply (word_eq 8). Qed.

Lemma addr12_eq : forall x y : addr12, wval x = wval y -> x = y.
Proof. intros x y. apply (word_eq 12). Qed.

(** Rebuilding a word of each width from its own value. *)
Lemma nib_wval : forall r : nibble, nib (wval r) = r.
Proof. intro r. apply (mkw_wval 4 r). Qed.

Lemma byt_wval : forall b : byte, byt (wval b) = b.
Proof. intro b. apply (mkw_wval 8 b). Qed.

Lemma adr_wval : forall a : addr12, adr (wval a) = a.
Proof. intro a. apply (mkw_wval 12 a). Qed.

(* ==================== Foundational Arithmetic Lemmas ================= *)

(** Modular bounds for standard bit widths. *)
Lemma mod16_bound : forall n, n mod 16 < 16.
Proof. intro n. apply Nat.mod_upper_bound. lia. Qed.

Lemma mod256_bound : forall n, n mod 256 < 256.
Proof. intro n. apply Nat.mod_upper_bound. lia. Qed.

Lemma mod4096_bound : forall n, n mod 4096 < 4096.
Proof. intro n. apply Nat.mod_upper_bound. lia. Qed.

Lemma mod4_bound : forall n, n mod 4 < 4.
Proof. intro n. apply Nat.mod_upper_bound. lia. Qed.

(** Division bounds for byte and address decomposition. *)
Lemma div16_byte_bound : forall n, n < 256 -> n / 16 < 16.
Proof. intros n Hn. apply Nat.Div0.div_lt_upper_bound. exact Hn. Qed.

Lemma div256_addr_bound : forall n, n < 4096 -> n / 256 < 16.
Proof. intros n Hn. apply Nat.Div0.div_lt_upper_bound. exact Hn. Qed.

(** Small value mod identities. *)
Lemma mod_small_16 : forall n, n < 16 -> n mod 16 = n.
Proof. intros n Hn. apply Nat.mod_small. exact Hn. Qed.

Lemma mod_small_256 : forall n, n < 256 -> n mod 256 = n.
Proof. intros n Hn. apply Nat.mod_small. exact Hn. Qed.

Lemma mod_small_4096 : forall n, n < 4096 -> n mod 4096 = n.
Proof. intros n Hn. apply Nat.mod_small. exact Hn. Qed.

(** Quotient and remainder of a 16-aligned offset. *)
Lemma div16_off : forall k d, d < 16 -> (k * 16 + d) / 16 = k.
Proof.
  intros k d Hd. rewrite Nat.div_add_l by lia.
  rewrite Nat.div_small by lia. lia.
Qed.

Lemma mod16_off : forall k d, d < 16 -> (k * 16 + d) mod 16 = d.
Proof.
  intros k d Hd. rewrite Nat.add_comm. rewrite Nat.Div0.mod_add.
  apply Nat.mod_small. exact Hd.
Qed.

(** Division-modulo identity for base 256. *)
Lemma divmod256 : forall a, a = 256 * (a / 256) + a mod 256.
Proof. intro a. apply Nat.div_mod. lia. Qed.

(** Parity helpers for register-pair encodings. *)
Lemma mod2_cases : forall n, n mod 2 = 0 \/ n mod 2 = 1.
Proof. intro n. pose proof (Nat.mod_upper_bound n 2). lia. Qed.

Lemma even_sub_mod : forall n, n mod 2 = 0 -> n - n mod 2 = n.
Proof. intros n H. rewrite H. lia. Qed.

Lemma odd_sub_mod : forall n, n mod 2 = 1 -> n - n mod 2 = n - 1.
Proof. intros n H. rewrite H. reflexivity. Qed.

(** The pair base index n - n mod 2 is always even. *)
Lemma pair_base_even : forall n, (n - n mod 2) mod 2 = 0.
Proof.
  intro n.
  pose proof (Nat.div_mod n 2 ltac:(lia)) as Hdm.
  assert (Hb : n - n mod 2 = 2 * (n / 2)) by lia.
  rewrite Hb. rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
Qed.

(** The successor of an even number is odd. *)
Lemma succ_even_odd : forall n, n mod 2 = 0 -> (n + 1) mod 2 = 1.
Proof.
  intros n H. rewrite Nat.Div0.add_mod. rewrite H. reflexivity.
Qed.

(** Nested modulo simplification for mod 16 then mod 2. *)
Lemma mod_16_mod_2_eq : forall n, (n mod 16) mod 2 = n mod 2.
Proof.
  intro n.
  pose proof (Nat.div_mod n 16 ltac:(lia)) as Hk.
  assert (H : n = 16 * (n / 16) + n mod 16) by exact Hk.
  rewrite H at 2.
  rewrite Nat.Div0.add_mod.
  assert (H16 : 16 * (n / 16) mod 2 = 0).
  { replace (16 * (n / 16)) with ((8 * (n / 16)) * 2) by lia.
    apply Nat.Div0.mod_mul. }
  rewrite H16. rewrite Nat.add_0_l. symmetry. apply Nat.Div0.mod_mod.
Qed.

(* ========================= List helpers ============================= *)

(** Updates list element at index n with x. Returns unchanged list if n >= length. *)
Definition update_nth {A} (n : nat) (x : A) (l : list A) : list A :=
  if n <? length l
  then firstn n l ++ x :: skipn (S n) l
  else l.

(** Proves update_nth preserves list length regardless of index validity. *)
Lemma update_nth_length : forall A (l : list A) n x,
  length (update_nth n x l) = length l.
Proof.
  intros A l n x.
  unfold update_nth.
  destruct (n <? length l) eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E.
  rewrite length_app. cbn [length].
  rewrite firstn_length_le by lia.
  rewrite length_skipn. lia.
Qed.

(** Proves Forall P is preserved when taking first n elements of list. *)
Lemma Forall_firstn : forall A (P:A->Prop) n (l:list A),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l H. revert n.
  induction H; intro n.
  - simpl. destruct n; constructor.
  - destruct n; simpl.
    + constructor.
    + constructor; auto.
Qed.

(** Proves Forall P is preserved when skipping first n elements of list. *)
Lemma Forall_skipn : forall A (P:A->Prop) n (l:list A),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n l H. revert n.
  induction H; intro n.
  - simpl. destruct n; constructor.
  - destruct n; simpl.
    + constructor; auto.
    + auto.
Qed.

(** Proves Forall P is preserved by update_nth when replacement element satisfies P. *)
Lemma Forall_update_nth : forall A (P:A->Prop) n x (l:list A),
  Forall P l -> P x -> Forall P (update_nth n x l).
Proof.
  intros A P n x l Hall Hx. unfold update_nth.
  destruct (n <? length l) eqn:En.
  - apply Forall_app; split.
    + apply Forall_firstn; assumption.
    + constructor.
      * assumption.
      * apply Forall_skipn; assumption.
  - assumption.
Qed.

(** Proves nth of update_nth at a different index is unchanged. *)
Lemma nth_update_nth_neq : forall A (l : list A) n m x d,
  n <> m ->
  nth n (update_nth m x l) d = nth n l d.
Proof.
  intros A l n m x d Hneq.
  unfold update_nth.
  destruct (m <? length l) eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E.
  generalize dependent n.
  generalize dependent m.
  induction l as [|a l' IH]; intros.
  - simpl in E. lia.
  - destruct m, n; simpl; try reflexivity; try lia.
    rewrite IH.
    + reflexivity.
    + simpl in E. lia.
    + lia.
Qed.

(** Proves nth of update_nth at the updated index equals the new element. *)
Lemma nth_update_nth_eq : forall A (l : list A) n x d,
  n < length l ->
  nth n (update_nth n x l) d = x.
Proof.
  intros A l n x d Hn.
  unfold update_nth.
  assert (Hlt: n <? length l = true) by (apply Nat.ltb_lt; exact Hn).
  rewrite Hlt.
  rewrite app_nth2.
  - rewrite firstn_length_le by lia.
    replace (n - n) with 0 by lia.
    simpl. reflexivity.
  - rewrite firstn_length_le by lia. lia.
Qed.

(** update_nth past the end of the list is the identity. *)
Lemma update_nth_out_of_bounds : forall A (l : list A) n x,
  n >= length l -> update_nth n x l = l.
Proof.
  intros A l n x Hn.
  unfold update_nth.
  assert (n <? length l = false) by (apply Nat.ltb_ge; exact Hn).
  rewrite H. reflexivity.
Qed.

(** Proves nth of list satisfying Forall bound also satisfies bound (with default). *)
Lemma nth_Forall_lt : forall (l:list nat) d n k,
  Forall (fun x => x < k) l -> d < k -> nth n l d < k.
Proof.
  intros l d n k Hall Hd. revert n.
  induction Hall; intros [|n]; simpl; auto.
Qed.

(** Proves Forall P holds for repeat x n when P x holds. *)
Lemma Forall_repeat : forall A (P : A -> Prop) x n, P x -> Forall P (repeat x n).
Proof.
  intros A P x n H. induction n; simpl; constructor; auto.
Qed.

(* ======================== 4002 RAM structure ======================== *)

(** 4002 RAM register: 16 main characters + 4 status characters, each a nibble
    by construction. *)
Record RAMReg := mkRAMReg {
  reg_main   : list nibble;  (* 16 main characters *)
  reg_status : list nibble   (* 4 status characters S0..S3 *)
}.

(** 4002 RAM chip: 4 registers + 4-bit output port. *)
Record RAMChip := mkRAMChip {
  chip_regs  : list RAMReg;  (* 4 registers *)
  chip_port  : nibble        (* 4-bit output port *)
}.

(** 4002 RAM bank: 4 chips. *)
Record RAMBank := mkRAMBank {
  bank_chips : list RAMChip  (* 4 chips per bank *)
}.

(** RAM address selection latched by SRC.  All indices bounded by type. *)
Record RAMSel := mkRAMSel {
  sel_chip : word2;   (* 0..3 *)
  sel_reg  : word2;   (* 0..3 *)
  sel_char : nibble   (* 0..15 *)
}.

(* ==================== The 4008/4009 programmer latch ================= *)

(** Hardware writes program memory in 4-bit halves: an external 4008/4009
    (or 4289) latch pair assembles two successive WPM transfers into one
    byte, which is why the MCS-4 manual requires an even number of WPM
    instructions.  The staging latch is part of the machine state; each
    armed WPM feeds the accumulator's nibble, high half first. *)
Record ProgLatch := mkProgLatch {
  pl_expect_low : bool;   (* false: the next transfer is the high half *)
  pl_hi         : nibble  (* the staged high half *)
}.

Definition latch_init : ProgLatch := mkProgLatch false (nib 0).

(* ============================ State ================================= *)

(** Complete Intel 4004 + MCS-4 system state.

    The program counter and three-level subroutine stack are physically one
    ring of four 12-bit dynamic registers with a 2-bit pointer selecting the
    row that acts as the PC.  The pointer itself is not architecturally
    observable (no instruction reads it), so the state stores the ring in
    pointer-relative coordinates: pc is the current row, and stk1..stk3 are
    the rows one, two, and three positions behind the pointer.  CALL and RET
    are then 4-row rotations; a fourth nested call overwrites the oldest row
    and a return past the ring's depth resumes a stale row, exactly as on
    silicon.  behavior.v proves this representation isomorphic to an
    explicit slots-and-pointer ring.

    DCL latches the accumulator's low three bits as the CM-RAM line code;
    codes 3,5,6,7 assert several lines at once, so RAM writes reach every
    selected bank (reads under multi-line selection are electrically
    undefined; see ram_read_main).

    Each 4001's I/O port is metal-mask configured as input or output.  The
    state keeps the WRR-written output latches, the environment-driven input
    pins, and the mask-time direction assignment (one direction per 4-bit
    port, matching the granularity of the fidelity claims). *)
Record Intel4004State := mkState {
  acc         : nibble;          (* 4-bit accumulator *)
  regs        : list nibble;     (* 16 4-bit index registers R0..R15 *)
  carry       : bool;            (* carry/link flag *)
  pc          : addr12;          (* address ring: the current row *)
  stk1        : addr12;          (* address ring: one row behind *)
  stk2        : addr12;          (* address ring: two rows behind *)
  stk3        : addr12;          (* address ring: three rows behind *)
  ram_sys     : list RAMBank;    (* 4 banks x 4 chips x 4 regs x (16+4) chars *)
  cm_code     : word3;           (* DCL latch: CM-RAM line code (acc low 3 bits) *)
  sel_ram     : RAMSel;          (* last RAM address sent by SRC *)
  out_ports   : list nibble;     (* 16 ROM output-port latches, written by WRR *)
  in_ports    : list nibble;     (* 16 ROM input pins, driven by the environment *)
  port_dirs   : list bool;       (* 16 mask-programmed directions; true = output *)
  sel_rom     : nibble;          (* last ROM port selected by SRC *)
  rom         : list byte;       (* 4096 bytes of program memory (WPM-writable) *)
  test_pin    : bool;            (* TEST input (active low in JCN condition) *)
  prom_addr   : addr12;          (* programmer address latch (loaded from ports) *)
  prom_enable : bool;            (* programmer write-enable (loaded from ports) *)
  prom_latch  : ProgLatch        (* 4008/4009 half-byte staging latch *)
}.

(* ---- Field updaters ---- *)

Definition with_acc (a : nibble) (s : Intel4004State) : Intel4004State :=
  mkState a (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_regs (r : list nibble) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) r (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_carry (c : bool) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) c (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_pc (a : addr12) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) a (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_ram (m : list RAMBank) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) m
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_cm (c : word3) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          c (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_select (rs : RAMSel) (k : nibble) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) rs (out_ports s) (in_ports s) (port_dirs s)
          k (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_out_ports (p : list nibble) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) p (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_in_ports (p : list nibble) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) p (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_rom (r : list byte) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) r (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_test (t : bool) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) t (prom_addr s) (prom_enable s) (prom_latch s).

Definition with_prom_addr (a : addr12) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) a (prom_enable s) (prom_latch s).

Definition with_prom_enable (e : bool) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) e (prom_latch s).

Definition with_prom_latch (pl : ProgLatch) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (pc s) (stk1 s) (stk2 s) (stk3 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) pl.

(* ---- Numeric accessors ---- *)

(** Accumulator value. *)
Definition aval (s : Intel4004State) : nat := wval (acc s).

(** Program counter value. *)
Definition pcv (s : Intel4004State) : nat := wval (pc s).

(** Carry bit as a number. *)
Definition cbit (s : Intel4004State) : nat := if carry s then 1 else 0.

Lemma aval_lt16 : forall s, aval s < 16.
Proof. intro s. apply nib_lt16. Qed.

Lemma pcv_lt4096 : forall s, pcv s < 4096.
Proof. intro s. apply addr12_lt4096. Qed.

(* ==================== The address ring: CALL and RET ================= *)

(** CALL: the return address is deposited in the current row, the pointer
    advances, and the target loads into the new current row.  In
    pointer-relative coordinates the rows rotate: the oldest saved row
    (three behind) is the one the advancing pointer overwrites, so it
    disappears — the hardware's discard-oldest overflow rule. *)
Definition ring_push (ret target : addr12) (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) target ret (stk1 s) (stk2 s) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

(** RET: the pointer backs up and that row resumes as the PC.  The vacated
    current row reappears three positions behind the new pointer holding
    the address one past the return instruction: the row was incremented
    during the return's own fetch and the rotation abandons it without a
    write-back.  Returning past the ring's depth therefore resumes a
    stale row holding that incremented address (validated against the
    transistor netlist captured from the 4004's masks). *)
Definition ring_pop (s : Intel4004State) : Intel4004State :=
  mkState (acc s) (regs s) (carry s) (stk1 s) (stk2 s) (stk3 s)
          (adr (pcv s + 1)) (ram_sys s)
          (cm_code s) (sel_ram s) (out_ports s) (in_ports s) (port_dirs s)
          (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_enable s) (prom_latch s).

(* =========================== Registers ============================== *)

(** Reads register r. Returns nib 0 if r >= length of register file. *)
Definition get_reg (s : Intel4004State) (r : nat) : nibble :=
  nth r (regs s) (nib 0).

(** Register value as a number. *)
Definition rval (s : Intel4004State) (r : nat) : nat := wval (get_reg s r).

(** Every register read is a nibble value, unconditionally. *)
Lemma rval_lt16 : forall s r, rval s r < 16.
Proof. intros s r. unfold rval. apply nib_lt16. Qed.

(** Sets register r to v. Preserves all other state fields. *)
Definition set_reg (s : Intel4004State) (r : nat) (v : nibble) : Intel4004State :=
  with_regs (update_nth r v (regs s)) s.

(** Reads register pair starting at r (rounds down to even). Returns high*16 + low. *)
Definition get_reg_pair (s : Intel4004State) (r : nat) : nat :=
  let r_even := r - (r mod 2) in
  rval s r_even * 16 + rval s (r_even + 1).

(** Register pair values are bytes, unconditionally. *)
Lemma get_reg_pair_lt256 : forall s r, get_reg_pair s r < 256.
Proof.
  intros s r. unfold get_reg_pair.
  pose proof (rval_lt16 s (r - r mod 2)).
  pose proof (rval_lt16 s (r - r mod 2 + 1)).
  lia.
Qed.

(** Sets register pair starting at r (rounds down to even) to v's nibbles. *)
Definition set_reg_pair (s : Intel4004State) (r : nat) (v : nat) : Intel4004State :=
  let r_even := r - (r mod 2) in
  with_regs (update_nth (r_even + 1) (nib (v mod 16))
              (update_nth r_even (nib (v / 16)) (regs s))) s.

(** Proves set_reg preserves register file length. *)
Lemma set_reg_preserves_length : forall s r v,
  length (regs (set_reg s r v)) = length (regs s).
Proof.
  intros. unfold set_reg. cbn [regs with_regs].
  apply update_nth_length.
Qed.

(** Proves set_reg_pair preserves register file length. *)
Lemma set_reg_pair_preserves_length : forall s r v,
  length (regs (set_reg_pair s r v)) = length (regs s).
Proof.
  intros. unfold set_reg_pair. cbn [regs with_regs].
  rewrite !update_nth_length. reflexivity.
Qed.

(* ============================ ROM =================================== *)

(** Fetches byte from ROM at address a. Returns byt 0 if a >= ROM length. *)
Definition fetch_byte (s : Intel4004State) (a : nat) : byte :=
  nth a (rom s) (byt 0).

(** Every fetched byte is a byte value, unconditionally. *)
Lemma fetch_byte_lt256 : forall s a, wval (fetch_byte s a) < 256.
Proof. intros. apply byte_lt256. Qed.

(** PC successor values, normalized to the 12-bit space. *)
Definition pc_inc1 (s : Intel4004State) : addr12 := adr (pcv s + 1).
Definition pc_inc2 (s : Intel4004State) : addr12 := adr (pcv s + 2).

(** Extracts page number (upper 4 bits) from a 12-bit address value. *)
Definition page_of (p : nat) : nat := p / 256.

(** Computes base address of the page containing p. *)
Definition page_base (p : nat) : nat := page_of p * 256.

(** Page bases of the next sequential instruction (1- and 2-byte forms). *)
Definition base_for_next1 (s : Intel4004State) : nat := page_base (wval (pc_inc1 s)).
Definition base_for_next2 (s : Intel4004State) : nat := page_base (wval (pc_inc2 s)).

(** Advance the program counter by k, wrapping in the 12-bit space. *)
Definition pc_bump (k : nat) (s : Intel4004State) : Intel4004State :=
  with_pc (adr (pcv s + k)) s.

(* ========================= RAM navigation =========================== *)

(** RAM system dimension constants. *)
Definition NBANKS := 4.
Definition NCHIPS := 4.
Definition NREGS  := 4.
Definition NMAIN  := 16.
Definition NSTAT  := 4.

(** Empty RAM structures. *)
Definition empty_reg : RAMReg := mkRAMReg (repeat (nib 0) NMAIN) (repeat (nib 0) NSTAT).
Definition empty_chip : RAMChip := mkRAMChip (repeat empty_reg NREGS) (nib 0).
Definition empty_bank : RAMBank := mkRAMBank (repeat empty_chip NCHIPS).
Definition empty_sys : list RAMBank := repeat empty_bank NBANKS.

(** Retrieves bank b from a system. Returns empty default if out of range. *)
Definition get_bank_sys (sys : list RAMBank) (b : nat) : RAMBank :=
  nth b sys empty_bank.

Definition get_bank (s : Intel4004State) (b : nat) : RAMBank :=
  get_bank_sys (ram_sys s) b.

(** Retrieves chip c from bank. *)
Definition get_chip (bk : RAMBank) (c : nat) : RAMChip :=
  nth c (bank_chips bk) empty_chip.

(** Retrieves register r from chip. *)
Definition get_regRAM (ch : RAMChip) (r : nat) : RAMReg :=
  nth r (chip_regs ch) empty_reg.

(** Retrieves main character i from register. *)
Definition get_main (rg : RAMReg) (i : nat) : nibble := nth i (reg_main rg) (nib 0).

(** Retrieves status character i from register. *)
Definition get_stat (rg : RAMReg) (i : nat) : nibble := nth i (reg_status rg) (nib 0).

(** Updates main character i in register to v. *)
Definition upd_main_in_reg (rg : RAMReg) (i : nat) (v : nibble) : RAMReg :=
  mkRAMReg (update_nth i v (reg_main rg)) (reg_status rg).

(** Updates status character i in register to v. *)
Definition upd_stat_in_reg (rg : RAMReg) (i : nat) (v : nibble) : RAMReg :=
  mkRAMReg (reg_main rg) (update_nth i v (reg_status rg)).

(** Updates register r in chip. *)
Definition upd_reg_in_chip (ch : RAMChip) (r : nat) (rg : RAMReg) : RAMChip :=
  mkRAMChip (update_nth r rg (chip_regs ch)) (chip_port ch).

(** Updates output port in chip to v. *)
Definition upd_port_in_chip (ch : RAMChip) (v : nibble) : RAMChip :=
  mkRAMChip (chip_regs ch) v.

(** Updates chip c in bank. *)
Definition upd_chip_in_bank (bk : RAMBank) (c : nat) (ch : RAMChip) : RAMBank :=
  mkRAMBank (update_nth c ch (bank_chips bk)).

(* ---- Point read-back equations at each level of the hierarchy ---- *)

Lemma get_main_upd_main_in_reg : forall rg i v,
  i < length (reg_main rg) ->
  get_main (upd_main_in_reg rg i v) i = v.
Proof.
  intros rg i v Hi.
  unfold get_main, upd_main_in_reg. cbn.
  apply nth_update_nth_eq. exact Hi.
Qed.

Lemma get_main_upd_main_in_reg_neq : forall rg i j v,
  i <> j ->
  get_main (upd_main_in_reg rg i v) j = get_main rg j.
Proof.
  intros rg i j v Hne.
  unfold get_main, upd_main_in_reg. cbn.
  apply nth_update_nth_neq. lia.
Qed.

Lemma get_stat_upd_stat_in_reg : forall rg i v,
  i < length (reg_status rg) ->
  get_stat (upd_stat_in_reg rg i v) i = v.
Proof.
  intros rg i v Hi.
  unfold get_stat, upd_stat_in_reg. cbn.
  apply nth_update_nth_eq. exact Hi.
Qed.

Lemma get_stat_upd_stat_in_reg_neq : forall rg i j v,
  i <> j ->
  get_stat (upd_stat_in_reg rg i v) j = get_stat rg j.
Proof.
  intros rg i j v Hne.
  unfold get_stat, upd_stat_in_reg. cbn.
  apply nth_update_nth_neq. lia.
Qed.

Lemma get_regRAM_upd_reg_in_chip : forall ch r rg,
  r < length (chip_regs ch) ->
  get_regRAM (upd_reg_in_chip ch r rg) r = rg.
Proof.
  intros ch r rg Hr.
  unfold get_regRAM, upd_reg_in_chip. cbn.
  apply nth_update_nth_eq. exact Hr.
Qed.

Lemma get_regRAM_upd_reg_in_chip_neq : forall ch r1 r2 rg,
  r1 <> r2 ->
  get_regRAM (upd_reg_in_chip ch r1 rg) r2 = get_regRAM ch r2.
Proof.
  intros ch r1 r2 rg Hne.
  unfold get_regRAM, upd_reg_in_chip. cbn.
  apply nth_update_nth_neq. lia.
Qed.

Lemma get_chip_upd_chip_in_bank : forall bk c ch,
  c < length (bank_chips bk) ->
  get_chip (upd_chip_in_bank bk c ch) c = ch.
Proof.
  intros bk c ch Hc.
  unfold get_chip, upd_chip_in_bank. cbn.
  apply nth_update_nth_eq. exact Hc.
Qed.

Lemma get_chip_upd_chip_in_bank_neq : forall bk c1 c2 ch,
  c1 <> c2 ->
  get_chip (upd_chip_in_bank bk c1 ch) c2 = get_chip bk c2.
Proof.
  intros bk c1 c2 ch Hne.
  unfold get_chip, upd_chip_in_bank. cbn.
  apply nth_update_nth_neq. lia.
Qed.

(* ==================== CM-RAM line decoding (DCL) ===================== *)

(** DCL bank selection via CM-RAM encoding (MCS-4 Users Manual): the low
    three accumulator bits X3X2X1 drive the CM-RAM lines.  Code 000 selects
    CM-RAM0; 001, 010, 100 select CM-RAM1/2/3; the remaining codes assert
    SEVERAL lines at once and address several banks simultaneously.  The
    line set is the default semantics: writes reach every selected bank. *)
Definition dcl_lines (c : word3) : list nat :=
  match wval c with
  | 0 => [0]
  | 1 => [1]
  | 2 => [2]
  | 3 => [1; 2]
  | 4 => [3]
  | 5 => [1; 3]
  | 6 => [2; 3]
  | _ => [1; 2; 3]
  end.

(** The banks currently addressed by the DCL latch. *)
Definition sel_lines (s : Intel4004State) : list nat := dcl_lines (cm_code s).

Lemma dcl_lines_bounded : forall c, Forall (fun b => b < 4) (dcl_lines c).
Proof.
  intro c. unfold dcl_lines.
  destruct (wval c) as [|[|[|[|[|[|[|k]]]]]]]; repeat constructor; lia.
Qed.

Lemma dcl_lines_nonempty : forall c, dcl_lines c <> [].
Proof.
  intro c. unfold dcl_lines.
  destruct (wval c) as [|[|[|[|[|[|[|k]]]]]]]; discriminate.
Qed.

Lemma dcl_lines_NoDup : forall c, NoDup (dcl_lines c).
Proof.
  intro c. unfold dcl_lines.
  destruct (wval c) as [|[|[|[|[|[|[|k]]]]]]];
    repeat constructor; simpl; intuition lia.
Qed.

(** The single-line codes 0,1,2,4 select exactly banks 0,1,2,3. *)
Definition dcl_bank (c : word3) : nat :=
  match wval c with
  | 1 => 1
  | 2 => 2
  | 4 => 3
  | _ => 0
  end.

Lemma dcl_bank_lt_4 : forall c, dcl_bank c < 4.
Proof.
  intro c. unfold dcl_bank.
  destruct (wval c) as [|[|[|[|[|k]]]]]; cbn; lia.
Qed.

Lemma dcl_lines_single : forall c,
  wval c = 0 \/ wval c = 1 \/ wval c = 2 \/ wval c = 4 ->
  dcl_lines c = [dcl_bank c].
Proof.
  intros c H. unfold dcl_lines, dcl_bank.
  destruct H as [H|[H|[H|H]]]; rewrite H; reflexivity.
Qed.

(* ==================== Multi-bank RAM writes and reads ================ *)

(** Write the currently selected main character of one bank. *)
Definition write_main_bank (sys : list RAMBank) (sel : RAMSel) (b : nat) (v : nibble)
  : list RAMBank :=
  let bk := get_bank_sys sys b in
  let ch := get_chip bk (wval (sel_chip sel)) in
  let rg := get_regRAM ch (wval (sel_reg sel)) in
  update_nth b (upd_chip_in_bank bk (wval (sel_chip sel))
                  (upd_reg_in_chip ch (wval (sel_reg sel))
                     (upd_main_in_reg rg (wval (sel_char sel)) v))) sys.

(** Write the selected main character of every bank in a line set. *)
Fixpoint write_main_banks (sys : list RAMBank) (sel : RAMSel) (bs : list nat) (v : nibble)
  : list RAMBank :=
  match bs with
  | [] => sys
  | b :: rest => write_main_banks (write_main_bank sys sel b v) sel rest v
  end.

(** Write status character idx of one bank at the selected chip/register. *)
Definition write_stat_bank (sys : list RAMBank) (sel : RAMSel) (idx : nat) (b : nat)
  (v : nibble) : list RAMBank :=
  let bk := get_bank_sys sys b in
  let ch := get_chip bk (wval (sel_chip sel)) in
  let rg := get_regRAM ch (wval (sel_reg sel)) in
  update_nth b (upd_chip_in_bank bk (wval (sel_chip sel))
                  (upd_reg_in_chip ch (wval (sel_reg sel))
                     (upd_stat_in_reg rg idx v))) sys.

Fixpoint write_stat_banks (sys : list RAMBank) (sel : RAMSel) (idx : nat)
  (bs : list nat) (v : nibble) : list RAMBank :=
  match bs with
  | [] => sys
  | b :: rest => write_stat_banks (write_stat_bank sys sel idx b v) sel idx rest v
  end.

(** Write the output port of the selected chip of one bank. *)
Definition write_port_bank (sys : list RAMBank) (sel : RAMSel) (b : nat) (v : nibble)
  : list RAMBank :=
  let bk := get_bank_sys sys b in
  let ch := get_chip bk (wval (sel_chip sel)) in
  update_nth b (upd_chip_in_bank bk (wval (sel_chip sel)) (upd_port_in_chip ch v)) sys.

Fixpoint write_port_banks (sys : list RAMBank) (sel : RAMSel) (bs : list nat)
  (v : nibble) : list RAMBank :=
  match bs with
  | [] => sys
  | b :: rest => write_port_banks (write_port_bank sys sel b v) sel rest v
  end.

(** Read the selected main character of one bank. *)
Definition read_main_bank (sys : list RAMBank) (sel : RAMSel) (b : nat) : nibble :=
  get_main (get_regRAM (get_chip (get_bank_sys sys b) (wval (sel_chip sel)))
              (wval (sel_reg sel)))
           (wval (sel_char sel)).

(** Read status character idx of one bank. *)
Definition read_stat_bank (sys : list RAMBank) (sel : RAMSel) (idx : nat) (b : nat)
  : nibble :=
  get_stat (get_regRAM (get_chip (get_bank_sys sys b) (wval (sel_chip sel)))
              (wval (sel_reg sel)))
           idx.

(** Agreement read over a nonempty list of per-bank reads: defined exactly
    when every selected bank drives the same value.  Reads under multi-line
    selection put several 4002s on the data bus at once, which no MCS-4
    document defines; the partial function is the fidelity claim. *)
Definition agree_read (reads : list nibble) : option nibble :=
  match reads with
  | [] => None
  | v :: rest =>
      if forallb (fun x => wval x =? wval v) rest then Some v else None
  end.

Definition ram_read_main_opt (s : Intel4004State) : option nibble :=
  agree_read (map (read_main_bank (ram_sys s) (sel_ram s)) (sel_lines s)).

Definition ram_read_stat_opt (s : Intel4004State) (idx : nat) : option nibble :=
  agree_read (map (read_stat_bank (ram_sys s) (sel_ram s) idx) (sel_lines s)).

(** Total reads used by execute: the agreed value when the selected banks
    are unanimous, and nib 0 as the documented convention for the
    electrically undefined disagreeing multi-line case.  On single-line
    codes the read is always defined (a one-bank set is unanimous), and any
    read after a write through the same selection is defined, because the
    write leaves the selected banks unanimous. *)
Definition ram_read_main (s : Intel4004State) : nibble :=
  match ram_read_main_opt s with Some v => v | None => nib 0 end.

Definition ram_read_stat (s : Intel4004State) (idx : nat) : nibble :=
  match ram_read_stat_opt s idx with Some v => v | None => nib 0 end.

(* =============================== ISA ================================ *)

(** Intel 4004 instruction set. 46 instructions total.  Operand widths are
    enforced by construction; only register-pair parity remains a side
    condition (instr_wf). *)
Inductive Instruction : Type :=
  | NOP : Instruction
  | JCN : nibble -> byte -> Instruction
  | FIM : nibble -> byte -> Instruction
  | SRC : nibble -> Instruction
  | FIN : nibble -> Instruction
  | JIN : nibble -> Instruction
  | JUN : addr12 -> Instruction
  | JMS : addr12 -> Instruction
  | INC : nibble -> Instruction
  | ISZ : nibble -> byte -> Instruction
  | ADD : nibble -> Instruction
  | SUB : nibble -> Instruction
  | LD  : nibble -> Instruction
  | XCH : nibble -> Instruction
  | BBL : nibble -> Instruction
  | LDM : nibble -> Instruction
  | WRM : Instruction
  | WMP : Instruction
  | WRR : Instruction
  | WPM : Instruction
  | WR0 : Instruction
  | WR1 : Instruction
  | WR2 : Instruction
  | WR3 : Instruction
  | SBM : Instruction
  | RDM : Instruction
  | RDR : Instruction
  | ADM : Instruction
  | RD0 : Instruction
  | RD1 : Instruction
  | RD2 : Instruction
  | RD3 : Instruction
  | CLB : Instruction
  | CLC : Instruction
  | IAC : Instruction
  | CMC : Instruction
  | CMA : Instruction
  | RAL : Instruction
  | RAR : Instruction
  | TCC : Instruction
  | DAC : Instruction
  | TCS : Instruction
  | STC : Instruction
  | DAA : Instruction
  | KBP : Instruction
  | DCL : Instruction.

(** Decodes two bytes into an instruction. Total (returns NOP for the
    undefined encodings; see decode_low_group_is_nop and decode_FE_FF_is_nop). *)
Definition decode (b1 b2 : byte) : Instruction :=
  let v := wval b1 in
  let opcode := v / 16 in
  let d := v mod 16 in
  match opcode with
  | 0 => NOP
  | 1 => JCN (nib d) b2
  | 2 => if d mod 2 =? 0 then FIM (nib d) b2 else SRC (nib d)
  | 3 => if d mod 2 =? 0 then FIN (nib d) else JIN (nib d)
  | 4 => JUN (adr (d * 256 + wval b2))
  | 5 => JMS (adr (d * 256 + wval b2))
  | 6 => INC (nib d)
  | 7 => ISZ (nib d) b2
  | 8 => ADD (nib d)
  | 9 => SUB (nib d)
  | 10 => LD (nib d)
  | 11 => XCH (nib d)
  | 12 => BBL (nib d)
  | 13 => LDM (nib d)
  | 14 =>
      match d with
      | 0 => WRM | 1 => WMP | 2 => WRR | 3 => WPM
      | 4 => WR0 | 5 => WR1 | 6 => WR2 | 7 => WR3
      | 8 => SBM | 9 => RDM | 10 => RDR | 11 => ADM
      | 12 => RD0 | 13 => RD1 | 14 => RD2 | _ => RD3
      end
  | 15 =>
      match d with
      | 0 => CLB | 1 => CLC | 2 => IAC | 3 => CMC
      | 4 => CMA | 5 => RAL | 6 => RAR | 7 => TCC
      | 8 => DAC | 9 => TCS | 10 => STC | 11 => DAA
      | 12 => KBP | 13 => DCL
      | _ => NOP
      end
  | _ => NOP
  end.

(* ========================== ENCODE ================================= *)

(** Encodes an instruction to its two-byte representation.  Operand bounds
    hold by type, so no defensive truncation is needed. *)
Definition encode (i : Instruction) : byte * byte :=
  match i with
  | NOP => (byt 0, byt 0)
  | JCN c a => (byt (16 + wval c), a)
  | FIM r d => (byt (32 + (wval r - wval r mod 2)), d)
  | SRC r    => (byt (32 + (wval r - wval r mod 2) + 1), byt 0)
  | FIN r    => (byt (48 + (wval r - wval r mod 2)), byt 0)
  | JIN r    => (byt (48 + (wval r - wval r mod 2) + 1), byt 0)
  | JUN a    => (byt (64 + wval a / 256), byt (wval a mod 256))
  | JMS a    => (byt (80 + wval a / 256), byt (wval a mod 256))
  | INC r    => (byt (96 + wval r), byt 0)
  | ISZ r a  => (byt (112 + wval r), a)
  | ADD r    => (byt (128 + wval r), byt 0)
  | SUB r    => (byt (144 + wval r), byt 0)
  | LD r     => (byt (160 + wval r), byt 0)
  | XCH r    => (byt (176 + wval r), byt 0)
  | BBL d    => (byt (192 + wval d), byt 0)
  | LDM d    => (byt (208 + wval d), byt 0)
  | WRM      => (byt 224, byt 0) | WMP => (byt 225, byt 0)
  | WRR      => (byt 226, byt 0) | WPM => (byt 227, byt 0)
  | WR0      => (byt 228, byt 0) | WR1 => (byt 229, byt 0)
  | WR2      => (byt 230, byt 0) | WR3 => (byt 231, byt 0)
  | SBM      => (byt 232, byt 0) | RDM => (byt 233, byt 0)
  | RDR      => (byt 234, byt 0) | ADM => (byt 235, byt 0)
  | RD0      => (byt 236, byt 0) | RD1 => (byt 237, byt 0)
  | RD2      => (byt 238, byt 0) | RD3 => (byt 239, byt 0)
  | CLB      => (byt 240, byt 0) | CLC => (byt 241, byt 0)
  | IAC      => (byt 242, byt 0) | CMC => (byt 243, byt 0)
  | CMA      => (byt 244, byt 0) | RAL => (byt 245, byt 0)
  | RAR      => (byt 246, byt 0) | TCC => (byt 247, byt 0)
  | DAC      => (byt 248, byt 0) | TCS => (byt 249, byt 0)
  | STC      => (byt 250, byt 0) | DAA => (byt 251, byt 0)
  | KBP      => (byt 252, byt 0) | DCL => (byt 253, byt 0)
  end.

(** Well-formedness predicate for instructions.  Operand widths hold by
    construction, so only the register-pair parity conditions remain: FIM
    and FIN take the even register of a pair, SRC and JIN the odd one. *)
Definition instr_wf (i : Instruction) : Prop :=
  match i with
  | FIM r _ => wval r mod 2 = 0
  | FIN r   => wval r mod 2 = 0
  | SRC r   => wval r mod 2 = 1
  | JIN r   => wval r mod 2 = 1
  | _ => True
  end.

(** Witness: NOP is trivially well-formed. *)
Lemma instr_wf_NOP : instr_wf NOP.
Proof. exact I. Qed.

(** Witness: FIM with even register is well-formed. *)
Lemma instr_wf_FIM_0_42 : instr_wf (FIM (nib 0) (byt 42)).
Proof. reflexivity. Qed.

(** Counterexample: FIM with odd register violates instr_wf. *)
Lemma instr_wf_FIM_odd_rejected : ~ instr_wf (FIM (nib 1) (byt 42)).
Proof. cbn. discriminate. Qed.

(** Counterexample: SRC with even register violates instr_wf. *)
Lemma instr_wf_SRC_even_rejected : ~ instr_wf (SRC (nib 0)).
Proof. cbn. discriminate. Qed.

(** Width constraints are inhabitation facts: no nibble reaches 16, no
    address reaches 4096. *)
Lemma no_oversized_operand : forall d : nibble, wval d < 16.
Proof. exact nib_lt16. Qed.

Lemma no_oversized_address : forall a : addr12, wval a < 4096.
Proof. exact addr12_lt4096. Qed.

(* ==================== Encode/decode bijection ======================== *)

(** Decode of a nibble-operand opcode row. *)
Lemma decode_row : forall k (r : nibble),
  k < 16 ->
  wval (byt (k * 16 + wval r)) / 16 = k /\
  wval (byt (k * 16 + wval r)) mod 16 = wval r.
Proof.
  intros k r Hk.
  pose proof (nib_lt16 r) as Hr.
  rewrite byt_val_small by lia.
  split; [apply div16_off | apply mod16_off]; lia.
Qed.

(** Main encode/decode bijection: decode inverts encode on well-formed
    instructions. *)
Lemma decode_encode_id : forall i, instr_wf i ->
  let '(b1, b2) := encode i in decode b1 b2 = i.
Proof.
  intros i Hwf.
  destruct i; try reflexivity; cbn [encode].

  - (* JCN *)
    unfold decode. cbv zeta.
    pose proof (nib_lt16 n) as Hc.
    replace (16 + wval n) with (1 * 16 + wval n) by lia.
    destruct (decode_row 1 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2.
    rewrite nib_wval. reflexivity.

  - (* FIM: even register *)
    cbn [instr_wf] in Hwf.
    unfold decode. cbv zeta.
    pose proof (nib_lt16 n) as Hr.
    rewrite even_sub_mod by exact Hwf.
    replace (32 + wval n) with (2 * 16 + wval n) by lia.
    destruct (decode_row 2 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2.
    rewrite Hwf. cbn [Nat.eqb].
    rewrite nib_wval. reflexivity.

  - (* SRC: odd register *)
    cbn [instr_wf] in Hwf.
    unfold decode. cbv zeta.
    pose proof (nib_lt16 n) as Hr.
    rewrite odd_sub_mod by exact Hwf.
    assert (Hpos : 1 <= wval n).
    { destruct (wval n); [discriminate Hwf | lia]. }
    replace (32 + (wval n - 1) + 1) with (2 * 16 + wval n) by lia.
    destruct (decode_row 2 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2.
    rewrite Hwf. cbn [Nat.eqb].
    rewrite nib_wval. reflexivity.

  - (* FIN: even register *)
    cbn [instr_wf] in Hwf.
    unfold decode. cbv zeta.
    pose proof (nib_lt16 n) as Hr.
    rewrite even_sub_mod by exact Hwf.
    replace (48 + wval n) with (3 * 16 + wval n) by lia.
    destruct (decode_row 3 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2.
    rewrite Hwf. cbn [Nat.eqb].
    rewrite nib_wval. reflexivity.

  - (* JIN: odd register *)
    cbn [instr_wf] in Hwf.
    unfold decode. cbv zeta.
    pose proof (nib_lt16 n) as Hr.
    rewrite odd_sub_mod by exact Hwf.
    assert (Hpos : 1 <= wval n).
    { destruct (wval n); [discriminate Hwf | lia]. }
    replace (48 + (wval n - 1) + 1) with (3 * 16 + wval n) by lia.
    destruct (decode_row 3 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2.
    rewrite Hwf. cbn [Nat.eqb].
    rewrite nib_wval. reflexivity.

  - (* JUN *)
    unfold decode. cbv zeta.
    pose proof (addr12_lt4096 a) as Ha.
    assert (Hhi : wval a / 256 < 16) by (apply div256_addr_bound; exact Ha).
    replace (64 + wval a / 256) with (4 * 16 + wval a / 256) by lia.
    assert (Hv : wval (byt (4 * 16 + wval a / 256)) = 4 * 16 + wval a / 256)
      by (apply byt_val_small; lia).
    rewrite Hv.
    rewrite div16_off by lia.
    rewrite mod16_off by lia.
    rewrite byt_val.
    rewrite (Nat.mod_small (wval a mod 256) 256) by apply mod256_bound.
    f_equal.
    apply addr12_eq.
    rewrite adr_val.
    pose proof (divmod256 (wval a)) as Hdm.
    rewrite Nat.mod_small by lia.
    lia.

  - (* JMS *)
    unfold decode. cbv zeta.
    pose proof (addr12_lt4096 a) as Ha.
    assert (Hhi : wval a / 256 < 16) by (apply div256_addr_bound; exact Ha).
    replace (80 + wval a / 256) with (5 * 16 + wval a / 256) by lia.
    assert (Hv : wval (byt (5 * 16 + wval a / 256)) = 5 * 16 + wval a / 256)
      by (apply byt_val_small; lia).
    rewrite Hv.
    rewrite div16_off by lia.
    rewrite mod16_off by lia.
    rewrite byt_val.
    rewrite (Nat.mod_small (wval a mod 256) 256) by apply mod256_bound.
    f_equal.
    apply addr12_eq.
    rewrite adr_val.
    pose proof (divmod256 (wval a)) as Hdm.
    rewrite Nat.mod_small by lia.
    lia.

  - (* INC *)
    unfold decode. cbv zeta.
    replace (96 + wval n) with (6 * 16 + wval n) by lia.
    destruct (decode_row 6 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2. rewrite nib_wval. reflexivity.

  - (* ISZ *)
    unfold decode. cbv zeta.
    replace (112 + wval n) with (7 * 16 + wval n) by lia.
    destruct (decode_row 7 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2. rewrite nib_wval. reflexivity.

  - (* ADD *)
    unfold decode. cbv zeta.
    replace (128 + wval n) with (8 * 16 + wval n) by lia.
    destruct (decode_row 8 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2. rewrite nib_wval. reflexivity.

  - (* SUB *)
    unfold decode. cbv zeta.
    replace (144 + wval n) with (9 * 16 + wval n) by lia.
    destruct (decode_row 9 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2. rewrite nib_wval. reflexivity.

  - (* LD *)
    unfold decode. cbv zeta.
    replace (160 + wval n) with (10 * 16 + wval n) by lia.
    destruct (decode_row 10 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2. rewrite nib_wval. reflexivity.

  - (* XCH *)
    unfold decode. cbv zeta.
    replace (176 + wval n) with (11 * 16 + wval n) by lia.
    destruct (decode_row 11 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2. rewrite nib_wval. reflexivity.

  - (* BBL *)
    unfold decode. cbv zeta.
    replace (192 + wval n) with (12 * 16 + wval n) by lia.
    destruct (decode_row 12 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2. rewrite nib_wval. reflexivity.

  - (* LDM *)
    unfold decode. cbv zeta.
    replace (208 + wval n) with (13 * 16 + wval n) by lia.
    destruct (decode_row 13 n ltac:(lia)) as [E1 E2].
    rewrite E1, E2. rewrite nib_wval. reflexivity.
Qed.

(** Every decoded instruction is well-formed: operand widths by
    construction, parities by the decode branch. *)
Lemma decode_instr_wf : forall b1 b2, instr_wf (decode b1 b2).
Proof.
  intros b1 b2.
  unfold decode. cbv zeta.
  assert (Hd : wval b1 mod 16 < 16) by apply mod16_bound.
  destruct (wval b1 / 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]]]]]];
    cbn [instr_wf]; try exact I.
  - (* opcode 2: FIM/SRC *)
    destruct (wval b1 mod 16 mod 2 =? 0) eqn:E; cbn [instr_wf];
      rewrite nib_val; rewrite (Nat.mod_small _ 16 Hd).
    + apply Nat.eqb_eq. exact E.
    + pose proof (mod2_cases (wval b1 mod 16)) as [H0 | H1].
      * rewrite H0 in E. discriminate.
      * exact H1.
  - (* opcode 3: FIN/JIN *)
    destruct (wval b1 mod 16 mod 2 =? 0) eqn:E; cbn [instr_wf];
      rewrite nib_val; rewrite (Nat.mod_small _ 16 Hd).
    + apply Nat.eqb_eq. exact E.
    + pose proof (mod2_cases (wval b1 mod 16)) as [H0 | H1].
      * rewrite H0 in E. discriminate.
      * exact H1.
  - (* opcode 14 *)
    destruct (wval b1 mod 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|m]]]]]]]]]]]]]]];
      exact I.
  - (* opcode 15 *)
    destruct (wval b1 mod 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|m]]]]]]]]]]]]]];
      exact I.
Qed.

(** Re-encoding a decoded instruction yields bytes that decode to the same
    instruction: encode picks a canonical representative of decode's fiber
    over any byte pair. *)
Theorem encode_decode_idempotent : forall b1 b2 : byte,
  let '(c1, c2) := encode (decode b1 b2) in
  decode c1 c2 = decode b1 b2.
Proof.
  intros b1 b2.
  exact (decode_encode_id (decode b1 b2) (decode_instr_wf b1 b2)).
Qed.

(* ============================ Semantics ============================= *)

(** Executes a single instruction. Total function over all 46 instructions. *)
Definition execute (s : Intel4004State) (inst : Instruction) : Intel4004State :=
  match inst with
  | NOP => pc_bump 1 s

  | LDM n => pc_bump 1 (with_acc n s)

  | LD r => pc_bump 1 (with_acc (get_reg s (wval r)) s)

  | XCH r =>
      pc_bump 1 (with_acc (get_reg s (wval r))
                   (with_regs (update_nth (wval r) (acc s) (regs s)) s))

  | INC r =>
      pc_bump 1 (with_regs
                   (update_nth (wval r) (nib (rval s (wval r) + 1)) (regs s)) s)

  | ADD r =>
      let sum := aval s + rval s (wval r) + cbit s in
      pc_bump 1 (with_carry (16 <=? sum) (with_acc (nib sum) s))

  | SUB r =>
      (* Subtract with borrow: the incoming carry IS the borrow (it is
         subtracted), and the outgoing carry is the borrow's complement
         (1 = no borrow), which is why chained subtractions complement the
         carry between digits. Verified on real silicon (Grinberg,
         Linux/4004): ACC + ~REG + ~CY. *)
      let diff := aval s + 16 - rval s (wval r) - cbit s in
      pc_bump 1 (with_carry (16 <=? diff) (with_acc (nib diff) s))

  | IAC =>
      let sum := aval s + 1 in
      pc_bump 1 (with_carry (16 <=? sum) (with_acc (nib sum) s))

  | DAC =>
      pc_bump 1 (with_carry (negb (aval s =? 0)) (with_acc (nib (aval s + 15)) s))

  | CLC => pc_bump 1 (with_carry false s)
  | STC => pc_bump 1 (with_carry true s)
  | CMC => pc_bump 1 (with_carry (negb (carry s)) s)
  | CMA => pc_bump 1 (with_acc (nib (15 - aval s)) s)
  | CLB => pc_bump 1 (with_carry false (with_acc (nib 0) s))

  | RAL =>
      pc_bump 1 (with_carry (8 <=? aval s)
                   (with_acc (nib (aval s * 2 + cbit s)) s))

  | RAR =>
      pc_bump 1 (with_carry (aval s mod 2 =? 1)
                   (with_acc (nib (aval s / 2 + (if carry s then 8 else 0))) s))

  | TCC => pc_bump 1 (with_carry false (with_acc (nib (cbit s)) s))

  | TCS => pc_bump 1 (with_carry false (with_acc (nib (if carry s then 10 else 9)) s))

  | DAA =>
      (* DAA: add 6 iff carry set or acc > 9; carry-out set on nibble
         overflow, else unchanged. *)
      let adjust := orb (carry s) (9 <? aval s) in
      let sum := aval s + (if adjust then 6 else 0) in
      pc_bump 1 (with_carry (orb (16 <=? sum) (carry s)) (with_acc (nib sum) s))

  | KBP =>
      (* Keyboard Process: convert 1-of-n code to binary position.
         Source: MCS-4 Assembly Language Programming Manual (1973), p.3-35.
         Verified on actual 4004 hardware by Dmitry Grinberg (Linux/4004). *)
      let result :=
        match aval s with
        | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4 | _ => 15
        end in
      pc_bump 1 (with_acc (nib result) s)

  | JUN a => with_pc a s

  | JMS a => ring_push (adr (pcv s + 2)) a s

  | BBL n => with_acc n (ring_pop s)

  | JCN cond off =>
      let c := wval cond in
      let c1 := c / 8 in
      let c2 := (c / 4) mod 2 in
      let c3 := (c / 2) mod 2 in
      let c4 := c mod 2 in
      let base_cond :=
        orb (andb (aval s =? 0) (c2 =? 1))
            (orb (andb (carry s) (c3 =? 1))
                 (andb (negb (test_pin s)) (c4 =? 1))) in
      let jump := if c1 =? 1 then negb base_cond else base_cond in
      if jump
      then with_pc (adr (base_for_next2 s + wval off)) s
      else pc_bump 2 s

  | FIM r data => pc_bump 2 (set_reg_pair s (wval r) (wval data))

  | ISZ r off =>
      let new_val := nib (rval s (wval r) + 1) in
      let s1 := with_regs (update_nth (wval r) new_val (regs s)) s in
      if wval new_val =? 0
      then pc_bump 2 s1
      else with_pc (adr (base_for_next2 s + wval off)) s1

  | SRC r =>
      (* Send register pair r externally:
         - ROM I/O: high nibble selects ROM port number (0..15)
         - RAM: high nibble = chip(2) & reg(2); low nibble = main char(4)
         - Does not modify CPU registers. *)
      let v := get_reg_pair s (wval r) in
      let hi := v / 16 in
      pc_bump 1 (with_select (mkRAMSel (w2 (hi / 4)) (w2 (hi mod 4)) (nib (v mod 16)))
                   (nib hi) s)

  | FIN r =>
      (* fetch indirect: lower 8 from R0:R1; page is that of the next
         instruction (the documented page-of-PC+1 rule) *)
      let page := page_of (wval (pc_inc1 s)) in
      let b := fetch_byte s (page * 256 + get_reg_pair s 0) in
      pc_bump 1 (set_reg_pair s (wval r) (wval b))

  | JIN r =>
      (* jump within page of the *next* instruction (quirk included) *)
      let page := page_of (wval (pc_inc1 s)) in
      with_pc (adr (page * 256 + get_reg_pair s (wval r))) s

  (* ------------------ 4002 RAM + 4001 ROM I/O ------------------ *)

  | WRM =>
      pc_bump 1 (with_ram
        (write_main_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s)) s)

  | RDM => pc_bump 1 (with_acc (ram_read_main s) s)

  | ADM =>
      let sum := aval s + wval (ram_read_main s) + cbit s in
      pc_bump 1 (with_carry (16 <=? sum) (with_acc (nib sum) s))

  | SBM =>
      (* Subtract memory with borrow: same convention as SUB. *)
      let diff := aval s + 16 - wval (ram_read_main s) - cbit s in
      pc_bump 1 (with_carry (16 <=? diff) (with_acc (nib diff) s))

  | WR0 =>
      pc_bump 1 (with_ram
        (write_stat_banks (ram_sys s) (sel_ram s) 0 (sel_lines s) (acc s)) s)
  | WR1 =>
      pc_bump 1 (with_ram
        (write_stat_banks (ram_sys s) (sel_ram s) 1 (sel_lines s) (acc s)) s)
  | WR2 =>
      pc_bump 1 (with_ram
        (write_stat_banks (ram_sys s) (sel_ram s) 2 (sel_lines s) (acc s)) s)
  | WR3 =>
      pc_bump 1 (with_ram
        (write_stat_banks (ram_sys s) (sel_ram s) 3 (sel_lines s) (acc s)) s)

  | RD0 => pc_bump 1 (with_acc (ram_read_stat s 0) s)
  | RD1 => pc_bump 1 (with_acc (ram_read_stat s 1) s)
  | RD2 => pc_bump 1 (with_acc (ram_read_stat s 2) s)
  | RD3 => pc_bump 1 (with_acc (ram_read_stat s 3) s)

  | WMP =>
      pc_bump 1 (with_ram
        (write_port_banks (ram_sys s) (sel_ram s) (sel_lines s) (acc s)) s)

  | WRR =>
      (* WRR writes the 4001's internal output latch; only output-configured
         lines expose it on the pins (see RDR). *)
      pc_bump 1 (with_out_ports
        (update_nth (wval (sel_rom s)) (acc s) (out_ports s)) s)

  | RDR =>
      (* RDR reads the selected port's pins: the output latch on an
         output-configured port, the environment's drive on an input port. *)
      let k := wval (sel_rom s) in
      let v := if nth k (port_dirs s) true
               then nth k (out_ports s) (nib 0)
               else nth k (in_ports s) (nib 0) in
      pc_bump 1 (with_acc v s)

  | WPM =>
      (* Write Program Memory.  Hardware transfers one 4-bit half per WPM;
         the external 4008/4009 latch pair assembles two transfers into a
         byte and commits it, high half first, at the programmer's address
         latch.  The staging latch advances only when the programmer is
         armed; a disarmed WPM is a no-op (modeling convention). *)
      if prom_enable s then
        if pl_expect_low (prom_latch s) then
          pc_bump 1 (with_prom_latch latch_init
            (with_rom (update_nth (wval (prom_addr s))
                         (byt (wval (pl_hi (prom_latch s)) * 16 + aval s))
                         (rom s)) s))
        else
          pc_bump 1 (with_prom_latch (mkProgLatch true (acc s)) s)
      else pc_bump 1 s

  | DCL =>
      (* Designate command line: latch the accumulator's low three bits as
         the CM-RAM line code. *)
      pc_bump 1 (with_cm (w3 (aval s)) s)
  end.

(* ======================= Small-step machine ========================= *)

(** Executes one fetch-decode-execute cycle. *)
Definition step (s : Intel4004State) : Intel4004State :=
  let b1 := fetch_byte s (pcv s) in
  let b2 := fetch_byte s ((pcv s + 1) mod 4096) in
  execute s (decode b1 b2).

(** Executes n steps. *)
Fixpoint steps (n : nat) (s : Intel4004State) : Intel4004State :=
  match n with
  | 0 => s
  | S n' => steps n' (step s)
  end.

(* ========================== Initial / Reset ========================= *)

(** Initial power-on state: all zeros, empty RAM, zero ROM.  The port
    directions are a mask-time configuration; the default configures every
    port as an output (init_state_dirs takes an explicit assignment). *)
Definition init_state_dirs (dirs : list bool) : Intel4004State :=
  mkState (nib 0) (repeat (nib 0) 16) false (adr 0) (adr 0) (adr 0) (adr 0)
          empty_sys (w3 0) (mkRAMSel (w2 0) (w2 0) (nib 0))
          (repeat (nib 0) 16) (repeat (nib 0) 16) dirs
          (nib 0) (repeat (byt 0) 4096) false (adr 0) false latch_init.

Definition init_state : Intel4004State := init_state_dirs (repeat true 16).

(** CPU-scope reset: the 4004's RESET held for the data-sheet interval
    clears the accumulator, carry, index registers, and the whole address
    ring (PC and all three saved rows), and disarms the programmer latch.
    Memory contents (4002 RAM, ROM), the 4001 port latches and pins, the
    mask-programmed directions, and the externally driven TEST level are
    untouched: they live outside the CPU.  The system-wide RESET line
    additionally clears 4002 RAM and output ports (see system_reset in
    fidelity.v). *)
Definition reset_state (s : Intel4004State) : Intel4004State :=
  mkState (nib 0) (repeat (nib 0) 16) false (adr 0) (adr 0) (adr 0) (adr 0)
          (ram_sys s) (w3 0) (mkRAMSel (w2 0) (w2 0) (nib 0))
          (out_ports s) (in_ports s) (port_dirs s)
          (nib 0) (rom s) (test_pin s) (adr 0) false latch_init.

(* ======================== Well-formedness =========================== *)

(** Well-formedness is purely structural: every value bound holds by
    construction, so only the container lengths remain. *)
Definition WF_reg (rg : RAMReg) : Prop :=
  length (reg_main rg) = NMAIN /\ length (reg_status rg) = NSTAT.

Definition WF_chip (ch : RAMChip) : Prop :=
  length (chip_regs ch) = NREGS /\ Forall WF_reg (chip_regs ch).

Definition WF_bank (bk : RAMBank) : Prop :=
  length (bank_chips bk) = NCHIPS /\ Forall WF_chip (bank_chips bk).

Definition WF (s : Intel4004State) : Prop :=
  length (regs s) = 16 /\
  length (ram_sys s) = NBANKS /\
  Forall WF_bank (ram_sys s) /\
  length (out_ports s) = 16 /\
  length (in_ports s) = 16 /\
  length (port_dirs s) = 16 /\
  length (rom s) = 4096.

(** Tactic to destruct WF into its 7 named components. *)
Ltac destruct_WF H :=
  destruct H as [HlenR [HsysLen [HsysFor [HoutLen [HinLen [HdirLen HromLen]]]]]].

(** Tactic for exhaustive case analysis on sub-16 values. *)
Ltac nibble_cases v :=
  do 16 (destruct v as [|v]; [simpl; try reflexivity; try lia |]); lia.

(** Proves empty RAM register satisfies WF_reg. *)
Lemma empty_reg_WF : WF_reg empty_reg.
Proof. split; apply repeat_length. Qed.

(** Proves empty RAM chip satisfies WF_chip. *)
Lemma empty_chip_WF : WF_chip empty_chip.
Proof.
  split; [apply repeat_length |].
  apply Forall_repeat. exact empty_reg_WF.
Qed.

(** Proves empty RAM bank satisfies WF_bank. *)
Lemma empty_bank_WF : WF_bank empty_bank.
Proof.
  split; [apply repeat_length |].
  apply Forall_repeat. exact empty_chip_WF.
Qed.

(** Proves the initial state satisfies WF, for any 16-entry direction mask. *)
Lemma init_state_dirs_WF : forall dirs,
  length dirs = 16 -> WF (init_state_dirs dirs).
Proof.
  intros dirs Hd.
  unfold WF, init_state_dirs, empty_sys.
  cbn [regs ram_sys out_ports in_ports port_dirs rom].
  repeat split; try (apply repeat_length); try exact Hd.
  apply Forall_repeat. exact empty_bank_WF.
Qed.

Lemma init_state_WF : WF init_state.
Proof. apply init_state_dirs_WF. apply repeat_length. Qed.

(** Counterexample: a state with the wrong register count violates WF. *)
Definition bad_state_wrong_reg_count : Intel4004State :=
  with_regs (repeat (nib 0) 8) init_state.

Lemma bad_state_wrong_reg_count_not_WF : ~ WF bad_state_wrong_reg_count.
Proof.
  intros [Hlen _].
  cbn [regs with_regs bad_state_wrong_reg_count] in Hlen.
  rewrite repeat_length in Hlen. discriminate.
Qed.

(** Counterexample: a state with a short ROM violates WF. *)
Definition bad_state_short_rom : Intel4004State :=
  with_rom (repeat (byt 0) 16) init_state.

Lemma bad_state_short_rom_not_WF : ~ WF bad_state_short_rom.
Proof.
  intros H. destruct_WF H.
  cbn [rom with_rom bad_state_short_rom] in HromLen.
  rewrite repeat_length in HromLen. discriminate.
Qed.

(** Proves reset_state preserves WF. *)
Lemma reset_state_WF : forall s, WF s -> WF (reset_state s).
Proof.
  intros s H. destruct_WF H.
  unfold WF, reset_state.
  cbn [regs ram_sys out_ports in_ports port_dirs rom].
  repeat split; try assumption; apply repeat_length.
Qed.

(** Reset clears all volatile CPU state: accumulator, carry, index
    registers, the whole address ring, the DCL and SRC latches, and the
    programmer registers. *)
Lemma reset_state_clears_volatile : forall s,
  let s' := reset_state s in
  acc s' = nib 0 /\
  carry s' = false /\
  pc s' = adr 0 /\
  stk1 s' = adr 0 /\ stk2 s' = adr 0 /\ stk3 s' = adr 0 /\
  regs s' = repeat (nib 0) 16 /\
  cm_code s' = w3 0 /\
  sel_ram s' = mkRAMSel (w2 0) (w2 0) (nib 0) /\
  sel_rom s' = nib 0 /\
  prom_addr s' = adr 0 /\
  prom_enable s' = false /\
  prom_latch s' = latch_init.
Proof. intros s. repeat split. Qed.

(** Reset preserves everything outside the CPU: memory, port latches and
    pins, the direction mask, and the TEST level. *)
Lemma reset_state_preserves_memory : forall s,
  let s' := reset_state s in
  ram_sys s' = ram_sys s /\
  rom s' = rom s /\
  out_ports s' = out_ports s /\
  in_ports s' = in_ports s /\
  port_dirs s' = port_dirs s /\
  test_pin s' = test_pin s.
Proof. intros s. repeat split. Qed.

(** The complete CPU-scope reset specification. *)
Theorem reset_specification : forall s, WF s ->
  WF (reset_state s) /\
  acc (reset_state s) = nib 0 /\
  carry (reset_state s) = false /\
  pc (reset_state s) = adr 0 /\
  stk1 (reset_state s) = adr 0 /\
  stk2 (reset_state s) = adr 0 /\
  stk3 (reset_state s) = adr 0 /\
  regs (reset_state s) = repeat (nib 0) 16 /\
  ram_sys (reset_state s) = ram_sys s /\
  rom (reset_state s) = rom s.
Proof.
  intros s HWF.
  split. { apply reset_state_WF. exact HWF. }
  repeat split.
Qed.

(* ==================== Multi-bank write structure ===================== *)

(** Structural preservation for the multi-bank write paths. *)

Lemma WF_reg_upd_main : forall rg i v,
  WF_reg rg -> WF_reg (upd_main_in_reg rg i v).
Proof.
  intros rg i v [H1 H2].
  split; cbn; [rewrite update_nth_length|]; assumption.
Qed.

Lemma WF_reg_upd_stat : forall rg i v,
  WF_reg rg -> WF_reg (upd_stat_in_reg rg i v).
Proof.
  intros rg i v [H1 H2].
  split; cbn; [|rewrite update_nth_length]; assumption.
Qed.

Lemma WF_chip_upd_reg : forall ch r rg,
  WF_chip ch -> WF_reg rg -> WF_chip (upd_reg_in_chip ch r rg).
Proof.
  intros ch r rg [H1 H2] Hrg.
  split; cbn.
  - rewrite update_nth_length. assumption.
  - apply Forall_update_nth; assumption.
Qed.

Lemma WF_chip_upd_port : forall ch v,
  WF_chip ch -> WF_chip (upd_port_in_chip ch v).
Proof.
  intros ch v [H1 H2]. split; cbn; assumption.
Qed.

Lemma WF_bank_upd_chip : forall bk c ch,
  WF_bank bk -> WF_chip ch -> WF_bank (upd_chip_in_bank bk c ch).
Proof.
  intros bk c ch [H1 H2] Hch.
  split; cbn.
  - rewrite update_nth_length. assumption.
  - apply Forall_update_nth; assumption.
Qed.

(** Extracting substructures of a well-formed system. *)
Lemma WF_bank_from_sys : forall sys b,
  Forall WF_bank sys -> WF_bank (get_bank_sys sys b).
Proof.
  intros sys b Hall.
  unfold get_bank_sys.
  destruct (Nat.lt_ge_cases b (length sys)) as [Hb | Hb].
  - rewrite Forall_forall in Hall. apply Hall. apply nth_In. exact Hb.
  - rewrite nth_overflow by lia. exact empty_bank_WF.
Qed.

Lemma WF_chip_from_bank : forall bk c,
  WF_bank bk -> WF_chip (get_chip bk c).
Proof.
  intros bk c [Hlen Hall].
  unfold get_chip.
  destruct (Nat.lt_ge_cases c (length (bank_chips bk))) as [Hc | Hc].
  - rewrite Forall_forall in Hall. apply Hall. apply nth_In. exact Hc.
  - rewrite nth_overflow by lia. exact empty_chip_WF.
Qed.

Lemma WF_reg_from_chip : forall ch r,
  WF_chip ch -> WF_reg (get_regRAM ch r).
Proof.
  intros ch r [Hlen Hall].
  unfold get_regRAM.
  destruct (Nat.lt_ge_cases r (length (chip_regs ch))) as [Hr | Hr].
  - rewrite Forall_forall in Hall. apply Hall. apply nth_In. exact Hr.
  - rewrite nth_overflow by lia. exact empty_reg_WF.
Qed.

(** One-bank writes preserve system length and bank well-formedness. *)
Lemma write_main_bank_length : forall sys sel b v,
  length (write_main_bank sys sel b v) = length sys.
Proof. intros. apply update_nth_length. Qed.

Lemma write_main_bank_WF : forall sys sel b v,
  Forall WF_bank sys -> Forall WF_bank (write_main_bank sys sel b v).
Proof.
  intros sys sel b v Hall.
  unfold write_main_bank. cbv zeta.
  apply Forall_update_nth; [assumption |].
  apply WF_bank_upd_chip; [apply WF_bank_from_sys; assumption |].
  apply WF_chip_upd_reg;
    [apply WF_chip_from_bank; apply WF_bank_from_sys; assumption |].
  apply WF_reg_upd_main.
  apply WF_reg_from_chip. apply WF_chip_from_bank.
  apply WF_bank_from_sys. assumption.
Qed.

Lemma write_stat_bank_length : forall sys sel idx b v,
  length (write_stat_bank sys sel idx b v) = length sys.
Proof. intros. apply update_nth_length. Qed.

Lemma write_stat_bank_WF : forall sys sel idx b v,
  Forall WF_bank sys -> Forall WF_bank (write_stat_bank sys sel idx b v).
Proof.
  intros sys sel idx b v Hall.
  unfold write_stat_bank. cbv zeta.
  apply Forall_update_nth; [assumption |].
  apply WF_bank_upd_chip; [apply WF_bank_from_sys; assumption |].
  apply WF_chip_upd_reg;
    [apply WF_chip_from_bank; apply WF_bank_from_sys; assumption |].
  apply WF_reg_upd_stat.
  apply WF_reg_from_chip. apply WF_chip_from_bank.
  apply WF_bank_from_sys. assumption.
Qed.

Lemma write_port_bank_length : forall sys sel b v,
  length (write_port_bank sys sel b v) = length sys.
Proof. intros. apply update_nth_length. Qed.

Lemma write_port_bank_WF : forall sys sel b v,
  Forall WF_bank sys -> Forall WF_bank (write_port_bank sys sel b v).
Proof.
  intros sys sel b v Hall.
  unfold write_port_bank. cbv zeta.
  apply Forall_update_nth; [assumption |].
  apply WF_bank_upd_chip; [apply WF_bank_from_sys; assumption |].
  apply WF_chip_upd_port.
  apply WF_chip_from_bank. apply WF_bank_from_sys. assumption.
Qed.

(** Multi-bank writes preserve system length and bank well-formedness. *)
Lemma write_main_banks_length : forall bs sys sel v,
  length (write_main_banks sys sel bs v) = length sys.
Proof.
  induction bs as [|b rest IH]; intros sys sel v; cbn [write_main_banks write_stat_banks write_port_banks].
  - reflexivity.
  - rewrite IH. apply write_main_bank_length.
Qed.

Lemma write_main_banks_WF : forall bs sys sel v,
  Forall WF_bank sys -> Forall WF_bank (write_main_banks sys sel bs v).
Proof.
  induction bs as [|b rest IH]; intros sys sel v Hall; cbn [write_main_banks write_stat_banks write_port_banks].
  - exact Hall.
  - apply IH. apply write_main_bank_WF. exact Hall.
Qed.

Lemma write_stat_banks_length : forall bs sys sel idx v,
  length (write_stat_banks sys sel idx bs v) = length sys.
Proof.
  induction bs as [|b rest IH]; intros sys sel idx v; cbn [write_main_banks write_stat_banks write_port_banks].
  - reflexivity.
  - rewrite IH. apply write_stat_bank_length.
Qed.

Lemma write_stat_banks_WF : forall bs sys sel idx v,
  Forall WF_bank sys -> Forall WF_bank (write_stat_banks sys sel idx bs v).
Proof.
  induction bs as [|b rest IH]; intros sys sel idx v Hall; cbn [write_main_banks write_stat_banks write_port_banks].
  - exact Hall.
  - apply IH. apply write_stat_bank_WF. exact Hall.
Qed.

Lemma write_port_banks_length : forall bs sys sel v,
  length (write_port_banks sys sel bs v) = length sys.
Proof.
  induction bs as [|b rest IH]; intros sys sel v; cbn [write_main_banks write_stat_banks write_port_banks].
  - reflexivity.
  - rewrite IH. apply write_port_bank_length.
Qed.

Lemma write_port_banks_WF : forall bs sys sel v,
  Forall WF_bank sys -> Forall WF_bank (write_port_banks sys sel bs v).
Proof.
  induction bs as [|b rest IH]; intros sys sel v Hall; cbn [write_main_banks write_stat_banks write_port_banks].
  - exact Hall.
  - apply IH. apply write_port_bank_WF. exact Hall.
Qed.

(* ==================== Multi-bank read-after-write ==================== *)

(** The written bank of a one-bank write. *)
Lemma write_main_bank_bank : forall sys sel b v,
  b < length sys ->
  get_bank_sys (write_main_bank sys sel b v) b
  = upd_chip_in_bank (get_bank_sys sys b) (wval (sel_chip sel))
      (upd_reg_in_chip (get_chip (get_bank_sys sys b) (wval (sel_chip sel)))
         (wval (sel_reg sel))
         (upd_main_in_reg
            (get_regRAM (get_chip (get_bank_sys sys b) (wval (sel_chip sel)))
               (wval (sel_reg sel)))
            (wval (sel_char sel)) v)).
Proof.
  intros sys sel b v Hb.
  unfold write_main_bank. cbv zeta.
  unfold get_bank_sys at 1.
  apply nth_update_nth_eq. exact Hb.
Qed.

(** Writes at other banks are invisible. *)
Lemma write_main_bank_other : forall sys sel b b' v,
  b' <> b ->
  get_bank_sys (write_main_bank sys sel b v) b' = get_bank_sys sys b'.
Proof.
  intros sys sel b b' v Hne.
  unfold write_main_bank, get_bank_sys. cbv zeta.
  apply nth_update_nth_neq. exact Hne.
Qed.

Lemma write_main_banks_other : forall bs sys sel b' v,
  ~ In b' bs ->
  get_bank_sys (write_main_banks sys sel bs v) b' = get_bank_sys sys b'.
Proof.
  induction bs as [|b rest IH]; intros sys sel b' v Hnin; cbn [write_main_banks write_stat_banks write_port_banks].
  - reflexivity.
  - rewrite IH by (intro Hin; apply Hnin; right; exact Hin).
    apply write_main_bank_other.
    intro Heq. apply Hnin. left. congruence.
Qed.

Lemma read_after_main_banks_other : forall bs sys sel b v,
  ~ In b bs ->
  read_main_bank (write_main_banks sys sel bs v) sel b = read_main_bank sys sel b.
Proof.
  intros bs sys sel b v Hnin. unfold read_main_bank.
  rewrite write_main_banks_other by exact Hnin. reflexivity.
Qed.

(** A written bank reads back the written value. *)
Lemma write_main_bank_hit : forall sys sel b v,
  b < length sys ->
  Forall WF_bank sys ->
  read_main_bank (write_main_bank sys sel b v) sel b = v.
Proof.
  intros sys sel b v Hb Hall.
  pose proof (WF_bank_from_sys sys b Hall) as Hbk.
  pose proof (WF_chip_from_bank _ (wval (sel_chip sel)) Hbk) as Hch.
  pose proof (WF_reg_from_chip _ (wval (sel_reg sel)) Hch) as Hrg.
  unfold read_main_bank.
  rewrite write_main_bank_bank by exact Hb.
  rewrite get_chip_upd_chip_in_bank
    by (destruct Hbk as [Hl _]; rewrite Hl;
        pose proof (w2_lt4 (sel_chip sel)); unfold NCHIPS; lia).
  rewrite get_regRAM_upd_reg_in_chip
    by (destruct Hch as [Hl _]; rewrite Hl;
        pose proof (w2_lt4 (sel_reg sel)); unfold NREGS; lia).
  apply get_main_upd_main_in_reg.
  destruct Hrg as [Hl _]. rewrite Hl.
  pose proof (nib_lt16 (sel_char sel)). unfold NMAIN. lia.
Qed.

(** Every bank in a duplicate-free line set reads back the written value. *)
Lemma write_main_banks_hit : forall bs sys sel v b,
  NoDup bs ->
  In b bs ->
  Forall (fun x => x < length sys) bs ->
  Forall WF_bank sys ->
  read_main_bank (write_main_banks sys sel bs v) sel b = v.
Proof.
  induction bs as [|bh rest IH]; intros sys sel v b Hnd Hin Hlen Hall.
  - destruct Hin.
  - inversion Hnd as [|? ? Hnin Hnd']; subst.
    inversion Hlen as [|? ? Hbh Hlen']; subst.
    cbn [write_main_banks write_stat_banks write_port_banks].
    destruct Hin as [Heq | Hin].
    + subst bh.
      rewrite read_after_main_banks_other by exact Hnin.
      apply write_main_bank_hit; assumption.
    + apply IH; try assumption.
      * eapply Forall_impl; [| exact Hlen'].
        intros x Hx. rewrite write_main_bank_length. exact Hx.
      * apply write_main_bank_WF; assumption.
Qed.

(** Status-write analogues. *)
Lemma write_stat_bank_bank : forall sys sel idx b v,
  b < length sys ->
  get_bank_sys (write_stat_bank sys sel idx b v) b
  = upd_chip_in_bank (get_bank_sys sys b) (wval (sel_chip sel))
      (upd_reg_in_chip (get_chip (get_bank_sys sys b) (wval (sel_chip sel)))
         (wval (sel_reg sel))
         (upd_stat_in_reg
            (get_regRAM (get_chip (get_bank_sys sys b) (wval (sel_chip sel)))
               (wval (sel_reg sel)))
            idx v)).
Proof.
  intros sys sel idx b v Hb.
  unfold write_stat_bank. cbv zeta.
  unfold get_bank_sys at 1.
  apply nth_update_nth_eq. exact Hb.
Qed.

Lemma write_stat_bank_other : forall sys sel idx b b' v,
  b' <> b ->
  get_bank_sys (write_stat_bank sys sel idx b v) b' = get_bank_sys sys b'.
Proof.
  intros sys sel idx b b' v Hne.
  unfold write_stat_bank, get_bank_sys. cbv zeta.
  apply nth_update_nth_neq. exact Hne.
Qed.

Lemma write_stat_banks_other : forall bs sys sel idx b' v,
  ~ In b' bs ->
  get_bank_sys (write_stat_banks sys sel idx bs v) b' = get_bank_sys sys b'.
Proof.
  induction bs as [|b rest IH]; intros sys sel idx b' v Hnin; cbn [write_main_banks write_stat_banks write_port_banks].
  - reflexivity.
  - rewrite IH by (intro Hin; apply Hnin; right; exact Hin).
    apply write_stat_bank_other.
    intro Heq. apply Hnin. left. congruence.
Qed.

Lemma read_after_stat_banks_other : forall bs sys sel idx b v,
  ~ In b bs ->
  read_stat_bank (write_stat_banks sys sel idx bs v) sel idx b
  = read_stat_bank sys sel idx b.
Proof.
  intros bs sys sel idx b v Hnin. unfold read_stat_bank.
  rewrite write_stat_banks_other by exact Hnin. reflexivity.
Qed.

Lemma write_stat_bank_hit : forall sys sel idx b v,
  idx < 4 ->
  b < length sys ->
  Forall WF_bank sys ->
  read_stat_bank (write_stat_bank sys sel idx b v) sel idx b = v.
Proof.
  intros sys sel idx b v Hidx Hb Hall.
  pose proof (WF_bank_from_sys sys b Hall) as Hbk.
  pose proof (WF_chip_from_bank _ (wval (sel_chip sel)) Hbk) as Hch.
  pose proof (WF_reg_from_chip _ (wval (sel_reg sel)) Hch) as Hrg.
  unfold read_stat_bank.
  rewrite write_stat_bank_bank by exact Hb.
  rewrite get_chip_upd_chip_in_bank
    by (destruct Hbk as [Hl _]; rewrite Hl;
        pose proof (w2_lt4 (sel_chip sel)); unfold NCHIPS; lia).
  rewrite get_regRAM_upd_reg_in_chip
    by (destruct Hch as [Hl _]; rewrite Hl;
        pose proof (w2_lt4 (sel_reg sel)); unfold NREGS; lia).
  apply get_stat_upd_stat_in_reg.
  destruct Hrg as [_ Hl]. rewrite Hl. unfold NSTAT. lia.
Qed.

Lemma write_stat_banks_hit : forall bs sys sel idx v b,
  idx < 4 ->
  NoDup bs ->
  In b bs ->
  Forall (fun x => x < length sys) bs ->
  Forall WF_bank sys ->
  read_stat_bank (write_stat_banks sys sel idx bs v) sel idx b = v.
Proof.
  induction bs as [|bh rest IH]; intros sys sel idx v b Hidx Hnd Hin Hlen Hall.
  - destruct Hin.
  - inversion Hnd as [|? ? Hnin Hnd']; subst.
    inversion Hlen as [|? ? Hbh Hlen']; subst.
    cbn [write_main_banks write_stat_banks write_port_banks].
    destruct Hin as [Heq | Hin].
    + subst bh.
      rewrite read_after_stat_banks_other by exact Hnin.
      apply write_stat_bank_hit; assumption.
    + apply IH; try assumption.
      * eapply Forall_impl; [| exact Hlen'].
        intros x Hx. rewrite write_stat_bank_length. exact Hx.
      * apply write_stat_bank_WF; assumption.
Qed.

(** Port-write analogues: the written port, and untouched banks. *)
Definition read_port_bank (sys : list RAMBank) (sel : RAMSel) (b : nat) : nibble :=
  chip_port (get_chip (get_bank_sys sys b) (wval (sel_chip sel))).

Lemma write_port_bank_bank : forall sys sel b v,
  b < length sys ->
  get_bank_sys (write_port_bank sys sel b v) b
  = upd_chip_in_bank (get_bank_sys sys b) (wval (sel_chip sel))
      (upd_port_in_chip (get_chip (get_bank_sys sys b) (wval (sel_chip sel))) v).
Proof.
  intros sys sel b v Hb.
  unfold write_port_bank. cbv zeta.
  unfold get_bank_sys at 1.
  apply nth_update_nth_eq. exact Hb.
Qed.

Lemma write_port_bank_other : forall sys sel b b' v,
  b' <> b ->
  get_bank_sys (write_port_bank sys sel b v) b' = get_bank_sys sys b'.
Proof.
  intros sys sel b b' v Hne.
  unfold write_port_bank, get_bank_sys. cbv zeta.
  apply nth_update_nth_neq. exact Hne.
Qed.

Lemma write_port_banks_other : forall bs sys sel b' v,
  ~ In b' bs ->
  get_bank_sys (write_port_banks sys sel bs v) b' = get_bank_sys sys b'.
Proof.
  induction bs as [|b rest IH]; intros sys sel b' v Hnin; cbn [write_port_banks].
  - reflexivity.
  - rewrite IH by (intro Hin; apply Hnin; right; exact Hin).
    apply write_port_bank_other.
    intro Heq. apply Hnin. left. congruence.
Qed.

Lemma read_after_port_banks_other : forall bs sys sel b v,
  ~ In b bs ->
  read_port_bank (write_port_banks sys sel bs v) sel b = read_port_bank sys sel b.
Proof.
  intros bs sys sel b v Hnin. unfold read_port_bank.
  rewrite write_port_banks_other by exact Hnin. reflexivity.
Qed.

Lemma write_port_bank_hit : forall sys sel b v,
  b < length sys ->
  Forall WF_bank sys ->
  read_port_bank (write_port_bank sys sel b v) sel b = v.
Proof.
  intros sys sel b v Hb Hall.
  pose proof (WF_bank_from_sys sys b Hall) as Hbk.
  unfold read_port_bank.
  rewrite write_port_bank_bank by exact Hb.
  rewrite get_chip_upd_chip_in_bank
    by (destruct Hbk as [Hl _]; rewrite Hl;
        pose proof (w2_lt4 (sel_chip sel)); unfold NCHIPS; lia).
  reflexivity.
Qed.

(** Every bank in a duplicate-free line set exposes the written port value. *)
Lemma write_port_banks_hit : forall bs sys sel v b,
  NoDup bs ->
  In b bs ->
  Forall (fun x => x < length sys) bs ->
  Forall WF_bank sys ->
  read_port_bank (write_port_banks sys sel bs v) sel b = v.
Proof.
  induction bs as [|bh rest IH]; intros sys sel v b Hnd Hin Hlen Hall.
  - destruct Hin.
  - inversion Hnd as [|? ? Hnin Hnd']; subst.
    inversion Hlen as [|? ? Hbh Hlen']; subst.
    cbn [write_port_banks].
    destruct Hin as [Heq | Hin].
    + subst bh.
      rewrite read_after_port_banks_other by exact Hnin.
      apply write_port_bank_hit; assumption.
    + apply IH; try assumption.
      * eapply Forall_impl; [| exact Hlen'].
        intros x Hx. rewrite write_port_bank_length. exact Hx.
      * apply write_port_bank_WF; assumption.
Qed.

(** Port writes never touch the character arrays: every chip's register
    list is preserved at every bank. *)
Lemma write_port_bank_chip_regs : forall sys sel b v b' c,
  Forall WF_bank sys ->
  chip_regs (get_chip (get_bank_sys (write_port_bank sys sel b v) b') c)
  = chip_regs (get_chip (get_bank_sys sys b') c).
Proof.
  intros sys sel b v b' c Hall.
  destruct (Nat.eq_dec b' b) as [-> | Hne].
  2:{ rewrite write_port_bank_other by exact Hne. reflexivity. }
  destruct (Nat.lt_ge_cases b (length sys)) as [Hb | Hb].
  2:{ unfold write_port_bank, get_bank_sys. cbv zeta.
      rewrite update_nth_out_of_bounds by exact Hb. reflexivity. }
  rewrite write_port_bank_bank by exact Hb.
  pose proof (WF_bank_from_sys sys b Hall) as Hbk.
  destruct (Nat.eq_dec c (wval (sel_chip sel))) as [-> | Hcne].
  - rewrite get_chip_upd_chip_in_bank
      by (destruct Hbk as [Hl _]; rewrite Hl;
          pose proof (w2_lt4 (sel_chip sel)); unfold NCHIPS; lia).
    reflexivity.
  - rewrite get_chip_upd_chip_in_bank_neq by congruence.
    reflexivity.
Qed.

Lemma write_port_banks_chip_regs : forall bs sys sel v b' c,
  Forall WF_bank sys ->
  chip_regs (get_chip (get_bank_sys (write_port_banks sys sel bs v) b') c)
  = chip_regs (get_chip (get_bank_sys sys b') c).
Proof.
  induction bs as [|b rest IH]; intros sys sel v b' c Hall; cbn [write_port_banks].
  - reflexivity.
  - rewrite IH by (apply write_port_bank_WF; exact Hall).
    apply write_port_bank_chip_regs. exact Hall.
Qed.

(** Agreement reads: a defined read means every selected bank drives it. *)
Lemma agree_read_some : forall reads v,
  agree_read reads = Some v ->
  forall x, In x reads -> x = v.
Proof.
  intros reads v H x Hin.
  destruct reads as [|v0 rest]; [destruct Hin |].
  cbn [agree_read] in H.
  destruct (forallb (fun x0 => wval x0 =? wval v0) rest) eqn:Ef; [|discriminate].
  injection H as <-.
  destruct Hin as [-> | Hin]; [reflexivity |].
  rewrite forallb_forall in Ef.
  specialize (Ef x Hin). apply Nat.eqb_eq in Ef.
  apply word_eq. exact Ef.
Qed.

(** Unanimity makes the read defined. *)
Lemma agree_read_all : forall reads v,
  reads <> [] ->
  (forall x, In x reads -> x = v) ->
  agree_read reads = Some v.
Proof.
  intros reads v Hne Hall.
  destruct reads as [|v0 rest]; [congruence |].
  assert (Hv0 : v0 = v) by (apply Hall; left; reflexivity).
  cbn [agree_read].
  assert (Ef : forallb (fun x => wval x =? wval v0) rest = true).
  { apply forallb_forall. intros x Hin.
    apply Nat.eqb_eq. rewrite (Hall x (or_intror Hin)). rewrite Hv0. reflexivity. }
  rewrite Ef. rewrite Hv0. reflexivity.
Qed.

(** A singleton read set is always defined: single-line DCL codes never hit
    the undefined case. *)
Lemma agree_read_single : forall v, agree_read [v] = Some v.
Proof. intro v. reflexivity. Qed.

(* ====================== Execute preserves WF ======================== *)

Ltac wf_step_solve :=
  unfold WF;
  repeat split;
  cbn [regs ram_sys out_ports in_ports port_dirs rom
       with_acc with_regs with_carry with_pc with_ram with_cm with_select
       with_out_ports with_in_ports with_rom with_test with_prom_addr
       with_prom_enable with_prom_latch pc_bump ring_push ring_pop
       set_reg set_reg_pair];
  repeat rewrite update_nth_length;
  try assumption.

(** Main preservation theorem: execute preserves WF for every instruction. *)
Theorem execute_preserves_WF :
  forall s i, WF s -> WF (execute s i).
Proof.
  intros s i HWF.
  assert (H := HWF). destruct_WF H.
  destruct i; cbn [execute].

  (* NOP *) - wf_step_solve.
  (* JCN *)
  - match goal with |- WF (if ?b then _ else _) => destruct b end; wf_step_solve.
  (* FIM *) - wf_step_solve.
  (* SRC *) - wf_step_solve.
  (* FIN *) - wf_step_solve.
  (* JIN *) - wf_step_solve.
  (* JUN *) - wf_step_solve.
  (* JMS *) - wf_step_solve.
  (* INC *) - wf_step_solve.
  (* ISZ *)
  - match goal with |- WF (if ?b then _ else _) => destruct b end; wf_step_solve.
  (* ADD *) - wf_step_solve.
  (* SUB *) - wf_step_solve.
  (* LD *) - wf_step_solve.
  (* XCH *) - wf_step_solve.
  (* BBL *) - wf_step_solve.
  (* LDM *) - wf_step_solve.
  (* WRM *)
  - wf_step_solve.
    + rewrite write_main_banks_length. assumption.
    + apply write_main_banks_WF. assumption.
  (* WMP *)
  - wf_step_solve.
    + rewrite write_port_banks_length. assumption.
    + apply write_port_banks_WF. assumption.
  (* WRR *) - wf_step_solve.
  (* WPM *)
  - destruct (prom_enable s); [destruct (pl_expect_low (prom_latch s)) |];
      wf_step_solve.
  (* WR0 *)
  - wf_step_solve.
    + rewrite write_stat_banks_length. assumption.
    + apply write_stat_banks_WF. assumption.
  (* WR1 *)
  - wf_step_solve.
    + rewrite write_stat_banks_length. assumption.
    + apply write_stat_banks_WF. assumption.
  (* WR2 *)
  - wf_step_solve.
    + rewrite write_stat_banks_length. assumption.
    + apply write_stat_banks_WF. assumption.
  (* WR3 *)
  - wf_step_solve.
    + rewrite write_stat_banks_length. assumption.
    + apply write_stat_banks_WF. assumption.
  (* SBM *) - wf_step_solve.
  (* RDM *) - wf_step_solve.
  (* RDR *) - wf_step_solve.
  (* ADM *) - wf_step_solve.
  (* RD0 *) - wf_step_solve.
  (* RD1 *) - wf_step_solve.
  (* RD2 *) - wf_step_solve.
  (* RD3 *) - wf_step_solve.
  (* CLB *) - wf_step_solve.
  (* CLC *) - wf_step_solve.
  (* IAC *) - wf_step_solve.
  (* CMC *) - wf_step_solve.
  (* CMA *) - wf_step_solve.
  (* RAL *) - wf_step_solve.
  (* RAR *) - wf_step_solve.
  (* TCC *) - wf_step_solve.
  (* DAC *) - wf_step_solve.
  (* TCS *) - wf_step_solve.
  (* STC *) - wf_step_solve.
  (* DAA *) - wf_step_solve.
  (* KBP *) - wf_step_solve.
  (* DCL *) - wf_step_solve.
Qed.

(** Every ROM byte after any instruction is a byte value, by construction. *)
Theorem memory_safety : forall s i,
  Forall (fun b => wval b < 256) (rom (execute s i)).
Proof.
  intros s i.
  apply Forall_forall. intros b _. apply byte_lt256.
Qed.

(** The program counter never leaves the 12-bit address space: bounds by
    construction. *)
Theorem no_arbitrary_jumps : forall s i, wval (pc (execute s i)) < 4096.
Proof. intros s i. apply addr12_lt4096. Qed.

(** Proves single step (fetch-decode-execute) preserves WF. *)
Theorem step_preserves_WF : forall s, WF s -> WF (step s).
Proof.
  intros s Hwf. unfold step.
  apply execute_preserves_WF. exact Hwf.
Qed.

(** Proves n-step execution preserves WF. *)
Theorem steps_preserve_WF : forall n s, WF s -> WF (steps n s).
Proof.
  induction n; simpl; intros; auto. apply IHn. apply step_preserves_WF; assumption.
Qed.

(* ============== Executing an instruction list (program big-step) ==== *)

Fixpoint exec_program (prog : list Instruction) (s : Intel4004State) : Intel4004State :=
  match prog with
  | [] => s
  | i :: rest => exec_program rest (execute s i)
  end.

Lemma exec_program_app : forall prog1 prog2 s,
  exec_program (prog1 ++ prog2) s = exec_program prog2 (exec_program prog1 s).
Proof.
  induction prog1; intros prog2 s.
  - simpl. reflexivity.
  - simpl. rewrite IHprog1. reflexivity.
Qed.

Lemma exec_program_preserves_WF : forall prog s,
  WF s -> WF (exec_program prog s).
Proof.
  induction prog as [|i rest IH]; intros s HWF; cbn.
  - exact HWF.
  - apply IH. apply execute_preserves_WF. exact HWF.
Qed.

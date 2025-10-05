(* ===================================================================== *)
(*  Intel 4004 Microprocessor + MCS-4 RAM/ROM I/O Formalization in Coq   *)
(* ===================================================================== *)

(* ======================= Imports and Setup ========================== *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Lia.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ===================== Basic bit-width types ======================== *)

Definition nibble := nat.
Definition nibble_of_nat (n : nat) : nibble := n mod 16.

Definition byte := nat.
Definition byte_of_nat (n : nat) : byte := n mod 256.

Definition addr12 := nat.
Definition addr12_of_nat (n : nat) : addr12 := n mod 4096.

Lemma addr12_bound : forall n, addr12_of_nat n < 4096.
Proof.
  intro n. unfold addr12_of_nat. apply Nat.mod_upper_bound. lia.
Qed.

Lemma nibble_lt16 : forall n, nibble_of_nat n < 16.
Proof. intro n. unfold nibble_of_nat. apply Nat.mod_upper_bound. lia. Qed.

(* ========================= List helpers ============================= *)

Definition update_nth {A} (n : nat) (x : A) (l : list A) : list A :=
  if n <? length l
  then firstn n l ++ x :: skipn (S n) l
  else l.

Lemma update_nth_length : forall A (l : list A) n x,
  length (update_nth n x l) = length l.
Proof.
  intros A l n x.
  revert n.
  induction l as [|h t IH]; intro n.
  - unfold update_nth. simpl.
    destruct (n <? 0) eqn:E; reflexivity.
  - unfold update_nth. simpl length at 2.
    destruct n.
    + vm_compute. reflexivity.
    + change (S n <? S (length t)) with (n <? length t).
      destruct (n <? length t) eqn:En.
      * change (firstn (S n) (h :: t)) with (h :: firstn n t).
        change (skipn (S (S n)) (h :: t)) with (skipn (S n) t).
        change ((h :: firstn n t) ++ x :: skipn (S n) t) with
               (h :: (firstn n t ++ x :: skipn (S n) t)).
        simpl length.
        f_equal.
        specialize (IH n). unfold update_nth in IH.
        rewrite En in IH. exact IH.
      * reflexivity.
Qed.

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

Lemma nth_Forall_lt : forall (l:list nat) d n k,
  Forall (fun x => x < k) l -> d < k -> nth n l d < k.
Proof.
  intros l d n k Hall Hd. revert n.
  induction Hall; intros [|n]; simpl; auto.
Qed.

Lemma Forall_repeat : forall A (P : A -> Prop) x n, P x -> Forall P (repeat x n).
Proof.
  intros A P x n H. induction n; simpl; constructor; auto.
Qed.

Lemma nth_in_or_default : forall A (n : nat) (l : list A) (d : A),
  {In (nth n l d) l} + {nth n l d = d}.
Proof.
  intros A n l d. revert n.
  induction l; intro n.
  - right. destruct n; reflexivity.
  - destruct n.
    + left. simpl. left. reflexivity.
    + simpl. destruct (IHl n) as [H|H].
      * left. right. assumption.
      * right. assumption.
Qed.

(* ======================== 4002 RAM structure ======================== *)

Record RAMReg := mkRAMReg {
  reg_main   : list nibble;  (* 16 main characters *)
  reg_status : list nibble   (* 4 status characters S0..S3 *)
}.

Record RAMChip := mkRAMChip {
  chip_regs  : list RAMReg;  (* 4 registers *)
  chip_port  : nibble        (* 4-bit output port *)
}.

Record RAMBank := mkRAMBank {
  bank_chips : list RAMChip  (* 4 chips per bank *)
}.

(* Selection latched by SRC; bank is selected by DCL separately. *)
Record RAMSel := mkRAMSel {
  sel_chip : nat;   (* 0..3 *)
  sel_reg  : nat;   (* 0..3 *)
  sel_char : nat    (* 0..15 *)
}.

(* ============================ State ================================= *)

Record Intel4004State := mkState {
  acc       : nibble;           (* 4-bit accumulator *)
  regs      : list nibble;      (* 16 4-bit registers R0..R15 *)
  carry     : bool;             (* carry/link flag *)
  pc        : addr12;           (* 12-bit program counter *)
  stack     : list addr12;      (* 3-level return stack *)
  ram_sys   : list RAMBank;     (* 4 banks × 4 chips × 4 regs × (16 main + 4 status) *)
  cur_bank  : nat;              (* 0..3, selected by DCL *)
  sel_ram   : RAMSel;           (* last RAM address sent by SRC (chip,reg,char) *)
  rom_ports : list nibble;      (* 16 ROM ports (4-bit), selected by last SRC *)
  sel_rom   : nat;              (* 0..15, last ROM port selected by SRC *)
  rom       : list byte;        (* program ROM (bytes) *)
  test_pin  : bool;             (* TEST input (active low in JCN condition) *)
  prog_pulses : nat             (* counts WPM pulses; observable but inert otherwise *)
}.

(* =========================== Registers ============================== *)

Definition get_reg (s : Intel4004State) (r : nat) : nibble :=
  nth r (regs s) 0.

Definition set_reg (s : Intel4004State) (r : nat) (v : nibble) : Intel4004State :=
  let new_regs := update_nth r (nibble_of_nat v) (regs s) in
  mkState (acc s) new_regs (carry s) (pc s) (stack s)
          (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
          (rom s) (test_pin s) (prog_pulses s).

Definition get_reg_pair (s : Intel4004State) (r : nat) : byte :=
  let r_even := r - (r mod 2) in
  let high := get_reg s r_even in
  let low  := get_reg s (r_even + 1) in
  (high * 16) + low.

Definition set_reg_pair (s : Intel4004State) (r : nat) (v : byte) : Intel4004State :=
  let r_even := r - (r mod 2) in
  let high := v / 16 in
  let low  := v mod 16 in
  let s1 := set_reg s r_even high in
  set_reg s1 (r_even + 1) low.

Lemma set_reg_preserves_length : forall s r v,
  length (regs (set_reg s r v)) = length (regs s).
Proof. intros. simpl. apply update_nth_length. Qed.

Lemma set_reg_pair_preserves_length : forall s r v,
  length (regs (set_reg_pair s r v)) = length (regs s).
Proof.
  intros. unfold set_reg_pair.
  rewrite set_reg_preserves_length.
  rewrite set_reg_preserves_length.
  reflexivity.
Qed.

Lemma set_reg_preserves_Forall16 : forall s r v,
  Forall (fun x => x < 16) (regs s) ->
  Forall (fun x => x < 16) (regs (set_reg s r v)).
Proof.
  intros. simpl. eapply Forall_update_nth; eauto. apply nibble_lt16.
Qed.

Lemma set_reg_pair_preserves_Forall16 : forall s r v,
  Forall (fun x => x < 16) (regs s) ->
  Forall (fun x => x < 16) (regs (set_reg_pair s r v)).
Proof.
  intros. unfold set_reg_pair.
  apply set_reg_preserves_Forall16.
  apply set_reg_preserves_Forall16.
  assumption.
Qed.

Lemma nth_reg0_lt16 : forall s n,
  Forall (fun x => x < 16) (regs s) ->
  nth n (regs s) 0 < 16.
Proof. intros. eapply nth_Forall_lt with (k:=16); eauto; lia. Qed.

(* ============================= Stack ================================ *)

Definition push_stack (s : Intel4004State) (addr : addr12) : Intel4004State :=
  let new_stack :=
    match stack s with
    | [] => [addr]
    | [a] => [addr; a]
    | [a; b] => [addr; a; b]
    | a :: b :: c :: _ => [addr; a; b] (* Max 3 levels *)
    end in
  mkState (acc s) (regs s) (carry s) (pc s) new_stack
          (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
          (rom s) (test_pin s) (prog_pulses s).

Definition pop_stack (s : Intel4004State) : (option addr12 * Intel4004State) :=
  match stack s with
  | [] => (None, s)
  | a :: rest =>
      (Some a, mkState (acc s) (regs s) (carry s) (pc s) rest
                       (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                       (rom s) (test_pin s) (prog_pulses s))
  end.

Lemma push_stack_len_le3 : forall s a,
  length (stack (push_stack s a)) <= 3.
Proof. intros s a. unfold push_stack. destruct (stack s) as [|x [|x0 [|x1 l]]]; simpl; lia. Qed.

Lemma pop_stack_len_le3 : forall s x s',
  length (stack s) <= 4 ->
  pop_stack s = (x, s') -> length (stack s') <= 3.
Proof.
  intros s x s' Hlen H. unfold pop_stack in H.
  destruct (stack s) as [|h l] eqn:Es; simpl in H.
  - inversion H; subst. rewrite Es. simpl. auto.
  - inversion H; subst; clear H; simpl.
    destruct l as [|h1 l']; simpl.
    + lia.
    + destruct l' as [|h2 l'']; simpl.
      * lia.
      * destruct l'' as [|h3 l''']; simpl.
        ** lia.
        ** destruct l''' as [|h4 l4].
           --- auto with arith.
           --- exfalso.
               subst. simpl in Hlen. lia.
Qed.

Lemma pop_stack_Forall_addr12 : forall s a s',
  Forall (fun x => x < 4096) (stack s) ->
  pop_stack s = (a, s') ->
  Forall (fun x => x < 4096) (stack s').
Proof.
  intros s a s' H Hp. unfold pop_stack in Hp.
  destruct (stack s) as [|h t] eqn:Es.
  - inversion Hp; subst. simpl. rewrite Es. auto.
  - inversion Hp; subst; simpl. inversion H; subst; auto.
Qed.

(* ============================ ROM =================================== *)

Definition fetch_byte (s : Intel4004State) (addr : addr12) : byte :=
  nth addr (rom s) 0.

Definition pc_inc1 (s : Intel4004State) : addr12 := addr12_of_nat (pc s + 1).
Definition pc_inc2 (s : Intel4004State) : addr12 := addr12_of_nat (pc s + 2).

Definition page_of (p:addr12) := p / 256.
Definition page_base (p:addr12) := (page_of p) * 256.

(* ========================= RAM navigation =========================== *)

(* Constants: 4 banks × 4 chips × 4 regs × (16 main + 4 status) *)
Definition NBANKS := 4.
Definition NCHIPS := 4.
Definition NREGS  := 4.
Definition NMAIN  := 16.
Definition NSTAT  := 4.

(* Safe getters with defaults *)
Definition get_bank (s:Intel4004State) (b:nat) : RAMBank :=
  nth b (ram_sys s) (mkRAMBank (repeat (mkRAMChip (repeat (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)) NREGS) 0) NCHIPS)).

Definition get_chip (bk:RAMBank) (c:nat) : RAMChip :=
  nth c (bank_chips bk) (mkRAMChip (repeat (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)) NREGS) 0).

Definition get_regRAM (ch:RAMChip) (r:nat) : RAMReg :=
  nth r (chip_regs ch) (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)).

Definition get_main (rg:RAMReg) (i:nat) : nibble := nth i (reg_main rg) 0.
Definition get_stat (rg:RAMReg) (i:nat) : nibble := nth i (reg_status rg) 0.

(* Nested updates *)
Definition upd_main_in_reg (rg:RAMReg) (i:nat) (v:nibble) : RAMReg :=
  mkRAMReg (update_nth i (nibble_of_nat v) (reg_main rg)) (reg_status rg).

Definition upd_stat_in_reg (rg:RAMReg) (i:nat) (v:nibble) : RAMReg :=
  mkRAMReg (reg_main rg) (update_nth i (nibble_of_nat v) (reg_status rg)).

Definition upd_reg_in_chip (ch:RAMChip) (r:nat) (rg:RAMReg) : RAMChip :=
  mkRAMChip (update_nth r rg (chip_regs ch)) (chip_port ch).

Definition upd_port_in_chip (ch:RAMChip) (v:nibble) : RAMChip :=
  mkRAMChip (chip_regs ch) (nibble_of_nat v).

Definition upd_chip_in_bank (bk:RAMBank) (c:nat) (ch:RAMChip) : RAMBank :=
  mkRAMBank (update_nth c ch (bank_chips bk)).

Definition upd_bank_in_sys (s:Intel4004State) (b:nat) (bk:RAMBank) : list RAMBank :=
  update_nth b bk (ram_sys s).

(* Read/write using the current bank and latched selection *)
Definition ram_read_main (s:Intel4004State) : nibble :=
  let bk := get_bank s (cur_bank s) in
  let ch := get_chip bk (sel_chip (sel_ram s)) in
  let rg := get_regRAM ch (sel_reg (sel_ram s)) in
  get_main rg (sel_char (sel_ram s)).

Definition ram_write_main_sys (s:Intel4004State) (v:nibble) : list RAMBank :=
  let b := cur_bank s in
  let c := sel_chip (sel_ram s) in
  let r := sel_reg  (sel_ram s) in
  let i := sel_char (sel_ram s) in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let rg := get_regRAM ch r in
  let rg' := upd_main_in_reg rg i v in
  let ch' := upd_reg_in_chip ch r rg' in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.

Definition ram_write_status_sys (s:Intel4004State) (idx:nat) (v:nibble) : list RAMBank :=
  let b := cur_bank s in
  let c := sel_chip (sel_ram s) in
  let r := sel_reg  (sel_ram s) in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let rg := get_regRAM ch r in
  let rg' := upd_stat_in_reg rg idx v in
  let ch' := upd_reg_in_chip ch r rg' in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.

Definition ram_write_port_sys (s:Intel4004State) (v:nibble) : list RAMBank :=
  let b := cur_bank s in
  let c := sel_chip (sel_ram s) in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let ch' := upd_port_in_chip ch v in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.

(* =============================== ISA ================================ *)

Inductive Instruction : Type :=
  | NOP : Instruction
  | JCN : nibble -> byte -> Instruction
  | FIM : nat -> byte -> Instruction
  | SRC : nat -> Instruction
  | FIN : nat -> Instruction
  | JIN : nat -> Instruction
  | JUN : addr12 -> Instruction
  | JMS : addr12 -> Instruction
  | INC : nat -> Instruction
  | ISZ : nat -> byte -> Instruction
  | ADD : nat -> Instruction
  | SUB : nat -> Instruction
  | LD  : nat -> Instruction
  | XCH : nat -> Instruction
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

(* Encode bytes -> Instruction *)
Definition decode (b1 : byte) (b2 : byte) : Instruction :=
  let opcode := b1 / 16 in
  let operand := b1 mod 16 in
  match opcode with
  | 0 => NOP
  | 1 => JCN operand b2
  | 2 => if operand mod 2 =? 0 then FIM operand b2 else SRC operand
  | 3 => if operand mod 2 =? 0 then FIN operand else JIN operand
  | 4 => JUN (addr12_of_nat ((operand * 256) + b2))
  | 5 => JMS (addr12_of_nat ((operand * 256) + b2))
  | 6 => INC operand
  | 7 => ISZ operand b2
  | 8 => ADD operand
  | 9 => SUB operand
  | 10 => LD operand
  | 11 => XCH operand
  | 12 => BBL operand
  | 13 => LDM operand
  | 14 =>
      match operand with
      | 0 => WRM | 1 => WMP | 2 => WRR | 3 => WPM
      | 4 => WR0 | 5 => WR1 | 6 => WR2 | 7 => WR3
      | 8 => SBM | 9 => RDM | 10 => RDR | 11 => ADM
      | 12 => RD0 | 13 => RD1 | 14 => RD2 | 15 => RD3
      | _ => NOP
      end
  | 15 =>
      match operand with
      | 0 => CLB | 1 => CLC | 2 => IAC | 3 => CMC
      | 4 => CMA | 5 => RAL | 6 => RAR | 7 => TCC
      | 8 => DAC | 9 => TCS | 10 => STC | 11 => DAA
      | 12 => KBP | 13 => DCL
      | _ => NOP
      end
  | _ => NOP
  end.

(* ========================== ENCODE ================================= *)

Definition encode (i:Instruction) : byte * byte :=
  match i with
  | NOP => (0,0)
  | JCN c a => (16 + c, a mod 256)
  | FIM r d => (32 + ((r - (r mod 2)) mod 16), d mod 256)
  | SRC r    => (32 + (((r - (r mod 2)) + 1) mod 16), 0)
  | FIN r    => (48 + ((r - (r mod 2)) mod 16), 0)
  | JIN r    => (48 + (((r - (r mod 2)) + 1) mod 16), 0)
  | JUN a    => (64 + ((a / 256) mod 16), a mod 256)
  | JMS a    => (80 + ((a / 256) mod 16), a mod 256)
  | INC r    => (96 + (r mod 16), 0)
  | ISZ r a  => (112 + (r mod 16), a mod 256)
  | ADD r    => (128 + (r mod 16), 0)
  | SUB r    => (144 + (r mod 16), 0)
  | LD r     => (160 + (r mod 16), 0)
  | XCH r    => (176 + (r mod 16), 0)
  | BBL d    => (192 + (d mod 16), 0)
  | LDM d    => (208 + (d mod 16), 0)
  | WRM      => (224,0) | WMP => (225,0) | WRR => (226,0) | WPM => (227,0)
  | WR0      => (228,0) | WR1 => (229,0) | WR2 => (230,0) | WR3 => (231,0)
  | SBM      => (232,0) | RDM => (233,0) | RDR => (234,0) | ADM => (235,0)
  | RD0      => (236,0) | RD1 => (237,0) | RD2 => (238,0) | RD3 => (239,0)
  | CLB      => (240,0) | CLC => (241,0) | IAC => (242,0) | CMC => (243,0)
  | CMA      => (244,0) | RAL => (245,0) | RAR => (246,0) | TCC => (247,0)
  | DAC      => (248,0) | TCS => (249,0) | STC => (250,0) | DAA => (251,0)
  | KBP      => (252,0) | DCL => (253,0)
  end.

(* Instruction well-formedness for encoding roundtrip & execution params *)
Definition instr_wf (i:Instruction) : Prop :=
  match i with
  | JCN c a => c < 16 /\ a < 256
  | FIM r d => r < 16 /\ r mod 2 = 0 /\ d < 256
  | SRC r   => r < 16 /\ r mod 2 = 1
  | FIN r   => r < 16 /\ r mod 2 = 0
  | JIN r   => r < 16 /\ r mod 2 = 1
  | JUN a   => a < 4096
  | JMS a   => a < 4096
  | INC r | ADD r | SUB r | LD r | XCH r => r < 16
  | ISZ r a => r < 16 /\ a < 256
  | BBL d | LDM d => d < 16
  | _ => True
  end.

Lemma even_sub_mod : forall n, n mod 2 = 0 -> n - n mod 2 = n.
Proof.
  intros n H. rewrite H. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma odd_sub_mod : forall n, n mod 2 = 1 -> n - n mod 2 = n - 1.
Proof.
  intros n H. rewrite H. reflexivity.
Qed.

Lemma odd_range_helper : forall n, n < 16 -> n mod 2 = 1 -> (n - n mod 2) + 1 < 16.
Proof.
  intros n Hn Hodd.
  rewrite odd_sub_mod by assumption.
  lia.
Qed.

Lemma mod2_cases : forall n, n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros n. pose proof (Nat.mod_upper_bound n 2).
  assert (n mod 2 < 2) by (apply H; lia).
  destruct (n mod 2); [left|right]; auto.
  destruct n0; auto. lia.
Qed.

Lemma decode_2_concrete_even : forall b,
  b < 256 ->
  decode 32 b = FIM 0 b /\
  decode 34 b = FIM 2 b /\
  decode 36 b = FIM 4 b /\
  decode 38 b = FIM 6 b /\
  decode 40 b = FIM 8 b /\
  decode 42 b = FIM 10 b /\
  decode 44 b = FIM 12 b /\
  decode 46 b = FIM 14 b.
Proof.
  intros b Hb.
  unfold decode. simpl.
  repeat split; reflexivity.
Qed.

Lemma src_encode_decode : forall n,
  n < 16 -> n mod 2 = 1 ->
  decode (32 + (((n - n mod 2) + 1) mod 16)) 0 = SRC n.
Proof.
  intros n Hn Hodd.
  rewrite odd_sub_mod by assumption.
  assert (H1: (n - 1 + 1) mod 16 = n).
  { assert (n > 0).
    { destruct n; [simpl in Hodd; discriminate | lia]. }
    rewrite Nat.sub_add by lia. apply Nat.mod_small. assumption. }
  rewrite H1.
  unfold decode.
  assert (H2: (32 + n) / 16 = 2).
  { symmetry. apply (Nat.div_unique (32 + n) 16 2 n); lia. }
  rewrite H2.
  assert (H3: (32 + n) mod 16 = n).
  { symmetry. apply (Nat.mod_unique (32 + n) 16 2 n); lia. }
  rewrite H3. simpl.
  (* Case analysis on odd values < 16 *)
  assert (n = 1 \/ n = 3 \/ n = 5 \/ n = 7 \/ n = 9 \/ n = 11 \/ n = 13 \/ n = 15).
  { clear H1 H2 H3.
    destruct n as [|n']; [simpl in Hodd; discriminate|].
    destruct n' as [|n'']; [left; reflexivity|].
    destruct n'' as [|n3]; [simpl in Hodd; discriminate|].
    destruct n3 as [|n4]; [right; left; reflexivity|].
    destruct n4 as [|n5]; [simpl in Hodd; discriminate|].
    destruct n5 as [|n6]; [right; right; left; reflexivity|].
    destruct n6 as [|n7]; [simpl in Hodd; discriminate|].
    destruct n7 as [|n8]; [right; right; right; left; reflexivity|].
    destruct n8 as [|n9]; [simpl in Hodd; discriminate|].
    destruct n9 as [|n10]; [right; right; right; right; left; reflexivity|].
    destruct n10 as [|n11]; [simpl in Hodd; discriminate|].
    destruct n11 as [|n12]; [right; right; right; right; right; left; reflexivity|].
    destruct n12 as [|n13]; [simpl in Hodd; discriminate|].
    destruct n13 as [|n14]; [right; right; right; right; right; right; left; reflexivity|].
    destruct n14 as [|n15]; [simpl in Hodd; discriminate|].
    destruct n15 as [|n16]; [right; right; right; right; right; right; right; reflexivity|].
    lia. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; reflexivity.
Qed.

Lemma fin_encode_decode : forall n,
  n < 16 -> n mod 2 = 0 ->
  decode (48 + ((n - n mod 2) mod 16)) 0 = FIN n.
Proof.
  intros n Hn Heven.
  rewrite even_sub_mod by assumption.
  assert (H1: n mod 16 = n) by (apply Nat.mod_small; lia).
  rewrite H1.
  unfold decode.
  assert (H2: (48 + n) / 16 = 3).
  { symmetry. apply (Nat.div_unique (48 + n) 16 3 n); lia. }
  rewrite H2.
  assert (H3: (48 + n) mod 16 = n).
  { symmetry. apply (Nat.mod_unique (48 + n) 16 3 n); lia. }
  rewrite H3. simpl.
  (* Case analysis on even values < 16 *)
  assert (n = 0 \/ n = 2 \/ n = 4 \/ n = 6 \/ n = 8 \/ n = 10 \/ n = 12 \/ n = 14).
  { clear H1 H2 H3.
    destruct n as [|n']; [left; reflexivity|].
    destruct n' as [|n'']; [simpl in Heven; discriminate|].
    destruct n'' as [|n3]; [right; left; reflexivity|].
    destruct n3 as [|n4]; [simpl in Heven; discriminate|].
    destruct n4 as [|n5]; [right; right; left; reflexivity|].
    destruct n5 as [|n6]; [simpl in Heven; discriminate|].
    destruct n6 as [|n7]; [right; right; right; left; reflexivity|].
    destruct n7 as [|n8]; [simpl in Heven; discriminate|].
    destruct n8 as [|n9]; [right; right; right; right; left; reflexivity|].
    destruct n9 as [|n10]; [simpl in Heven; discriminate|].
    destruct n10 as [|n11]; [right; right; right; right; right; left; reflexivity|].
    destruct n11 as [|n12]; [simpl in Heven; discriminate|].
    destruct n12 as [|n13]; [right; right; right; right; right; right; left; reflexivity|].
    destruct n13 as [|n14]; [simpl in Heven; discriminate|].
    destruct n14 as [|n15]; [right; right; right; right; right; right; right; reflexivity|].
    destruct n15; try lia. simpl in Heven. discriminate. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; reflexivity.
Qed.

Lemma jin_encode_decode : forall n,
  n < 16 -> n mod 2 = 1 ->
  decode (48 + (((n - n mod 2) + 1) mod 16)) 0 = JIN n.
Proof.
  intros n Hn Hodd.
  rewrite odd_sub_mod by assumption.
  assert (H1: (n - 1 + 1) mod 16 = n).
  { assert (n > 0).
    { destruct n; [simpl in Hodd; discriminate | lia]. }
    rewrite Nat.sub_add by lia. apply Nat.mod_small. assumption. }
  rewrite H1.
  unfold decode.
  assert (H2: (48 + n) / 16 = 3).
  { symmetry. apply (Nat.div_unique (48 + n) 16 3 n); lia. }
  rewrite H2.
  assert (H3: (48 + n) mod 16 = n).
  { symmetry. apply (Nat.mod_unique (48 + n) 16 3 n); lia. }
  rewrite H3. simpl.
  (* Case analysis on odd values < 16 *)
  assert (n = 1 \/ n = 3 \/ n = 5 \/ n = 7 \/ n = 9 \/ n = 11 \/ n = 13 \/ n = 15).
  { clear H1 H2 H3.
    destruct n as [|n']; [simpl in Hodd; discriminate|].
    destruct n' as [|n'']; [left; reflexivity|].
    destruct n'' as [|n3]; [simpl in Hodd; discriminate|].
    destruct n3 as [|n4]; [right; left; reflexivity|].
    destruct n4 as [|n5]; [simpl in Hodd; discriminate|].
    destruct n5 as [|n6]; [right; right; left; reflexivity|].
    destruct n6 as [|n7]; [simpl in Hodd; discriminate|].
    destruct n7 as [|n8]; [right; right; right; left; reflexivity|].
    destruct n8 as [|n9]; [simpl in Hodd; discriminate|].
    destruct n9 as [|n10]; [right; right; right; right; left; reflexivity|].
    destruct n10 as [|n11]; [simpl in Hodd; discriminate|].
    destruct n11 as [|n12]; [right; right; right; right; right; left; reflexivity|].
    destruct n12 as [|n13]; [simpl in Hodd; discriminate|].
    destruct n13 as [|n14]; [right; right; right; right; right; right; left; reflexivity|].
    destruct n14 as [|n15]; [simpl in Hodd; discriminate|].
    destruct n15 as [|n16]; [right; right; right; right; right; right; right; reflexivity|].
    lia. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; reflexivity.
Qed.

Lemma divmod_representation : forall a,
  a = 256 * (a / 256) + a mod 256.
Proof.
  intro a.
  apply Nat.div_mod.
  lia.
Qed.

Lemma mod_add_multiple : forall a b n,
  n <> 0 ->
  (n * a + b) mod n = b mod n.
Proof.
  intros a b n Hn.
  rewrite Nat.add_mod by exact Hn.
  assert (n * a mod n = 0).
  { rewrite Nat.mul_comm.
    apply Nat.mod_mul.
    exact Hn. }
  rewrite H.
  rewrite Nat.add_0_l.
  rewrite Nat.mod_mod by exact Hn.
  reflexivity.
Qed.

Lemma div_256_mul_256_add_mod_256_eq : forall a,
  (a / 256) * 256 + a mod 256 = a.
Proof.
  intro a.
  rewrite Nat.mul_comm.
  symmetry.
  apply Nat.div_mod.
  lia.
Qed.

Lemma addr12_of_nat_mod_small : forall n,
  n < 4096 ->
  addr12_of_nat n = n.
Proof.
  intros n Hn.
  unfold addr12_of_nat.
  apply Nat.mod_small.
  exact Hn.
Qed.

Lemma divmod_sum_eq : forall a,
  exists q r, a = q * 256 + r /\ r < 256 /\ q = a / 256 /\ r = a mod 256.
Proof.
  intro a.
  exists (a / 256), (a mod 256).
  split.
  - pose proof (divmod_representation a) as H.
    rewrite Nat.mul_comm in H. exact H.
  - split.
    + apply Nat.mod_upper_bound. lia.
    + split; reflexivity.
Qed.

Lemma addr12_reconstruction : forall a q r,
  a < 4096 ->
  a = q * 256 + r ->
  r < 256 ->
  addr12_of_nat (q * 256 + r) = a.
Proof.
  intros a q r Ha Heq Hr.
  unfold addr12_of_nat.
  rewrite <- Heq.
  apply Nat.mod_small.
  exact Ha.
Qed.

Lemma addr12_div_mod_identity : forall a,
  a < 4096 ->
  addr12_of_nat ((a / 256) * 256 + a mod 256) = a.
Proof.
  intros a Ha.
  apply addr12_reconstruction with (q := a / 256) (r := a mod 256).
  - exact Ha.
  - pose proof (divmod_representation a) as H.
    rewrite Nat.mul_comm in H. exact H.
  - apply Nat.mod_upper_bound. lia.
Qed.

Lemma jun_jms_encode_helper : forall a,
  a < 4096 ->
  (64 + (a / 256)) / 16 = 4 /\
  (64 + (a / 256)) mod 16 = a / 256 /\
  (80 + (a / 256)) / 16 = 5 /\
  (80 + (a / 256)) mod 16 = a / 256.
Proof.
  intros a Ha.
  assert (Hdiv: a / 256 < 16).
  { destruct (le_lt_dec 16 (a / 256)) as [Hge|Hlt].
    - exfalso.
      assert (4096 <= 256 * (a / 256)).
      { replace 4096 with (256 * 16) by reflexivity.
        apply Nat.mul_le_mono_l. exact Hge. }
      assert (a < 256 * (a / 256)).
      { lia. }
      assert (256 * (a / 256) <= a).
      { destruct a; [simpl; lia|].
        pose proof (Nat.div_mod (S a) 256).
        assert (256 <> 0) by lia.
        specialize (H1 H2).
        assert (S a = 256 * (S a / 256) + S a mod 256) by exact H1.
        rewrite H3.
        assert (S a mod 256 < 256).
        { apply Nat.mod_upper_bound. lia. }
        lia. }
      lia.
    - exact Hlt. }
  split; [symmetry; apply (Nat.div_unique (64 + a / 256) 16 4 (a / 256)); lia|].
  split.
  - replace 64 with (16 * 4) by reflexivity.
    rewrite mod_add_multiple by lia.
    apply Nat.mod_small.
    exact Hdiv.
  - split; [symmetry; apply (Nat.div_unique (80 + a / 256) 16 5 (a / 256)); lia|].
    replace 80 with (16 * 5) by reflexivity.
    rewrite mod_add_multiple by lia.
    apply Nat.mod_small.
    exact Hdiv.
Qed.

Lemma fim_encode_decode : forall n b,
  n < 16 -> n mod 2 = 0 -> b < 256 ->
  decode (32 + ((n - n mod 2) mod 16)) (b mod 256) = FIM n b.
Proof.
  intros n b Hn Heven Hb.
  rewrite even_sub_mod by assumption.
  assert (H1: n mod 16 = n) by (apply Nat.mod_small; lia).
  rewrite H1.
  assert (H2: b mod 256 = b) by (apply Nat.mod_small; lia).
  rewrite H2.
  (* Now do case analysis on the even values of n < 16 *)
  assert (n = 0 \/ n = 2 \/ n = 4 \/ n = 6 \/ n = 8 \/ n = 10 \/ n = 12 \/ n = 14).
  { clear H1 H2.
    destruct n as [|n']; [left; reflexivity|].
    destruct n' as [|n'']; [simpl in Heven; discriminate|].
    destruct n'' as [|n3]; [right; left; reflexivity|].
    destruct n3 as [|n4]; [simpl in Heven; discriminate|].
    destruct n4 as [|n5]; [right; right; left; reflexivity|].
    destruct n5 as [|n6]; [simpl in Heven; discriminate|].
    destruct n6 as [|n7]; [right; right; right; left; reflexivity|].
    destruct n7 as [|n8]; [simpl in Heven; discriminate|].
    destruct n8 as [|n9]; [right; right; right; right; left; reflexivity|].
    destruct n9 as [|n10]; [simpl in Heven; discriminate|].
    destruct n10 as [|n11]; [right; right; right; right; right; left; reflexivity|].
    destruct n11 as [|n12]; [simpl in Heven; discriminate|].
    destruct n12 as [|n13]; [right; right; right; right; right; right; left; reflexivity|].
    destruct n13 as [|n14]; [simpl in Heven; discriminate|].
    destruct n14 as [|n15]; [right; right; right; right; right; right; right; reflexivity|].
    destruct n15; try lia. simpl in Heven. discriminate. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; reflexivity.
Qed.

Lemma decode_encode_id : forall i, instr_wf i -> let '(b1,b2) := encode i in decode b1 b2 = i.
Proof.
  intros i Hwf. destruct i; simpl in *; try reflexivity; try lia.
  - (* JCN *) destruct Hwf as [Hc Ha].
    change (decode (16 + n) (b mod 256) = JCN n b).
    unfold decode.
    assert (E1: (16 + n) / 16 = 1).
    { symmetry. apply (Nat.div_unique (16 + n) 16 1 n); lia. }
    assert (E2: (16 + n) mod 16 = n).
    { symmetry. apply (Nat.mod_unique (16 + n) 16 1 n); lia. }
    rewrite E1, E2.
    change (JCN n (b mod 256) = JCN n b).
    f_equal. apply Nat.mod_small. assumption.
  - (* FIM *) destruct Hwf as (Hr & Hev & Hd).
    apply fim_encode_decode; assumption.
  - (* SRC *) destruct Hwf as (Hr & Hodd).
    apply src_encode_decode; assumption.
  - (* FIN *) destruct Hwf as (Hr & Hev).
    apply fin_encode_decode; assumption.
  - (* JIN *) destruct Hwf as (Hr & Hodd).
    apply jin_encode_decode; assumption.
  - (* JUN *)
    change (decode (64 + (a / 256 mod 16)) (a mod 256) = JUN a).
    unfold decode.
    pose proof (jun_jms_encode_helper a Hwf) as [H1 [H2 [H3 H4]]].
    assert (HMod: a / 256 mod 16 = a / 256).
    { apply Nat.mod_small.
      assert (HDivLt: a / 256 < 16).
      { assert (Ha4096: a < 4096) by exact Hwf.
        destruct (le_lt_dec 16 (a / 256)) as [HGe16|HLt16]; [|exact HLt16].
        exfalso.
        assert (HContra: 4096 <= 256 * (a / 256)).
        { replace 4096 with (256 * 16) by reflexivity.
          apply Nat.mul_le_mono_l. exact HGe16. }
        assert (HMulDiv: 256 * (a / 256) <= a).
        { pose proof (Nat.div_mod a 256) as HDivMod.
          assert (H256Nz: 256 <> 0) by lia.
          specialize (HDivMod H256Nz).
          assert (HEq: a = 256 * (a / 256) + a mod 256) by exact HDivMod.
          rewrite HEq.
          assert (a mod 256 < 256) by (apply Nat.mod_upper_bound; lia).
          lia. }
        lia. }
      exact HDivLt. }
    rewrite HMod.
    unfold decode.
    rewrite H1.
    rewrite H2.
    f_equal.
    unfold addr12_of_nat.
    assert (HDecomp: (a / 256) * 256 + a mod 256 = a).
    { pose proof (divmod_representation a) as Hdm.
      rewrite Nat.mul_comm in Hdm.
      symmetry. exact Hdm. }
    rewrite HDecomp.
    apply Nat.mod_small.
    exact Hwf.
  - (* JMS *)
    change (decode (80 + (a / 256 mod 16)) (a mod 256) = JMS a).
    unfold decode.
    pose proof (jun_jms_encode_helper a Hwf) as [H1 [H2 [H3 H4]]].
    assert (HMod: a / 256 mod 16 = a / 256).
    { apply Nat.mod_small.
      assert (HDivLt: a / 256 < 16).
      { assert (Ha4096: a < 4096) by exact Hwf.
        destruct (le_lt_dec 16 (a / 256)) as [HGe16|HLt16]; [|exact HLt16].
        exfalso.
        assert (HContra: 4096 <= 256 * (a / 256)).
        { replace 4096 with (256 * 16) by reflexivity.
          apply Nat.mul_le_mono_l. exact HGe16. }
        assert (HMulDiv: 256 * (a / 256) <= a).
        { pose proof (Nat.div_mod a 256) as HDivMod.
          assert (H256Nz: 256 <> 0) by lia.
          specialize (HDivMod H256Nz).
          assert (HEq: a = 256 * (a / 256) + a mod 256) by exact HDivMod.
          rewrite HEq.
          assert (a mod 256 < 256) by (apply Nat.mod_upper_bound; lia).
          lia. }
        lia. }
      exact HDivLt. }
    rewrite HMod.
    rewrite H3.
    rewrite H4.
    f_equal.
    unfold addr12_of_nat.
    assert (HDecomp: (a / 256) * 256 + a mod 256 = a).
    { pose proof (divmod_representation a) as Hdm.
      rewrite Nat.mul_comm in Hdm.
      symmetry. exact Hdm. }
    rewrite HDecomp.
    apply Nat.mod_small.
    exact Hwf.
  - (* INC *)
    change (decode (96 + n mod 16) 0 = INC n).
    unfold decode.
    assert (H_div: (96 + n mod 16) / 16 = 6).
    { assert (Hmod_small: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
      rewrite Hmod_small.
      assert (96 + n < 112) by lia.
      assert (96 <= 96 + n) by lia.
      symmetry.
      apply Nat.div_unique with (r := n).
      - lia.
      - reflexivity. }
    assert (H_mod: (96 + n mod 16) mod 16 = n mod 16).
    { assert (Hmod_small: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
      rewrite Hmod_small.
      symmetry.
      apply Nat.mod_unique with (q := 6).
      - lia.
      - reflexivity. }
    rewrite H_div, H_mod.
    change (INC (n mod 16) = INC n).
    f_equal.
    apply Nat.mod_small. exact Hwf.
  - (* ISZ *)
    destruct Hwf as [Hr Hb].
    change (decode (112 + n mod 16) (b mod 256) = ISZ n b).
    unfold decode.
    assert (H_div: (112 + n mod 16) / 16 = 7).
    { assert (n mod 16 = n) by (apply Nat.mod_small; exact Hr).
      rewrite H.
      symmetry. apply Nat.div_unique with (r := n); lia. }
    assert (H_mod: (112 + n mod 16) mod 16 = n mod 16).
    { assert (n mod 16 = n) by (apply Nat.mod_small; exact Hr).
      rewrite H.
      symmetry.
      apply Nat.mod_unique with (q := 7); lia. }
    rewrite H_div, H_mod.
    change (ISZ (n mod 16) (b mod 256) = ISZ n b).
    f_equal.
    + apply Nat.mod_small. exact Hr.
    + apply Nat.mod_small. exact Hb.
  - (* ADD *)
    change (decode (128 + n mod 16) 0 = ADD n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (128 + n) / 16 = 8) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (128 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 8); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* SUB *)
    change (decode (144 + n mod 16) 0 = SUB n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (144 + n) / 16 = 9) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (144 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 9); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* LD *)
    change (decode (160 + n mod 16) 0 = LD n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (160 + n) / 16 = 10) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (160 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 10); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* XCH *)
    change (decode (176 + n mod 16) 0 = XCH n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (176 + n) / 16 = 11) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (176 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 11); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* BBL *)
    change (decode (192 + n mod 16) 0 = BBL n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (192 + n) / 16 = 12) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (192 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 12); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* LDM *)
    change (decode (208 + n mod 16) 0 = LDM n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (208 + n) / 16 = 13) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (208 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 13); lia. }
    rewrite H_div, H_mod.
    reflexivity.
Qed.

(* ============================ Semantics ============================= *)

(* Helpers to compute the page base to use (quirks/spec accurate):
   - FIN/JIN are 1-byte but use the page of PC+1 (next instruction).
   - JCN/ISZ are 2-byte and branch within the page of PC+2 (after the instruction).
*)
Definition base_for_next1 (s:Intel4004State) := page_base (pc_inc1 s).
Definition base_for_next2 (s:Intel4004State) := page_base (pc_inc2 s).

Definition execute (s : Intel4004State) (inst : Instruction) : Intel4004State :=
  match inst with
  | NOP =>
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | LDM n =>
      mkState (nibble_of_nat n) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | LD r =>
      mkState (get_reg s r) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | XCH r =>
      let old_acc := acc s in
      let old_reg := get_reg s r in
      let s1 := set_reg s r old_acc in
      mkState old_reg (regs s1) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | INC r =>
      let new_val := nibble_of_nat (get_reg s r + 1) in
      let s1 := set_reg s r new_val in
      mkState (acc s) (regs s1) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | ADD r =>
      let sum := (acc s) + (get_reg s r) + (if carry s then 1 else 0) in
      mkState (nibble_of_nat sum) (regs s) (16 <=? sum) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | SUB r =>
      let reg_val := get_reg s r in
      let borrow := if carry s then 0 else 1 in
      let diff := (acc s) + 16 - reg_val - borrow in
      mkState (nibble_of_nat diff) (regs s) (16 <=? diff) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | IAC =>
      let sum := (acc s) + 1 in
      mkState (nibble_of_nat sum) (regs s) (16 <=? sum) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | DAC =>
      let newv := (acc s) + 15 in  (* -1 mod 16 *)
      let borrow := (acc s =? 0) in
      mkState (nibble_of_nat newv) (regs s) (negb borrow) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | CLC =>
      mkState (acc s) (regs s) false (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | STC =>
      mkState (acc s) (regs s) true (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | CMC =>
      mkState (acc s) (regs s) (negb (carry s)) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | CMA =>
      mkState (nibble_of_nat (15 - (acc s))) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | CLB =>
      mkState 0 (regs s) false (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | RAL =>
      let new_acc := nibble_of_nat ((acc s) * 2 + if carry s then 1 else 0) in
      let new_carry := 8 <=? (acc s) in
      mkState new_acc (regs s) new_carry (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | RAR =>
      let new_acc := nibble_of_nat ((acc s) / 2 + if carry s then 8 else 0) in
      let new_carry := (acc s) mod 2 =? 1 in
      mkState new_acc (regs s) new_carry (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | TCC =>
      mkState (if carry s then 1 else 0) (regs s) false (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | TCS =>
      mkState (if carry s then 10 else 9) (regs s) false (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | DAA =>
      let adjusted := if (9 <? acc s) || carry s then (acc s + 6) else acc s in
      mkState (nibble_of_nat adjusted)
              (regs s)
              ((9 <? acc s) || carry s || (16 <=? adjusted))
              (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | KBP =>
      let result :=
        match acc s with
        | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4 | _ => 15
        end in
      mkState result (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | JUN addr =>
      mkState (acc s) (regs s) (carry s) addr (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | JMS addr =>
      let s1 := push_stack s (addr12_of_nat (pc s + 2)) in
      mkState (acc s) (regs s) (carry s) addr (stack s1)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | BBL n =>
      match pop_stack s with
      | (Some addr, s1) =>
          mkState (nibble_of_nat n) (regs s1) (carry s) addr (stack s1)
                  (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                  (rom s) (test_pin s) (prog_pulses s)
      | (None, s1) =>
          mkState (nibble_of_nat n) (regs s1) (carry s) (pc_inc1 s) (stack s1)
                  (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                  (rom s) (test_pin s) (prog_pulses s)
      end

  | JCN cond off =>
      let c1 := cond / 8 in
      let c2 := (cond / 4) mod 2 in
      let c3 := (cond / 2) mod 2 in
      let c4 := cond mod 2 in
      let base_cond :=
        orb (andb (acc s =? 0) (c2 =? 1))
            (orb (andb (carry s) (c3 =? 1))
                 (andb (negb (test_pin s)) (c4 =? 1))) in
      let jump := if c1 =? 1 then negb base_cond else base_cond in
      if jump
      then mkState (acc s) (regs s) (carry s)
                   (addr12_of_nat (base_for_next2 s + off))
                   (stack s) (ram_sys s) (cur_bank s) (sel_ram s)
                   (rom_ports s) (sel_rom s) (rom s) (test_pin s) (prog_pulses s)
      else mkState (acc s) (regs s) (carry s) (pc_inc2 s) (stack s)
                   (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                   (rom s) (test_pin s) (prog_pulses s)

  | FIM r data =>
      (* load immediate into register *pair* r (even) *)
      let s1 := set_reg_pair s r data in
      mkState (acc s) (regs s1) (carry s) (pc_inc2 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | ISZ r off =>
      let new_val := nibble_of_nat (get_reg s r + 1) in
      let s1 := set_reg s r new_val in
      if new_val =? 0
      then mkState (acc s) (regs s1) (carry s) (pc_inc2 s) (stack s)
                   (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                   (rom s) (test_pin s) (prog_pulses s)
      else mkState (acc s) (regs s1) (carry s)
                   (addr12_of_nat (base_for_next2 s + off))
                   (stack s) (ram_sys s) (cur_bank s) (sel_ram s)
                   (rom_ports s) (sel_rom s) (rom s) (test_pin s) (prog_pulses s)

  | SRC r =>
      (* Send register pair r externally:
         - ROM I/O: high nibble selects ROM port number (0..15)
         - RAM: high nibble = chip(2) & reg(2); low nibble = main char(4)
         - Does not modify CPU registers. *)
      let v := get_reg_pair s r in
      let hi := v / 16 in
      let lo := v mod 16 in
      let chip := hi / 4 in
      let rno  := hi mod 4 in
      let selr := mkRAMSel chip rno lo in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) selr (rom_ports s) hi
              (rom s) (test_pin s) (prog_pulses s)

  | FIN r =>
      (* fetch indirect: lower 8 from R0:R1; page is that of next instr *)
      let page := page_of (pc_inc1 s) in
      let low8 := (get_reg_pair s 0) mod 256 in
      let addr := addr12_of_nat (page * 256 + low8) in
      let b := fetch_byte s addr in
      let s1 := set_reg_pair s r b in
      mkState (acc s) (regs s1) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | JIN r =>
      (* jump within page of *next* instruction (quirk included) *)
      let page := page_of (pc_inc1 s) in
      let low8 := (get_reg_pair s r) mod 256 in
      let addr := addr12_of_nat (page * 256 + low8) in
      mkState (acc s) (regs s) (carry s) addr (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  (* ------------------ 4002 RAM + 4001 ROM I/O ------------------ *)

  | WRM =>
      let new_sys := ram_write_main_sys s (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | RDM =>
      let v := ram_read_main s in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | ADM =>
      let v := ram_read_main s in
      let sum := (acc s) + v + (if carry s then 1 else 0) in
      mkState (nibble_of_nat sum) (regs s) (16 <=? sum) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | SBM =>
      let v := ram_read_main s in
      let borrow := if carry s then 0 else 1 in
      let diff := (acc s) + 16 - v - borrow in
      mkState (nibble_of_nat diff) (regs s) (16 <=? diff) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | WR0 =>
      let new_sys := ram_write_status_sys s 0 (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)
  | WR1 =>
      let new_sys := ram_write_status_sys s 1 (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)
  | WR2 =>
      let new_sys := ram_write_status_sys s 2 (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)
  | WR3 =>
      let new_sys := ram_write_status_sys s 3 (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | RD0 =>
      let b := get_bank s (cur_bank s) in
      let ch := get_chip b (sel_chip (sel_ram s)) in
      let rg := get_regRAM ch (sel_reg (sel_ram s)) in
      let v := get_stat rg 0 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)
  | RD1 =>
      let b := get_bank s (cur_bank s) in
      let ch := get_chip b (sel_chip (sel_ram s)) in
      let rg := get_regRAM ch (sel_reg (sel_ram s)) in
      let v := get_stat rg 1 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)
  | RD2 =>
      let b := get_bank s (cur_bank s) in
      let ch := get_chip b (sel_chip (sel_ram s)) in
      let rg := get_regRAM ch (sel_reg (sel_ram s)) in
      let v := get_stat rg 2 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)
  | RD3 =>
      let b := get_bank s (cur_bank s) in
      let ch := get_chip b (sel_chip (sel_ram s)) in
      let rg := get_regRAM ch (sel_reg (sel_ram s)) in
      let v := get_stat rg 3 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | WMP =>
      let new_sys := ram_write_port_sys s (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | WRR =>
      let new_ports := update_nth (sel_rom s) (nibble_of_nat (acc s)) (rom_ports s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) new_ports (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | RDR =>
      let v := nth (sel_rom s) (rom_ports s) 0 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)

  | WPM =>
      (* Program-memory write pulse (not visible to our ROM contents).
         We count pulses to make the effect explicit and non-stub. *)
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (S (prog_pulses s))

  | DCL =>
      (* Designate command line: select RAM bank from ACC (lower 2 bits, 0..3) *)
      let nb := (acc s) mod NBANKS in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) nb (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prog_pulses s)
  end.

(* ======================= Small-step machine ========================= *)

Definition step (s : Intel4004State) : Intel4004State :=
  let b1 := fetch_byte s (pc s) in
  let b2 := fetch_byte s (addr12_of_nat (pc s + 1)) in
  let inst := decode b1 b2 in
  execute s inst.

Fixpoint steps (n : nat) (s : Intel4004State) : Intel4004State :=
  match n with
  | 0 => s
  | S n' => steps n' (step s)
  end.

(* ========================== Initial / Reset ========================= *)

Definition empty_reg : RAMReg := mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT).
Definition empty_chip : RAMChip := mkRAMChip (repeat empty_reg NREGS) 0.
Definition empty_bank : RAMBank := mkRAMBank (repeat empty_chip NCHIPS).
Definition empty_sys : list RAMBank := repeat empty_bank NBANKS.

Definition init_state : Intel4004State :=
  mkState 0 (repeat 0 16) false 0 [] empty_sys 0 (mkRAMSel 0 0 0)
          (repeat 0 16) 0 (repeat 0 4096) false 0.

Definition reset_state (s:Intel4004State) : Intel4004State :=
  mkState 0 (regs s) false 0 [] (ram_sys s) 0 (mkRAMSel 0 0 0)
          (repeat 0 16) 0 (rom s) false 0.

(* ======================== Well-formedness =========================== *)

(* Shapes and bounds for the RAM system *)
Definition WF_reg (rg:RAMReg) : Prop :=
  length (reg_main rg) = NMAIN /\
  Forall (fun x => x < 16) (reg_main rg) /\
  length (reg_status rg) = NSTAT /\
  Forall (fun x => x < 16) (reg_status rg).

Definition WF_chip (ch:RAMChip) : Prop :=
  length (chip_regs ch) = NREGS /\
  Forall WF_reg (chip_regs ch) /\
  chip_port ch < 16.

Definition WF_bank (bk:RAMBank) : Prop :=
  length (bank_chips bk) = NCHIPS /\
  Forall WF_chip (bank_chips bk).

Definition WF_sel (sr:RAMSel) : Prop :=
  sel_chip sr < NCHIPS /\ sel_reg sr < NREGS /\ sel_char sr < NMAIN.

Definition WF (s : Intel4004State) : Prop :=
  length (regs s) = 16 /\
  Forall (fun x => x < 16) (regs s) /\
  acc s < 16 /\
  pc s < 4096 /\
  length (stack s) <= 3 /\
  Forall (fun a => a < 4096) (stack s) /\
  length (ram_sys s) = NBANKS /\
  Forall WF_bank (ram_sys s) /\
  cur_bank s < NBANKS /\
  WF_sel (sel_ram s) /\
  length (rom_ports s) = 16 /\
  Forall (fun x => x < 16) (rom_ports s) /\
  sel_rom s < 16 /\
  Forall (fun b => b < 256) (rom s) /\
  length (rom s) = 4096.

(* Helper lemmas for init_state_WF *)

Lemma repeat_0_lt_16 : forall n, Forall (fun x => x < 16) (repeat 0 n).
Proof.
  intros n.
  apply Forall_repeat.
  lia.
Qed.

Lemma repeat_0_lt_256 : forall n, Forall (fun x => x < 256) (repeat 0 n).
Proof.
  intros n.
  apply Forall_repeat.
  lia.
Qed.

Lemma empty_reg_WF : WF_reg empty_reg.
Proof.
  unfold WF_reg, empty_reg.
  unfold NMAIN, NSTAT.
  simpl.
  repeat split; try reflexivity.
  - repeat constructor.
  - repeat constructor.
Qed.

Lemma repeat_empty_reg_WF : forall n, Forall WF_reg (repeat empty_reg n).
Proof.
  intros n.
  apply Forall_repeat.
  apply empty_reg_WF.
Qed.

Lemma empty_chip_WF : WF_chip empty_chip.
Proof.
  unfold WF_chip, empty_chip.
  unfold NREGS.
  simpl.
  repeat split; try lia; try reflexivity.
  repeat constructor; apply empty_reg_WF.
Qed.

Lemma repeat_empty_chip_WF : forall n, Forall WF_chip (repeat empty_chip n).
Proof.
  intros n.
  apply Forall_repeat.
  apply empty_chip_WF.
Qed.

Lemma empty_bank_WF : WF_bank empty_bank.
Proof.
  unfold WF_bank, empty_bank.
  unfold NCHIPS.
  simpl.
  split; [reflexivity|].
  repeat constructor; apply empty_chip_WF.
Qed.

Lemma repeat_empty_bank_WF : forall n, Forall WF_bank (repeat empty_bank n).
Proof.
  intros n.
  apply Forall_repeat.
  apply empty_bank_WF.
Qed.

Lemma default_sel_WF : WF_sel (mkRAMSel 0 0 0).
Proof.
  unfold WF_sel.
  unfold NCHIPS, NREGS, NMAIN.
  simpl.
  repeat split; lia.
Qed.

Lemma init_state_WF : WF init_state.
Proof.
  unfold WF, init_state.
  unfold empty_sys.
  unfold NBANKS.
  split. reflexivity.
  split. apply repeat_0_lt_16.
  split. simpl; lia.
  split. simpl; lia.
  split. simpl; lia.
  split. constructor.
  split. reflexivity.
  split. apply repeat_empty_bank_WF.
  split. simpl; lia.
  split. apply default_sel_WF.
  split. reflexivity.
  split. apply repeat_0_lt_16.
  split. simpl; lia.
  split. apply repeat_0_lt_256.
  reflexivity.
Qed.

(* ====================== Preservation lemmas ========================= *)

(* Structural helpers about updates preserving shapes and <16 *)
Lemma WF_reg_upd_main : forall rg i v,
  WF_reg rg -> WF_reg (upd_main_in_reg rg i v).
Proof.
  intros [mv sv] i v [Hmv_len [Hmv_bound [Hsv_len Hsv_bound]]].
  unfold upd_main_in_reg, WF_reg. simpl.
  repeat split.
  - rewrite update_nth_length. assumption.
  - eapply Forall_update_nth; eauto. apply nibble_lt16.
  - assumption.
  - assumption.
Qed.

Lemma WF_reg_upd_stat : forall rg i v,
  WF_reg rg -> WF_reg (upd_stat_in_reg rg i v).
Proof.
  intros [mv sv] i v [Hmv_len [Hmv_bound [Hsv_len Hsv_bound]]].
  unfold upd_stat_in_reg, WF_reg. simpl.
  repeat split.
  - assumption.
  - assumption.
  - rewrite update_nth_length. assumption.
  - eapply Forall_update_nth; eauto. apply nibble_lt16.
Qed.

Lemma WF_chip_upd_reg : forall ch r rg,
  WF_chip ch -> WF_reg rg -> WF_chip (upd_reg_in_chip ch r rg).
Proof.
  intros [regs port] r rg [Hlen [Hall Hport]] Hrg.
  unfold upd_reg_in_chip, WF_chip. simpl.
  repeat split.
  - rewrite update_nth_length. assumption.
  - eapply Forall_update_nth; eauto.
  - assumption.
Qed.

Lemma WF_chip_upd_port : forall ch v,
  WF_chip ch -> WF_chip (upd_port_in_chip ch v).
Proof.
  intros [regs port] v [Hlen [Hall Hport]].
  unfold upd_port_in_chip, WF_chip. simpl. repeat split; auto.
  apply nibble_lt16.
Qed.

Lemma WF_bank_upd_chip : forall bk c ch,
  WF_bank bk -> WF_chip ch -> WF_bank (upd_chip_in_bank bk c ch).
Proof.
  intros [chips] c ch [Hlen Hall] Hch.
  unfold upd_chip_in_bank, WF_bank. simpl.
  repeat split.
  - rewrite update_nth_length; assumption.
  - eapply Forall_update_nth; eauto.
Qed.

Lemma WF_sys_upd_bank : forall s b bk,
  WF s -> WF_bank bk -> length (upd_bank_in_sys s b bk) = NBANKS /\
                         Forall WF_bank (upd_bank_in_sys s b bk).
Proof.
  intros s b bk H WFbk.
  unfold WF in H.
  destruct H as [Hregs_len [Hregs_forall [Hacc [Hpc [Hstack_len [Hstack_forall [Hram_len [Hram_forall _]]]]]]]].
  unfold upd_bank_in_sys. split.
  - rewrite update_nth_length. assumption.
  - eapply Forall_update_nth; eauto.
Qed.

(* ==================== RAM read-after-write lemmas =================== *)

Lemma get_main_upd_main_in_reg : forall rg i v,
  WF_reg rg ->
  i < NMAIN ->
  get_main (upd_main_in_reg rg i v) i = nibble_of_nat v.
Proof.
  intros rg i v [Hlen_main _] Hi.
  unfold get_main, upd_main_in_reg. simpl.
  rewrite nth_update_nth_eq by lia.
  reflexivity.
Qed.

Lemma get_regRAM_upd_reg_in_chip : forall ch r rg,
  WF_chip ch ->
  r < NREGS ->
  get_regRAM (upd_reg_in_chip ch r rg) r = rg.
Proof.
  intros ch r rg [Hlen _] Hr.
  unfold get_regRAM, upd_reg_in_chip. simpl.
  rewrite nth_update_nth_eq by lia.
  reflexivity.
Qed.

Lemma get_chip_upd_chip_in_bank : forall bk c ch,
  WF_bank bk ->
  c < NCHIPS ->
  get_chip (upd_chip_in_bank bk c ch) c = ch.
Proof.
  intros bk c ch [Hlen _] Hc.
  unfold get_chip, upd_chip_in_bank. simpl.
  rewrite nth_update_nth_eq by lia.
  reflexivity.
Qed.

Lemma get_bank_upd_bank_in_sys : forall s b bk,
  WF s ->
  b < NBANKS ->
  get_bank (mkState (acc s) (regs s) (carry s) (pc s) (stack s)
                     (upd_bank_in_sys s b bk) (cur_bank s) (sel_ram s)
                     (rom_ports s) (sel_rom s) (rom s) (test_pin s) (prog_pulses s))
           b = bk.
Proof.
  intros s b bk [_ [_ [_ [_ [_ [_ [Hsys_len _]]]]]]] Hb.
  unfold get_bank, upd_bank_in_sys. simpl.
  rewrite nth_update_nth_eq by lia.
  reflexivity.
Qed.

Lemma WF_bank_from_sys : forall s b,
  WF s ->
  b < NBANKS ->
  WF_bank (get_bank s b).
Proof.
  intros s b Hwf Hb.
  destruct Hwf as [_ [_ [_ [_ [_ [_ [Hlen [Hforall _]]]]]]]].
  rewrite Forall_forall in Hforall.
  apply Hforall. eapply nth_In. lia.
Qed.

Lemma WF_chip_from_bank : forall bk c,
  WF_bank bk ->
  c < NCHIPS ->
  WF_chip (get_chip bk c).
Proof.
  intros bk c [Hlen Hforall] Hc.
  rewrite Forall_forall in Hforall.
  apply Hforall. eapply nth_In. lia.
Qed.

Lemma WF_reg_from_chip : forall ch r,
  WF_chip ch ->
  r < NREGS ->
  WF_reg (get_regRAM ch r).
Proof.
  intros ch r [Hlen [Hforall _]] Hr.
  rewrite Forall_forall in Hforall.
  apply Hforall. eapply nth_In. lia.
Qed.

Lemma ram_write_then_read_main : forall s v,
  WF s ->
  cur_bank s < NBANKS ->
  sel_chip (sel_ram s) < NCHIPS ->
  sel_reg (sel_ram s) < NREGS ->
  sel_char (sel_ram s) < NMAIN ->
  ram_read_main (mkState (acc s) (regs s) (carry s) (pc s) (stack s)
                          (ram_write_main_sys s v) (cur_bank s) (sel_ram s)
                          (rom_ports s) (sel_rom s) (rom s) (test_pin s) (prog_pulses s))
  = nibble_of_nat v.
Proof.
  intros s v Hwf Hb Hc Hr Hi.
  unfold ram_read_main, ram_write_main_sys. simpl.
  rewrite get_bank_upd_bank_in_sys; [|assumption|assumption].
  rewrite get_chip_upd_chip_in_bank.
  - rewrite get_regRAM_upd_reg_in_chip.
    + apply get_main_upd_main_in_reg; [|assumption].
      apply WF_reg_from_chip; [|assumption].
      apply WF_chip_from_bank; [|assumption].
      apply WF_bank_from_sys; assumption.
    + apply WF_chip_from_bank; [|assumption].
      apply WF_bank_from_sys; assumption.
    + assumption.
  - apply WF_bank_from_sys; assumption.
  - assumption.
Qed.

(* ====================== Execute preserves WF ======================== *)

(* Helper lemma: opcode 0 (NOP) is always True *)
Lemma decode_opcode_0_wf : forall b1 b2,
  b1 / 16 = 0 ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 H. unfold decode. rewrite H. simpl. trivial.
Qed.

(* Helper lemma: opcode 1 (JCN) is always True *)
Lemma decode_opcode_1_wf : forall b1 b2,
  b1 / 16 = 1 ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 H. unfold decode. rewrite H. simpl. trivial.
Qed.

(* Helper: neither FIM nor SRC match JUN/JMS *)
Lemma fim_src_not_jun_jms : forall r b,
  match FIM r b with | JUN _ | JMS _ => False | _ => True end /\
  match SRC r with | JUN _ | JMS _ => False | _ => True end.
Proof. intros; split; exact I. Qed.

(* Helper lemma: opcode 2 (FIM or SRC) is always True *)
Lemma decode_opcode_2_wf : forall b1 b2,
  b1 / 16 = 2 ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 H. unfold decode. rewrite H.
  cbv beta iota match.
  destruct ((b1 mod 16) mod 2 =? 0);
  generalize (fim_src_not_jun_jms (b1 mod 16) b2); intros [H1 H2];
  [exact H1 | exact H2].
Qed.

(* Helper: neither FIN nor JIN match JUN/JMS *)
Lemma fin_jin_not_jun_jms : forall r,
  match FIN r with | JUN _ | JMS _ => False | _ => True end /\
  match JIN r with | JUN _ | JMS _ => False | _ => True end.
Proof. intros; split; exact I. Qed.

(* Helper lemma: opcode 3 (FIN or JIN) is always True *)
Lemma decode_opcode_3_wf : forall b1 b2,
  b1 / 16 = 3 ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 H. unfold decode. rewrite H.
  cbv beta iota match.
  destruct ((b1 mod 16) mod 2 =? 0);
  generalize (fin_jin_not_jun_jms (b1 mod 16)); intros [H1 H2];
  [exact H1 | exact H2].
Qed.

(* Helper lemma: opcode 4 (JUN) satisfies the bound *)
Lemma decode_opcode_4_wf : forall b1 b2,
  b1 / 16 = 4 ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 H. unfold decode. rewrite H. simpl.
  apply addr12_bound.
Qed.

(* Helper lemma: opcode 5 (JMS) satisfies the bound *)
Lemma decode_opcode_5_wf : forall b1 b2,
  b1 / 16 = 5 ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 H. unfold decode. rewrite H. simpl.
  apply addr12_bound.
Qed.

(* Helper lemma: opcodes 6-13 are always True *)
Lemma decode_opcode_6_to_13_wf : forall b1 b2 n,
  6 <= n <= 13 ->
  b1 / 16 = n ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 n Hrange H. unfold decode. rewrite H.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; simpl; trivial.
  destruct n; simpl; trivial.
  destruct n; simpl; trivial.
  destruct n; simpl; trivial.
  destruct n; simpl; trivial.
  destruct n; simpl; trivial.
  destruct n; simpl; trivial.
  destruct n; simpl; trivial.
  lia.
Qed.

(* Helper lemma: opcode 14 instructions never match JUN/JMS *)
Lemma opcode_14_not_jun_jms : forall b1 b2,
  b1 / 16 = 14 ->
  match decode b1 b2 with
  | JUN _ | JMS _ => False
  | _ => True
  end.
Proof.
  intros b1 b2 H.
  unfold decode. rewrite H. cbv beta iota match.
  destruct (b1 mod 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]];
    simpl; try exact I.
  (* The 16th case: if n = 0 then RD3, else NOP. Both don't match JUN/JMS *)
  destruct n; simpl; exact I.
Qed.

(* Helper lemma: opcode 15 instructions never match JUN/JMS *)
Lemma opcode_15_not_jun_jms : forall b1 b2,
  b1 / 16 = 15 ->
  match decode b1 b2 with
  | JUN _ | JMS _ => False
  | _ => True
  end.
Proof.
  intros b1 b2 H.
  unfold decode. rewrite H. cbv beta iota match.
  (* We need to prove that operand 0-13 produce instructions that aren't JUN/JMS,
     and operands 14+ produce NOP which also isn't JUN/JMS *)
  destruct (b1 mod 16) as [|n1]; simpl; try exact I.  (* 0: CLB *)
  destruct n1 as [|n2]; simpl; try exact I.           (* 1: CLC *)
  destruct n2 as [|n3]; simpl; try exact I.           (* 2: IAC *)
  destruct n3 as [|n4]; simpl; try exact I.           (* 3: CMC *)
  destruct n4 as [|n5]; simpl; try exact I.           (* 4: CMA *)
  destruct n5 as [|n6]; simpl; try exact I.           (* 5: RAL *)
  destruct n6 as [|n7]; simpl; try exact I.           (* 6: RAR *)
  destruct n7 as [|n8]; simpl; try exact I.           (* 7: TCC *)
  destruct n8 as [|n9]; simpl; try exact I.           (* 8: DAC *)
  destruct n9 as [|n10]; simpl; try exact I.          (* 9: TCS *)
  destruct n10 as [|n11]; simpl; try exact I.         (* 10: STC *)
  destruct n11 as [|n12]; simpl; try exact I.         (* 11: DAA *)
  destruct n12 as [|n13]; simpl; try exact I.         (* 12: KBP *)
  destruct n13 as [|n14]; simpl.                      (* 13: DCL *)
  - exact I.  (* Case 13: DCL *)
  - (* Now n14 represents cases 14+, which all produce NOP *)
    (* The _ case in the match produces NOP *)
    exact I.
Qed.

(* Helper: opcodes 6-13 never produce JUN/JMS *)
Lemma decode_opcodes_6_to_13_not_jun_jms : forall b1 b2,
  6 <= b1 / 16 <= 13 ->
  match decode b1 b2 with
  | JUN _ | JMS _ => False
  | _ => True
  end.
Proof.
  intros b1 b2 H.
  unfold decode.
  assert (b1 / 16 = 6 \/ b1 / 16 = 7 \/ b1 / 16 = 8 \/ b1 / 16 = 9 \/
          b1 / 16 = 10 \/ b1 / 16 = 11 \/ b1 / 16 = 12 \/ b1 / 16 = 13) by lia.
  destruct H0 as [H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]];
    rewrite H0; simpl; trivial.
Qed.

(* Helper: opcodes >= 16 produce NOP, never JUN/JMS *)
Lemma decode_opcode_16_plus_not_jun_jms : forall b1 b2,
  b1 / 16 >= 16 ->
  match decode b1 b2 with
  | JUN _ | JMS _ => False
  | _ => True
  end.
Proof.
  intros b1 b2 H.
  unfold decode.
  destruct (b1 / 16); try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
Qed.

(* Decode params are wf enough for absolute JUN/JMS *)
Lemma decode_instr_wf_jun_jms : forall b1 b2,
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2.
  destruct (b1 / 16) eqn:E.
  - apply decode_opcode_0_wf; auto.
  - destruct n as [|n1].
    + apply decode_opcode_1_wf; auto.
    + destruct n1 as [|n2].
      * apply decode_opcode_2_wf; auto.
      * destruct n2 as [|n3].
        -- apply decode_opcode_3_wf; auto.
        -- destruct n3 as [|n4].
           ++ apply decode_opcode_4_wf; auto.
           ++ destruct n4 as [|n5].
              ** apply decode_opcode_5_wf; auto.
              ** (* opcodes 6 and beyond *)
                 assert (b1 / 16 >= 6).
                 { rewrite E. lia. }
                 destruct (le_dec (b1 / 16) 13);
                   [generalize (decode_opcodes_6_to_13_not_jun_jms b1 b2);
                    intros Hlem; assert (6 <= b1 / 16 <= 13) by lia;
                    specialize (Hlem H0); destruct (decode b1 b2); auto; contradiction |].
                 (* b1/16 >= 14 *)
                 destruct (eq_nat_dec (b1 / 16) 14);
                   [generalize (opcode_14_not_jun_jms b1 b2);
                    intros Hlem14; specialize (Hlem14 e);
                    destruct (decode b1 b2); auto; contradiction |].
                 destruct (eq_nat_dec (b1 / 16) 15) as [e15|ne15];
                   [generalize (opcode_15_not_jun_jms b1 b2);
                    intros Hlem15; specialize (Hlem15 e15);
                    destruct (decode b1 b2); auto; contradiction |].
                 (* b1/16 >= 16 *)
                 generalize (decode_opcode_16_plus_not_jun_jms b1 b2).
                 intros Hlem16.
                 assert (Hgt16: b1 / 16 >= 16) by lia.
                 specialize (Hlem16 Hgt16).
                 destruct (decode b1 b2); auto; contradiction.
Qed.

(* Helper lemma for mod 16 bounds *)
Lemma mod_16_lt : forall n, n mod 16 < 16.
Proof. intro n. apply Nat.mod_upper_bound. lia. Qed.

(* Helper for reasoning about mod 2 *)
Lemma mod2_eq_iff : forall n, (n mod 2 =? 0) = true <-> n mod 2 = 0.
Proof. intro n. split; intro H. apply Nat.eqb_eq in H. exact H. apply Nat.eqb_eq. exact H. Qed.

Lemma mod2_neq_iff : forall n, (n mod 2 =? 0) = false <-> n mod 2 = 1.
Proof.
  intro n. split; intro H.
  - apply Nat.eqb_neq in H.
    assert (n mod 2 = 0 \/ n mod 2 = 1) by apply mod2_cases.
    destruct H0; [contradiction|exact H0].
  - apply Nat.eqb_neq. intro Hc. rewrite H in Hc. discriminate.
Qed.

(* Simplification lemma for mod expressions *)
Lemma mod_16_mod_2_eq : forall n, (n mod 16) mod 2 = n mod 2.
Proof.
  intro n.
  (* We use that (n mod 16) and n differ by a multiple of 16, which is even *)
  assert (H: exists k, n = 16 * k + n mod 16).
  { exists (n / 16). apply Nat.div_mod. lia. }
  destruct H as [k Hk].
  rewrite Hk at 2.
  rewrite Nat.add_mod by lia.
  assert (16 * k mod 2 = 0).
  { (* 16 = 0 mod 2, so 16 * k = 0 mod 2 *)
    assert (H16mod: 16 mod 2 = 0) by reflexivity.
    rewrite <- Nat.mul_mod_idemp_l by lia.
    rewrite H16mod.
    simpl. reflexivity. }
  rewrite H.
  rewrite Nat.add_0_l.
  rewrite Nat.mod_mod by lia.
  reflexivity.
Qed.

Lemma simpl_mod2_check : forall n, ((n mod 16) mod 2 =? 0) = (n mod 2 =? 0).
Proof.
  intro n.
  rewrite mod_16_mod_2_eq.
  reflexivity.
Qed.

(* Helper lemmas for decode_instr_wf *)

Lemma decode_NOP_wf : instr_wf NOP.
Proof.
  unfold instr_wf. trivial.
Qed.

Lemma decode_JCN_wf : forall c a,
  c < 16 -> a < 256 -> instr_wf (JCN c a).
Proof.
  intros c a Hc Ha.
  unfold instr_wf. split; assumption.
Qed.

Lemma decode_FIM_wf : forall r d,
  r < 16 -> r mod 2 = 0 -> d < 256 -> instr_wf (FIM r d).
Proof.
  intros r d Hr Heven Hd.
  unfold instr_wf. repeat split; assumption.
Qed.

Lemma decode_SRC_wf : forall r,
  r < 16 -> r mod 2 = 1 -> instr_wf (SRC r).
Proof.
  intros r Hr Hodd.
  unfold instr_wf. split; assumption.
Qed.

Lemma decode_FIN_wf : forall r,
  r < 16 -> r mod 2 = 0 -> instr_wf (FIN r).
Proof.
  intros r Hr Heven.
  unfold instr_wf. split; assumption.
Qed.

Lemma decode_JIN_wf : forall r,
  r < 16 -> r mod 2 = 1 -> instr_wf (JIN r).
Proof.
  intros r Hr Hodd.
  unfold instr_wf. split; assumption.
Qed.

Lemma decode_JUN_wf : forall a,
  a < 4096 -> instr_wf (JUN a).
Proof.
  intros a Ha.
  unfold instr_wf. assumption.
Qed.

Lemma decode_JMS_wf : forall a,
  a < 4096 -> instr_wf (JMS a).
Proof.
  intros a Ha.
  unfold instr_wf. assumption.
Qed.

Lemma decode_INC_wf : forall r,
  r < 16 -> instr_wf (INC r).
Proof.
  intros r Hr.
  unfold instr_wf. assumption.
Qed.

Lemma decode_ISZ_wf : forall r a,
  r < 16 -> a < 256 -> instr_wf (ISZ r a).
Proof.
  intros r a Hr Ha.
  unfold instr_wf. split; assumption.
Qed.

Lemma decode_ADD_wf : forall r,
  r < 16 -> instr_wf (ADD r).
Proof.
  intros r Hr.
  unfold instr_wf. assumption.
Qed.

Lemma decode_SUB_wf : forall r,
  r < 16 -> instr_wf (SUB r).
Proof.
  intros r Hr.
  unfold instr_wf. assumption.
Qed.

Lemma decode_LD_wf : forall r,
  r < 16 -> instr_wf (LD r).
Proof.
  intros r Hr.
  unfold instr_wf. assumption.
Qed.

Lemma decode_XCH_wf : forall r,
  r < 16 -> instr_wf (XCH r).
Proof.
  intros r Hr.
  unfold instr_wf. assumption.
Qed.

Lemma decode_BBL_wf : forall d,
  d < 16 -> instr_wf (BBL d).
Proof.
  intros d Hd.
  unfold instr_wf. assumption.
Qed.

Lemma decode_LDM_wf : forall d,
  d < 16 -> instr_wf (LDM d).
Proof.
  intros d Hd.
  unfold instr_wf. assumption.
Qed.

Lemma decode_other_wf : forall instr,
  (instr = WRM \/ instr = WMP \/ instr = WRR \/ instr = WPM \/
   instr = WR0 \/ instr = WR1 \/ instr = WR2 \/ instr = WR3 \/
   instr = SBM \/ instr = RDM \/ instr = RDR \/ instr = ADM \/
   instr = RD0 \/ instr = RD1 \/ instr = RD2 \/ instr = RD3 \/
   instr = CLB \/ instr = CLC \/ instr = IAC \/ instr = CMC \/
   instr = CMA \/ instr = RAL \/ instr = RAR \/ instr = TCC \/
   instr = DAC \/ instr = TCS \/ instr = STC \/ instr = DAA \/
   instr = KBP \/ instr = DCL) -> instr_wf instr.
Proof.
  intros instr Hinstr.
  unfold instr_wf.
  destruct Hinstr as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
  rewrite H; trivial.
Qed.

Lemma decode_wf_opcode_0 : forall b1 b2,
  b1 / 16 = 0 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. exact I.
Qed.

Lemma decode_wf_opcode_1 : forall b1 b2,
  b1 / 16 = 1 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf. split.
  apply mod_16_lt. assumption.
Qed.

Lemma decode_wf_opcode_2 : forall b1 b2,
  b1 / 16 = 2 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H.
  destruct ((b1 mod 16) mod 2 =? 0) eqn:E.
  - apply decode_FIM_wf.
    + apply mod_16_lt.
    + apply mod2_eq_iff. exact E.
    + exact H0.
  - apply decode_SRC_wf.
    + apply mod_16_lt.
    + apply mod2_neq_iff. exact E.
Qed.

Lemma decode_wf_opcode_3 : forall b1 b2,
  b1 / 16 = 3 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H.
  destruct ((b1 mod 16) mod 2 =? 0) eqn:E.
  - apply decode_FIN_wf.
    + apply mod_16_lt.
    + apply mod2_eq_iff. exact E.
  - apply decode_JIN_wf.
    + apply mod_16_lt.
    + apply mod2_neq_iff. exact E.
Qed.

Lemma decode_wf_opcode_4 : forall b1 b2,
  b1 / 16 = 4 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply addr12_bound.
Qed.

Lemma decode_wf_opcode_5 : forall b1 b2,
  b1 / 16 = 5 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply addr12_bound.
Qed.

Lemma decode_wf_opcode_6 : forall b1 b2,
  b1 / 16 = 6 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply mod_16_lt.
Qed.

Lemma decode_wf_opcode_7 : forall b1 b2,
  b1 / 16 = 7 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf. split.
  apply mod_16_lt. assumption.
Qed.

Lemma decode_wf_opcode_8 : forall b1 b2,
  b1 / 16 = 8 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply mod_16_lt.
Qed.

Lemma decode_wf_opcode_9 : forall b1 b2,
  b1 / 16 = 9 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply mod_16_lt.
Qed.

Lemma decode_wf_opcode_10 : forall b1 b2,
  b1 / 16 = 10 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply mod_16_lt.
Qed.

Lemma decode_wf_opcode_11 : forall b1 b2,
  b1 / 16 = 11 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply mod_16_lt.
Qed.

Lemma decode_wf_opcode_12 : forall b1 b2,
  b1 / 16 = 12 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply mod_16_lt.
Qed.

Lemma decode_wf_opcode_13 : forall b1 b2,
  b1 / 16 = 13 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H. simpl. unfold instr_wf.
  apply mod_16_lt.
Qed.

Lemma decode_wf_opcode_14 : forall b1 b2,
  b1 / 16 = 14 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H.
  destruct (b1 mod 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|m]]]]]]]]]]]]]]]; simpl;
    unfold instr_wf; try exact I.
  destruct m; exact I.
Qed.

Lemma decode_wf_opcode_15 : forall b1 b2,
  b1 / 16 = 15 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode. rewrite H.
  destruct (b1 mod 16) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|m]]]]]]]]]]]]]]; simpl;
    unfold instr_wf; exact I.
Qed.

Lemma decode_wf_opcode_ge_16 : forall b1 b2,
  b1 / 16 >= 16 -> b2 < 256 -> instr_wf (decode b1 b2).
Proof.
  intros. unfold decode.
  destruct (b1 / 16); try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; try lia.
  destruct n; unfold instr_wf; exact I.
Qed.

Lemma b1_div_16_lt_16 : forall b1, b1 < 256 -> b1 / 16 < 16.
Proof.
  intros. apply Nat.div_lt_upper_bound. lia. lia.
Qed.

Lemma decode_instr_wf : forall b1 b2,
  b1 < 256 -> b2 < 256 ->
  instr_wf (decode b1 b2).
Proof.
  intros b1 b2 Hb1 Hb2.
  assert (Hdiv: b1 / 16 < 16) by (apply b1_div_16_lt_16; assumption).
  destruct (b1 / 16) eqn:E.
  - apply decode_wf_opcode_0; assumption.
  - destruct n as [|n1].
    + apply decode_wf_opcode_1; assumption.
    + destruct n1 as [|n2].
      * apply decode_wf_opcode_2; assumption.
      * destruct n2 as [|n3].
        ** apply decode_wf_opcode_3; assumption.
        ** destruct n3 as [|n4].
           *** apply decode_wf_opcode_4; assumption.
           *** destruct n4 as [|n5].
               **** apply decode_wf_opcode_5; assumption.
               **** destruct n5 as [|n6].
                    ***** apply decode_wf_opcode_6; assumption.
                    ***** destruct n6 as [|n7].
                          ****** apply decode_wf_opcode_7; assumption.
                          ****** destruct n7 as [|n8].
                                 ******* apply decode_wf_opcode_8; assumption.
                                 ******* destruct n8 as [|n9].
                                         ******** apply decode_wf_opcode_9; assumption.
                                         ******** destruct n9 as [|n10].
                                                  ********* apply decode_wf_opcode_10; assumption.
                                                  ********* destruct n10 as [|n11].
                                                            ********** apply decode_wf_opcode_11; assumption.
                                                            ********** destruct n11 as [|n12].
                                                                       *********** apply decode_wf_opcode_12; assumption.
                                                                       *********** destruct n12 as [|n13].
                                                                                   ************ apply decode_wf_opcode_13; assumption.
                                                                                   ************ destruct n13 as [|n14].
                                                                                                ************* apply decode_wf_opcode_14; assumption.
                                                                                                ************* destruct n14 as [|n15].
                                                                                                              ************** apply decode_wf_opcode_15; assumption.
                                                                                                              ************** lia.
Qed.

(* Helper lemmas for execute_preserves_WF *)

Lemma execute_NOP_preserves_WF : forall s,
  WF s -> WF (execute s NOP).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor HromLen]]]]]]]]]]]]]].
  split. assumption.  (* length regs = 16 *)
  split. assumption.  (* Forall < 16 regs *)
  split. assumption.  (* acc < 16 *)
  split. apply addr12_bound.  (* pc < 4096 *)
  split. assumption.  (* stack length <= 3 *)
  split. assumption.  (* Forall < 4096 stack *)
  split. assumption.  (* ram_sys length = NBANKS *)
  split. assumption.  (* Forall WF_bank ram_sys *)
  split. assumption.  (* cur_bank < NBANKS *)
  split. assumption.  (* WF_sel sel_ram *)
  split. assumption.  (* rom_ports length = 16 *)
  split. assumption.  (* Forall < 16 rom_ports *)
  split. assumption.  (* sel_rom < 16 *)
  split. assumption.  (* Forall < 256 rom *)
  assumption.  (* rom length = 4096 *)
Qed.


Theorem execute_preserves_WF :
  forall s i, WF s -> instr_wf i -> WF (execute s i).
Proof.
Admitted.

Theorem step_preserves_WF : forall s, WF s -> WF (step s).
Proof.
  intros s Hwf. unfold step.
  set (b1 := fetch_byte s (pc s)).
  set (b2 := fetch_byte s (addr12_of_nat (pc s + 1))).
  apply (execute_preserves_WF s (decode b1 b2)); auto.
  apply decode_instr_wf.
  - unfold b1, fetch_byte.
    destruct (nth_in_or_default _ (pc s) (rom s) 0) as [Hin|Hdef].
    + destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HromFor _]]]]]]]]]]]]]].
      rewrite Forall_forall in HromFor.
      apply HromFor. exact Hin.
    + rewrite Hdef. lia.
  - unfold b2, fetch_byte.
    destruct (nth_in_or_default _ (addr12_of_nat (pc s + 1)) (rom s) 0) as [Hin|Hdef].
    + destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HromFor _]]]]]]]]]]]]]].
      rewrite Forall_forall in HromFor.
      apply HromFor. exact Hin.
    + rewrite Hdef. lia.
Qed.

Theorem steps_preserve_WF : forall n s, WF s -> WF (steps n s).
Proof.
  induction n; simpl; intros; auto. apply IHn. apply step_preserves_WF; assumption.
Qed.

(* ======================== Sanity theorems =========================== *)

Theorem nop_preserves_state : forall s,
  let s' := execute s NOP in
  acc s' = acc s /\ regs s' = regs s /\ carry s' = carry s /\ pc s' = addr12_of_nat (pc s + 1).
Proof. intros s. simpl. repeat split; reflexivity. Qed.

Theorem ldm_loads_immediate : forall s n,
  n < 16 ->
  let s' := execute s (LDM n) in
  acc s' = n /\ pc s' = addr12_of_nat (pc s + 1).
Proof.
  intros s n H. simpl. split.
  - unfold nibble_of_nat. rewrite Nat.mod_small; auto.
  - reflexivity.
Qed.

Theorem clb_clears : forall s,
  let s' := execute s CLB in
  acc s' = 0 /\ carry s' = false /\ pc s' = addr12_of_nat (pc s + 1).
Proof. intros s. simpl. repeat split; reflexivity. Qed.

(* Carry/Link check examples *)
Lemma sub_link_matches_spec : forall s r,
  let s' := execute s (SUB r) in
  carry s' = (16 <=? (acc s + 16 - get_reg s r - (if carry s then 0 else 1))).
Proof. intros; simpl; reflexivity. Qed.

Lemma dac_link_matches_spec : forall s,
  let s' := execute s DAC in carry s' = negb (acc s =? 0).
Proof. intros; simpl; reflexivity. Qed.

Lemma daa_adjust_rule : forall s,
  let s' := execute s DAA in
  acc s' = nibble_of_nat (if (9 <? acc s) || carry s then acc s + 6 else acc s) /\
  carry s' = ((9 <? acc s) || carry s || (16 <=? (if (9 <? acc s) || carry s then acc s + 6 else acc s))).
Proof. intros; simpl; split; reflexivity. Qed.

(* --- Page-relative control flow utilities (spec-accurate bases) --- *)

Lemma jin_pc_within_page : forall s r,
  let s' := execute s (JIN r) in
  exists off, off < 256 /\ pc s' = addr12_of_nat (page_base (pc_inc1 s) + off).
Proof.
  intros s r. simpl.
  eexists ((get_reg_pair s r) mod 256). split.
  - apply Nat.mod_upper_bound. lia.
  - reflexivity.
Qed.

Lemma fin_reads_from_page_of_next : forall s r,
  let s' := execute s (FIN r) in
  exists off, off < 256 /\
    regs s' = regs (set_reg_pair s r (fetch_byte s (addr12_of_nat (page_base (pc_inc1 s) + off)))).
Proof.
  intros. simpl.
  eexists ((get_reg_pair s 0) mod 256). split.
  - apply Nat.mod_upper_bound. lia.
  - reflexivity.
Qed.

Lemma isz_pc_shape : forall s r off,
  let s' := execute s (ISZ r off) in
  regs s' = regs (set_reg s r (nibble_of_nat (get_reg s r + 1))) /\
  (pc s' = addr12_of_nat (pc s + 2) \/
   pc s' = addr12_of_nat (page_base (pc_inc2 s) + off)).
Proof.
  intros s r off.
  unfold execute.
  remember (nibble_of_nat (get_reg s r + 1)) as new_val.
  remember (set_reg s r new_val) as s1.
  destruct (new_val =? 0) eqn:E.
  - simpl. split.
    + subst s1. reflexivity.
    + left. reflexivity.
  - simpl. split.
    + subst s1. reflexivity.
    + right. reflexivity.
Qed.

Lemma jcn_pc_shape : forall s cond off,
  let s' := execute s (JCN cond off) in
  (pc s' = addr12_of_nat (pc s + 2)) \/
  (pc s' = addr12_of_nat (base_for_next2 s + off)).
Proof.
  intros s cond off.
  cbv [execute].
  cbv [base_for_next2 pc_inc2].
  destruct (if (cond / 8 =? 1)
            then
             negb
               (orb (andb (acc s =? 0) ((cond / 4) mod 2 =? 1))
                    (orb (andb (carry s) ((cond / 2) mod 2 =? 1))
                         (andb (negb (test_pin s)) (cond mod 2 =? 1))))
            else
             orb (andb (acc s =? 0) ((cond / 4) mod 2 =? 1))
                 (orb (andb (carry s) ((cond / 2) mod 2 =? 1))
                      (andb (negb (test_pin s)) (cond mod 2 =? 1)))) eqn:E.
  - right. simpl. reflexivity.
  - left. simpl. reflexivity.
Qed.

(* --- Determinism & PC-shape of step --- *)

Theorem step_deterministic : forall s s1 s2,
  s1 = step s -> s2 = step s -> s1 = s2.
Proof. congruence. Qed.

Lemma pc_shape_nop : forall s, pc (execute s NOP) = addr12_of_nat (pc s + 1).
Proof. intros. unfold execute. unfold pc_inc1. reflexivity. Qed.

Lemma pc_shape_jun : forall s a, pc (execute s (JUN a)) = a.
Proof. intros. unfold execute. reflexivity. Qed.

Lemma pc_shape_jms : forall s a, pc (execute s (JMS a)) = a.
Proof. intros. unfold execute. reflexivity. Qed.

Lemma pc_shape_fim : forall s r d, pc (execute s (FIM r d)) = addr12_of_nat (pc s + 2).
Proof. intros. unfold execute. unfold pc_inc2. reflexivity. Qed.

Lemma page_base_eq_page_times_256 : forall a,
  page_base a = page_of a * 256.
Proof. intros. unfold page_base. reflexivity. Qed.

Lemma pc_shape_jin : forall s r,
  pc (execute s (JIN r)) = addr12_of_nat (page_of (pc_inc1 s) * 256 + get_reg_pair s r mod 256).
Proof. intros. unfold execute. reflexivity. Qed.

Lemma jin_pc_in_page_range : forall s r,
  exists off, off < 256 /\ pc (execute s (JIN r)) = addr12_of_nat (page_base (pc_inc1 s) + off).
Proof.
  intros. exists (get_reg_pair s r mod 256).
  split.
  - apply Nat.mod_upper_bound. lia.
  - rewrite pc_shape_jin. rewrite page_base_eq_page_times_256. reflexivity.
Qed.

Lemma pc_shape_isz_zero : forall s r off,
  nibble_of_nat (get_reg s r + 1) = 0 ->
  pc (execute s (ISZ r off)) = addr12_of_nat (pc s + 2).
Proof.
  intros. unfold execute. rewrite H. unfold pc_inc2. reflexivity.
Qed.

Lemma pc_shape_isz_nonzero : forall s r off,
  nibble_of_nat (get_reg s r + 1) <> 0 ->
  pc (execute s (ISZ r off)) = addr12_of_nat (page_base (pc_inc2 s) + off).
Proof.
  intros. unfold execute.
  destruct (nibble_of_nat (get_reg s r + 1) =? 0) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma pc_shape_bbl_some : forall s d addr s1,
  pop_stack s = (Some addr, s1) ->
  pc (execute s (BBL d)) = addr.
Proof. intros. unfold execute. rewrite H. reflexivity. Qed.

Lemma pc_shape_bbl_none : forall s d s1,
  pop_stack s = (None, s1) ->
  pc (execute s (BBL d)) = addr12_of_nat (pc s + 1).
Proof. intros. unfold execute. rewrite H. unfold pc_inc1. reflexivity. Qed.

Lemma stack_addr_bound : forall s addr s1,
  WF s ->
  pop_stack s = (Some addr, s1) ->
  addr < 4096.
Proof.
  intros s addr s1 Hwf Hpop.
  unfold WF in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ [Hstack_all _]]]]]].
  unfold pop_stack in Hpop.
  destruct (stack s) as [|a rest] eqn:E.
  - discriminate.
  - inversion Hpop; subst. simpl in Hstack_all.
    inversion Hstack_all; subst. assumption.
Qed.

Lemma execute_pc_bounded : forall s i,
  instr_wf i ->
  WF s ->
  pc (execute s i) = addr12_of_nat (pc s + 1) \/
  pc (execute s i) = addr12_of_nat (pc s + 2) \/
  (exists off, off < 256 /\ pc (execute s i) = addr12_of_nat (page_base (pc_inc1 s) + off)) \/
  (exists off, off < 256 /\ pc (execute s i) = addr12_of_nat (page_base (pc_inc2 s) + off)) \/
  (exists a, pc (execute s i) = a /\ a < 4096).
Proof.
  intros s i Hwf_i Hwf_s.
  destruct i.

  - left. apply pc_shape_nop.

  - destruct Hwf_i as [Hc Ha].
    unfold execute.
    set (c1 := n / 8).
    set (c2 := (n / 4) mod 2).
    set (c3 := (n / 2) mod 2).
    set (c4 := n mod 2).
    set (base_cond := orb (andb (acc s =? 0) (c2 =? 1))
                          (orb (andb (carry s) (c3 =? 1))
                               (andb (negb (test_pin s)) (c4 =? 1)))).
    set (jump := if c1 =? 1 then negb base_cond else base_cond).
    destruct jump.
    + right. right. right. left.
      exists b. split.
      * exact Ha.
      * unfold base_for_next2, page_base, page_of, pc_inc2. reflexivity.
    + right. left. unfold pc_inc2. reflexivity.

  - right. left. apply pc_shape_fim.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - right. right. left.
    apply jin_pc_in_page_range.

  - right. right. right. right.
    exists a. split.
    + apply pc_shape_jun.
    + exact Hwf_i.

  - right. right. right. right.
    exists a. split.
    + apply pc_shape_jms.
    + exact Hwf_i.

  - left. unfold execute, pc_inc1. reflexivity.

  - destruct Hwf_i as [Hr Hb].
    unfold execute.
    remember (nibble_of_nat (get_reg s n + 1)) as new_val.
    destruct (new_val =? 0) eqn:E.
    + right. left. unfold pc_inc2. reflexivity.
    + right. right. right. left.
      exists b. split.
      * exact Hb.
      * unfold base_for_next2, page_base, page_of, pc_inc2. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - unfold execute.
    destruct (pop_stack s) as [[addr|] s'] eqn:Epop.
    + right. right. right. right.
      exists addr. split.
      * reflexivity.
      * eapply stack_addr_bound; eauto.
    + left. unfold pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.

  - left. unfold execute, pc_inc1. reflexivity.
Qed.

Theorem step_pc_shape :
  forall s,
  WF s ->
  let s' := step s in
  pc s' = addr12_of_nat (pc s + 1) \/
  pc s' = addr12_of_nat (pc s + 2) \/
  (exists off, off < 256 /\ pc s' = addr12_of_nat (page_base (pc_inc1 s) + off)) \/
  (exists off, off < 256 /\ pc s' = addr12_of_nat (page_base (pc_inc2 s) + off)) \/
  (exists a, pc s' = a /\ (a < 4096)).
Proof.
Admitted.

(* --- Frames (no unintended writes) --- *)

Lemma pop_stack_preserves_regs : forall s opt s',
  pop_stack s = (opt, s') -> regs s' = regs s.
Proof.
  intros s opt s' H.
  unfold pop_stack in H.
  destruct (stack s) as [|a rest] eqn:E.
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
Qed.

Definition writes_regs (i:Instruction) : bool :=
  match i with
  | XCH _ | INC _ | FIM _ _ | FIN _ | ISZ _ _ => true
  | _ => false
  end.

Definition writes_ram (i:Instruction) : bool :=
  match i with
  | WRM | WMP | WR0 | WR1 | WR2 | WR3 => true
  | _ => false
  end.

Lemma execute_regs_frame : forall s i,
  writes_regs i = false ->
  regs (execute s i) = regs s.
Proof.
  intros s i H.
  destruct i; simpl in H; try discriminate; unfold execute; fold execute;
  try reflexivity.
  - set (c1 := n / 8).
    set (c2 := (n / 4) mod 2).
    set (c3 := (n / 2) mod 2).
    set (c4 := n mod 2).
    set (base_cond := orb (andb (acc s =? 0) (c2 =? 1)) (orb (andb (carry s) (c3 =? 1)) (andb (negb (test_pin s)) (c4 =? 1)))).
    set (jump := if c1 =? 1 then negb base_cond else base_cond).
    destruct jump; reflexivity.
  - destruct (pop_stack s) as [[a_opt|] s'] eqn:Epop.
    + rewrite (pop_stack_preserves_regs s (Some a_opt) s' Epop). reflexivity.
    + rewrite (pop_stack_preserves_regs s None s' Epop). reflexivity.
Qed.

Lemma execute_ram_frame : forall s i,
  writes_ram i = false ->
  ram_sys (execute s i) = ram_sys s.
Proof.
  intros s i H.
  destruct i; simpl in H; try discriminate; unfold execute; fold execute;
  try reflexivity.
  - set (c1 := n / 8).
    set (c2 := (n / 4) mod 2).
    set (c3 := (n / 2) mod 2).
    set (c4 := n mod 2).
    set (base_cond := orb (andb (acc s =? 0) (c2 =? 1)) (orb (andb (carry s) (c3 =? 1)) (andb (negb (test_pin s)) (c4 =? 1)))).
    set (jump := if c1 =? 1 then negb base_cond else base_cond).
    destruct jump; reflexivity.
  - set (new_val := nibble_of_nat (get_reg s n + 1)).
    destruct (new_val =? 0); reflexivity.
  - destruct (pop_stack s) as [[?|] ?]; reflexivity.
Qed.

(* --- KBP mapping & TEST note --- *)

Lemma kbp_map_cases : forall s,
  let s' := execute s KBP in
  acc s' = match acc s with
           | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4 | _ => 15
           end.
Proof. intros; simpl; reflexivity. Qed.

(* ================== Simple end-to-end port sanity =================== *)

(* After SRC selecting ROM port P and WRR, the ROM port P holds ACC. *)
Lemma src_wrr_updates_rom_port : forall s r,
  WF s ->
  let pair := get_reg_pair s r in
  let P := pair / 16 in
  let s1 := execute s (SRC r) in
  let s2 := execute s1 WRR in
  nth P (rom_ports s2) 0 = acc s.
Proof.
  intros s r Hwf pair P s1 s2.
  subst pair P s1 s2.
  unfold execute at 2. fold execute.
  unfold execute at 1. fold execute.
  simpl rom_ports.
  rewrite nth_update_nth_eq.
  - unfold execute. fold execute. simpl. unfold nibble_of_nat.
    rewrite Nat.mod_small by (destruct Hwf as [_ [_ [Hacc _]]]; exact Hacc).
    reflexivity.
  - destruct Hwf as [Hregs_len [Hregs_forall [_ [_ [_ [_ [_ [_ [_ [_ [Hlen _]]]]]]]]]]].
    rewrite Hlen.
    assert (get_reg_pair s r < 256).
    { unfold get_reg_pair.
      set (r_even := r - r mod 2).
      assert (get_reg s r_even < 16) by (eapply nth_Forall_lt; eauto; lia).
      assert (get_reg s (r_even + 1) < 16) by (eapply nth_Forall_lt; eauto; lia).
      unfold get_reg in *.
      assert (H1: nth r_even (regs s) 0 * 16 < 16 * 16) by nia.
      assert (H2: nth (r_even + 1) (regs s) 0 < 16) by assumption.
      nia. }
    assert (get_reg_pair s r / 16 < 16) by (apply Nat.div_lt_upper_bound; lia).
    exact H0.
Qed.

Lemma get_reg_pair_bound : forall s r,
  length (regs s) = 16 ->
  Forall (fun x => x < 16) (regs s) ->
  get_reg_pair s r < 256.
Proof.
  intros s r Hlen Hall.
  unfold get_reg_pair, get_reg.
  set (r_even := r - r mod 2).
  assert (Hrlo: nth (r_even + 1) (regs s) 0 < 16).
  { destruct (Nat.lt_ge_cases (r_even + 1) 16).
    - eapply nth_Forall_lt; eauto; lia.
    - rewrite nth_overflow by lia. lia. }
  assert (Hrhi: nth r_even (regs s) 0 < 16).
  { destruct (Nat.lt_ge_cases r_even 16).
    - eapply nth_Forall_lt; eauto; lia.
    - rewrite nth_overflow by lia. lia. }
  nia.
Qed.

Lemma wrm_then_rdm_reads_back : forall s r,
  WF s ->
  let v := acc s in
  let s1 := execute s (SRC r) in
  let s2 := execute s1 WRM in
  let s3 := execute s2 RDM in
  acc s3 = v.
Proof.
  intros s r Hwf v s1 s2 s3.
  subst v s1 s2 s3.
  unfold WF in Hwf.
  destruct Hwf as [Hregs_len Hwf_rest].
  destruct Hwf_rest as [Hregs_all Hwf_rest].
  destruct Hwf_rest as [Hacc Hwf_rest].
  destruct Hwf_rest as [Hpc Hwf_rest].
  destruct Hwf_rest as [Hstack_len Hwf_rest].
  destruct Hwf_rest as [Hstack_all Hwf_rest].
  destruct Hwf_rest as [Hram_len Hwf_rest].
  destruct Hwf_rest as [Hram_all Hwf_rest].
  destruct Hwf_rest as [Hbank Hwf_rest].
  destruct Hwf_rest as [Hsel Hwf_rest].
  destruct Hwf_rest as [Hrom_len Hwf_rest].
  destruct Hwf_rest as [Hrom_all Hwf_rest].
  destruct Hwf_rest as [Hsel_rom Hwf_rest].
  destruct Hwf_rest as [Hrom_bytes Hrom_len2].
  unfold execute at 3. unfold execute at 2. unfold execute at 1.
  assert (Hpair: get_reg_pair s r < 256) by (apply get_reg_pair_bound; auto).
  set (hi := get_reg_pair s r / 16) in *.
  set (lo := get_reg_pair s r mod 16) in *.
  set (chip := hi / 4) in *.
  set (rno := hi mod 4) in *.
  assert (Hhi: hi < 16) by (subst hi; apply Nat.div_lt_upper_bound; lia).
  assert (Hlo: lo < 16) by (subst lo; apply Nat.mod_bound_pos; lia).
  assert (Hchip: chip < 4) by (subst chip; apply Nat.div_lt_upper_bound; lia).
  assert (Hrno: rno < 4) by (subst rno; apply Nat.mod_bound_pos; lia).
  set (selr := mkRAMSel chip rno lo) in *.
  set (s1 := mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
                     (ram_sys s) (cur_bank s) selr
                     (rom_ports s) hi (rom s) (test_pin s) (prog_pulses s)).
  assert (Hs1_props: cur_bank s1 = cur_bank s /\ sel_ram s1 = selr /\ ram_sys s1 = ram_sys s /\ acc s1 = acc s).
  { subst s1. simpl. auto. }
  destruct Hs1_props as [Hs1_bank [Hs1_sel [Hs1_ram Hs1_acc]]].
  assert (Hsel_bounds: sel_chip selr < NCHIPS /\ sel_reg selr < NREGS /\ sel_char selr < NMAIN).
  { subst selr. simpl. unfold NCHIPS, NREGS, NMAIN. split; [|split]; lia. }
  destruct Hsel_bounds as [Hsel_chip [Hsel_reg Hsel_char]].
  set (s2 := mkState (acc s1) (regs s1) (carry s1) (pc_inc1 s1) (stack s1)
                     (ram_write_main_sys s1 (acc s1)) (cur_bank s1) (sel_ram s1)
                     (rom_ports s1) (sel_rom s1) (rom s1) (test_pin s1) (prog_pulses s1)).
  assert (Hs1_WF: WF s1).
  { subst s1 selr. unfold WF. simpl.
    split. exact Hregs_len.
    split. exact Hregs_all.
    split. exact Hacc.
    split. { unfold pc_inc1. apply addr12_bound. }
    split. exact Hstack_len.
    split. exact Hstack_all.
    split. exact Hram_len.
    split. exact Hram_all.
    split. exact Hbank.
    split. { unfold WF_sel. simpl. unfold NCHIPS, NREGS, NMAIN. split; [|split]; lia. }
    split. exact Hrom_len.
    split. exact Hrom_all.
    split. { simpl. lia. }
    split. exact Hrom_bytes.
    exact Hrom_len2. }
  assert (Heq: ram_read_main s2 = nibble_of_nat (acc s1)).
  { subst s2. apply ram_write_then_read_main.
    - exact Hs1_WF.
    - rewrite Hs1_bank. exact Hbank.
    - rewrite Hs1_sel. exact Hsel_chip.
    - rewrite Hs1_sel. exact Hsel_reg.
    - rewrite Hs1_sel. exact Hsel_char. }
  rewrite Heq. rewrite Hs1_acc.
  unfold nibble_of_nat. rewrite Nat.mod_small by lia. reflexivity.
Qed.
    

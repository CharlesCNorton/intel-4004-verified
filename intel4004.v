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

(** Type alias for 4-bit values (0-15). No inherent bounds enforcement. *)
Definition nibble := nat.

(** Normalizes arbitrary nat to 4-bit range via mod 16. *)
Definition nibble_of_nat (n : nat) : nibble := n mod 16.

(** Type alias for 8-bit values (0-255). No inherent bounds enforcement. *)
Definition byte := nat.

(** Normalizes arbitrary nat to 8-bit range via mod 256. *)
Definition byte_of_nat (n : nat) : byte := n mod 256.

(** Type alias for 12-bit addresses (0-4095). No inherent bounds enforcement. *)
Definition addr12 := nat.

(** Normalizes arbitrary nat to 12-bit address space via mod 4096. *)
Definition addr12_of_nat (n : nat) : addr12 := n mod 4096.

(** Proves addr12_of_nat always produces values strictly less than 4096. *)
Lemma addr12_bound : forall n, addr12_of_nat n < 4096.
Proof.
  intro n. unfold addr12_of_nat. apply Nat.mod_upper_bound. lia.
Qed.

(** Proves nibble_of_nat always produces values strictly less than 16. *)
Lemma nibble_lt16 : forall n, nibble_of_nat n < 16.
Proof. intro n. unfold nibble_of_nat. apply Nat.mod_upper_bound. lia. Qed.

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

(** Proves nth of update_nth at same index returns the updated element. *)
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

(** Decides whether nth n l d is actually in l or equals the default d. *)
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

(** 4002 RAM register: 16 main characters + 4 status characters. No bounds enforced. *)
Record RAMReg := mkRAMReg {
  reg_main   : list nibble;  (* 16 main characters *)
  reg_status : list nibble   (* 4 status characters S0..S3 *)
}.

(** 4002 RAM chip: 4 registers + 4-bit output port. No bounds enforced. *)
Record RAMChip := mkRAMChip {
  chip_regs  : list RAMReg;  (* 4 registers *)
  chip_port  : nibble        (* 4-bit output port *)
}.

(** 4002 RAM bank: 4 chips. No bounds enforced. *)
Record RAMBank := mkRAMBank {
  bank_chips : list RAMChip  (* 4 chips per bank *)
}.

(** RAM address selection state. Chip/reg latched by SRC; bank by DCL. No bounds enforced. *)
Record RAMSel := mkRAMSel {
  sel_chip : nat;   (* 0..3 *)
  sel_reg  : nat;   (* 0..3 *)
  sel_char : nat    (* 0..15 *)
}.

(* ============================ State ================================= *)

(** Complete Intel 4004 + MCS-4 system state. 17 fields. No bounds enforced by types. *)
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
  rom       : list byte;        (* program ROM (bytes) - writable via WPM *)
  test_pin  : bool;             (* TEST input (active low in JCN condition) *)
  prom_addr : addr12;           (* PROM programming address (set via ROM ports) *)
  prom_data : byte;             (* PROM programming data (set via ROM ports) *)
  prom_enable : bool            (* PROM write enable (set via ROM port control) *)
}.

(* =========================== Registers ============================== *)

(** Reads register r. Returns 0 if r >= length of register file. *)
Definition get_reg (s : Intel4004State) (r : nat) : nibble :=
  nth r (regs s) 0.

(** Sets register r to normalized value v. Preserves all other state fields. *)
Definition set_reg (s : Intel4004State) (r : nat) (v : nibble) : Intel4004State :=
  let new_regs := update_nth r (nibble_of_nat v) (regs s) in
  mkState (acc s) new_regs (carry s) (pc s) (stack s)
          (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
          (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s).

(** Reads register pair starting at r (rounds down to even). Returns high*16 + low. *)
Definition get_reg_pair (s : Intel4004State) (r : nat) : byte :=
  let r_even := r - (r mod 2) in
  let high := get_reg s r_even in
  let low  := get_reg s (r_even + 1) in
  (high * 16) + low.

(** Sets register pair starting at r (rounds down to even) to v split into high/low nibbles. *)
Definition set_reg_pair (s : Intel4004State) (r : nat) (v : byte) : Intel4004State :=
  let r_even := r - (r mod 2) in
  let high := v / 16 in
  let low  := v mod 16 in
  let s1 := set_reg s r_even high in
  set_reg s1 (r_even + 1) low.

(** Proves set_reg preserves register file length. *)
Lemma set_reg_preserves_length : forall s r v,
  length (regs (set_reg s r v)) = length (regs s).
Proof. intros. simpl. apply update_nth_length. Qed.

(** Proves set_reg_pair preserves register file length. *)
Lemma set_reg_pair_preserves_length : forall s r v,
  length (regs (set_reg_pair s r v)) = length (regs s).
Proof.
  intros. unfold set_reg_pair.
  rewrite set_reg_preserves_length.
  rewrite set_reg_preserves_length.
  reflexivity.
Qed.

(** Proves set_reg preserves Forall (< 16) bound on registers. *)
Lemma set_reg_preserves_Forall16 : forall s r v,
  Forall (fun x => x < 16) (regs s) ->
  Forall (fun x => x < 16) (regs (set_reg s r v)).
Proof.
  intros. simpl. eapply Forall_update_nth; eauto. apply nibble_lt16.
Qed.

(** Proves set_reg_pair preserves Forall (< 16) bound on registers. *)
Lemma set_reg_pair_preserves_Forall16 : forall s r v,
  Forall (fun x => x < 16) (regs s) ->
  Forall (fun x => x < 16) (regs (set_reg_pair s r v)).
Proof.
  intros. unfold set_reg_pair.
  apply set_reg_preserves_Forall16.
  apply set_reg_preserves_Forall16.
  assumption.
Qed.

(** Proves nth of bounded register file with default 0 is also bounded. *)
Lemma nth_reg0_lt16 : forall s n,
  Forall (fun x => x < 16) (regs s) ->
  nth n (regs s) 0 < 16.
Proof. intros. eapply nth_Forall_lt with (k:=16); eauto; lia. Qed.

(* ============================= Stack ================================ *)

(** Pushes addr onto 3-level stack. Discards bottom level if full. *)
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
          (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s).

(** Pops top address from stack. Returns None if stack empty. *)
Definition pop_stack (s : Intel4004State) : (option addr12 * Intel4004State) :=
  match stack s with
  | [] => (None, s)
  | a :: rest =>
      (Some a, mkState (acc s) (regs s) (carry s) (pc s) rest
                       (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                       (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s))
  end.

(** Proves push_stack always produces stack of length <= 3. *)
Lemma push_stack_len_le3 : forall s a,
  length (stack (push_stack s a)) <= 3.
Proof. intros s a. unfold push_stack. destruct (stack s) as [|x [|x0 [|x1 l]]]; simpl; lia. Qed.

(** Proves pop_stack preserves stack length bound <= 3 when input <= 4. *)
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

(** Proves pop_stack preserves Forall (< 4096) on stack addresses. *)
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

(** Fetches byte from ROM at addr. Returns 0 if addr >= ROM length. *)
Definition fetch_byte (s : Intel4004State) (addr : addr12) : byte :=
  nth addr (rom s) 0.

(** Increments PC by 1, normalized to 12-bit address space. *)
Definition pc_inc1 (s : Intel4004State) : addr12 := addr12_of_nat (pc s + 1).

(** Increments PC by 2, normalized to 12-bit address space. *)
Definition pc_inc2 (s : Intel4004State) : addr12 := addr12_of_nat (pc s + 2).

(** Extracts page number (upper 4 bits) from 12-bit address. *)
Definition page_of (p:addr12) := p / 256.

(** Computes base address of page containing p. *)
Definition page_base (p:addr12) := (page_of p) * 256.

(* ========================= RAM navigation =========================== *)

(** RAM system dimension constants. *)
Definition NBANKS := 4.
Definition NCHIPS := 4.
Definition NREGS  := 4.
Definition NMAIN  := 16.
Definition NSTAT  := 4.

(** Retrieves bank b from state. Returns empty default if b >= NBANKS. *)
Definition get_bank (s:Intel4004State) (b:nat) : RAMBank :=
  nth b (ram_sys s) (mkRAMBank (repeat (mkRAMChip (repeat (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)) NREGS) 0) NCHIPS)).

(** Retrieves chip c from bank. Returns empty default if c >= NCHIPS. *)
Definition get_chip (bk:RAMBank) (c:nat) : RAMChip :=
  nth c (bank_chips bk) (mkRAMChip (repeat (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)) NREGS) 0).

(** Retrieves register r from chip. Returns empty default if r >= NREGS. *)
Definition get_regRAM (ch:RAMChip) (r:nat) : RAMReg :=
  nth r (chip_regs ch) (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)).

(** Retrieves main character i from register. Returns 0 if i >= NMAIN. *)
Definition get_main (rg:RAMReg) (i:nat) : nibble := nth i (reg_main rg) 0.

(** Retrieves status character i from register. Returns 0 if i >= NSTAT. *)
Definition get_stat (rg:RAMReg) (i:nat) : nibble := nth i (reg_status rg) 0.

(** Updates main character i in register to normalized v. *)
Definition upd_main_in_reg (rg:RAMReg) (i:nat) (v:nibble) : RAMReg :=
  mkRAMReg (update_nth i (nibble_of_nat v) (reg_main rg)) (reg_status rg).

(** Updates status character i in register to normalized v. *)
Definition upd_stat_in_reg (rg:RAMReg) (i:nat) (v:nibble) : RAMReg :=
  mkRAMReg (reg_main rg) (update_nth i (nibble_of_nat v) (reg_status rg)).

(** Updates register r in chip with new register value. *)
Definition upd_reg_in_chip (ch:RAMChip) (r:nat) (rg:RAMReg) : RAMChip :=
  mkRAMChip (update_nth r rg (chip_regs ch)) (chip_port ch).

(** Updates output port in chip to normalized v. *)
Definition upd_port_in_chip (ch:RAMChip) (v:nibble) : RAMChip :=
  mkRAMChip (chip_regs ch) (nibble_of_nat v).

(** Updates chip c in bank with new chip value. *)
Definition upd_chip_in_bank (bk:RAMBank) (c:nat) (ch:RAMChip) : RAMBank :=
  mkRAMBank (update_nth c ch (bank_chips bk)).

(** Updates bank b in system with new bank value. Returns updated bank list. *)
Definition upd_bank_in_sys (s:Intel4004State) (b:nat) (bk:RAMBank) : list RAMBank :=
  update_nth b bk (ram_sys s).

(** Reads main character from RAM using current bank and latched selection. *)
Definition ram_read_main (s:Intel4004State) : nibble :=
  let bk := get_bank s (cur_bank s) in
  let ch := get_chip bk (sel_chip (sel_ram s)) in
  let rg := get_regRAM ch (sel_reg (sel_ram s)) in
  get_main rg (sel_char (sel_ram s)).

(** Writes main character to RAM using current bank and latched selection. Returns updated bank list. *)
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

(** Writes status character idx to RAM using current bank and latched selection. Returns updated bank list. *)
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

(** Writes to RAM chip output port using current bank and latched chip selection. Returns updated bank list. *)
Definition ram_write_port_sys (s:Intel4004State) (v:nibble) : list RAMBank :=
  let b := cur_bank s in
  let c := sel_chip (sel_ram s) in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let ch' := upd_port_in_chip ch v in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.

(* =============================== ISA ================================ *)

(** Intel 4004 instruction set. 43 instructions total. *)
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

(** Decodes two bytes into Intel 4004 instruction. Always total (returns NOP for invalid). *)
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

(** Encodes instruction to two-byte representation. Inverse of decode for well-formed instructions. *)
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

(** Well-formedness predicate for instructions. Ensures parameters are in valid ranges. *)
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

(** Proves n - n mod 2 = n when n is even. *)
Lemma even_sub_mod : forall n, n mod 2 = 0 -> n - n mod 2 = n.
Proof.
  intros n H. rewrite H. rewrite Nat.sub_0_r. reflexivity.
Qed.

(** Proves n - n mod 2 = n - 1 when n is odd. *)
Lemma odd_sub_mod : forall n, n mod 2 = 1 -> n - n mod 2 = n - 1.
Proof.
  intros n H. rewrite H. reflexivity.
Qed.

(** Proves (n - n mod 2) + 1 < 16 for odd n < 16. *)
Lemma odd_range_helper : forall n, n < 16 -> n mod 2 = 1 -> (n - n mod 2) + 1 < 16.
Proof.
  intros n Hn Hodd.
  rewrite odd_sub_mod by assumption.
  lia.
Qed.

(** Proves every natural number is either even or odd. *)
Lemma mod2_cases : forall n, n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros n. pose proof (Nat.mod_upper_bound n 2).
  assert (n mod 2 < 2) by (apply H; lia).
  destruct (n mod 2); [left|right]; auto.
  destruct n0; auto. lia.
Qed.

(** Proves decode correctly interprets all even opcode 2 variants as FIM with correct register indices. *)
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

(** Proves encode-decode roundtrip for SRC instruction with odd register indices. *)
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

(** Proves encode-decode roundtrip for FIN instruction with even register indices. *)
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

(** Proves encode-decode roundtrip for JIN instruction with odd register indices. *)
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

(** Proves division-modulo identity for base 256. *)
Lemma divmod_representation : forall a,
  a = 256 * (a / 256) + a mod 256.
Proof.
  intro a.
  apply Nat.div_mod.
  lia.
Qed.

(** Proves adding multiple of n doesn't change result mod n. *)
Lemma mod_add_multiple : forall a b n,
  n <> 0 ->
  (n * a + b) mod n = b mod n.
Proof.
  intros a b n Hn.
  rewrite Nat.Div0.add_mod by exact Hn.
  assert (n * a mod n = 0).
  { rewrite Nat.mul_comm.
    apply Nat.Div0.mod_mul. }
  rewrite H.
  rewrite Nat.add_0_l.
  rewrite Nat.Div0.mod_mod by exact Hn.
  reflexivity.
Qed.

(** Proves division-modulo reconstruction identity for base 256. *)
Lemma div_256_mul_256_add_mod_256_eq : forall a,
  (a / 256) * 256 + a mod 256 = a.
Proof.
  intro a.
  rewrite Nat.mul_comm.
  symmetry.
  apply Nat.div_mod.
  lia.
Qed.

(** Proves addr12_of_nat is identity for values already in 12-bit range. *)
Lemma addr12_of_nat_mod_small : forall n,
  n < 4096 ->
  addr12_of_nat n = n.
Proof.
  intros n Hn.
  unfold addr12_of_nat.
  apply Nat.mod_small.
  exact Hn.
Qed.

(** Proves existence of quotient-remainder representation for any nat. *)
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

(** Proves addr12_of_nat reconstructs 12-bit address from page and offset. *)
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

(** Proves addr12_of_nat with explicit div/mod is identity for 12-bit values. *)
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

(** Proves encoding arithmetic for JUN/JMS opcodes produces correct div/mod results. *)
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

(** Proves encode-decode roundtrip for FIM instruction. *)
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

(** Main encode-decode bijection theorem: decode (encode i) = i for all well-formed instructions. *)
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

(** Computes page base for PC+1. Used by 1-byte indirect jumps (FIN/JIN). *)
Definition base_for_next1 (s:Intel4004State) := page_base (pc_inc1 s).

(** Computes page base for PC+2. Used by 2-byte conditional branches (JCN/ISZ). *)
Definition base_for_next2 (s:Intel4004State) := page_base (pc_inc2 s).

(** Executes single instruction. Returns new state. Total function (handles all 43 instructions). *)
Definition execute (s : Intel4004State) (inst : Instruction) : Intel4004State :=
  match inst with
  | NOP =>
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | LDM n =>
      mkState (nibble_of_nat n) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | LD r =>
      mkState (get_reg s r) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | XCH r =>
      let old_acc := acc s in
      let old_reg := get_reg s r in
      let s1 := set_reg s r old_acc in
      mkState old_reg (regs s1) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | INC r =>
      let new_val := nibble_of_nat (get_reg s r + 1) in
      let s1 := set_reg s r new_val in
      mkState (acc s) (regs s1) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | ADD r =>
      let sum := (acc s) + (get_reg s r) + (if carry s then 1 else 0) in
      mkState (nibble_of_nat sum) (regs s) (16 <=? sum) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | SUB r =>
      let reg_val := get_reg s r in
      let borrow := if carry s then 0 else 1 in
      let diff := (acc s) + 16 - reg_val - borrow in
      mkState (nibble_of_nat diff) (regs s) (16 <=? diff) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | IAC =>
      let sum := (acc s) + 1 in
      mkState (nibble_of_nat sum) (regs s) (16 <=? sum) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | DAC =>
      let newv := (acc s) + 15 in  (* -1 mod 16 *)
      let borrow := (acc s =? 0) in
      mkState (nibble_of_nat newv) (regs s) (negb borrow) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | CLC =>
      mkState (acc s) (regs s) false (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | STC =>
      mkState (acc s) (regs s) true (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | CMC =>
      mkState (acc s) (regs s) (negb (carry s)) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | CMA =>
      mkState (nibble_of_nat (15 - (acc s))) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | CLB =>
      mkState 0 (regs s) false (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | RAL =>
      let new_acc := nibble_of_nat ((acc s) * 2 + if carry s then 1 else 0) in
      let new_carry := 8 <=? (acc s) in
      mkState new_acc (regs s) new_carry (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | RAR =>
      let new_acc := nibble_of_nat ((acc s) / 2 + if carry s then 8 else 0) in
      let new_carry := (acc s) mod 2 =? 1 in
      mkState new_acc (regs s) new_carry (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | TCC =>
      mkState (if carry s then 1 else 0) (regs s) false (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | TCS =>
      mkState (if carry s then 10 else 9) (regs s) false (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | DAA =>
      let acc_with_carry := acc s + (if carry s then 1 else 0) in
      let needs_adjust := 9 <? acc_with_carry in
      let adjusted := if needs_adjust then acc_with_carry + 6 else acc_with_carry in
      mkState (nibble_of_nat adjusted)
              (regs s)
              (16 <=? adjusted)
              (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | KBP =>
      (* Keyboard Process: Convert 1-of-n code to binary position
         Returns position (1-4) for single-bit values (1,2,4,8)
         Returns 15 for any other value (including 0 and multi-bit values)
         NOTE: Real 4004 behavior for multi-bit inputs is undocumented;
         returning 15 is a conservative choice matching the datasheet spec. *)
      let result :=
        match acc s with
        | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4 | _ => 15
        end in
      mkState result (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | JUN addr =>
      mkState (acc s) (regs s) (carry s) addr (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | JMS addr =>
      let s1 := push_stack s (addr12_of_nat (pc s + 2)) in
      mkState (acc s) (regs s) (carry s) addr (stack s1)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | BBL n =>
      match pop_stack s with
      | (Some addr, s1) =>
          mkState (nibble_of_nat n) (regs s1) (carry s) addr (stack s1)
                  (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                  (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
      | (None, s1) =>
          mkState (nibble_of_nat n) (regs s1) (carry s) (pc_inc1 s) (stack s1)
                  (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                  (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
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
                   (rom_ports s) (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
      else mkState (acc s) (regs s) (carry s) (pc_inc2 s) (stack s)
                   (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                   (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | FIM r data =>
      (* load immediate into register *pair* r (even) *)
      let s1 := set_reg_pair s r data in
      mkState (acc s) (regs s1) (carry s) (pc_inc2 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | ISZ r off =>
      let new_val := nibble_of_nat (get_reg s r + 1) in
      let s1 := set_reg s r new_val in
      if new_val =? 0
      then mkState (acc s) (regs s1) (carry s) (pc_inc2 s) (stack s)
                   (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                   (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
      else mkState (acc s) (regs s1) (carry s)
                   (addr12_of_nat (base_for_next2 s + off))
                   (stack s) (ram_sys s) (cur_bank s) (sel_ram s)
                   (rom_ports s) (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

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
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | FIN r =>
      (* fetch indirect: lower 8 from R0:R1; page is that of next instr *)
      let page := page_of (pc_inc1 s) in
      let low8 := (get_reg_pair s 0) mod 256 in
      let addr := addr12_of_nat (page * 256 + low8) in
      let b := fetch_byte s addr in
      let s1 := set_reg_pair s r b in
      mkState (acc s) (regs s1) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | JIN r =>
      (* jump within page of *next* instruction (quirk included) *)
      let page := page_of (pc_inc1 s) in
      let low8 := (get_reg_pair s r) mod 256 in
      let addr := addr12_of_nat (page * 256 + low8) in
      mkState (acc s) (regs s) (carry s) addr (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  (* ------------------ 4002 RAM + 4001 ROM I/O ------------------ *)

  | WRM =>
      let new_sys := ram_write_main_sys s (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | RDM =>
      let v := ram_read_main s in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | ADM =>
      let v := ram_read_main s in
      let sum := (acc s) + v + (if carry s then 1 else 0) in
      mkState (nibble_of_nat sum) (regs s) (16 <=? sum) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | SBM =>
      let v := ram_read_main s in
      let borrow := if carry s then 0 else 1 in
      let diff := (acc s) + 16 - v - borrow in
      mkState (nibble_of_nat diff) (regs s) (16 <=? diff) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | WR0 =>
      let new_sys := ram_write_status_sys s 0 (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
  | WR1 =>
      let new_sys := ram_write_status_sys s 1 (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
  | WR2 =>
      let new_sys := ram_write_status_sys s 2 (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
  | WR3 =>
      let new_sys := ram_write_status_sys s 3 (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | RD0 =>
      let b := get_bank s (cur_bank s) in
      let ch := get_chip b (sel_chip (sel_ram s)) in
      let rg := get_regRAM ch (sel_reg (sel_ram s)) in
      let v := get_stat rg 0 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
  | RD1 =>
      let b := get_bank s (cur_bank s) in
      let ch := get_chip b (sel_chip (sel_ram s)) in
      let rg := get_regRAM ch (sel_reg (sel_ram s)) in
      let v := get_stat rg 1 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
  | RD2 =>
      let b := get_bank s (cur_bank s) in
      let ch := get_chip b (sel_chip (sel_ram s)) in
      let rg := get_regRAM ch (sel_reg (sel_ram s)) in
      let v := get_stat rg 2 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
  | RD3 =>
      let b := get_bank s (cur_bank s) in
      let ch := get_chip b (sel_chip (sel_ram s)) in
      let rg := get_regRAM ch (sel_reg (sel_ram s)) in
      let v := get_stat rg 3 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | WMP =>
      let new_sys := ram_write_port_sys s (acc s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              new_sys (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | WRR =>
      let new_ports := update_nth (sel_rom s) (nibble_of_nat (acc s)) (rom_ports s) in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) new_ports (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | RDR =>
      let v := nth (sel_rom s) (rom_ports s) 0 in
      mkState v (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | WPM =>
      (* Write Program Memory: Programs PROM at latched address/data
         When prom_enable is true, writes prom_data to ROM at prom_addr *)
      let new_rom := if prom_enable s
                     then update_nth (prom_addr s) (prom_data s) (rom s)
                     else rom s in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
              new_rom (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)

  | DCL =>
      (* Designate command line: select RAM bank from ACC (lower 2 bits, 0..3) *)
      let nb := (acc s) mod NBANKS in
      mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
              (ram_sys s) nb (sel_ram s) (rom_ports s) (sel_rom s)
              (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)
  end.

(* ======================= Small-step machine ========================= *)

(** Executes one fetch-decode-execute cycle. *)
Definition step (s : Intel4004State) : Intel4004State :=
  let b1 := fetch_byte s (pc s) in
  let b2 := fetch_byte s (addr12_of_nat (pc s + 1)) in
  let inst := decode b1 b2 in
  execute s inst.

(** Executes n steps. Defined tail-recursively (steps from current state). *)
Fixpoint steps (n : nat) (s : Intel4004State) : Intel4004State :=
  match n with
  | 0 => s
  | S n' => steps n' (step s)
  end.

(* ========================== Initial / Reset ========================= *)

(** Empty RAM register: all zeros. *)
Definition empty_reg : RAMReg := mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT).

(** Empty RAM chip: 4 empty registers, port 0. *)
Definition empty_chip : RAMChip := mkRAMChip (repeat empty_reg NREGS) 0.

(** Empty RAM bank: 4 empty chips. *)
Definition empty_bank : RAMBank := mkRAMBank (repeat empty_chip NCHIPS).

(** Empty RAM system: 4 empty banks. *)
Definition empty_sys : list RAMBank := repeat empty_bank NBANKS.

(** Initial power-on state: all zeros, empty RAM, empty ROM. *)
Definition init_state : Intel4004State :=
  mkState 0 (repeat 0 16) false 0 [] empty_sys 0 (mkRAMSel 0 0 0)
          (repeat 0 16) 0 (repeat 0 4096) false 0 0 false.

(** Reset state: clears CPU state but preserves RAM and ROM. *)
Definition reset_state (s:Intel4004State) : Intel4004State :=
  mkState 0 (regs s) false 0 [] (ram_sys s) 0 (mkRAMSel 0 0 0)
          (repeat 0 16) 0 (rom s) false 0 0 false.

(* ======================== Well-formedness =========================== *)

(** Well-formedness for RAM register: correct lengths and all nibbles bounded. *)
Definition WF_reg (rg:RAMReg) : Prop :=
  length (reg_main rg) = NMAIN /\
  Forall (fun x => x < 16) (reg_main rg) /\
  length (reg_status rg) = NSTAT /\
  Forall (fun x => x < 16) (reg_status rg).

(** Well-formedness for RAM chip: correct length, all registers WF, port bounded. *)
Definition WF_chip (ch:RAMChip) : Prop :=
  length (chip_regs ch) = NREGS /\
  Forall WF_reg (chip_regs ch) /\
  chip_port ch < 16.

(** Well-formedness for RAM bank: correct length and all chips WF. *)
Definition WF_bank (bk:RAMBank) : Prop :=
  length (bank_chips bk) = NCHIPS /\
  Forall WF_chip (bank_chips bk).

(** Well-formedness for RAM selection: all indices in valid ranges. *)
Definition WF_sel (sr:RAMSel) : Prop :=
  sel_chip sr < NCHIPS /\ sel_reg sr < NREGS /\ sel_char sr < NMAIN.

(** Main well-formedness invariant: all state fields have correct shapes and bounds. *)
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
  length (rom s) = 4096 /\
  prom_addr s < 4096 /\
  prom_data s < 256.

(** Proves repeat 0 n satisfies Forall (< 16). *)
Lemma repeat_0_lt_16 : forall n, Forall (fun x => x < 16) (repeat 0 n).
Proof.
  intros n.
  apply Forall_repeat.
  lia.
Qed.

(** Proves repeat 0 n satisfies Forall (< 256). *)
Lemma repeat_0_lt_256 : forall n, Forall (fun x => x < 256) (repeat 0 n).
Proof.
  intros n.
  apply Forall_repeat.
  lia.
Qed.

(** Proves empty RAM register satisfies WF_reg. *)
Lemma empty_reg_WF : WF_reg empty_reg.
Proof.
  unfold WF_reg, empty_reg.
  unfold NMAIN, NSTAT.
  simpl.
  repeat split; try reflexivity.
  - repeat constructor.
  - repeat constructor.
Qed.

(** Proves repeat empty_reg n satisfies Forall WF_reg. *)
Lemma repeat_empty_reg_WF : forall n, Forall WF_reg (repeat empty_reg n).
Proof.
  intros n.
  apply Forall_repeat.
  apply empty_reg_WF.
Qed.

(** Proves empty RAM chip satisfies WF_chip. *)
Lemma empty_chip_WF : WF_chip empty_chip.
Proof.
  unfold WF_chip, empty_chip.
  unfold NREGS.
  simpl.
  repeat split; try lia; try reflexivity.
  repeat constructor; apply empty_reg_WF.
Qed.

(** Proves repeat empty_chip n satisfies Forall WF_chip. *)
Lemma repeat_empty_chip_WF : forall n, Forall WF_chip (repeat empty_chip n).
Proof.
  intros n.
  apply Forall_repeat.
  apply empty_chip_WF.
Qed.

(** Proves empty RAM bank satisfies WF_bank. *)
Lemma empty_bank_WF : WF_bank empty_bank.
Proof.
  unfold WF_bank, empty_bank.
  unfold NCHIPS.
  simpl.
  split; [reflexivity|].
  repeat constructor; apply empty_chip_WF.
Qed.

(** Proves repeat empty_bank n satisfies Forall WF_bank. *)
Lemma repeat_empty_bank_WF : forall n, Forall WF_bank (repeat empty_bank n).
Proof.
  intros n.
  apply Forall_repeat.
  apply empty_bank_WF.
Qed.

(** Proves default RAM selection (0,0,0) satisfies WF_sel. *)
Lemma default_sel_WF : WF_sel (mkRAMSel 0 0 0).
Proof.
  unfold WF_sel.
  unfold NCHIPS, NREGS, NMAIN.
  simpl.
  repeat split; lia.
Qed.

(** Proves init_state satisfies WF. *)
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
  split. reflexivity.
  split. simpl; lia.
  simpl; lia.
Qed.

(* ====================== Preservation lemmas ========================= *)

(** Proves updating main character in WF register preserves WF_reg. *)
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

(** Proves updating status character in WF register preserves WF_reg. *)
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

(** Proves updating port in WF chip preserves WF_chip. *)
Lemma WF_chip_upd_port : forall ch v,
  WF_chip ch -> WF_chip (upd_port_in_chip ch v).
Proof.
  intros [regs port] v [Hlen [Hall Hport]].
  unfold upd_port_in_chip, WF_chip. simpl. repeat split; auto.
  apply nibble_lt16.
Qed.

(** Proves updating chip in WF bank preserves WF_bank. *)
Lemma WF_bank_upd_chip : forall bk c ch,
  WF_bank bk -> WF_chip ch -> WF_bank (upd_chip_in_bank bk c ch).
Proof.
  intros [chips] c ch [Hlen Hall] Hch.
  unfold upd_chip_in_bank, WF_bank. simpl.
  repeat split.
  - rewrite update_nth_length; assumption.
  - eapply Forall_update_nth; eauto.
Qed.

(** Proves updating bank in WF system preserves length and Forall WF_bank. *)
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

(** Proves reading main character after write returns normalized written value. *)
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

(** Proves reading register after update returns the updated register. *)
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

(** Proves reading chip after update returns the updated chip. *)
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

(** Proves reading bank after update returns the updated bank. *)
Lemma get_bank_upd_bank_in_sys : forall s b bk,
  WF s ->
  b < NBANKS ->
  get_bank (mkState (acc s) (regs s) (carry s) (pc s) (stack s)
                     (upd_bank_in_sys s b bk) (cur_bank s) (sel_ram s)
                     (rom_ports s) (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s))
           b = bk.
Proof.
  intros s b bk [_ [_ [_ [_ [_ [_ [Hsys_len _]]]]]]] Hb.
  unfold get_bank, upd_bank_in_sys. simpl.
  rewrite nth_update_nth_eq by lia.
  reflexivity.
Qed.

(** Proves bank extracted from WF system is WF. *)
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

(** Proves chip extracted from WF bank is WF. *)
Lemma WF_chip_from_bank : forall bk c,
  WF_bank bk ->
  c < NCHIPS ->
  WF_chip (get_chip bk c).
Proof.
  intros bk c [Hlen Hforall] Hc.
  rewrite Forall_forall in Hforall.
  apply Hforall. eapply nth_In. lia.
Qed.

(** Proves register extracted from WF chip is WF. *)
Lemma WF_reg_from_chip : forall ch r,
  WF_chip ch ->
  r < NREGS ->
  WF_reg (get_regRAM ch r).
Proof.
  intros ch r [Hlen [Hforall _]] Hr.
  rewrite Forall_forall in Hforall.
  apply Hforall. eapply nth_In. lia.
Qed.

(** Main RAM read-after-write correctness: reading main RAM returns normalized written value. *)
Lemma ram_write_then_read_main : forall s v,
  WF s ->
  cur_bank s < NBANKS ->
  sel_chip (sel_ram s) < NCHIPS ->
  sel_reg (sel_ram s) < NREGS ->
  sel_char (sel_ram s) < NMAIN ->
  ram_read_main (mkState (acc s) (regs s) (carry s) (pc s) (stack s)
                          (ram_write_main_sys s v) (cur_bank s) (sel_ram s)
                          (rom_ports s) (sel_rom s) (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s))
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

(** Proves decode with opcode 0 produces well-formed instruction (always NOP). *)
Lemma decode_opcode_0_wf : forall b1 b2,
  b1 / 16 = 0 ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 H. unfold decode. rewrite H. simpl. trivial.
Qed.

(** Proves decode with opcode 1 produces well-formed instruction (always JCN). *)
Lemma decode_opcode_1_wf : forall b1 b2,
  b1 / 16 = 1 ->
  match decode b1 b2 with
  | JUN a | JMS a => a < 4096
  | _ => True
  end.
Proof.
  intros b1 b2 H. unfold decode. rewrite H. simpl. trivial.
Qed.

(** Proves FIM and SRC never decode as JUN or JMS. *)
Lemma fim_src_not_jun_jms : forall r b,
  match FIM r b with | JUN _ | JMS _ => False | _ => True end /\
  match SRC r with | JUN _ | JMS _ => False | _ => True end.
Proof. intros; split; exact I. Qed.

(** Proves decode with opcode 2 produces well-formed instruction (FIM or SRC). *)
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

(** Proves FIN and JIN never decode as JUN or JMS. *)
Lemma fin_jin_not_jun_jms : forall r,
  match FIN r with | JUN _ | JMS _ => False | _ => True end /\
  match JIN r with | JUN _ | JMS _ => False | _ => True end.
Proof. intros; split; exact I. Qed.

(** Proves decode with opcode 3 produces well-formed instruction (FIN or JIN). *)
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

(** Proves decode with opcode 4 produces well-formed JUN with bounded address. *)
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

(** Proves decode with opcode 5 produces well-formed JMS with bounded address. *)
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

(** Proves decode with opcodes 6-13 produces well-formed instructions (never JUN/JMS). *)
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

(** Proves decode with opcode 14 never produces JUN or JMS. *)
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
(* Opcodes 6-13 (INC through ADD) never decode to absolute jumps. *)
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
(* Out-of-range opcodes (≥16) decode to NOP, never produce absolute jumps. *)
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
(* All decoded JUN/JMS instructions have 12-bit addresses < 4096. *)
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
(* Modulo 16 always yields values strictly less than 16. *)
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
(* Nested modulo simplification: (n mod 16) mod 2 = n mod 2. *)
Lemma mod_16_mod_2_eq : forall n, (n mod 16) mod 2 = n mod 2.
Proof.
  intro n.
  (* We use that (n mod 16) and n differ by a multiple of 16, which is even *)
  assert (H: exists k, n = 16 * k + n mod 16).
  { exists (n / 16). apply Nat.div_mod. lia. }
  destruct H as [k Hk].
  rewrite Hk at 2.
  rewrite Nat.Div0.add_mod by lia.
  assert (16 * k mod 2 = 0).
  { (* 16 = 0 mod 2, so 16 * k = 0 mod 2 *)
    assert (H16mod: 16 mod 2 = 0) by reflexivity.
    rewrite <- Nat.Div0.mul_mod_idemp_l by lia.
    rewrite H16mod.
    simpl. reflexivity. }
  rewrite H.
  rewrite Nat.add_0_l.
  rewrite Nat.Div0.mod_mod by lia.
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
  intros. apply Nat.Div0.div_lt_upper_bound. lia.
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
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
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
  split. assumption.  (* rom length = 4096 *)
  split. assumption.  (* prom_addr < 4096 *)
  assumption.  (* prom_data < 256 *)
Qed.


Lemma execute_NOP_WF : forall s, WF s -> WF (execute s NOP).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_LDM_WF : forall s n, WF s -> instr_wf (LDM n) -> WF (execute s (LDM n)).
Proof.
  intros s n HWF Hwfi. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_LD_WF : forall s r, WF s -> instr_wf (LD r) -> WF (execute s (LD r)).
Proof.
  intros s r HWF Hwfi. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. eapply nth_Forall_lt; eauto; lia.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_XCH_WF : forall s r, WF s -> instr_wf (XCH r) -> WF (execute s (XCH r)).
Proof.
  intros s r HWF Hwfi. unfold execute. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  set (s1 := set_reg s r (acc s)).
  assert (Hs1_len: length (regs s1) = 16).
  { subst s1. rewrite set_reg_preserves_length. assumption. }
  assert (Hs1_for: Forall (fun x => x < 16) (regs s1)).
  { subst s1. apply set_reg_preserves_Forall16. assumption. }
  unfold WF. simpl.
  split. assumption.
  split. assumption.
  split. eapply nth_Forall_lt; eauto; lia.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_INC_WF : forall s r, WF s -> instr_wf (INC r) -> WF (execute s (INC r)).
Proof.
  intros s r HWF Hwfi. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  set (s1 := set_reg s r (nibble_of_nat (get_reg s r + 1))).
  assert (Hs1_len: length (regs s1) = 16).
  { subst s1. rewrite set_reg_preserves_length. assumption. }
  assert (Hs1_for: Forall (fun x => x < 16) (regs s1)).
  { subst s1. apply set_reg_preserves_Forall16. assumption. }
  unfold WF. simpl.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_ADD_WF : forall s r, WF s -> instr_wf (ADD r) -> WF (execute s (ADD r)).
Proof.
  intros s r HWF Hwfi. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_SUB_WF : forall s r, WF s -> instr_wf (SUB r) -> WF (execute s (SUB r)).
Proof.
  intros s r HWF Hwfi. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_IAC_WF : forall s, WF s -> WF (execute s IAC).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_DAC_WF : forall s, WF s -> WF (execute s DAC).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_CLC_WF : forall s, WF s -> WF (execute s CLC).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_STC_WF : forall s, WF s -> WF (execute s STC).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_CMC_WF : forall s, WF s -> WF (execute s CMC).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_CMA_WF : forall s, WF s -> WF (execute s CMA).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_CLB_WF : forall s, WF s -> WF (execute s CLB).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. lia.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_RAL_WF : forall s, WF s -> WF (execute s RAL).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_RAR_WF : forall s, WF s -> WF (execute s RAR).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_TCC_WF : forall s, WF s -> WF (execute s TCC).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. destruct (carry s); lia.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_TCS_WF : forall s, WF s -> WF (execute s TCS).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. destruct (carry s); lia.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_DAA_WF : forall s, WF s -> WF (execute s DAA).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_KBP_WF : forall s, WF s -> WF (execute s KBP).
Proof.
  intros s HWF. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split.
    { assert (H: acc s < 16) by exact Hacc.
      destruct (acc s) eqn:E; simpl; [lia|].
      destruct n eqn:E1; simpl; [lia|].
      destruct n0 eqn:E2; simpl; [lia|].
      destruct n1 eqn:E3; simpl; [lia|].
      destruct n2 eqn:E4; simpl; [lia|].
      destruct n3 eqn:E5; simpl; [lia|].
      destruct n4 eqn:E6; simpl; [lia|].
      destruct n5 eqn:E7; simpl; [lia|].
      destruct n6 eqn:E8; simpl; [lia|].
      destruct n7 eqn:E9; simpl; [lia|].
      destruct n8 eqn:E10; simpl; [lia|].
      destruct n9 eqn:E11; simpl; [lia|].
      destruct n10 eqn:E12; simpl; [lia|].
      destruct n11 eqn:E13; simpl; [lia|].
      destruct n12 eqn:E14; simpl; [lia|].
      subst. simpl in H. lia. }
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_JUN_WF : forall s a, WF s -> instr_wf (JUN a) -> WF (execute s (JUN a)).
Proof.
  intros s a HWF Hwfi. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. assumption.
  split. exact Hwfi.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma get_reg_pair_bound_helper : forall s r,
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

Lemma execute_JMS_WF : forall s a, WF s -> instr_wf (JMS a) -> WF (execute s (JMS a)).
Proof.
  intros s a HWF Hwfi. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  set (s1 := push_stack s (addr12_of_nat (pc s + 2))).
  assert (Hs1_len: length (stack s1) <= 3).
  { subst s1. apply push_stack_len_le3. }
  assert (Hs1_for: Forall (fun x => x < 4096) (stack s1)).
  { subst s1. unfold push_stack. simpl.
    assert (HF := HstkFor).
    destruct (stack s) as [|h1 [|h2 [|h3 t]]]; simpl.
    - constructor; [apply addr12_bound | constructor].
    - inversion HF; subst.
      constructor; [apply addr12_bound | constructor; auto].
    - inversion HF; subst.
      inversion H2; subst.
      constructor; [apply addr12_bound | constructor; auto].
    - inversion HF; subst.
      inversion H2; subst.
      inversion H4; subst.
      constructor; [apply addr12_bound | constructor; auto]. }
  unfold WF. simpl.
  split. assumption.
  split. assumption.
  split. assumption.
  split. exact Hwfi.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_JCN_WF : forall s c a, WF s -> instr_wf (JCN c a) -> WF (execute s (JCN c a)).
Proof.
  intros s c a HWF Hwfi. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  set (c1 := c / 8).
  set (c2 := (c / 4) mod 2).
  set (c3 := (c / 2) mod 2).
  set (c4 := c mod 2).
  set (base_cond := orb (andb (acc s =? 0) (c2 =? 1))
                        (orb (andb (carry s) (c3 =? 1))
                             (andb (negb (test_pin s)) (c4 =? 1)))).
  set (jump := if c1 =? 1 then negb base_cond else base_cond).
  destruct jump.
  - unfold WF. simpl.
    split. assumption.
    split. assumption.
    split. assumption.
    split. apply addr12_bound.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
  - unfold WF. simpl.
    split. assumption.
    split. assumption.
    split. assumption.
    split. apply addr12_bound.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
Qed.

Lemma execute_FIM_WF : forall s r d, WF s -> instr_wf (FIM r d) -> WF (execute s (FIM r d)).
Proof.
  intros s r d HWF Hwfi. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  set (s1 := set_reg_pair s r d).
  assert (Hs1_len: length (regs s1) = 16).
  { subst s1. rewrite set_reg_pair_preserves_length. assumption. }
  assert (Hs1_for: Forall (fun x => x < 16) (regs s1)).
  { subst s1. apply set_reg_pair_preserves_Forall16. assumption. }
  unfold WF. simpl.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_SRC_WF : forall s r, WF s -> instr_wf (SRC r) -> WF (execute s (SRC r)).
Proof.
  intros s r HWF Hwfi. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  set (v := get_reg_pair s r).
  set (hi := v / 16).
  set (lo := v mod 16).
  set (chip := hi / 4).
  set (rno := hi mod 4).
  assert (Hv: v < 256).
  { subst v. apply get_reg_pair_bound_helper; auto. }
  assert (Hhi: hi < 16).
  { subst hi. apply Nat.Div0.div_lt_upper_bound. exact Hv. }
  assert (Hchip: chip < 4).
  { subst chip. apply Nat.Div0.div_lt_upper_bound. exact Hhi. }
  assert (Hrno: rno < 4).
  { subst rno. apply Nat.mod_upper_bound. lia. }
  assert (Hlo: lo < 16).
  { subst lo. apply Nat.mod_upper_bound. lia. }
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. unfold WF_sel. unfold NCHIPS, NREGS, NMAIN. simpl. split; [exact Hchip | split; [exact Hrno | exact Hlo]].
  split. assumption.
  split. assumption.
  split. exact Hhi.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_FIN_WF : forall s r, WF s -> instr_wf (FIN r) -> WF (execute s (FIN r)).
Proof.
  intros s r HWF Hwfi. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  set (s1 := set_reg_pair s r _).
  assert (Hs1_len: length (regs s1) = 16).
  { subst s1. rewrite set_reg_pair_preserves_length. assumption. }
  assert (Hs1_for: Forall (fun x => x < 16) (regs s1)).
  { subst s1. apply set_reg_pair_preserves_Forall16. assumption. }
  unfold WF. simpl.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_JIN_WF : forall s r, WF s -> instr_wf (JIN r) -> WF (execute s (JIN r)).
Proof.
  intros s r HWF Hwfi. unfold execute, WF in *. simpl.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_ISZ_WF : forall s r a, WF s -> instr_wf (ISZ r a) -> WF (execute s (ISZ r a)).
Proof.
  intros s r a HWF Hwfi. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  set (s1 := set_reg s r _).
  assert (Hs1_len: length (regs s1) = 16).
  { subst s1. rewrite set_reg_preserves_length. assumption. }
  assert (Hs1_for: Forall (fun x => x < 16) (regs s1)).
  { subst s1. apply set_reg_preserves_Forall16. assumption. }
  destruct (nibble_of_nat (get_reg s r + 1) =? 0).
  - unfold WF. simpl.
    split. assumption.
    split. assumption.
    split. assumption.
    split. apply addr12_bound.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
  - unfold WF. simpl.
    split. assumption.
    split. assumption.
    split. assumption.
    split. apply addr12_bound.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
Qed.

(* Stack pop preserves all state fields except stack itself. *)
Lemma pop_stack_preserves_fields : forall s opt_addr s',
  pop_stack s = (opt_addr, s') ->
  regs s' = regs s /\
  acc s' = acc s /\
  carry s' = carry s /\
  pc s' = pc s /\
  ram_sys s' = ram_sys s /\
  cur_bank s' = cur_bank s /\
  sel_ram s' = sel_ram s /\
  rom_ports s' = rom_ports s /\
  sel_rom s' = sel_rom s /\
  rom s' = rom s /\
  test_pin s' = test_pin s /\
  prom_addr s' = prom_addr s /\
  prom_data s' = prom_data s /\
  prom_enable s' = prom_enable s.
Proof.
  intros s opt_addr s' Hpop.
  unfold pop_stack in Hpop.
  destruct (stack s) as [|h t]; inversion Hpop; subst; simpl;
    repeat split; reflexivity.
Qed.

(* Popped address respects 12-bit bound if stack was well-formed. *)
Lemma pop_stack_preserves_addr_bound : forall s opt_addr s',
  pop_stack s = (opt_addr, s') ->
  Forall (fun a => a < 4096) (stack s) ->
  match opt_addr with
  | Some addr => addr < 4096
  | None => True
  end.
Proof.
  intros s opt_addr s' Hpop Hall.
  unfold pop_stack in Hpop.
  destruct (stack s) as [|h t]; inversion Hpop; subst; simpl; auto.
  inversion Hall; auto.
Qed.

Lemma execute_BBL_WF : forall s d, WF s -> instr_wf (BBL d) -> WF (execute s (BBL d)).
Proof.
  intros s d HWF Hwfi. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  destruct (pop_stack s) as [[addr|] s'] eqn:Epop.
  - assert (Hs'_len: length (stack s') <= 3).
    { eapply pop_stack_len_le3; eauto; lia. }
    assert (Hs'_for: Forall (fun x => x < 4096) (stack s')).
    { eapply pop_stack_Forall_addr12; eauto. }
    assert (Haddr: addr < 4096).
    { pose proof (pop_stack_preserves_addr_bound s (Some addr) s' Epop HstkFor).
      simpl in H. exact H. }
    pose proof (pop_stack_preserves_fields s (Some addr) s' Epop) as Hfields.
    destruct Hfields as [Hregs [Hacc' [Hcarry [Hpc' [Hram [Hbank' [Hsel' [Hrp [Hsr [Hrom [Htest [Hpaddr' [Hpdata' Hpenable']]]]]]]]]]]]].
    unfold WF. simpl.
    split. rewrite Hregs. assumption.
    split. rewrite Hregs. assumption.
    split. apply nibble_lt16.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
  - assert (Hs'_len: length (stack s') <= 3).
    { eapply pop_stack_len_le3; eauto; lia. }
    assert (Hs'_for: Forall (fun x => x < 4096) (stack s')).
    { eapply pop_stack_Forall_addr12; eauto. }
    pose proof (pop_stack_preserves_fields s None s' Epop) as Hfields.
    destruct Hfields as [Hregs [Hacc' [Hcarry [Hpc' [Hram [Hbank' [Hsel' [Hrp [Hsr [Hrom [Htest [Hpaddr' [Hpdata' Hpenable']]]]]]]]]]]]].
    unfold WF. simpl.
    split. rewrite Hregs. assumption.
    split. rewrite Hregs. assumption.
    split. apply nibble_lt16.
    split. apply addr12_bound.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
Qed.

(* Writing to main RAM preserves system-level bank count invariant. *)
Lemma ram_write_main_sys_preserves_len : forall s v,
  WF s -> length (ram_write_main_sys s v) = NBANKS.
Proof.
  intros s v HWF.
  unfold ram_write_main_sys.
  assert (Hbank: cur_bank s < NBANKS) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]; exact H).
  assert (Hsel: WF_sel (sel_ram s)) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
  destruct Hsel as [Hchip [Hreg Hchar]].
  pose proof (WF_bank_from_sys s (cur_bank s) HWF Hbank) as Hbk.
  pose proof (WF_chip_from_bank _ (sel_chip (sel_ram s)) Hbk Hchip) as Hch.
  pose proof (WF_reg_from_chip _ (sel_reg (sel_ram s)) Hch Hreg) as Hrg.
  pose proof (WF_reg_upd_main _ (sel_char (sel_ram s)) v Hrg) as Hrg'.
  pose proof (WF_chip_upd_reg _ (sel_reg (sel_ram s)) _ Hch Hrg') as Hch'.
  pose proof (WF_bank_upd_chip _ (sel_chip (sel_ram s)) _ Hbk Hch') as Hbk'.
  eapply WF_sys_upd_bank; eauto.
Qed.

(* Writing to main RAM preserves well-formedness of all banks. *)
Lemma ram_write_main_sys_preserves_WF_bank : forall s v,
  WF s -> Forall WF_bank (ram_write_main_sys s v).
Proof.
  intros s v HWF.
  unfold ram_write_main_sys.
  assert (Hbank: cur_bank s < NBANKS) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]; exact H).
  assert (Hsel: WF_sel (sel_ram s)) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
  destruct Hsel as [Hchip [Hreg Hchar]].
  pose proof (WF_bank_from_sys s (cur_bank s) HWF Hbank) as Hbk.
  pose proof (WF_chip_from_bank _ (sel_chip (sel_ram s)) Hbk Hchip) as Hch.
  pose proof (WF_reg_from_chip _ (sel_reg (sel_ram s)) Hch Hreg) as Hrg.
  pose proof (WF_reg_upd_main _ (sel_char (sel_ram s)) v Hrg) as Hrg'.
  pose proof (WF_chip_upd_reg _ (sel_reg (sel_ram s)) _ Hch Hrg') as Hch'.
  pose proof (WF_bank_upd_chip _ (sel_chip (sel_ram s)) _ Hbk Hch') as Hbk'.
  eapply WF_sys_upd_bank; eauto.
Qed.

Lemma ram_write_status_sys_preserves_len : forall s idx v,
  WF s -> length (ram_write_status_sys s idx v) = NBANKS.
Proof.
  intros s idx v HWF.
  unfold ram_write_status_sys.
  assert (Hbank: cur_bank s < NBANKS) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]; exact H).
  assert (Hsel: WF_sel (sel_ram s)) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
  destruct Hsel as [Hchip [Hreg Hchar]].
  pose proof (WF_bank_from_sys s (cur_bank s) HWF Hbank) as Hbk.
  pose proof (WF_chip_from_bank _ (sel_chip (sel_ram s)) Hbk Hchip) as Hch.
  pose proof (WF_reg_from_chip _ (sel_reg (sel_ram s)) Hch Hreg) as Hrg.
  pose proof (WF_reg_upd_stat _ idx v Hrg) as Hrg'.
  pose proof (WF_chip_upd_reg _ (sel_reg (sel_ram s)) _ Hch Hrg') as Hch'.
  pose proof (WF_bank_upd_chip _ (sel_chip (sel_ram s)) _ Hbk Hch') as Hbk'.
  eapply WF_sys_upd_bank; eauto.
Qed.

Lemma ram_write_status_sys_preserves_WF_bank : forall s idx v,
  WF s -> Forall WF_bank (ram_write_status_sys s idx v).
Proof.
  intros s idx v HWF.
  unfold ram_write_status_sys.
  assert (Hbank: cur_bank s < NBANKS) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]; exact H).
  assert (Hsel: WF_sel (sel_ram s)) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
  destruct Hsel as [Hchip [Hreg Hchar]].
  pose proof (WF_bank_from_sys s (cur_bank s) HWF Hbank) as Hbk.
  pose proof (WF_chip_from_bank _ (sel_chip (sel_ram s)) Hbk Hchip) as Hch.
  pose proof (WF_reg_from_chip _ (sel_reg (sel_ram s)) Hch Hreg) as Hrg.
  pose proof (WF_reg_upd_stat _ idx v Hrg) as Hrg'.
  pose proof (WF_chip_upd_reg _ (sel_reg (sel_ram s)) _ Hch Hrg') as Hch'.
  pose proof (WF_bank_upd_chip _ (sel_chip (sel_ram s)) _ Hbk Hch') as Hbk'.
  eapply WF_sys_upd_bank; eauto.
Qed.

Lemma ram_write_port_sys_preserves_len : forall s v,
  WF s -> length (ram_write_port_sys s v) = NBANKS.
Proof.
  intros s v HWF.
  unfold ram_write_port_sys.
  assert (Hbank: cur_bank s < NBANKS) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]; exact H).
  assert (Hsel: WF_sel (sel_ram s)) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
  destruct Hsel as [Hchip [Hreg Hchar]].
  pose proof (WF_bank_from_sys s (cur_bank s) HWF Hbank) as Hbk.
  pose proof (WF_chip_from_bank _ (sel_chip (sel_ram s)) Hbk Hchip) as Hch.
  pose proof (WF_chip_upd_port _ v Hch) as Hch'.
  pose proof (WF_bank_upd_chip _ (sel_chip (sel_ram s)) _ Hbk Hch') as Hbk'.
  eapply WF_sys_upd_bank; eauto.
Qed.

Lemma ram_write_port_sys_preserves_WF_bank : forall s v,
  WF s -> Forall WF_bank (ram_write_port_sys s v).
Proof.
  intros s v HWF.
  unfold ram_write_port_sys.
  assert (Hbank: cur_bank s < NBANKS) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]; exact H).
  assert (Hsel: WF_sel (sel_ram s)) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
  destruct Hsel as [Hchip [Hreg Hchar]].
  pose proof (WF_bank_from_sys s (cur_bank s) HWF Hbank) as Hbk.
  pose proof (WF_chip_from_bank _ (sel_chip (sel_ram s)) Hbk Hchip) as Hch.
  pose proof (WF_chip_upd_port _ v Hch) as Hch'.
  pose proof (WF_bank_upd_chip _ (sel_chip (sel_ram s)) _ Hbk Hch') as Hbk'.
  eapply WF_sys_upd_bank; eauto.
Qed.

Lemma update_nth_preserves_length : forall A (l : list A) (n : nat) (x : A),
  length (update_nth n x l) = length l.
Proof.
  intros A l n x.
  apply update_nth_length.
Qed.

Lemma update_nth_preserves_Forall16 : forall (l : list nat) (n : nat) (x : nat),
  Forall (fun y => y < 16) l ->
  x < 16 ->
  Forall (fun y => y < 16) (update_nth n x l).
Proof.
  intros l n x Hall Hx.
  apply Forall_update_nth; auto.
Qed.

(* Reading from main RAM under WF yields 4-bit value. *)
Lemma ram_read_main_bound : forall s,
  WF s ->
  ram_read_main s < 16.
Proof.
  intros s HWF.
  unfold ram_read_main.
  assert (Hbank: cur_bank s < NBANKS) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]; exact H).
  assert (Hsel: WF_sel (sel_ram s)) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
  destruct Hsel as [Hchip [Hreg Hchar]].
  pose proof (WF_bank_from_sys s (cur_bank s) HWF Hbank) as Hbk.
  pose proof (WF_chip_from_bank _ (sel_chip (sel_ram s)) Hbk Hchip) as Hch.
  pose proof (WF_reg_from_chip _ (sel_reg (sel_ram s)) Hch Hreg) as Hrg.
  destruct Hrg as [Hmain_len [Hmain_for _]].
  unfold get_main.
  eapply nth_Forall_lt; eauto; lia.
Qed.

(* Reading from status RAM under WF yields 4-bit value. *)
Lemma get_stat_bound : forall s,
  WF s ->
  forall idx,
  let b := get_bank s (cur_bank s) in
  let ch := get_chip b (sel_chip (sel_ram s)) in
  let rg := get_regRAM ch (sel_reg (sel_ram s)) in
  get_stat rg idx < 16.
Proof.
  intros s HWF idx.
  assert (Hbank: cur_bank s < NBANKS) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]; exact H).
  assert (Hsel: WF_sel (sel_ram s)) by (destruct HWF as [_ [_ [_ [_ [_ [_ [_ [_ [_ [H _]]]]]]]]]]; exact H).
  destruct Hsel as [Hchip [Hreg Hchar]].
  pose proof (WF_bank_from_sys s (cur_bank s) HWF Hbank) as Hbk.
  pose proof (WF_chip_from_bank _ (sel_chip (sel_ram s)) Hbk Hchip) as Hch.
  pose proof (WF_reg_from_chip _ (sel_reg (sel_ram s)) Hch Hreg) as Hrg.
  destruct Hrg as [_ [_ [Hstat_len Hstat_for]]].
  unfold get_stat.
  eapply nth_Forall_lt; eauto; lia.
Qed.

Lemma execute_WRM_WF : forall s, WF s -> WF (execute s WRM).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. apply ram_write_main_sys_preserves_len. assumption.
  split. apply ram_write_main_sys_preserves_WF_bank. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_WMP_WF : forall s, WF s -> WF (execute s WMP).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. apply ram_write_port_sys_preserves_len. assumption.
  split. apply ram_write_port_sys_preserves_WF_bank. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_WRR_WF : forall s, WF s -> WF (execute s WRR).
Proof.
  intros s HWF. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF. simpl.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. rewrite update_nth_length. assumption.
  split. apply Forall_update_nth; auto. apply nibble_lt16.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma update_nth_preserves_Forall256 : forall (l : list nat) (n : nat) (x : nat),
  Forall (fun y => y < 256) l ->
  x < 256 ->
  Forall (fun y => y < 256) (update_nth n x l).
Proof.
  intros l n x Hall Hx.
  apply Forall_update_nth; auto.
Qed.

Lemma execute_WPM_WF : forall s, WF s -> WF (execute s WPM).
Proof.
  intros s HWF. unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF. simpl.
  destruct (prom_enable s) eqn:Eprom.
  - split. assumption.
    split. assumption.
    split. assumption.
    split. apply addr12_bound.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. apply update_nth_preserves_Forall256; assumption.
    split. rewrite update_nth_length. assumption.
    split. assumption.
    assumption.
  - split. assumption.
    split. assumption.
    split. assumption.
    split. apply addr12_bound.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    split. assumption.
    assumption.
Qed.

Lemma execute_WR0_WF : forall s, WF s -> WF (execute s WR0).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. apply ram_write_status_sys_preserves_len. assumption.
  split. apply ram_write_status_sys_preserves_WF_bank. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_WR1_WF : forall s, WF s -> WF (execute s WR1).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. apply ram_write_status_sys_preserves_len. assumption.
  split. apply ram_write_status_sys_preserves_WF_bank. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_WR2_WF : forall s, WF s -> WF (execute s WR2).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. apply ram_write_status_sys_preserves_len. assumption.
  split. apply ram_write_status_sys_preserves_WF_bank. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_WR3_WF : forall s, WF s -> WF (execute s WR3).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. apply ram_write_status_sys_preserves_len. assumption.
  split. apply ram_write_status_sys_preserves_WF_bank. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_SBM_WF : forall s, WF s -> WF (execute s SBM).
Proof.
  intros s HWF. unfold execute, WF in *.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_RDM_WF : forall s, WF s -> WF (execute s RDM).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. apply ram_read_main_bound. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_RDR_WF : forall s, WF s -> WF (execute s RDR).
Proof.
  intros s HWF. unfold execute, WF in *.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. eapply nth_Forall_lt; eauto; lia.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_ADM_WF : forall s, WF s -> WF (execute s ADM).
Proof.
  intros s HWF. unfold execute, WF in *.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. apply nibble_lt16.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_RD0_WF : forall s, WF s -> WF (execute s RD0).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. apply get_stat_bound. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_RD1_WF : forall s, WF s -> WF (execute s RD1).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. apply get_stat_bound. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_RD2_WF : forall s, WF s -> WF (execute s RD2).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. apply get_stat_bound. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_RD3_WF : forall s, WF s -> WF (execute s RD3).
Proof.
  intros s HWF.
  assert (HWF': WF s) by assumption.
  unfold execute.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  unfold WF.
  split. assumption.
  split. assumption.
  split. apply get_stat_bound. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma execute_DCL_WF : forall s, WF s -> WF (execute s DCL).
Proof.
  intros s HWF. unfold execute, WF in *.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply addr12_bound.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. apply Nat.mod_upper_bound. unfold NBANKS. lia.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  split. assumption.
  assumption.
Qed.

(** Main preservation theorem: execute preserves WF for all well-formed instructions. *)
Theorem execute_preserves_WF :
  forall s i, WF s -> instr_wf i -> WF (execute s i).
Proof.
  intros s i HWF Hwfi.
  destruct i.
  - apply execute_NOP_WF; assumption.
  - apply execute_JCN_WF; assumption.
  - apply execute_FIM_WF; assumption.
  - apply execute_SRC_WF; assumption.
  - apply execute_FIN_WF; assumption.
  - apply execute_JIN_WF; assumption.
  - apply execute_JUN_WF; assumption.
  - apply execute_JMS_WF; assumption.
  - apply execute_INC_WF; assumption.
  - apply execute_ISZ_WF; assumption.
  - apply execute_ADD_WF; assumption.
  - apply execute_SUB_WF; assumption.
  - apply execute_LD_WF; assumption.
  - apply execute_XCH_WF; assumption.
  - apply execute_BBL_WF; assumption.
  - apply execute_LDM_WF; assumption.
  - apply execute_WRM_WF; assumption.
  - apply execute_WMP_WF; assumption.
  - apply execute_WRR_WF; assumption.
  - apply execute_WPM_WF; assumption.
  - apply execute_WR0_WF; assumption.
  - apply execute_WR1_WF; assumption.
  - apply execute_WR2_WF; assumption.
  - apply execute_WR3_WF; assumption.
  - apply execute_SBM_WF; assumption.
  - apply execute_RDM_WF; assumption.
  - apply execute_RDR_WF; assumption.
  - apply execute_ADM_WF; assumption.
  - apply execute_RD0_WF; assumption.
  - apply execute_RD1_WF; assumption.
  - apply execute_RD2_WF; assumption.
  - apply execute_RD3_WF; assumption.
  - apply execute_CLB_WF; assumption.
  - apply execute_CLC_WF; assumption.
  - apply execute_IAC_WF; assumption.
  - apply execute_CMC_WF; assumption.
  - apply execute_CMA_WF; assumption.
  - apply execute_RAL_WF; assumption.
  - apply execute_RAR_WF; assumption.
  - apply execute_TCC_WF; assumption.
  - apply execute_DAC_WF; assumption.
  - apply execute_TCS_WF; assumption.
  - apply execute_STC_WF; assumption.
  - apply execute_DAA_WF; assumption.
  - apply execute_KBP_WF; assumption.
  - apply execute_DCL_WF; assumption.
Qed.

(** Proves single step (fetch-decode-execute) preserves WF. *)
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

(** Proves n-step execution preserves WF. *)
Theorem steps_preserve_WF : forall n s, WF s -> WF (steps n s).
Proof.
  induction n; simpl; intros; auto. apply IHn. apply step_preserves_WF; assumption.
Qed.

(* ==================== Behavioral correctness theorems ==================== *)

(* NOP preserves all state except incrementing PC. *)
Theorem nop_preserves_state : forall s,
  let s' := execute s NOP in
  acc s' = acc s /\ regs s' = regs s /\ carry s' = carry s /\ pc s' = addr12_of_nat (pc s + 1).
Proof. intros s. simpl. repeat split; reflexivity. Qed.

(* LDM loads immediate value into accumulator. *)
Theorem ldm_loads_immediate : forall s n,
  n < 16 ->
  let s' := execute s (LDM n) in
  acc s' = n /\ pc s' = addr12_of_nat (pc s + 1).
Proof.
  intros s n H. simpl. split.
  - unfold nibble_of_nat. rewrite Nat.mod_small; auto.
  - reflexivity.
Qed.

(* CLB clears both accumulator and carry. *)
Theorem clb_clears : forall s,
  let s' := execute s CLB in
  acc s' = 0 /\ carry s' = false /\ pc s' = addr12_of_nat (pc s + 1).
Proof. intros s. simpl. repeat split; reflexivity. Qed.

(* Carry/Link check examples *)
(* SUB sets carry iff result did not underflow (borrow did not occur). *)
Lemma sub_link_matches_spec : forall s r,
  let s' := execute s (SUB r) in
  carry s' = (16 <=? (acc s + 16 - get_reg s r - (if carry s then 0 else 1))).
Proof. intros; simpl; reflexivity. Qed.

(* DAC sets carry iff accumulator was non-zero (no underflow to zero). *)
Lemma dac_link_matches_spec : forall s,
  let s' := execute s DAC in carry s' = negb (acc s =? 0).
Proof. intros; simpl; reflexivity. Qed.

(* DAA performs BCD adjustment: adds 6 if (acc+carry) > 9. *)
Lemma daa_adjust_rule : forall s,
  let s' := execute s DAA in
  let acc_with_carry := acc s + (if carry s then 1 else 0) in
  let needs_adjust := 9 <? acc_with_carry in
  let adjusted := if needs_adjust then acc_with_carry + 6 else acc_with_carry in
  acc s' = nibble_of_nat adjusted /\
  carry s' = (16 <=? adjusted).
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

(* Step function is deterministic: equal inputs produce equal outputs. *)
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
  intros s Hwf. unfold step.
  set (b1 := fetch_byte s (pc s)).
  set (b2 := fetch_byte s (addr12_of_nat (pc s + 1))).
  apply (execute_pc_bounded s (decode b1 b2)).
  - apply decode_instr_wf.
    + unfold b1, fetch_byte.
      destruct (nth_in_or_default _ (pc s) (rom s) 0) as [Hin|Hdef].
      * destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HromFor _]]]]]]]]]]]]]].
        rewrite Forall_forall in HromFor.
        apply HromFor. exact Hin.
      * rewrite Hdef. lia.
    + unfold b2, fetch_byte.
      destruct (nth_in_or_default _ (addr12_of_nat (pc s + 1)) (rom s) 0) as [Hin|Hdef].
      * destruct Hwf as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [HromFor _]]]]]]]]]]]]]].
        rewrite Forall_forall in HromFor.
        apply HromFor. exact Hin.
      * rewrite Hdef. lia.
  - exact Hwf.
Qed.

Definition is_jump (i:Instruction) : bool :=
  match i with
  | JCN _ _ | JUN _ | JMS _ | JIN _ | BBL _ | ISZ _ _ => true
  | _ => false
  end.

Corollary pc_monotonic_non_jump : forall s i,
  WF s ->
  instr_wf i ->
  is_jump i = false ->
  pc (execute s i) = addr12_of_nat (pc s + 1) \/
  pc (execute s i) = addr12_of_nat (pc s + 2).
Proof.
  intros s i HWF Hwfi Hjump.
  destruct i; simpl in Hjump; try discriminate; unfold execute;
  try (left; unfold pc_inc1; reflexivity);
  try (right; unfold pc_inc2; reflexivity).
Qed.

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

Definition writes_acc (i:Instruction) : bool :=
  match i with
  | LDM _ | LD _ | ADD _ | SUB _ | INC _ | XCH _ | BBL _
  | SBM | RDM | RDR | ADM | RD0 | RD1 | RD2 | RD3
  | CLB | CMA | IAC | DAC | RAL | RAR | TCC | TCS | DAA | KBP => true
  | _ => false
  end.

Lemma execute_acc_frame : forall s i,
  writes_acc i = false ->
  acc (execute s i) = acc s.
Proof.
  intros s i H.
  destruct i; simpl in H; try discriminate; unfold execute; try reflexivity;
  try (destruct (prom_enable s); reflexivity).
  - set (c1 := n / 8).
    set (c2 := (n / 4) mod 2).
    set (c3 := (n / 2) mod 2).
    set (c4 := n mod 2).
    set (base_cond := orb (andb (acc s =? 0) (c2 =? 1)) (orb (andb (carry s) (c3 =? 1)) (andb (negb (test_pin s)) (c4 =? 1)))).
    set (jump := if c1 =? 1 then negb base_cond else base_cond).
    destruct jump; reflexivity.
  - set (new_val := nibble_of_nat (get_reg s n + 1)).
    destruct (new_val =? 0); reflexivity.
Qed.

(* --- KBP mapping & TEST note --- *)

(* KBP encodes single-bit positions (0,1,2,4,8) to indices (0,1,2,3,4), else 15. *)
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
    assert (get_reg_pair s r / 16 < 16) by (apply Nat.Div0.div_lt_upper_bound; lia).
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

(* End-to-end RAM roundtrip: SRC+WRM+RDM reads back original accumulator. *)
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
  assert (Hhi: hi < 16) by (subst hi; apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hlo: lo < 16) by (subst lo; apply Nat.mod_bound_pos; lia).
  assert (Hchip: chip < 4) by (subst chip; apply Nat.Div0.div_lt_upper_bound; lia).
  assert (Hrno: rno < 4) by (subst rno; apply Nat.mod_bound_pos; lia).
  set (selr := mkRAMSel chip rno lo) in *.
  set (s1 := mkState (acc s) (regs s) (carry s) (pc_inc1 s) (stack s)
                     (ram_sys s) (cur_bank s) selr
                     (rom_ports s) hi (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s)).
  assert (Hs1_props: cur_bank s1 = cur_bank s /\ sel_ram s1 = selr /\ ram_sys s1 = ram_sys s /\ acc s1 = acc s).
  { subst s1. simpl. auto. }
  destruct Hs1_props as [Hs1_bank [Hs1_sel [Hs1_ram Hs1_acc]]].
  assert (Hsel_bounds: sel_chip selr < NCHIPS /\ sel_reg selr < NREGS /\ sel_char selr < NMAIN).
  { subst selr. simpl. unfold NCHIPS, NREGS, NMAIN. split; [|split]; lia. }
  destruct Hsel_bounds as [Hsel_chip [Hsel_reg Hsel_char]].
  set (s2 := mkState (acc s1) (regs s1) (carry s1) (pc_inc1 s1) (stack s1)
                     (ram_write_main_sys s1 (acc s1)) (cur_bank s1) (sel_ram s1)
                     (rom_ports s1) (sel_rom s1) (rom s1) (test_pin s1) (prom_addr s1) (prom_data s1) (prom_enable s1)).
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

Corollary src_wrr_rom_port_roundtrip : forall s r,
  WF s ->
  let v := acc s in
  let s1 := execute s (SRC r) in
  let s2 := execute s1 WRR in
  nth (sel_rom s1) (rom_ports s2) 0 = v.
Proof.
  intros s r Hwf v s1 s2.
  subst v s1 s2.
  unfold execute at 1. fold execute.
  simpl sel_rom.
  apply src_wrr_updates_rom_port.
  exact Hwf.
Qed.

Lemma jms_bbl_roundtrip : forall s addr data,
  WF s ->
  length (stack s) <= 2 ->
  addr < 4096 ->
  let s1 := execute s (JMS addr) in
  let s2 := execute s1 (BBL data) in
  pc s2 = addr12_of_nat (pc s + 2).
Proof.
  intros s addr data Hwf Hstack Haddr s1 s2.
  subst s1 s2.
  unfold execute at 2. fold execute.
  unfold execute at 1. fold execute.
  set (ret_addr := addr12_of_nat (pc s + 2)).
  set (s_pushed := push_stack s ret_addr).
  unfold s_pushed, push_stack.
  destruct (stack s) as [|a [|b [|c rest]]] eqn:Estack.
  - simpl. unfold pop_stack. simpl. reflexivity.
  - simpl. unfold pop_stack. simpl. reflexivity.
  - simpl. unfold pop_stack. simpl. reflexivity.
  - simpl in Hstack. lia.
Qed.

Corollary steps_from_init_WF : forall n, WF (steps n init_state).
Proof.
  intros n. apply steps_preserve_WF. apply init_state_WF.
Qed.

Corollary steps_deterministic : forall n s1 s2,
  s1 = s2 -> steps n s1 = steps n s2.
Proof.
  intros n s1 s2 Heq. rewrite Heq. reflexivity.
Qed.

Corollary reg_pair_addressing_invariant : forall s r,
  r mod 2 = 0 ->
  get_reg_pair s r = get_reg_pair s (r + 1).
Proof.
  intros s r Heven.
  unfold get_reg_pair.
  assert (Hr_even: r - r mod 2 = r) by (rewrite Heven; lia).
  assert (Hr1_even: (r + 1) - (r + 1) mod 2 = r).
  { replace ((r + 1) mod 2) with 1.
    - lia.
    - rewrite Nat.Div0.add_mod by lia.
      rewrite Heven. simpl. reflexivity. }
  rewrite Hr_even, Hr1_even.
  reflexivity.
Qed.

Lemma r_even_bound : forall r,
  r - r mod 2 < 16 \/ r - r mod 2 >= 16.
Proof.
  intro r. lia.
Qed.

(* ==================== Fetch increment equalities ==================== *)

Lemma pc_inc1_unfold : forall s,
  pc_inc1 s = addr12_of_nat (pc s + 1).
Proof.
  intros s. unfold pc_inc1. reflexivity.
Qed.

Lemma pc_inc2_unfold : forall s,
  pc_inc2 s = addr12_of_nat (pc s + 2).
Proof.
  intros s. unfold pc_inc2. reflexivity.
Qed.

(* ==================== update_nth out-of-bounds ==================== *)

Lemma update_nth_out_of_bounds : forall A (l : list A) n x,
  n >= length l -> update_nth n x l = l.
Proof.
  intros A l n x Hn.
  unfold update_nth.
  assert (n <? length l = false).
  { apply Nat.ltb_ge. exact Hn. }
  rewrite H. reflexivity.
Qed.

(* ==================== Register round-trips ==================== *)

Lemma get_reg_set_reg_same : forall s r v,
  length (regs s) = 16 ->
  r < 16 ->
  get_reg (set_reg s r v) r = nibble_of_nat v.
Proof.
  intros s r v Hlen Hr.
  unfold get_reg, set_reg. simpl.
  apply nth_update_nth_eq. rewrite Hlen. assumption.
Qed.

(* ==================== Encode range (bytes < 256) ==================== *)

(* Helper lemma for arithmetic bounds *)
Lemma add_bound_32_256 : forall n, n < 16 -> 16 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (16 + n <= 16 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (16 + 15 = 31) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=31); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_48_256 : forall n, n < 16 -> 32 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (32 + n <= 32 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (32 + 15 = 47) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=47); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_64_256 : forall n, n < 16 -> 48 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (48 + n <= 48 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (48 + 15 = 63) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=63); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_80_256 : forall n, n < 16 -> 64 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (64 + n <= 64 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (64 + 15 = 79) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=79); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_96_256 : forall n, n < 16 -> 80 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (80 + n <= 80 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (80 + 15 = 95) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=95); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_112_256 : forall n, n < 16 -> 96 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (96 + n <= 96 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (96 + 15 = 111) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=111); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_128_256 : forall n, n < 16 -> 112 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (112 + n <= 112 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (112 + 15 = 127) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=127); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_144_256 : forall n, n < 16 -> 128 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (128 + n <= 128 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (128 + 15 = 143) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=143); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_160_256 : forall n, n < 16 -> 144 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (144 + n <= 144 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (144 + 15 = 159) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=159); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_176_256 : forall n, n < 16 -> 160 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (160 + n <= 160 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (160 + 15 = 175) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=175); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_192_256 : forall n, n < 16 -> 176 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (176 + n <= 176 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (176 + 15 = 191) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=191); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_208_256 : forall n, n < 16 -> 192 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (192 + n <= 192 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (192 + 15 = 207) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=207); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma add_bound_224_256 : forall n, n < 16 -> 208 + n < 256.
Proof.
  intros n Hn.
  assert (n <= 15).
  { unfold lt in Hn. apply Nat.succ_le_mono. exact Hn. }
  assert (208 + n <= 208 + 15).
  { apply Nat.add_le_mono_l. exact H. }
  assert (208 + 15 = 223) by reflexivity.
  rewrite H1 in H0.
  apply Nat.le_lt_trans with (m:=223); [exact H0 | unfold lt; repeat constructor].
Qed.

Lemma encode_NOP_range : fst (encode NOP) < 256 /\ snd (encode NOP) < 256.
Proof.
  unfold encode, fst, snd. split; unfold lt; repeat constructor.
Qed.

Lemma encode_JCN_range : forall n b,
  instr_wf (JCN n b) ->
  fst (encode (JCN n b)) < 256 /\ snd (encode (JCN n b)) < 256.
Proof.
  intros n b Hwf. unfold instr_wf in Hwf. destruct Hwf as [Hn Hb].
  unfold encode, fst, snd.
  split.
  - apply add_bound_32_256. exact Hn.
  - assert (b = b mod 256).
    { symmetry. apply Nat.mod_small. exact Hb. }
    rewrite <- H. exact Hb.
Qed.

Lemma encode_FIM_range : forall n b,
  instr_wf (FIM n b) ->
  fst (encode (FIM n b)) < 256 /\ snd (encode (FIM n b)) < 256.
Proof.
  intros n b Hwf. unfold instr_wf in Hwf. destruct Hwf as [Hn [Heven Hb]].
  unfold encode, fst, snd.
  split.
  - assert ((n - n mod 2) mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_48_256. exact H.
  - assert (b = b mod 256).
    { symmetry. apply Nat.mod_small. exact Hb. }
    rewrite <- H. exact Hb.
Qed.

Lemma encode_SRC_range : forall n,
  instr_wf (SRC n) ->
  fst (encode (SRC n)) < 256 /\ snd (encode (SRC n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf. destruct Hwf as [Hn Hodd].
  unfold encode, fst, snd.
  split.
  - assert (((n - n mod 2 + 1) mod 16) < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_48_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_FIN_range : forall n,
  instr_wf (FIN n) ->
  fst (encode (FIN n)) < 256 /\ snd (encode (FIN n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf. destruct Hwf as [Hn Heven].
  unfold encode, fst, snd.
  split.
  - assert ((n - n mod 2) mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_64_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_JIN_range : forall n,
  instr_wf (JIN n) ->
  fst (encode (JIN n)) < 256 /\ snd (encode (JIN n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf. destruct Hwf as [Hn Hodd].
  unfold encode, fst, snd.
  split.
  - assert (((n - n mod 2 + 1) mod 16) < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_64_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_JUN_range : forall a,
  instr_wf (JUN a) ->
  fst (encode (JUN a)) < 256 /\ snd (encode (JUN a)) < 256.
Proof.
  intros a Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert ((a / 256) mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_80_256. exact H.
  - assert (a mod 256 < 256) by (apply Nat.mod_upper_bound; lia).
    exact H.
Qed.

Lemma encode_JMS_range : forall a,
  instr_wf (JMS a) ->
  fst (encode (JMS a)) < 256 /\ snd (encode (JMS a)) < 256.
Proof.
  intros a Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert ((a / 256) mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_96_256. exact H.
  - assert (a mod 256 < 256) by (apply Nat.mod_upper_bound; lia).
    exact H.
Qed.

Lemma encode_INC_range : forall n,
  instr_wf (INC n) ->
  fst (encode (INC n)) < 256 /\ snd (encode (INC n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_112_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_ISZ_range : forall n b,
  instr_wf (ISZ n b) ->
  fst (encode (ISZ n b)) < 256 /\ snd (encode (ISZ n b)) < 256.
Proof.
  intros n b Hwf. unfold instr_wf in Hwf. destruct Hwf as [Hn Hb].
  unfold encode, fst, snd.
  split.
  - assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_128_256. exact H.
  - assert (b = b mod 256).
    { symmetry. apply Nat.mod_small. exact Hb. }
    rewrite <- H. exact Hb.
Qed.

Lemma encode_ADD_range : forall n,
  instr_wf (ADD n) ->
  fst (encode (ADD n)) < 256 /\ snd (encode (ADD n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_144_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_SUB_range : forall n,
  instr_wf (SUB n) ->
  fst (encode (SUB n)) < 256 /\ snd (encode (SUB n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_160_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_LD_range : forall n,
  instr_wf (LD n) ->
  fst (encode (LD n)) < 256 /\ snd (encode (LD n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_176_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_XCH_range : forall n,
  instr_wf (XCH n) ->
  fst (encode (XCH n)) < 256 /\ snd (encode (XCH n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_192_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_BBL_range : forall n,
  instr_wf (BBL n) ->
  fst (encode (BBL n)) < 256 /\ snd (encode (BBL n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_208_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_LDM_range : forall n,
  instr_wf (LDM n) ->
  fst (encode (LDM n)) < 256 /\ snd (encode (LDM n)) < 256.
Proof.
  intros n Hwf. unfold instr_wf in Hwf.
  unfold encode, fst, snd.
  split.
  - assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
    apply add_bound_224_256. exact H.
  - unfold lt. repeat constructor.
Qed.

Lemma encode_WRM_range : fst (encode WRM) < 256 /\ snd (encode WRM) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_WMP_range : fst (encode WMP) < 256 /\ snd (encode WMP) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_WRR_range : fst (encode WRR) < 256 /\ snd (encode WRR) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_WPM_range : fst (encode WPM) < 256 /\ snd (encode WPM) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_WR0_range : fst (encode WR0) < 256 /\ snd (encode WR0) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_WR1_range : fst (encode WR1) < 256 /\ snd (encode WR1) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_WR2_range : fst (encode WR2) < 256 /\ snd (encode WR2) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_WR3_range : fst (encode WR3) < 256 /\ snd (encode WR3) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_SBM_range : fst (encode SBM) < 256 /\ snd (encode SBM) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_RDM_range : fst (encode RDM) < 256 /\ snd (encode RDM) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_RDR_range : fst (encode RDR) < 256 /\ snd (encode RDR) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_ADM_range : fst (encode ADM) < 256 /\ snd (encode ADM) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_RD0_range : fst (encode RD0) < 256 /\ snd (encode RD0) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_RD1_range : fst (encode RD1) < 256 /\ snd (encode RD1) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_RD2_range : fst (encode RD2) < 256 /\ snd (encode RD2) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_RD3_range : fst (encode RD3) < 256 /\ snd (encode RD3) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_CLB_range : fst (encode CLB) < 256 /\ snd (encode CLB) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_CLC_range : fst (encode CLC) < 256 /\ snd (encode CLC) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_IAC_range : fst (encode IAC) < 256 /\ snd (encode IAC) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_CMC_range : fst (encode CMC) < 256 /\ snd (encode CMC) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_CMA_range : fst (encode CMA) < 256 /\ snd (encode CMA) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_RAL_range : fst (encode RAL) < 256 /\ snd (encode RAL) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_RAR_range : fst (encode RAR) < 256 /\ snd (encode RAR) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_TCC_range : fst (encode TCC) < 256 /\ snd (encode TCC) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_DAC_range : fst (encode DAC) < 256 /\ snd (encode DAC) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_TCS_range : fst (encode TCS) < 256 /\ snd (encode TCS) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_STC_range : fst (encode STC) < 256 /\ snd (encode STC) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_DAA_range : fst (encode DAA) < 256 /\ snd (encode DAA) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_KBP_range : fst (encode KBP) < 256 /\ snd (encode KBP) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_DCL_range : fst (encode DCL) < 256 /\ snd (encode DCL) < 256.
Proof. unfold encode, fst, snd. split; unfold lt; repeat constructor. Qed.

Lemma encode_range : forall i,
  instr_wf i ->
  fst (encode i) < 256 /\ snd (encode i) < 256.
Proof.
  intros i Hwf.
  destruct i.
  - apply encode_NOP_range.
  - apply encode_JCN_range. exact Hwf.
  - apply encode_FIM_range. exact Hwf.
  - apply encode_SRC_range. exact Hwf.
  - apply encode_FIN_range. exact Hwf.
  - apply encode_JIN_range. exact Hwf.
  - apply encode_JUN_range. exact Hwf.
  - apply encode_JMS_range. exact Hwf.
  - apply encode_INC_range. exact Hwf.
  - apply encode_ISZ_range. exact Hwf.
  - apply encode_ADD_range. exact Hwf.
  - apply encode_SUB_range. exact Hwf.
  - apply encode_LD_range. exact Hwf.
  - apply encode_XCH_range. exact Hwf.
  - apply encode_BBL_range. exact Hwf.
  - apply encode_LDM_range. exact Hwf.
  - apply encode_WRM_range.
  - apply encode_WMP_range.
  - apply encode_WRR_range.
  - apply encode_WPM_range.
  - apply encode_WR0_range.
  - apply encode_WR1_range.
  - apply encode_WR2_range.
  - apply encode_WR3_range.
  - apply encode_SBM_range.
  - apply encode_RDM_range.
  - apply encode_RDR_range.
  - apply encode_ADM_range.
  - apply encode_RD0_range.
  - apply encode_RD1_range.
  - apply encode_RD2_range.
  - apply encode_RD3_range.
  - apply encode_CLB_range.
  - apply encode_CLC_range.
  - apply encode_IAC_range.
  - apply encode_CMC_range.
  - apply encode_CMA_range.
  - apply encode_RAL_range.
  - apply encode_RAR_range.
  - apply encode_TCC_range.
  - apply encode_DAC_range.
  - apply encode_TCS_range.
  - apply encode_STC_range.
  - apply encode_DAA_range.
  - apply encode_KBP_range.
  - apply encode_DCL_range.
Qed.

Corollary instr_encodes_to_valid_bytes : forall i,
  instr_wf i ->
  let '(b1, b2) := encode i in
  b1 < 256 /\ b2 < 256.
Proof.
  intros i Hwf.
  destruct (encode i) as [b1 b2] eqn:E.
  assert (H := encode_range i Hwf).
  rewrite E in H. simpl in H.
  exact H.
Qed.

Corollary instr_encodes_to_two_bytes : forall i,
  instr_wf i ->
  exists b1 b2, encode i = (b1, b2) /\ b1 < 256 /\ b2 < 256.
Proof.
  intros i Hwf.
  destruct (encode i) as [b1 b2] eqn:E.
  exists b1, b2.
  assert (H := encode_range i Hwf).
  rewrite E in H. simpl in H.
  split; [reflexivity | exact H].
Qed.

Corollary instr_encodes_to_exactly_two_valid_bytes : forall i,
  instr_wf i ->
  exists! p : byte * byte,
    encode i = p /\
    fst p < 256 /\ snd p < 256 /\
    decode (fst p) (snd p) = i.
Proof.
  intros i Hwf.
  destruct (encode i) as [b1 b2] eqn:Eenc.
  exists (b1, b2).
  split.
  - split; [reflexivity | ].
    simpl.
    assert (Hrange := encode_range i Hwf).
    rewrite Eenc in Hrange.
    simpl in Hrange.
    split; [apply Hrange | ].
    split; [apply Hrange | ].
    pose proof (decode_encode_id i Hwf) as Hdec.
    rewrite Eenc in Hdec.
    simpl in Hdec.
    exact Hdec.
  - intros [b1' b2'] [Henc' [Hfst' [Hsnd' Hdec']]].
    simpl in Hfst', Hsnd', Hdec'.
    congruence.
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
  - simpl. reflexivity.
  - simpl. inversion Hall; subst.
    destruct (encode i) as [b1 b2] eqn:E.
    simpl.
    assert (Hdec: decode b1 b2 = i).
    { pose proof (decode_encode_id i H1) as H.
      rewrite E in H. simpl in H. exact H. }
    rewrite Hdec.
    rewrite IH; auto.
Qed.


(* ===================================================================== *)
(*                         HOARE LOGIC LAYER                             *)
(* ===================================================================== *)

(* ==================== Hoare Triple Definition ======================= *)

Definition hoare_triple (P Q : Intel4004State -> Prop) (i : Instruction) : Prop :=
  forall s, WF s -> P s ->
    let s' := execute s i in
    WF s' /\ Q s'.

Notation "{{ P }} i {{ Q }}" := (hoare_triple P Q i) (at level 90, i at next level).

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

(* ==================== Accumulator Instructions =================== *)

Lemma hoare_LDM : forall n,
  {{ fun _ => n < 16 }}
     LDM n
  {{ fun s => acc s = nibble_of_nat n }}.
Proof.
  intros n. unfold hoare_triple, execute. intros s HWF Hn.
  split.
  - apply execute_LDM_WF; auto; unfold instr_wf; exact Hn.
  - simpl; reflexivity.
Qed.

Lemma hoare_LD : forall r old_r,
  {{ fun s => get_reg s r = old_r /\ r < 16 }}
     LD r
  {{ fun s => acc s = old_r }}.
Proof.
  intros r old_r. unfold hoare_triple. intros s HWF [Hold Hr].
  split.
  - apply execute_LD_WF. exact HWF. unfold instr_wf. exact Hr.
  - unfold execute. simpl. exact Hold.
Qed.

Lemma hoare_CLB :
  {{ fun _ => True }}
     CLB
  {{ fun s => acc s = 0 /\ carry s = false }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split.
  - apply execute_CLB_WF. exact HWF.
  - unfold execute. simpl. split; reflexivity.
Qed.

Lemma hoare_CLC : forall old_acc,
  {{ fun s => acc s = old_acc }}
     CLC
  {{ fun s => acc s = old_acc /\ carry s = false }}.
Proof.
  intros old_acc. unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_CLC_WF. exact HWF.
  - unfold execute. simpl. split; [exact Hacc | reflexivity].
Qed.


Lemma hoare_STC : forall old_acc,
  {{ fun s => acc s = old_acc }}
     STC
  {{ fun s => acc s = old_acc /\ carry s = true }}.
Proof.
  intros old_acc. unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_STC_WF. exact HWF.
  - unfold execute. simpl. split; [exact Hacc | reflexivity].
Qed.

Lemma hoare_CMC : forall old_acc old_carry,
  {{ fun s => acc s = old_acc /\ carry s = old_carry }}
     CMC
  {{ fun s => acc s = old_acc /\ carry s = negb old_carry }}.
Proof.
  intros old_acc old_carry. unfold hoare_triple. intros s HWF [Hacc Hcarry].
  split.
  - apply execute_CMC_WF. exact HWF.
  - unfold execute. simpl. split; [exact Hacc | rewrite Hcarry; reflexivity].
Qed.

Lemma hoare_CMA :
  {{ fun s => acc s < 16 }}
     CMA
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_CMA_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_IAC :
  {{ fun s => acc s < 16 }}
     IAC
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_IAC_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_DAC :
  {{ fun s => acc s < 16 }}
     DAC
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_DAC_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_RAL :
  {{ fun s => acc s < 16 }}
     RAL
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_RAL_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_RAR :
  {{ fun s => acc s < 16 }}
     RAR
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_RAR_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_TCC :
  {{ fun _ => True }}
     TCC
  {{ fun s => acc s < 16 /\ carry s = false }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split.
  - apply execute_TCC_WF. exact HWF.
  - unfold execute. simpl. split; [destruct (carry s); lia | reflexivity].
Qed.

Lemma hoare_TCS :
  {{ fun _ => True }}
     TCS
  {{ fun s => acc s < 16 /\ carry s = false }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split.
  - apply execute_TCS_WF. exact HWF.
  - unfold execute. simpl. split; [destruct (carry s); lia | reflexivity].
Qed.

Lemma hoare_DAA :
  {{ fun s => acc s < 16 }}
     DAA
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_DAA_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_KBP :
  {{ fun s => acc s < 16 }}
     KBP
  {{ fun s => acc s < 16 }}.
Proof.
Admitted.

(* ==================== Register Instructions ====================== *)

Lemma hoare_INC : forall r,
  {{ fun s => r < length (regs s) }}
     INC r
  {{ fun s => get_reg s r < 16 }}.
Proof.
  intros r. unfold hoare_triple, execute. intros s HWF Hr.
  split.
  - apply execute_INC_WF; auto. unfold instr_wf.
    destruct HWF as [HlenR _]. lia.
  - unfold get_reg, set_reg. simpl.
    rewrite nth_update_nth_eq by assumption.
    apply nibble_lt16.
Qed.

Lemma hoare_ADD : forall r,
  {{ fun s => r < length (regs s) /\ acc s < 16 /\ get_reg s r < 16 }}
     ADD r
  {{ fun s => acc s < 16 }}.
Proof.
  intros r. unfold hoare_triple, execute. intros s HWF [Hr [Hacc Hreg]].
  split.
  - apply execute_ADD_WF; auto. unfold instr_wf.
    destruct HWF as [HlenR _]. lia.
  - apply nibble_lt16.
Qed.

Lemma hoare_SUB : forall r,
  {{ fun s => r < length (regs s) /\ acc s < 16 /\ get_reg s r < 16 }}
     SUB r
  {{ fun s => acc s < 16 }}.
Proof.
  intros r. unfold hoare_triple, execute. intros s HWF [Hr [Hacc Hreg]].
  split.
  - apply execute_SUB_WF; auto. unfold instr_wf.
    destruct HWF as [HlenR _]. lia.
  - apply nibble_lt16.
Qed.

Lemma hoare_XCH : forall r,
  {{ fun s => r < length (regs s) }}
     XCH r
  {{ fun s => acc s < 16 /\ get_reg s r < 16 }}.
Proof.
Admitted.

(* ==================== Control Flow =============================== *)

Lemma hoare_NOP : forall P,
  {{ P }}
     NOP
  {{ P }}.
Proof.
Admitted.

Lemma hoare_JUN : forall addr,
  {{ fun s => addr < 4096 }}
     JUN addr
  {{ fun s => pc s = addr }}.
Proof.
Admitted.

Lemma hoare_JMS : forall addr,
  {{ fun s => addr < 4096 /\ length (stack s) <= 3 }}
     JMS addr
  {{ fun s => pc s = addr /\ length (stack s) <= 3 }}.
Proof.
Admitted.

Lemma hoare_BBL : forall d,
  {{ fun s => d < 16 }}
     BBL d
  {{ fun s => acc s = nibble_of_nat d /\ length (stack s) <= 3 }}.
Proof.
Admitted.

(* ==================== RAM/ROM Operations ========================= *)

Lemma hoare_RDM :
  {{ fun _ => True }}
     RDM
  {{ fun s => acc s < 16 }}.
Proof.
Admitted.

Lemma hoare_WRM :
  {{ fun s => acc s < 16 }}
     WRM
  {{ fun _ => True }}.
Proof.
Admitted.

Lemma hoare_ADM :
  {{ fun s => acc s < 16 }}
     ADM
  {{ fun s => acc s < 16 }}.
Proof.
Admitted.

Lemma hoare_SBM :
  {{ fun s => acc s < 16 }}
     SBM
  {{ fun s => acc s < 16 }}.
Proof.
Admitted.

Lemma hoare_DCL :
  {{ fun _ => True }}
     DCL
  {{ fun s => cur_bank s < NBANKS }}.
Proof.
Admitted.

(* ==================== Program-Level Hoare Logic ================== *)

Fixpoint exec_program (prog : list Instruction) (s : Intel4004State) : Intel4004State :=
  match prog with
  | [] => s
  | i :: rest => exec_program rest (execute s i)
  end.

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

Lemma exec_program_app : forall prog1 prog2 s,
  exec_program (prog1 ++ prog2) s = exec_program prog2 (exec_program prog1 s).
Proof.
  induction prog1; intros prog2 s.
  - simpl. reflexivity.
  - simpl. rewrite IHprog1. reflexivity.
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

(* ==================== Example Verifications ====================== *)

Example ex_load_5 :
  {{| fun _ => True |}}
      [LDM 5]
  {{| fun s => acc s = 5 |}}.
Proof.
Admitted.

Example ex_clear :
  {{| fun _ => True |}}
      [CLB]
  {{| fun s => acc s = 0 /\ carry s = false |}}.
Proof.
  apply hoare_single. apply hoare_CLB.
Qed.

Example ex_ldm_iac :
  {{| fun _ => True |}}
      [LDM 5; IAC]
  {{| fun s => acc s = 6 |}}.
Proof.
Admitted.

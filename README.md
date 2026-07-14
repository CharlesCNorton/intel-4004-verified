# Formal Verification of the Intel 4004 Microprocessor in Coq

**Author:** Charles C. Norton  
**Date:** October 7, 2025 (revised July 2026)  
**Proof Assistant:** Rocq 9.0

## Abstract

This repository contains a machine-checked formalization of the Intel 4004 microprocessor and associated MCS-4 system components (4002 RAM, 4001 ROM) in the Coq proof assistant. The formalization comprises operational semantics for all 46 instructions of the 4004 instruction set architecture (ISA), a complete system state model over dependent fixed-width words, and a Hoare logic framework for compositional program verification. The operational semantics follows the hardware where the data sheets define it: multi-bank CM-RAM selection, the four-row address register ring (including its overflow discard and stale-row underflow), half-byte PROM programming through the 4008/4009 latch pair, and mask-programmed port directions are the behavior of `execute` itself. Beyond the instruction-level model, the development includes separation logic over the RAM hierarchy, execution-time analysis, a machine-cycle microarchitecture refinement, and a verified compiler, with if/while control flow, whose ROM images provably run on the fetch-decode-execute machine, together with a PC-indexed simulation method for arbitrary branching control-flow graphs. The development extracts to OCaml and is differentially tested against an independent reference implementation.

The Intel 4004, introduced by Intel Corporation in 1971, was the first commercially available microprocessor. Despite its historical significance, no prior formal verification of the complete system has been published. This work provides a reference specification suitable for emulator validation, certified tool development, and preservation of architectural knowledge.

## Scope

### Formalized Components

The formalization provides complete operational semantics for all 46 instructions of the 4004 ISA. This includes arithmetic operations (ADD, SUB, INC, DAC, IAC, DAA), logical operations (complement via CMA, masking operations), control flow primitives (JUN, JMS, JCN, BBL, JIN), register manipulation (LD, XCH, LDM, FIM, FIN), and memory-mapped I/O operations (WRM, RDM, WMP, WRR, RDR, SRC, DCL).

The system state model is a record over dependent fixed-width words encompassing the 4-bit accumulator, sixteen 4-bit index registers, the carry/link flag, the four-row 12-bit address register ring (the program counter and three saved rows, held in pointer-relative coordinates), the hierarchical 4002 RAM system (organized as 4 banks, each containing 4 chips, each containing 4 registers, each containing 20 characters), the CM-RAM line code latched by DCL, the SRC-latched RAM and ROM addresses, the 4001 output-port latches, input pins, and mask-programmed port directions, program ROM, the PROM programmer state (address latch, write-enable, and the half-byte staging latch), and the TEST pin input signal.

Memory architecture is modeled hierarchically following the MCS-4 specification. The 4002 RAM uses explicit bank selection via DCL, chip and register addressing via SRC, and character-level read/write via RDM and WRM instructions. The ROM model includes byte-addressable program memory with support for runtime PROM programming through the WPM instruction. This captures the unusual capability of the 4004 to modify its own program memory through external programming circuitry.

### Verified Properties

The formalization establishes encode/decode bijection for all well-formed instructions, demonstrating that the assembler encoding is invertible and complete. Well-formedness preservation is proven for all instructions under execution, unconditionally: value bounds hold by construction and the invariant is purely structural. Memory consistency is verified through read-after-write correctness lemmas for RAM operations, including the multi-bank write semantics of every DCL line code. The address ring is proven to implement the call/return discipline with the hardware's overflow discard and stale-row underflow, in lockstep with an explicit slots-and-pointer presentation of the ring. Register pair addressing correctness is established for FIM, FIN, JIN, and SRC instructions. A timing model assigns instruction cycle counts matching the published MCS-4 documentation. A small-step to big-step bridge theorem shows the fetch-decode-execute machine, running on a packed ROM image, reproduces list-level program execution for straight-line code, with a concrete ROM program executed on the machine as a corollary. A PC-indexed simulation theorem generalizes the method to arbitrary branching control-flow graphs, with a measured variant that bounds the number of steps to an exit, and a compiler for a source language with if and while is proven correct all the way into ROM images running on the machine, for images placed anywhere in ROM: conditionals compile to a NOP-padded page-local skip over an absolute jump, so generated code crosses page boundaries freely.

A Hoare logic framework provides pre and postcondition specifications for every instruction: per-instruction rules across the register, accumulator, branch, call/return, RAM, port, and PROM-programming operations, plus one value-level rule whose postcondition is the data-sheet reference function, covering the fifteen-instruction ALU class at once. Frame rules establish non-interference properties for register file modifications, RAM updates, and accumulator changes. Consequence rules enable pre and postcondition strengthening and weakening. Compositional reasoning principles support sequential program verification. The framework includes verified example programs demonstrating register value copying, accumulator computation pipelines, subroutine invocation with the ring call/return discipline, and RAM read-modify-write sequences.

### Known Limitations

The specification is validated by differential testing (`make run`) against an independent reference implementation written directly from the MCS-4 data sheet in a different style: instruction decoding exhaustively over all 65,536 byte pairs, the ALU and flags exhaustively over all accumulator/carry/operand combinations, DAA against decimal arithmetic, branch and jump program-counter semantics exhaustively over all 4,096 program-counter values and all sixteen JCN condition codes (including page-boundary and wraparound cases), the FIN page-of-next-instruction rule, the subroutine address ring including the overflow discard and the stale-row underflow, RAM main and status memory over the full bank/chip/register/character address space under two independent value patterns, the multi-line DCL bank sets, memory-operand arithmetic, and the machine-cycle timing rule. That oracle lives in this repository and shares an author with the model, so the model is additionally cross-validated against the third-party Pyntel4004 emulator (v1.2, PyPI): the exhaustive 9,216-vector accumulator/carry set, dumped from the extracted model, is replayed instruction by instruction on Pyntel4004. Sixteen of the eighteen operations agree on every vector, including SUB, whose borrow convention (the incoming carry is the borrow, the outgoing carry its complement: ACC + ~REG + ~CY) follows the silicon-verified behavior documented by the Linux/4004 project. The disagreements are Pyntel4004 defects adjudicated against the data sheet: its ADD reduces overflowing sums by 14 rather than 16, its DAC writes the constant 8 regardless of input, its JCN invert bit fails to invert the TEST term and its taken JCN and ISZ branches load the raw address byte with no page composition, its FIN reads its RAM array rather than program ROM, and it has no 12-bit wraparound; its executer-loop program-counter convention is compensated rather than counted. The `crossval/` harness makes that comparison reproducible (`make crossval`) and extends it beyond the ALU to the JCN, ISZ, JUN/JMS/JIN/FIN, stack-discipline, and RAM suites; its vector dump doubles as a bench vector set for eventual silicon validation. Validation against physical 4004 silicon remains future work.

Instruction timing is deterministic on the 4004: there is no READY pin and no wait-state mechanism, so the model's one- and two-machine-cycle counts are the hardware's counts, not an idealization. What the model does not represent are analog quantities below the digital abstraction: chip-select setup, data-bus hold, and propagation delays through external latches.

I/O operations use a functional model of ROM and RAM chip behavior at nibble granularity; the electrical bus characteristics above are outside the model's universe.

The 4004 instruction set does not include hardware interrupt support. External interrupt logic sometimes employed in MCS-4 system designs is not modeled, as it falls outside the processor's architectural specification.

### Modeling Choices

The operational semantics follows the hardware wherever the MCS-4 documents define it. The conventions that remain, each marked at its definition, are:

- **Multi-line DCL reads.** The low three accumulator bits drive the CM-RAM lines: codes 0, 1, 2, 4 select banks 0 through 3 (`dcl_acc_determines_bank`), and codes 3, 5, 6, 7 assert several lines at once, so a write reaches banks {1,2}, {1,3}, {2,3}, {1,2,3} simultaneously (`dcl_write_reaches_all_selected`, `dcl_write_frames_unselected`). A read under multi-line selection puts several 4002s on the data bus at once, which no MCS-4 document defines: the specification-level reader (`ram_read_main_opt`) is partial, defined exactly when every selected bank agrees, and the total reader used by `execute` returns 0 in the undefined case (`ram_read_main_undefined_convention`). Single-line reads are always defined (`dcl_read_single_line`), as is any read after a write through the same selection, because the write leaves the selected banks unanimous (`dcl_multiwrite_read_defined`).
- **Disarmed WPM.** Hardware writes program memory in 4-bit halves assembled by the external 4008/4009 latch pair, two WPMs per byte, high half first; that is `execute`'s WPM (`wpm_stage`, `wpm_commit`, `wpm_byte_spec`, `load_then_fetch`), with the programmer's address and write-enable latched from the ROM output ports (`prom_ports_drive_write`). A WPM with the programmer disarmed is a no-op that also leaves the staging latch alone.
- **Port direction granularity.** 4001 port lines are metal-mask configured as inputs or outputs; the model assigns one direction per 4-bit port rather than per line. WRR writes the output latch, and RDR reads the selected port's pins: the latch on an output port (`wrr_rdr_roundtrip`) and the externally driven value on an input port (`rdr_reads_driven_input`, `rdr_after_wrr_input_port_reads_environment`).
- **Undefined opcodes.** Bytes 0x00 through 0x0F and 0xFE/0xFF decode to NOP (`decode_low_group_is_nop`, `decode_FE_FF_is_nop`); the data sheet marks these encodings unused and silicon behavior is not claimed.

No MCS-4 document defines a return past the ring's depth; the model gives it the silicon meaning, a stale row resuming as the PC (`bbl_underflow_from_reset`, `ring_underflow_agrees`), rather than leaving it unspecified.

Reset is modeled at two scopes. `reset_specification` proves a full-length CPU RESET clears the accumulator, carry, index registers, and the whole address ring while 4002 RAM, ROM, the port latches and pins, the direction mask, and the TEST level are preserved. The system-wide RESET line additionally clears 4002 RAM and the output ports per the 4002 data sheet (`system_reset_specification`), and refines the CPU-scope reset (`system_reset_refines_cpu_reset`).

## Technical Approach

### Type System Design

The machine's quantities are dependent fixed-width words: `word w` packages a natural number with a proof that it lies below 2^w, and `nibble := word 4`, `byte := word 8`, `addr12 := word 12` (with 2- and 3-bit widths for the RAM selection indices and the CM-RAM code). Bounds hold by construction. The bound is a boolean equation, so word equality reduces to value equality without axioms, and extraction erases the proof: a word extracts to a bare OCaml integer. The proof component is canonicalized on construction, so full-state equalities of concrete machine runs are decided by `vm_compute`.

### Well-Formedness Invariants

The well-formedness predicate `WF : Intel4004State -> Prop` is purely structural: seven conjuncts fixing container lengths (sixteen index registers, the 4-bank/4-chip/4-register/20-character RAM hierarchy, sixteen entries in each port array and in the direction mask, 4096 ROM bytes). All value bounds are enforced by the word types, and preservation under execution holds unconditionally, with no instruction side conditions (`execute_preserves_WF`).

### Operational Semantics

Instruction execution is defined by the total function `execute : Intel4004State -> Instruction -> Intel4004State`. Each instruction case constructs the successor state through field updaters, preserving all unmodified components. Page-relative addressing for JIN and FIN instructions correctly uses the page number of PC+1 (not the current PC), matching documented hardware behavior. The program counter and three-level stack are one four-row ring: CALL deposits the return address and advances, a fourth nested call overwrites the oldest row, and a return past the ring's depth resumes a stale row. RAM writes reach every bank the DCL line code addresses. The KBP (keyboard process) instruction implements the exact lookup table documented in the 1973 MCS-4 Assembly Language Programming Manual (single-bit positions 0,1,2,4,8 map to indices 0,1,2,3,4; all other inputs map to 15). SUB and SBM subtract the incoming carry as the borrow and emit its complement as the outgoing carry (ACC + ~REG + ~CY), matching silicon-verified behavior, which is why chained subtractions complement the carry between digits.

### Proof Strategy

Preservation of well-formedness under execution proceeds by structural case analysis over instructions; each case reduces to length preservation of the updated containers and is discharged uniformly. Helper lemmas establish preservation of the RAM hierarchy structure under the multi-bank write paths.

Encode/decode bijection is proven by case analysis over instruction constructors. Each case establishes that `decode (fst (encode i)) (snd (encode i)) = i` for well-formed `i`, by arithmetic reasoning about division and modulo operations in the encoding scheme; the width bounds come from the operand types.

Memory consistency lemmas proceed by symbolic execution of the read and write operations, applying update and access lemmas for nested list structures. The hierarchical RAM addressing (bank, chip, register, character) requires four levels of list update/access reasoning.

### Hoare Logic Encoding

Hoare triples are encoded as `hoare_triple (P Q : Intel4004State -> Prop) (i : Instruction) : Prop` defined as universal quantification over well-formed states satisfying the precondition, ensuring the postcondition holds in the successor state while preserving well-formedness. Program-level triples use similar encoding with iterated execution function. Soundness of weakest precondition calculus is established by induction over program structure.

## File Organization

The development is five Coq theory files (machine, behavior, verification, control, fidelity) and an audit/extraction file, all under `theories/`, with the OCaml differential harness and build files at the root and the third-party cross-validation harness under `crossval/`.

**machine.v**: the machine itself. Dependent fixed-width words and their algebra, modular arithmetic, list utilities, the 4002 RAM structures, the system state with its field updaters, register and register-pair access, the four-row address ring (CALL/RET as rotations), ROM fetch and page arithmetic, hierarchical RAM navigation with the CM-RAM line decoding and the multi-bank write and agreement-read combinators, the 46-instruction type, the total decoder and encoder with the parity-only well-formedness predicate and the encode/decode bijection, the operational semantics (`execute`), the fetch-decode-execute machine (`step`, `steps`) and the program big-step (`exec_program`), initial and reset states, the structural `WF` invariant with counterexamples, unconditional preservation (`execute_preserves_WF`), and the multi-bank read-after-write lemmas.

**behavior.v**: what the machine does. Value-level correctness of the arithmetic instructions (memory operands included), ISZ loop theory, JCN condition semantics and the TEST pin, the multi-bank DCL write and read theorems stated against `execute` for characters, status characters, and output ports alike (with a proof that port writes touch no character), the ROM ports under direction masks, PC shapes, page-boundary crossings and wraparound, register/RAM/accumulator/ROM/ring frames, KBP, end-to-end roundtrips, the timing model, half-byte WPM programming with `load_then_fetch` and the port-driven programmer latch, register-pair algebra, program layout, the independent data-sheet correspondences (DAA vs decimal, the 4-bit adder identity, machine cycles, undefined opcodes), checked accessors and the WF-carrying state bundle, fetch fidelity, the reactive TEST/port environment, the small-step bridge (`code_at`, `steps_tracks_exec_program`) with a looping ROM program verified by a PC-indexed invariant, halting, execution-time analysis (exact straight-line times, 8n/16n bounds, the counting loop's exact 272 clock periods), the ALU simulation against an in-file independent reference, the isomorphism between the machine's pointer-relative address ring and an explicit slots-and-pointer ring, and the machine-cycle microarchitecture refinement.

**verification.v**: program verification. Hoare triples carrying `WF` with structural and frame rules, per-instruction and value-level specifications covering the whole instruction set, ISZ and JCN branch rules anchored to the pre-state PC, program-level triples with sequencing, weakest preconditions and verification conditions, verified example programs (register copying, accumulator pipelines, ring call/return discipline, RAM read-modify-write, the ISZ counting loop), single-digit and multi-digit BCD addition verified against decimal arithmetic, separation logic over the RAM hierarchy with small-footprint WRM/RDM rules for single-line DCL codes, and the verified expression/statement compiler with a packed assembler and the end-to-end theorem that compiled ROM images run correctly on the machine (`compiled_stmt_runs_on_machine`).

**control.v**: control flow. The PC-indexed simulation theorems for arbitrary branching control-flow graphs (`pc_indexed_simulation`, and `pc_indexed_reaches` with a decreasing measure), and a source language with assignment, sequencing, if, and while: fuel-indexed semantics, a page-free byte-level code generator (conditionals compile to a NOP-padded page-local skip over an absolute JUN, so images may span pages and sit anywhere in ROM), and the end-to-end theorem that whenever the source semantics terminates, the generated ROM image runs on the fetch-decode-execute machine to the block exit with the final environment in the low registers (`cgen_correct`, `compiled_cstmt_runs_on_machine`). Loop reasoning closes at the source level with the while invariant rule (`cwhile_rule`), and a compiled countdown loop is executed concretely on the machine.

**fidelity.v**: fidelity closures. Undefined-opcode decoding as a theorem (`decode_low_group_is_nop`), system-scope RESET (`system_reset_specification`), TEST-pin sampling adequacy (`test_pin_only_affects_jcn`), the partiality of multi-line DCL reads with its disagreement witness and total-reader convention, the address ring's underflow closed under its silicon meaning, the port-direction read-back caveat, the typed bounds of every state field (`state_bounds_by_construction`), disassembler and validator correctness, and one value-level Hoare rule covering the whole ALU (`hoare_alu_value`).

**audit.v**: `Print Assumptions` for every headline theorem (`make check` fails if any assumption base is nonempty, and reports the count) and the OCaml extraction used by the differential harness.

**driver.ml**: the differential test harness, an independent reference implementation written from the MCS-4 data sheet in a different style.

## Building

The formalization requires the Rocq Prover 9.0 or later. No external dependencies beyond the standard library are required. Building the differential-test harness additionally requires OCaml with ocamlfind.

```
make           # compile the development (machine, behavior, verification, control, fidelity)
make check     # confirm every headline theorem is axiom-free
make run       # extract to OCaml and run the differential test harness
make crossval  # replay model vectors on the Pyntel4004 emulator (pip install Pyntel4004)
```

Compilation completes in a few minutes on contemporary hardware and does not require significant memory. The `check` target exits nonzero if any checked theorem depends on an axiom. The differential harness cross-checks decoding, the ALU, branch and jump program-counter semantics, the address ring including its underflow, RAM main and status memory with the multi-line DCL bank sets, memory-operand arithmetic, and instruction timing against an independent reference implementation.

## Open Items

- Gate-level equivalence checking against a trusted 4004 netlist (the machine-cycle microarchitecture level is done: `microcycle_refines_steps`). Blocked on obtaining a trustworthy netlist artifact, and a standalone project at that point.
- Validation against physical 4004 silicon. The emulator cross-validation now covers the ALU exhaustively plus the control-flow, stack, and RAM suites (`crossval/`), and the vector dump doubles as the bench vector set; the remaining step needs a 4004 on the bench.

## Citation

If this work is used in academic research, please cite:

```
@misc{norton2025intel4004,
  author = {Norton, Charles C.},
  title = {Formal Verification of the Intel 4004 Microprocessor in Coq},
  year = {2025},
  howpublished = {\url{https://github.com/CharlesCNorton/intel-4004-verified}},
  note = {Machine-checked formalization of the Intel 4004 ISA in the Rocq Prover}
}
```

## Acknowledgments

This work relies on the comprehensive technical documentation produced by Intel Corporation's MCS-4 development team in 1973, particularly the MCS-4 Assembly Language Programming Manual and the MCS-4 Micro Computer Set Users Manual. The clarity and precision of that documentation, produced by Federico Faggin's engineering team, made this formalization tractable.

## License

MIT

## Contact

Charles C. Norton  

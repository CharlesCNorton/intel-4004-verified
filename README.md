# Formal Verification of the Intel 4004 Microprocessor in Coq

**Author:** Charles C. Norton  
**Date:** October 7, 2025  
**Proof Assistant:** Coq 8.18+

## Abstract

This repository contains a machine-checked formalization of the Intel 4004 microprocessor and associated MCS-4 system components (4002 RAM, 4001 ROM) in the Coq proof assistant. The formalization comprises operational semantics for all 43 instructions of the 4004 instruction set architecture (ISA), a complete system state model, and a Hoare logic framework for compositional program verification.

The Intel 4004, introduced by Intel Corporation in 1971, was the first commercially available microprocessor. Despite its historical significance, no prior formal verification of the complete system has been published. This work provides a reference specification suitable for emulator validation, certified tool development, and preservation of architectural knowledge.

## Scope

### Formalized Components

The formalization provides complete operational semantics for all 43 instructions of the 4004 ISA. This includes arithmetic operations (ADD, SUB, INC, DAC, IAC, DAA), logical operations (complement via CMA, masking operations), control flow primitives (JUN, JMS, JCN, BBL, JIN), register manipulation (LD, XCH, LDM, FIM, FIN), and memory-mapped I/O operations (WRM, RDM, WMP, WRR, RDR, SRC, DCL).

The system state model consists of a 17-field record encompassing the 4-bit accumulator, sixteen 4-bit general-purpose registers, carry/link flag, 12-bit program counter, 3-level return address stack, hierarchical 4002 RAM system (organized as 4 banks, each containing 4 chips, each containing 4 registers, each containing 20 characters), 4001 ROM port array, PROM programming state (address, data, enable), and TEST pin input signal.

Memory architecture is modeled hierarchically following the MCS-4 specification. The 4002 RAM uses explicit bank selection via DCL, chip and register addressing via SRC, and character-level read/write via RDM and WRM instructions. The ROM model includes byte-addressable program memory with support for runtime PROM programming through the WPM instruction. This captures the unusual capability of the 4004 to modify its own program memory through external programming circuitry.

### Verified Properties

The formalization establishes encode/decode bijection for all well-formed instructions, demonstrating that the assembler encoding is invertible and complete. Well-formedness preservation is proven for all instructions under execution, ensuring that valid machine states remain valid after single-step execution. Memory consistency is verified through read-after-write correctness lemmas for RAM operations. Stack discipline is proven to maintain the 3-level LIFO invariant with documented overflow behavior matching the hardware specification. Register pair addressing correctness is established for FIM, FIN, JIN, and SRC instructions. A timing model assigns instruction cycle counts matching the published MCS-4 documentation.

A Hoare logic framework provides pre and postcondition specifications for all instructions. Frame rules establish non-interference properties for register file modifications, RAM updates, and accumulator changes. Consequence rules enable pre and postcondition strengthening and weakening. Compositional reasoning principles support sequential program verification. The framework includes verified example programs demonstrating register value copying, accumulator computation pipelines, subroutine invocation with stack discipline, and RAM read-modify-write sequences.

### Known Limitations

Three lemmas concerning PROM programming operations (`load_program_preserves_WF`, `load_preserves_rom_length`, `load_then_fetch`) are stated but remain admitted. These lemmas concern well-formedness preservation and functional correctness of iterative ROM loading operations. The proofs are tractable but require additional structural induction over program lists and are documented as future work.

The formalization has not been validated against reference emulator implementations or physical 4004 silicon. Establishing empirical correspondence with existing cycle-accurate emulators would strengthen confidence in the specification's accuracy. Such validation remains future work pending identification of suitable reference implementations.

The timing model reflects ideal instruction execution without memory wait states, bus arbitration delays, or clock stretching. Physical 4004 systems exhibit variable timing based on RAM access patterns and external memory device characteristics. The current model abstracts these hardware-level timing interactions.

I/O operations use an abstract functional model of ROM and RAM chip behavior. Physical timing characteristics including chip-select setup times, data bus hold requirements, and propagation delays through external latches are not captured in the current formalization.

The 4004 instruction set does not include hardware interrupt support. External interrupt logic sometimes employed in MCS-4 system designs is not modeled, as it falls outside the processor's architectural specification.

## Technical Approach

### Type System Design

The formalization employs type aliases over Coq's natural number type (`nibble := nat`, `byte := nat`, `addr12 := nat`) with explicit normalization functions (`nibble_of_nat`, `byte_of_nat`, `addr12_of_nat`) rather than dependent types with static bounds enforcement. This design prioritizes proof simplicity and compatibility with standard Coq tactics over compile-time guarantee of bit-width constraints. Bounds are instead maintained through well-formedness predicates verified as invariants under execution.

### Well-Formedness Invariants

The central well-formedness predicate `WF : Intel4004State -> Prop` consists of seventeen conjuncts establishing bounds on all state components. Register file length is fixed at 16 elements with each register bounded by 16. Accumulator and carry flag bounds are enforced. Program counter is constrained to 12-bit address space (0-4095). Stack length is bounded by 3 with each return address in valid range. RAM system structure maintains 4 banks of 4 chips of 4 registers of 20 characters each, with all character values bounded by 16. ROM and ROM port arrays maintain appropriate size and element bounds. PROM programming state components are similarly constrained.

### Operational Semantics

Instruction execution is defined by the total function `execute : Intel4004State -> Instruction -> Intel4004State`. Each instruction case explicitly constructs the successor state, preserving all unmodified components. Page-relative addressing for JIN and FIN instructions correctly uses the page number of PC+1 (not the current PC), matching documented hardware behavior. The 3-level stack implements wraparound semantics, discarding the oldest entry on overflow. The KBP (keyboard process) instruction implements the exact lookup table documented in the 1973 MCS-4 Assembly Language Programming Manual (single-bit positions 0,1,2,4,8 map to indices 0,1,2,3,4; all other inputs map to 15).

### Proof Strategy

Preservation of well-formedness under execution proceeds by structural case analysis over instructions. Each case establishes that all 17 well-formedness conjuncts are preserved by that instruction's semantics. Helper lemmas establish preservation of substructures (register file bounds, RAM hierarchy structure, stack length bounds). The proof is approximately 2000 lines.

Encode/decode bijection is proven by exhaustive case analysis over instruction constructors. Each case establishes that `decode (fst (encode i)) (snd (encode i)) = i` for well-formed `i`. The proof requires careful arithmetic reasoning about division and modulo operations in the encoding scheme. Approximately 800 lines of proof establish this property.

Memory consistency lemmas proceed by symbolic execution of the read and write operations, applying update and access lemmas for nested list structures. The hierarchical RAM addressing (bank, chip, register, character) requires four levels of list update/access reasoning. Approximately 400 lines establish the core read-after-write property.

### Hoare Logic Encoding

Hoare triples are encoded as `hoare_triple (P Q : Intel4004State -> Prop) (i : Instruction) : Prop` defined as universal quantification over well-formed states satisfying the precondition, ensuring the postcondition holds in the successor state while preserving well-formedness. Program-level triples use similar encoding with iterated execution function. Soundness of weakest precondition calculus is established by induction over program structure.

## File Organization

The formalization is contained in a single 7000-line Coq source file organized into the following sections:

**Imports and Setup** (lines 1-50): Standard library imports (lists, arithmetic, booleans, natural numbers) and proof automation configuration.

**Basic Types** (lines 51-150): Type aliases for nibbles, bytes, and 12-bit addresses with normalization functions and bound lemmas.

**List Utilities** (lines 151-350): Generic list update function with length preservation, element preservation, and access lemmas. Forall predicate preservation lemmas for list operations.

**RAM Structure** (lines 351-450): Record types for RAM registers (16 main + 4 status characters), RAM chips (4 registers + output port), RAM banks (4 chips), and RAM address selection state.

**System State** (lines 451-550): Complete Intel4004State record with 17 fields. Register access and update functions with pair addressing support.

**Stack Operations** (lines 551-650): Push and pop operations with 3-level wraparound semantics. Length and bounds preservation lemmas.

**ROM Operations** (lines 651-750): Byte fetch function, PC increment utilities, page address computation functions.

**RAM Navigation** (lines 751-950): Hierarchical accessor and update functions for four-level RAM structure (bank/chip/register/character). Main character and status character read/write operations.

**Instruction Set** (lines 951-1050): Inductive type defining all 43 instructions with parameters.

**Decode Function** (lines 1051-1150): Total decoder from two bytes to instruction, handling all opcode patterns including disambiguation of even/odd register indices for FIM/SRC and FIN/JIN.

**Encode Function** (lines 1151-1250): Inverse encoder from instruction to byte pair.

**Well-Formedness Predicate** (lines 1251-1350): Definition of `instr_wf` for instruction parameter bounds.

**Encode/Decode Bijection** (lines 1351-1850): Lemmas establishing decode-after-encode identity for each instruction class. Main theorem `decode_encode_id`.

**Execute Function** (lines 1851-2450): Operational semantics defining state transition for each instruction. Handles all control flow, arithmetic, logical, memory, and I/O operations.

**Well-Formedness Invariants** (lines 2451-2650): Definitions of `WF_reg`, `WF_chip`, `WF_bank`, `WF_sel`, and `WF` predicates. Initial state and reset state well-formedness lemmas.

**Preservation Proofs** (lines 2651-3450): Individual lemmas establishing `WF` preservation for each instruction. Main theorem `execute_preserves_WF`. Step and multi-step preservation corollaries.

**Behavioral Correctness** (lines 3451-3650): Theorems characterizing specific instruction behaviors (NOP preservation, LDM loading, arithmetic computation, stack discipline).

**Timing Model** (lines 3651-3750): Cycle count function assigning 8, 16, or 24 cycles per instruction. Determinism and bounds lemmas.

**PROM Programming** (lines 3751-3900): WPM semantics, load_program function for iterative ROM programming. Three admitted lemmas concerning well-formedness and correctness.

**Hoare Logic** (lines 3901-4200): Hoare triple definitions, structural rules (consequence, conjunction, disjunction, existential quantification), frame rules (register/RAM/accumulator non-interference).

**Instruction Specifications** (lines 4201-4600): Pre/postcondition lemmas for each instruction in Hoare logic.

**Program Verification** (lines 4601-4800): Program-level Hoare triples, sequencing lemma, consequence rule, weakest precondition calculus with soundness proof.

**Verified Examples** (lines 4801-7000): Example verified programs including register copying, accumulator pipelines, subroutine invocation, RAM read-modify-write, and BCD arithmetic sequences.

## Building

The formalization requires Coq 8.18 or later with standard library. No external dependencies beyond the base Coq installation are required.

```
coqc Intel4004.v
```

Compilation time is approximately 45 seconds on contemporary hardware (tested on AMD Ryzen 9 5950X, 64GB RAM). The proof does not require significant memory resources.

## Citation

If this work is used in academic research, please cite:

```
@misc{norton2025intel4004,
  author = {Norton, Charles C.},
  title = {Formal Verification of the Intel 4004 Microprocessor in Coq},
  year = {2025},
  howpublished = {\url{https://github.com/...}},
  note = {Machine-checked formalization of the Intel 4004 ISA with 7000+ lines of Coq proofs}
}
```

## Acknowledgments

This work relies on the comprehensive technical documentation produced by Intel Corporation's MCS-4 development team in 1973, particularly the MCS-4 Assembly Language Programming Manual and the MCS-4 Micro Computer Set Users Manual. The clarity and precision of that documentation, produced by Federico Faggin's engineering team, made this formalization tractable.

## License

MIT

## Contact

Charles C. Norton  

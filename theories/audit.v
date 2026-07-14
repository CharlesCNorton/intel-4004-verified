(* Audit and extraction. Print Assumptions confirms every headline theorem
   is closed under the global context (make check fails otherwise), and the
   model is extracted to OCaml for the differential test harness (make run).
   Kept separate so the main development stays warning-free. *)

From FourK Require Import machine behavior verification control fidelity.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlNatInt.

(* Build a CPU state with a given accumulator, carry, and register file;
   all other fields at their power-on defaults. Used to drive the ALU.
   Words extract to bare integers, so the harness passes plain values;
   taking them at word type keeps state construction allocation-free in
   the ROM (the harness shares one ROM list across a whole suite). *)
Definition test_state (a : nibble) (c : bool) (r : list nibble)
                      : Intel4004State :=
  with_carry c (with_acc a (with_regs r init_state)).

(* General builder for the control-flow, ring, and memory suites: given
   accumulator, carry, register file, program counter, TEST level, and ROM;
   everything else at power-on defaults. *)
Definition mk_state (a : nibble) (c : bool) (r : list nibble) (p : addr12)
                    (tp : bool) (romv : list byte) : Intel4004State :=
  with_test tp (with_pc p (with_rom romv
    (with_carry c (with_acc a (with_regs r init_state))))).

(* Numeric observations for the harness: words extract to bare integers,
   and these project the fields the tests compare. *)
Definition stkv1 (s : Intel4004State) : nat := wval (stk1 s).
Definition stkv2 (s : Intel4004State) : nat := wval (stk2 s).
Definition stkv3 (s : Intel4004State) : nat := wval (stk3 s).
Definition ramv (s : Intel4004State) : nat := wval (ram_read_main s).

Set Extraction Output Directory ".".

Extraction "intel4004_model.ml"
  decode encode execute cycles test_state mk_state
  aval carry pcv rval stkv1 stkv2 stkv3 ramv.

(* Core correctness and safety theorems *)
Print Assumptions decode_encode_id.
Print Assumptions decode_instr_wf.
Print Assumptions encode_decode_idempotent.
Print Assumptions encode_decode_list_id.
Print Assumptions execute_preserves_WF.
Print Assumptions step_preserves_WF.
Print Assumptions steps_preserve_WF.
Print Assumptions no_arbitrary_jumps.
Print Assumptions memory_safety.
Print Assumptions state_bounds_by_construction.
Print Assumptions reset_specification.
Print Assumptions init_state_WF.
Print Assumptions wp_soundness.
Print Assumptions count_loop_16_iterations.

(* Arithmetic, timing, decoding, and program-logic theorems *)
Print Assumptions add_computes_sum.
Print Assumptions sub_computes_difference.
Print Assumptions arithmetic_operations_functionally_correct.
Print Assumptions daa_decimal_correct.
Print Assumptions daa_bcd_adjust_correct.
Print Assumptions add_value_correct.
Print Assumptions cycles_eq_machine.
Print Assumptions machine_cycles_one_or_two.
Print Assumptions two_word_is_two_cycle.
Print Assumptions max_cycles_per_instruction.
Print Assumptions timing_preserves_WF.
Print Assumptions decode_FE_FF_is_nop.
Print Assumptions decode_surjective_on_wf.
Print Assumptions hoare_prog_repeat.
Print Assumptions vc_sound.
Print Assumptions progress.
Print Assumptions ram_main_is_frame_bank.
Print Assumptions bcd_add_digits_correct.
Print Assumptions compile_correct.

(* Branch semantics and the TEST pin *)
Print Assumptions jcn_condition_decides_branch.
Print Assumptions jcn_jz_semantics.
Print Assumptions jcn_jt_semantics.
Print Assumptions isz_branch_taken.
Print Assumptions isz_branch_not_taken.
Print Assumptions isz_increments_reg.
Print Assumptions jcn_branch_stays_in_page.
Print Assumptions isz_branch_stays_in_page.
Print Assumptions jin_stays_in_page.
Print Assumptions test_pin_only_affects_jcn.
Print Assumptions test_input_controls_branch.
Print Assumptions execute_pc_shape.
Print Assumptions step_pc_shape.
Print Assumptions nonjump_pc_advances_by_bytes.
Print Assumptions step_fetch_is_length_faithful.

(* The address ring: motion, roundtrips, overflow, underflow, and the
   isomorphism with the slots-and-pointer presentation *)
Print Assumptions jms_ring_motion.
Print Assumptions bbl_ring_motion.
Print Assumptions jms_bbl_roundtrip.
Print Assumptions jms_discards_oldest.
Print Assumptions bbl_underflow_from_reset.
Print Assumptions bbl_reads_stale_row.
Print Assumptions four_returns_close_the_ring.
Print Assumptions rotating_ring_complete.
Print Assumptions ring_tracks_jms.
Print Assumptions ring_tracks_bbl.
Print Assumptions ring_underflow_resumes_stale.
Print Assumptions ring_underflow_agrees.

(* Multi-bank DCL semantics of the machine *)
Print Assumptions dcl_acc_determines_bank.
Print Assumptions dcl_multi_line_codes.
Print Assumptions dcl_write_reaches_all_selected.
Print Assumptions dcl_write_frames_unselected.
Print Assumptions dcl_single_line_writes_one_bank.
Print Assumptions dcl_multiwrite_read_defined.
Print Assumptions dcl_read_single_line.
Print Assumptions ram_read_main_opt_none.
Print Assumptions ram_read_main_defined.
Print Assumptions wrm_then_rdm_reads_back.
Print Assumptions wmp_writes_selected_ports.
Print Assumptions wmp_frames_unselected_ports.
Print Assumptions wmp_preserves_characters.
Print Assumptions wrs_then_rds_reads_back.
Print Assumptions adm_computes_sum.
Print Assumptions sbm_computes_difference.

(* ROM ports under mask-programmed directions *)
Print Assumptions wrr_writes_to_selected_port.
Print Assumptions wrr_rdr_roundtrip.
Print Assumptions src_wrr_updates_rom_port.
Print Assumptions rdr_reads_driven_input.
Print Assumptions rdr_after_wrr_input_port_reads_environment.

(* PROM programming through the half-byte 4008/4009 latch pair *)
Print Assumptions wpm_stage.
Print Assumptions wpm_commit.
Print Assumptions wpm_disabled_is_nop.
Print Assumptions wpm_byte_spec.
Print Assumptions load_then_fetch.
Print Assumptions load_program_fetches_bytes.
Print Assumptions load_program_preserves_other_rom.
Print Assumptions prom_ports_drive_write.

(* Register pairs *)
Print Assumptions fim_operates_on_pairs.
Print Assumptions src_uses_pair_value.
Print Assumptions fin_operates_on_pairs.
Print Assumptions jin_uses_pair_for_jump.
Print Assumptions register_pairs_partition.
Print Assumptions set_reg_pair_get_pair.

(* The small-step / big-step bridge and a machine-run loop *)
Print Assumptions steps_tracks_exec_program.
Print Assumptions demo_runs_on_machine.
Print Assumptions iszloop_runs_on_machine.
Print Assumptions iszloop_confined_forever.
Print Assumptions self_loop_halts_within_0.
Print Assumptions halted_confines_pc.

(* Value-level specifications and the ALU simulation *)
Print Assumptions hoare_IAC_value.
Print Assumptions hoare_DAC_value.
Print Assumptions hoare_DAA_value.
Print Assumptions hoare_RDM_value.
Print Assumptions hoare_WRM_writes.
Print Assumptions hoare_alu_value.
Print Assumptions alu_matches_ref.
Print Assumptions intel4004_transition_sound.

(* Per-instruction Hoare coverage: pairs, ports, status, PROM, memory
   operands *)
Print Assumptions hoare_FIN.
Print Assumptions hoare_JIN.
Print Assumptions hoare_WRR.
Print Assumptions hoare_RDR.
Print Assumptions hoare_WMP.
Print Assumptions hoare_WPM_stage.
Print Assumptions hoare_WPM_commit.
Print Assumptions hoare_WPM_disabled.
Print Assumptions hoare_WRs_writes.
Print Assumptions hoare_RDs_value.
Print Assumptions hoare_ADM_value.
Print Assumptions hoare_SBM_value.

(* Separation logic over the RAM hierarchy *)
Print Assumptions star_comm.
Print Assumptions star_assoc.
Print Assumptions wrm_sep_frame.
Print Assumptions rdm_sep.

(* Multi-byte BCD arithmetic *)
Print Assumptions bcd_sum_correct.
Print Assumptions bcd_add_prog_correct.

(* Execution-time analysis *)
Print Assumptions straightline_time_bounds.
Print Assumptions machine_time_bounds.
Print Assumptions machine_time_straightline.
Print Assumptions iszloop_machine_time.

(* Machine-cycle microarchitecture refinement *)
Print Assumptions microcycle_refines_step.
Print Assumptions microcycle_refines_steps.
Print Assumptions run_cycles_is_mc_time.

(* Verified compiler with ROM-image refinement *)
Print Assumptions compile_expr_correct.
Print Assumptions compile_stmt_correct.
Print Assumptions compiled_stmt_runs_on_machine.

(* PC-indexed simulation for arbitrary control-flow graphs *)
Print Assumptions pc_indexed_simulation.
Print Assumptions pc_indexed_reaches.

(* Compiled control flow: if/while refined into a ROM image on the machine *)
Print Assumptions cgen_correct.
Print Assumptions compiled_cstmt_runs_on_machine.
Print Assumptions cwhile_rule.

(* Fidelity closures *)
Print Assumptions decode_low_group_is_nop.
Print Assumptions system_reset_specification.
Print Assumptions system_reset_refines_cpu_reset.
Print Assumptions ram_read_main_undefined_convention.

(* Disassembler and program validator *)
Print Assumptions disassemble_encode_list.
Print Assumptions valid_program_encode_list.

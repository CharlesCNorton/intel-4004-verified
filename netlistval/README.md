# Netlist validation

Differential testing of the extracted machine-checked model against a
transistor-level simulation of the Intel 4004, using the netlist
captured from Intel's released mask artwork.

## The oracle

For the 4004's 35th anniversary Intel released the chip's schematics
and mask artwork for non-commercial use. Lajos Kintli captured a
transistor netlist from the mask layers, machine-compared it against a
netlist independently recognized from the redrawn schematic until the
two agreed (1807 transistors, 427 pullups), and validated the result by
simulating MCS-4 programs (the i400x analyzer, 4004.com). Peter Monta's
FPGA-netlist-tools redistributes that layout netlist as a plain text
file; this harness pins it by commit and fetches it at build time:

    https://raw.githubusercontent.com/pmonta/FPGA-netlist-tools/
      6bdbdf93db27e00356f0707dcc04fba3c5d2d865/masks/4004/
      lajos-4004-layout-netlist.txt

The netlist is a derivative of Intel's mask release (non-commercial
license) and is therefore fetched on demand, never committed to this
repository.

`sim4004.py` is an independent switch-level simulator over that
netlist, implementing the semantics documented for the i400x analyzer:
defined/pulled/floating high-low signal states plus undefined,
transistors as logic-level switches, pullups as weak drives, charge
retention on isolated groups with dominant-capacitance resolution, and
zero-propagation-delay relaxation. The built-in environment implements
the ROM side of the MCS-4 bus protocol (address latch at A1-A3, data at
M1/M2, bus turnaround at M2's end) and logs one line per machine cycle
of exactly what external hardware sees: the fetch address, the data-bus
nibbles the CPU drives at X1/X2/X3, and the CM-ROM/CM-RAM line states
per subcycle.

## The comparison

`gen_netlist.ml` (built against the extracted model, like the
differential harness) writes suite ROM images and the model's expected
bus trace for each: fetch addresses for every machine cycle (two-word
instructions and FIN's indirect fetch included), the accumulator on the
bus at X2 for WRM/WMP/WRR/WPM/WR0-3, the register pair at X2/X3 for
SRC, the operand for LDM, and the CM masks at A3 (the DCL line
selection), M2 (I/O designation), and X2 (SRC send). `compare.py`
checks every claimed field; any disagreement fails the run.

Suites: undefined opcodes, the full one-word ALU group over every
accumulator value and carry level, register-file operations with SRC
dumps, JCN over all sixteen conditions and flag settings (TEST driven
both ways), ISZ/JIN/FIN, page-boundary branches including a taken JCN
spanning addresses 4094-4095 (the page-wrap composition), fetch
wraparound at 4095, five nested calls and six returns through the
address ring (overflow discard and stale-row underflow, all visible in
the fetch trace), DCL over every accumulator value (the multi-line
CM-RAM sets asserted simultaneously on the pins), disarmed WPM, and
seeded random straight-line programs with periodic probe blocks.

## Running

    make netlistval

runs the three stages (requires OCaml with ocamlfind for the generator
and Python 3 for the simulation and comparison):

    make netlistval-gen     # build ROMs + expected traces from the model
    make netlistval-run     # simulate the netlist over every suite
    make netlistval-check   # compare and report

## Scope

This validates the CPU at its pins: instruction fetch and control flow,
the data-path values the chip exposes on the bus, and the CM line
behavior, against transistors traced from the production masks. It does
not cover 4002-side behavior (multi-line RAM reads remain
bench-hardware territory) or the analog quantities below the digital
abstraction.

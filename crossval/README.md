# Third-party cross-validation against Pyntel4004

The extracted, machine-checked model dumps vector sets (`dump_vectors.ml`,
built and run by `make crossval` from the repository root), and
`pyntel_crossval.py` replays them instruction by instruction on the
third-party Pyntel4004 emulator (PyPI `Pyntel4004`, v1.2), writing
`report.txt`.

Suites: the exhaustive 9,216-vector ALU set; JCN over all sixteen condition
codes with accumulator, carry, TEST, page-boundary, and wraparound samples;
ISZ; JUN, JMS, JIN, and FIN targets; subroutine stack discipline observed
through the return program counters; RAM main and status round trips over
all four banks; and the timing table and first-byte decode table (model-only
where Pyntel4004 has no counterpart, kept because the dump doubles as a
bench vector set for eventual validation against physical 4004 silicon).

Disagreements are classified by direction-checked predicates and adjudicated
against the MCS-4 data sheet.  The known Pyntel4004 defect classes: ADD
reduces overflowing sums by 14 rather than 16; DAC writes the constant 8
regardless of input; JCN's invert bit fails to invert the TEST term of the
condition, and taken JCN and ISZ branches load the raw address byte with no
page composition, missing the data sheet's page rule entirely (visible in
hardware/instructions/transfer_control.py); FIN reads its RAM array rather
than program ROM and drops the
current page base (visible in hardware/instructions/idx.py); and 12-bit
wraparound is unsupported, raising on program counters or return addresses
past 4094.  Its executer-loop convention (jms, jin, and bbl store the target
minus one for a post-incrementing fetch loop, while jun stores the target
directly) is compensated, not counted.  BBL past the stack's depth is
undefined by every MCS-4 document, so those rows are excluded rather than
scored.  Any disagreement outside these classes fails `make crossval` and
must be adjudicated before shipping.

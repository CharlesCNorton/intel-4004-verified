#!/usr/bin/env python3
"""Compare the machine-checked model's expected bus traces against the
transistor-netlist simulation traces.

Usage: compare.py <build_dir> <suite> [<suite> ...]

Per machine cycle the following are compared (an expected field of -1
makes no claim):

  addr   the 12-bit fetch address the CPU emitted during A1-A3
  x1..x3 the data-bus nibbles the CPU drove during X1/X2/X3
  cmA3   {cm_rom, cm_ram3..cm_ram0} during A3 (the DCL line selection)
  cmM2   the same mask during M2 (I/O designation)
  cmX2   the same mask during X2 (SRC address send)

Any disagreement is a finding; there are no adjudicated classes.
Exit status 0 iff every suite matches on every claimed field.
"""

import csv
import sys


def load(path):
    with open(path) as f:
        return [[int(x) for x in row] for row in csv.reader(f) if row]


def compare(build, suite):
    exp = load(f"{build}/{suite}.expected.csv")
    got = load(f"{build}/{suite}.trace.csv")
    n = min(len(exp), len(got))
    if len(exp) != len(got):
        print(f"  {suite}: row count expected {len(exp)} netlist {len(got)}"
              f" (comparing first {n})")
    bad = 0
    checked = 0
    for k in range(n):
        e = exp[k]
        g = got[k]
        # expected: cyc,addr,x1,x2,x3,cmA3,cmM2,cmX2
        # netlist:  cyc,addr,x1,x2,x3,cm0..cm7  (labels: internal
        #           subcycle i is netlist cm[i]; A3=3, M2=5, X2=7)
        fields = [
            ("addr", e[1], g[1]),
            ("x1", e[2], g[2]),
            ("x2", e[3], g[3]),
            ("x3", e[4], g[4]),
            ("cmA3", e[5], g[5 + 3]),
            ("cmM2", e[6], g[5 + 5]),
            ("cmX2", e[7], g[5 + 7]),
        ]
        for name, ev, gv in fields:
            if ev < 0:
                continue
            checked += 1
            if ev != gv:
                bad += 1
                if bad <= 10:
                    print(f"  {suite} cycle {e[0]}: {name} "
                          f"model={ev} netlist={gv}")
    verdict = "MATCH" if bad == 0 else f"{bad} MISMATCHES"
    print(f"{suite}: {checked} checks, {verdict}")
    return bad


def main():
    build = sys.argv[1]
    total = 0
    for suite in sys.argv[2:]:
        total += compare(build, suite)
    if total == 0:
        print("RESULT: the netlist simulation agrees with the model on "
              "every claimed field.")
    else:
        print(f"RESULT: {total} disagreements need investigation.")
    sys.exit(0 if total == 0 else 1)


if __name__ == "__main__":
    main()

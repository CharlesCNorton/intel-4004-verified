#!/usr/bin/env python3
"""Run the transistor-netlist simulation over every generated suite.

Usage: run_suites.py <netlist.txt> <build_dir> [jobs]

Reads <build_dir>/manifest.csv (suite,cycles,test) written by
gen_netlist, simulates each suite ROM on the netlist, and writes
<build_dir>/<suite>.trace.csv.  Suites run in parallel processes.
"""

import csv
import multiprocessing
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sim4004


def run_one(args):
    netlist, build, name, cycles, test = args
    t0 = time.time()
    sim = sim4004.Sim(netlist)
    sim.set_gate_states()
    env = sim4004.MCS4Env(sim, load_rom(f"{build}/{name}.hex"), test,
                          f"{build}/{name}.trace.csv")
    env.run(1200, cycles, pocpol=1)
    return f"{name}: {cycles} cycles in {time.time() - t0:.1f}s"


def load_rom(path):
    rom = []
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                rom.append(int(line, 16))
    return rom + [0] * (4096 - len(rom))


def main():
    netlist, build = sys.argv[1], sys.argv[2]
    jobs = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    with open(f"{build}/manifest.csv") as f:
        suites = [(netlist, build, r[0], int(r[1]), int(r[2]))
                  for r in csv.reader(f) if r]
    with multiprocessing.Pool(jobs) as pool:
        for line in pool.imap_unordered(run_one, suites):
            print(line, flush=True)


if __name__ == "__main__":
    main()

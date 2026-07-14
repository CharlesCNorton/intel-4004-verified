#!/usr/bin/env python3
"""Switch-level simulator for the Intel 4004 transistor netlist.

Netlist: Lajos Kintli's layout capture of Intel's released 4004 mask
artwork (the file distributed in Peter Monta's FPGA-netlist-tools as
masks/4004/lajos-4004-layout-netlist.txt, exported from the i400x
analyzer).  Component lines:

    T,x,y,name,gate,c1,c2,flag     enhancement FET (logic-level switch)
    R,x,y,name,t1,t2,,flag         resistor (pullup to VDD, or pad
                                   protector when a terminal is GND)
    C,...                          bootstrap capacitor (folded into the
                                   pullups by the capture; ignored, as
                                   in Kintli's own simulator)

Simulation semantics follow the i400x analyzer readme:
  - signal states: defined/pulled/floating high/low, plus undefined
  - a transistor conducts iff its gate is at logic high; undefined
    gates read as off
  - a channel group touching GND through transistors is pulled low;
    touching VDD is pulled high; both at once is undefined
  - a group driven by nothing but a pullup resistor floats high...
    (is pulled high weakly)
  - an isolated group keeps its charge; when floating nodes of both
    levels merge, the level with the dominant total capacitance wins
    (capacitance estimated by transistor-terminal count)
  - zero propagation delay: relax to a fixpoint after each clock edge
  - external outputs change and are sampled at CLK2 falling edges; the
    environment answers at the following CLK1 rising edge

The built-in environment implements the MCS-4 ROM side of the bus
protocol over a 4096-byte image and writes one trace line per machine
cycle:

    cycle,fetch_addr,x1,x2,x3,cm0,...,cm7

where x1/x2/x3 are the data-bus nibbles the CPU drove at the X1/X2/X3
CLK2 falls (-1 when any bit floats), and cmK packs
{cm_rom,cm_ram3,cm_ram2,cm_ram1,cm_ram0} sampled at subcycle K's CLK2
fall (subcycles 0..7 = A1,A2,A3,M1,M2,X1,X2,X3).
"""

import argparse
import sys

# node states
UX, DL, DH, PL, PH, FL, FH = range(7)
HIGHS = (DH, PH, FH)
LOWS = (DL, PL, FL)


def level(s):
    if s in HIGHS:
        return 1
    if s in LOWS:
        return 0
    return None


class Sim:
    def __init__(self, netlist_path):
        self.node_ids = {}
        self.names = []
        self.state = []
        self.cap = []
        self.gates_of = []    # node -> list of transistor ids gated by it
        self.chans_of = []    # node -> list of transistor ids with a channel terminal here
        self.pullup = []      # node -> bool (has VDD resistor)
        self.t_gate = []
        self.t_c1 = []
        self.t_c2 = []
        self.t_on = []
        self.driven = {}      # node id -> forced level (external pins)

        def nid(name):
            i = self.node_ids.get(name)
            if i is None:
                i = len(self.names)
                self.node_ids[name] = i
                self.names.append(name)
                self.state.append(UX)
                self.cap.append(0)
                self.gates_of.append([])
                self.chans_of.append([])
                self.pullup.append(False)
            return i

        self.GND = nid('GND')
        self.VDD = nid('VDD')

        with open(netlist_path) as f:
            for line in f:
                parts = line.strip().split(',')
                if not parts or not parts[0]:
                    continue
                kind = parts[0]
                if kind == 'T':
                    g, c1, c2 = nid(parts[4]), nid(parts[5]), nid(parts[6])
                    t = len(self.t_gate)
                    self.t_gate.append(g)
                    self.t_c1.append(c1)
                    self.t_c2.append(c2)
                    self.t_on.append(False)
                    self.gates_of[g].append(t)
                    self.chans_of[c1].append(t)
                    self.chans_of[c2].append(t)
                    self.cap[g] += 1
                    self.cap[c1] += 1
                    self.cap[c2] += 1
                elif kind == 'R':
                    a, b = nid(parts[4]), nid(parts[5])
                    if a == self.VDD:
                        self.pullup[b] = True
                    elif b == self.VDD:
                        self.pullup[a] = True
                    # GND-side protector resistors are inert: the pads
                    # they guard are always externally driven
                elif kind == 'C':
                    continue

        # power-on: every node starts as stored low charge (as in the
        # visual6502 engine); undefined appears only through contention
        # or bus release, so the bring-up relaxation cannot strand
        # regions behind undefined gates
        for n in range(len(self.names)):
            self.state[n] = FL
        self.state[self.GND] = DL
        self.state[self.VDD] = DH
        nn = len(self.names)
        self.mark = bytearray(nn)
        self.inq = bytearray(nn)
        self.work = []
        self.oscillations = 0
        self.evals = 0
        for n in range(nn):
            if n != self.GND and n != self.VDD:
                self.inq[n] = 1
                self.work.append(n)

    def enqueue(self, n):
        if not self.inq[n]:
            self.inq[n] = 1
            self.work.append(n)

    def drive(self, name, lvl):
        n = self.node_ids[name]
        self.driven[n] = lvl
        s = DH if lvl else DL
        if self.state[n] != s:
            self.state[n] = s
            on = lvl == 1
            for t in self.gates_of[n]:
                if self.t_on[t] != on:
                    self.t_on[t] = on
                    self.enqueue(self.t_c1[t])
                    self.enqueue(self.t_c2[t])
            self.enqueue(n)

    def release(self, name):
        n = self.node_ids[name]
        if n in self.driven:
            del self.driven[n]
            self.enqueue(n)

    def read(self, name):
        return level(self.state[self.node_ids[name]])

    def relax(self, budget=20000):
        """Process the worklist to a fixpoint (or until the eval budget
        runs out, which indicates an oscillating subnetwork; the state
        is then left as-is, as in the i400x analyzer)."""
        state = self.state
        cap = self.cap
        chans_of = self.chans_of
        gates_of = self.gates_of
        t_on = self.t_on
        t_c1 = self.t_c1
        t_c2 = self.t_c2
        pullup = self.pullup
        driven = self.driven
        GND = self.GND
        VDD = self.VDD
        inq = self.inq
        work = self.work
        evals = 0

        while work:
            seed = work.pop()
            inq[seed] = 0
            if seed == GND or seed == VDD:
                continue
            evals += 1
            if evals > budget:
                # oscillating subnetwork: stop here but keep the
                # remaining worklist so progress resumes on the next
                # clock edge (the seed just popped is requeued)
                self.oscillations += 1
                if not inq[seed]:
                    inq[seed] = 1
                    work.append(seed)
                break
            # one BFS collecting the whole verdict
            group = [seed]
            mark = self.mark
            mark[seed] = 1
            hit_gnd = hit_vdd = has_pull = False
            drv0 = drv1 = False
            chi = clo = 0
            i = 0
            while i < len(group):
                n = group[i]
                i += 1
                if n in driven:
                    if driven[n]:
                        drv1 = True
                    else:
                        drv0 = True
                if pullup[n]:
                    has_pull = True
                s = state[n]
                if s in HIGHS:
                    chi += cap[n]
                elif s in LOWS:
                    clo += cap[n]
                for t in chans_of[n]:
                    if not t_on[t]:
                        continue
                    a = t_c1[t]
                    b = t_c2[t]
                    m = b if a == n else a
                    if m == GND:
                        hit_gnd = True
                    elif m == VDD:
                        hit_vdd = True
                    elif not mark[m]:
                        mark[m] = 1
                        group.append(m)
            for n in group:
                mark[n] = 0
            # resolve
            if drv0 and drv1:
                s = UX
            elif drv1:
                s = DH
            elif drv0:
                s = DL
            elif hit_gnd and hit_vdd:
                s = UX
            elif hit_gnd:
                s = PL
            elif hit_vdd:
                s = PH
            elif has_pull:
                s = PH
            elif chi == 0 and clo == 0:
                s = UX
            elif chi > clo:
                s = FH
            elif clo > chi:
                s = FL
            else:
                s = UX
            on = s in HIGHS
            for n in group:
                if n in driven:
                    continue
                if state[n] != s:
                    state[n] = s
                    for t in gates_of[n]:
                        if t_on[t] != on:
                            t_on[t] = on
                            for m in (t_c1[t], t_c2[t]):
                                if not inq[m]:
                                    inq[m] = 1
                                    work.append(m)
        self.evals += evals

    def set_gate_states(self):
        for t in range(len(self.t_gate)):
            self.t_on[t] = level(self.state[self.t_gate[t]]) == 1


class MCS4Env:
    """The ROM side of the MCS-4 bus, plus clocking and tracing."""

    SUB = ('A1', 'A2', 'A3', 'M1', 'M2', 'X1', 'X2', 'X3')

    def __init__(self, sim, rom, test, tracefile):
        self.sim = sim
        self.rom = rom
        self.trace = open(tracefile, 'w')
        self.sub = 0          # subcycle index, resynced by SYNC
        self.addr = 0
        self.cycle = 0
        self.started = False
        self.have_addr = False
        self.tracing = False
        self.xbus = {}
        self.cm = [0] * 8
        self.bus_drive = None  # nibble currently driven, or None
        sim.drive('CLK1', 0)
        sim.drive('CLK2', 0)
        sim.drive('TEST_PAD', test)
        sim.drive('POC', 1)
        sim.relax()

    def bus_read(self):
        bits = [self.sim.read(f'D{k}') for k in range(4)]
        if any(b is None for b in bits):
            return -1
        return bits[0] | bits[1] << 1 | bits[2] << 2 | bits[3] << 3

    def bus_set(self, nib):
        for k in range(4):
            self.sim.drive(f'D{k}', (nib >> k) & 1)
        self.bus_drive = nib

    def bus_release(self):
        if self.bus_drive is not None:
            for k in range(4):
                self.sim.release(f'D{k}')
            self.bus_drive = None

    def clock_phase(self):
        """One CLK1 pulse then one CLK2 pulse (one subcycle).

        Alignment (established against the netlist's own timing chain):
        the chip's internal subcycle K occupies my label K's window, its
        bus value settles at the preceding CLK2 fall and is stable
        through K's CLK1 phase (the bus precharges during CLK2 high), so
        sampling happens after the CLK1 rise; the environment presents
        ROM data across windows 4 and 5 (internal M1/M2) and returns the
        bus at the fall that ends window 5."""
        s = self.sim
        e0 = s.evals
        s.drive('CLK1', 1)
        s.relax()
        # stable mid-window point: sample here
        self.env_clk1up()
        s.drive('CLK1', 0)
        s.relax()
        self.env_mid()
        s.drive('CLK2', 1)
        s.relax()
        s.drive('CLK2', 0)
        s.relax()
        self.env_clk2fall()
        self.phase_evals = s.evals - e0

    def env_clk1up(self):
        """Sample the bus and CM lines mid-window: internal subcycle
        values are stable across their CLK1 phase."""
        s = self.sim
        sub = self.sub
        cmmask = 0
        for i, name in enumerate(('CMRAM0', 'CMRAM1', 'CMRAM2', 'CMRAM3', 'CMROM')):
            v = s.read(name)
            cmmask |= (1 if v == 1 else 0) << i
        self.cm[sub] = cmmask
        if sub == 0:
            # internal X3 of the current machine cycle: the cycle is
            # complete; emit iff its address phases were traced
            self.xbus[7] = self.bus_read()
            if self.have_addr:
                self.emit()
            self.have_addr = False
        elif sub == 1:
            self.addr = (self.addr & 0xff0) | max(self.bus_read(), 0)
        elif sub == 2:
            self.addr = (self.addr & 0xf0f) | max(self.bus_read(), 0) << 4
        elif sub == 3:
            self.addr = (self.addr & 0x0ff) | max(self.bus_read(), 0) << 8
            self.have_addr = self.tracing
        elif sub == 6:
            self.xbus[5] = self.bus_read()
        elif sub == 7:
            self.xbus[6] = self.bus_read()

    def env_mid(self):
        # data for internal M1/M2 is presented across my windows 4 and 5
        # (the chip latches OPR/OPA at its M1/M2); a 4001 held in reset
        # drives nothing, so the CPU decodes NOPs until release and its
        # single/double-cycle state cannot be mid-instruction then
        sub = self.sub
        if sub == 4:
            self.bus_set(self.rom[self.addr] >> 4 if self.tracing else 0)
        elif sub == 5:
            self.bus_set(self.rom[self.addr] & 15 if self.tracing else 0)

    def env_clk2fall(self):
        sub = self.sub
        if sub == 5:
            # bus turnaround: the fall ending window 5 starts the chip's
            # X1 drive
            self.bus_release()
        sync = self.sim.read('SYNC')
        if sync == 1:
            self.sub = 0
            self.started = True
        else:
            self.sub = min(self.sub + 1, 7)

    def emit(self):
        f = self.trace
        f.write('%d,%d,%d,%d,%d,%s\n' % (
            self.cycle, self.addr,
            self.xbus.get(5, -1), self.xbus.get(6, -1), self.xbus.get(7, -1),
            ','.join(str(v) for v in self.cm)))
        self.xbus = {}
        self.cycle += 1

    def run(self, resetclks, maxcycles, pocpol=1, verbose=False):
        import time
        t0 = time.time()
        # power-on clear
        self.sim.drive('POC', pocpol)
        for i in range(resetclks):
            self.clock_phase()
            if verbose and (i + 1) % 200 == 0:
                print('reset phase %d evals %d osc %d %.1fs' %
                      (i + 1, self.sim.evals, self.sim.oscillations,
                       time.time() - t0), file=sys.stderr)
        # release just after A1 of a (reset) cycle: that cycle's M1/M2
        # arrive with the pin clear, so it executes instruction 0
        # seamlessly (the internal POC lags the pin by a few clocks and
        # expires during A2-A3); tracing starts with this cycle
        guard = 0
        while self.sub != 1 and guard < 64:
            self.clock_phase()
            guard += 1
        self.sim.drive('POC', 1 - pocpol)
        self.have_addr = False
        self.tracing = True
        self.cycle = 0
        # failsafe phase bound so a dead chip cannot spin forever
        maxphases = (maxcycles + 4) * 8 * 4
        phases = 0
        while self.cycle < maxcycles and phases < maxphases:
            self.clock_phase()
            phases += 1
        if verbose:
            print('done: %d cycles, evals %d, osc %d, %.1fs' %
                  (self.cycle, self.sim.evals, self.sim.oscillations,
                   time.time() - t0), file=sys.stderr)
        self.trace.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--netlist', required=True)
    ap.add_argument('--rom', required=True)
    ap.add_argument('--trace', required=True)
    ap.add_argument('--cycles', type=int, default=100)
    ap.add_argument('--resetclks', type=int, default=1200)
    ap.add_argument('--test', type=int, default=1)
    ap.add_argument('--pocpol', type=int, default=1,
                    help='logic level that asserts POC during reset')
    args = ap.parse_args()

    rom = []
    with open(args.rom) as f:
        for line in f:
            line = line.strip()
            if line:
                rom.append(int(line, 16))
    rom += [0] * (4096 - len(rom))

    sim = Sim(args.netlist)
    sim.set_gate_states()
    env = MCS4Env(sim, rom, args.test, args.trace)
    env.run(args.resetclks, args.cycles, pocpol=args.pocpol)


if __name__ == '__main__':
    main()

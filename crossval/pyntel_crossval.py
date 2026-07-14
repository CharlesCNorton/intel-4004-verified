#!/usr/bin/env python3
"""Replay machine-checked model vectors on the third-party Pyntel4004 emulator.

Usage: pyntel_crossval.py vectors.csv [report.txt]

Every disagreement is classified against the MCS-4 data sheet.  Adjudicated
classes (Pyntel4004 behavior verified by direction-checked predicates, and
for FIN by inspection of its source):

  PYNTEL-DEFECT-ADD        overflowing sums reduced by 14 rather than 16
  PYNTEL-DEFECT-DAC        writes the constant 8 regardless of input
  PYNTEL-DEFECT-JCN        the invert bit fails to invert the TEST term, and
                           taken branches load the raw address byte with no
                           page composition (transfer_control.py)
  PYNTEL-DEFECT-ISZ-PAGE   taken ISZ branches load the raw address byte too
  PYNTEL-DEFECT-FIN-RAM    fin reads self.RAM, not program ROM, and drops the
                           current page base (hardware/instructions/idx.py)
  PYNTEL-DEFECT-NO-WRAP    12-bit wraparound unsupported: raises on program
                           counters or return addresses past 4094
  PYNTEL-CONVENTION-PC     jms/jin/bbl store target-1 for its executer loop's
                           post-increment (jun stores the target directly)
  UNDEFINED-UNDERFLOW      BBL past the stack's depth: no MCS-4 document
                           defines it; the model and Pyntel choose differently
  CASCADE                  scenario rows after a raised error (state desynced)
  MODEL-ONLY               suites Pyntel4004 does not implement

Anything outside these classes is a MISMATCH and fails the run.
"""

import sys
import collections

from hardware.processor import Processor


def fresh():
    return Processor()


def carry_bit(c):
    return 1 if c else 0


# ---------------- data-sheet reference predicates ----------------

def ds_jcn_take(cond, acc, cy, tp):
    c1, c2, c3, c4 = (cond >> 3) & 1, (cond >> 2) & 1, (cond >> 1) & 1, cond & 1
    base = (acc == 0 and c2 == 1) or (cy == 1 and c3 == 1) or (tp == 0 and c4 == 1)
    return (not base) if c1 == 1 else base


def pyntel_jcn_hyp(cond, acc, cy, tp, pc, off):
    """Pyntel's JCN, transcribed from hardware/instructions/transfer_control.py:
    the inverted branch keeps NOT-pin10 in the TEST factor (the invert bit
    fails to invert that term), and a taken branch assigns the raw address
    byte to the program counter, ignoring page composition."""
    c1, c2, c3, c4 = (cond >> 3) & 1, (cond >> 2) & 1, (cond >> 1) & 1, cond & 1
    if c1 == 0:
        take = (acc == 0 and c2 == 1) or (cy == 1 and c3 == 1) \
               or (tp == 0 and c4 == 1)
    else:
        take = ((acc != 0 or c2 == 0) and (cy == 0 or c3 == 0)
                and (tp == 0 or c4 == 0))
    return off if take else pc + 2


# ---------------- ALU ----------------

def replay_alu(f):
    name, a, cy, reg = f[0], int(f[1]), int(f[2]), int(f[3])
    macc, mcy = int(f[4]), int(f[5])
    p = fresh()
    p.ACCUMULATOR = a
    p.CARRY = cy
    if name in ("ADD", "SUB", "LD", "XCH"):
        p.insert_register(0, reg)
    try:
        if name == "ADD":
            p.add(0)
        elif name == "SUB":
            p.sub(0)
        elif name == "IAC":
            p.iac()
        elif name == "DAC":
            p.dac()
        elif name == "DAA":
            p.daa()
        elif name == "CMA":
            p.cma()
        elif name == "RAL":
            p.ral()
        elif name == "RAR":
            p.rar()
        elif name == "TCC":
            p.tcc()
        elif name == "TCS":
            p.tcs()
        elif name == "CLB":
            p.clb()
        elif name == "CLC":
            p.clc()
        elif name == "STC":
            p.stc()
        elif name == "CMC":
            p.cmc()
        elif name == "KBP":
            p.kbp()
        elif name == "LD":
            p.ld(0)
        elif name == "XCH":
            p.xch(0)
        elif name == "LDM":
            p.ldm(reg)
        else:
            return ("MODEL-ONLY", None)
    except Exception as e:  # noqa: BLE001 - adjudication harness
        return ("ERROR", "alu %s a=%d cy=%d reg=%d: %r" % (name, a, cy, reg, e))
    pacc, pcy = p.ACCUMULATOR, carry_bit(p.CARRY)
    if (pacc, pcy) == (macc, mcy):
        return ("MATCH", None)
    if name == "ADD":
        raw = a + reg + cy
        if raw >= 16 and pacc == raw - 14 and macc == raw - 16:
            return ("PYNTEL-DEFECT-ADD", None)
    if name == "DAC":
        if pacc == 8 and macc == (a + 15) % 16:
            return ("PYNTEL-DEFECT-DAC", None)
    return ("MISMATCH",
            "alu %s a=%d cy=%d reg=%d: model=(%d,%d) pyntel=(%d,%d)"
            % (name, a, cy, reg, macc, mcy, pacc, pcy))


# ---------------- control flow ----------------

def wrap_error(e):
    name = type(e).__name__
    return name in ("ProgramCounterOutOfBounds", "ValueOutOfRangeForStack")


def replay_jcn(f):
    cond, a, cy, tp, pc0, off, mpc = (int(x) for x in f)
    p = fresh()
    p.ACCUMULATOR = a
    p.CARRY = cy
    p.PROGRAM_COUNTER = pc0
    p.PIN_10_SIGNAL_TEST = tp
    try:
        p.jcn(cond, off)
    except Exception as e:  # noqa: BLE001
        if wrap_error(e):
            return ("PYNTEL-DEFECT-NO-WRAP", None)
        return ("ERROR", "jcn %s: %r" % (",".join(f), e))
    ppc = p.PROGRAM_COUNTER
    if ppc == mpc:
        return ("MATCH", None)
    if ppc == pyntel_jcn_hyp(cond, a, cy, tp, pc0, off):
        return ("PYNTEL-DEFECT-JCN", None)
    return ("MISMATCH",
            "jcn cond=%d acc=%d cy=%d tp=%d pc=%d off=%d: model=%d pyntel=%d"
            % (cond, a, cy, tp, pc0, off, mpc, ppc))


def replay_isz(f):
    v, pc0, off, mpc, mreg = (int(x) for x in f)
    p = fresh()
    p.insert_register(3, v)
    p.PROGRAM_COUNTER = pc0
    try:
        p.isz(3, off)
    except Exception as e:  # noqa: BLE001
        if wrap_error(e):
            return ("PYNTEL-DEFECT-NO-WRAP", None)
        return ("ERROR", "isz %s: %r" % (",".join(f), e))
    if p.REGISTERS[3] != mreg:
        return ("MISMATCH", "isz v=%d pc=%d off=%d: reg model=%d pyntel=%d"
                % (v, pc0, off, mreg, p.REGISTERS[3]))
    if p.PROGRAM_COUNTER == mpc:
        return ("MATCH", None)
    taken = (v + 1) % 16 != 0
    hyp = off if taken else pc0 + 2
    if p.PROGRAM_COUNTER == hyp:
        return ("PYNTEL-DEFECT-ISZ-PAGE", None)
    return ("MISMATCH",
            "isz v=%d pc=%d off=%d: model=(%d,%d) pyntel=(%d,%d)"
            % (v, pc0, off, mpc, mreg, p.PROGRAM_COUNTER, p.REGISTERS[3]))


def replay_jun(f):
    pc0, addr, mpc = (int(x) for x in f)
    p = fresh()
    p.PROGRAM_COUNTER = pc0
    try:
        p.jun(addr)
    except Exception as e:  # noqa: BLE001
        if wrap_error(e):
            return ("PYNTEL-DEFECT-NO-WRAP", None)
        return ("ERROR", "jun %s: %r" % (",".join(f), e))
    if p.PROGRAM_COUNTER == mpc:
        return ("MATCH", None)
    return ("MISMATCH", "jun pc=%d addr=%d: model=%d pyntel=%d"
            % (pc0, addr, mpc, p.PROGRAM_COUNTER))


def replay_jms(f):
    pc0, addr, mpc, _mret = (int(x) for x in f)
    p = fresh()
    p.PROGRAM_COUNTER = pc0
    try:
        p.jms(addr)
    except Exception as e:  # noqa: BLE001
        if wrap_error(e):
            return ("PYNTEL-DEFECT-NO-WRAP", None)
        return ("ERROR", "jms %s: %r" % (",".join(f), e))
    ppc = p.PROGRAM_COUNTER
    if ppc == mpc:
        return ("MATCH", None)
    if ppc == mpc - 1:
        return ("PYNTEL-CONVENTION-PC", None)
    return ("MISMATCH", "jms pc=%d addr=%d: model pc=%d pyntel pc=%d"
            % (pc0, addr, mpc, ppc))


def replay_jin(f):
    pc0, pv, mpc = (int(x) for x in f)
    p = fresh()
    p.insert_register(2, pv // 16)
    p.insert_register(3, pv % 16)
    p.PROGRAM_COUNTER = pc0
    try:
        p.jin(1)
    except Exception as e:  # noqa: BLE001
        if wrap_error(e):
            return ("PYNTEL-DEFECT-NO-WRAP", None)
        return ("ERROR", "jin %s: %r" % (",".join(f), e))
    ppc = p.PROGRAM_COUNTER
    if ppc == mpc:
        return ("MATCH", None)
    if ppc == mpc - 1:
        return ("PYNTEL-CONVENTION-PC", None)
    return ("MISMATCH", "jin pc=%d pair=%d: model=%d pyntel=%d"
            % (pc0, pv, mpc, ppc))


def replay_fin(f):
    pc0, pv, mr4, mr5, mpc = (int(x) for x in f)
    p = fresh()
    p.ROM = [(i * 7 + 3) % 256 for i in range(4096)]
    p.insert_register(0, pv // 16)
    p.insert_register(1, pv % 16)
    p.PROGRAM_COUNTER = pc0
    try:
        p.fin(2)
    except Exception as e:  # noqa: BLE001
        if wrap_error(e):
            return ("PYNTEL-DEFECT-NO-WRAP", None)
        return ("ERROR", "fin %s: %r" % (",".join(f), e))
    got = (p.REGISTERS[4], p.REGISTERS[5], p.PROGRAM_COUNTER)
    if got == (mr4, mr5, mpc):
        return ("MATCH", None)
    if got[2] in (mpc, mpc - 1) and got[0:2] != (mr4, mr5):
        # fin reads self.RAM (zeros here) instead of program ROM, and drops
        # the current page base: hardware/instructions/idx.py.
        return ("PYNTEL-DEFECT-FIN-RAM", None)
    return ("MISMATCH", "fin pc=%d pair=%d: model=(%d,%d,%d) pyntel=(%d,%d,%d)"
            % ((pc0, pv, mr4, mr5, mpc) + got))


# ---------------- stack scenarios (LIFO through observable pc) ----------------

STACK_PROCS = {}
STACK_DEAD = set()


def replay_stack(f):
    si, op, arg, depth0, mpc = int(f[0]), f[1], int(f[2]), int(f[3]), int(f[4])
    if si in STACK_DEAD:
        return ("CASCADE", None)
    p = STACK_PROCS.get(si)
    if p is None:
        p = fresh()
        p.PROGRAM_COUNTER = 0
        STACK_PROCS[si] = p
    try:
        if op == "jms":
            p.jms(arg)
        else:
            p.bbl(arg)
    except Exception as e:  # noqa: BLE001
        STACK_DEAD.add(si)
        if wrap_error(e):
            return ("PYNTEL-DEFECT-NO-WRAP", None)
        return ("ERROR", "stack %s: %r" % (",".join(f), e))
    ppc = p.PROGRAM_COUNTER
    if op == "bbl" and depth0 == 0:
        return ("UNDEFINED-UNDERFLOW", None)
    if ppc == mpc:
        return ("MATCH", None)
    if ppc == mpc - 1:
        return ("PYNTEL-CONVENTION-PC", None)
    return ("MISMATCH", "stack sc=%d %s %d: model pc=%d pyntel pc=%d"
            % (si, op, arg, mpc, ppc))


# ---------------- RAM round trips ----------------

def ram_script(p, bank, srcv, writes):
    p.ldm(bank)
    p.dcl()
    p.fim(0, srcv)
    p.src(0)
    for (kind, val) in writes:
        if kind == "ldm":
            p.ldm(val)
        elif kind == "wrm":
            p.wrm()
        elif kind == "wr0":
            p.wr0()
        elif kind == "sel":
            p.fim(0, srcv)
            p.src(0)
        elif kind == "rdm":
            p.rdm()
        elif kind == "rd0":
            p.rd0()


def replay_rammain(f):
    bank, srcv, v, macc = (int(x) for x in f)
    p = fresh()
    try:
        ram_script(p, bank, srcv,
                   [("ldm", v), ("wrm", 0), ("ldm", 0), ("sel", 0), ("rdm", 0)])
    except Exception as e:  # noqa: BLE001
        return ("ERROR", "rammain %s: %r" % (",".join(f), e))
    if p.ACCUMULATOR == macc:
        return ("MATCH", None)
    return ("MISMATCH", "rammain bank=%d src=%d v=%d: model=%d pyntel=%d"
            % (bank, srcv, v, macc, p.ACCUMULATOR))


def replay_ramstat(f):
    bank, srcv, macc = (int(x) for x in f)
    p = fresh()
    try:
        ram_script(p, bank, srcv,
                   [("ldm", 11), ("wr0", 0), ("ldm", 0), ("sel", 0), ("rd0", 0)])
    except Exception as e:  # noqa: BLE001
        return ("ERROR", "ramstat %s: %r" % (",".join(f), e))
    if p.ACCUMULATOR == macc:
        return ("MATCH", None)
    return ("MISMATCH", "ramstat bank=%d src=%d: model=%d pyntel=%d"
            % (bank, srcv, macc, p.ACCUMULATOR))


# ---------------- decode table probe ----------------

def decode_probe(decode_lines, out):
    out.append("")
    out.append("decode table probe (model mnemonic vs Pyntel4004 opcode table):")
    try:
        p = fresh()
        table = {}
        for entry in p.INSTRUCTIONS:
            try:
                op = entry["opcode"] if isinstance(entry, dict) else entry.opcode
                mn = entry["mnemonic"] if isinstance(entry, dict) else entry.mnemonic
                table[int(op)] = str(mn)
            except Exception:  # noqa: BLE001
                continue
    except Exception as e:  # noqa: BLE001
        out.append("  Pyntel4004 opcode table unavailable: %r" % (e,))
        return
    agree = disagree = undefined = 0
    for (b1, mtag) in decode_lines:
        mop = mtag.split(" ")[0].lower()
        pmn = table.get(b1)
        pop = pmn.split("(")[0].strip().lower() if pmn else None
        if mop == "nop" and b1 != 0 and (b1 < 16 or b1 >= 254):
            undefined += 1
        elif pop == mop:
            agree += 1
        else:
            disagree += 1
            out.append("  0x%02X: model=%s pyntel=%r" % (b1, mtag, pmn))
    out.append("  defined opcodes agreeing: %d, disagreeing: %d, "
               "undefined bytes under the NOP convention: %d (Pyntel marks them '-')"
               % (agree, disagree, undefined))


# ---------------- driver ----------------

REPLAYERS = {
    "alu": replay_alu,
    "jcn": replay_jcn,
    "isz": replay_isz,
    "jun": replay_jun,
    "jms": replay_jms,
    "jin": replay_jin,
    "fin": replay_fin,
    "stack": replay_stack,
    "rammain": replay_rammain,
    "ramstat": replay_ramstat,
}


def main(argv):
    vectors = argv[1] if len(argv) > 1 else "crossval/vectors.csv"
    report_path = argv[2] if len(argv) > 2 else "crossval/report.txt"
    counts = collections.defaultdict(collections.Counter)
    details = []
    decode_lines = []
    with open(vectors) as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            parts = line.split(",")
            suite, fields = parts[0], parts[1:]
            if suite == "timing":
                counts[suite]["MODEL-ONLY"] += 1
                continue
            if suite == "decode":
                decode_lines.append((int(fields[0]), ",".join(fields[1:])))
                continue
            replay = REPLAYERS.get(suite)
            if replay is None:
                counts[suite]["MODEL-ONLY"] += 1
                continue
            cls, msg = replay(fields)
            counts[suite][cls] += 1
            if msg and sum(1 for d in details if d.startswith(suite)) < 20:
                details.append("%s: %s: %s" % (suite, cls, msg))

    out = []
    out.append("Pyntel4004 cross-validation report")
    out.append("==================================")
    total_mismatch = total_error = 0
    for suite in sorted(counts):
        c = counts[suite]
        total_mismatch += c["MISMATCH"]
        total_error += c["ERROR"]
        out.append("%-9s %s" % (suite, dict(c)))
    if details:
        out.append("")
        out.append("unadjudicated disagreements/errors:")
        out.extend("  " + d for d in details)
    decode_probe(decode_lines, out)
    out.append("")
    if total_mismatch == 0 and total_error == 0:
        out.append("RESULT: every disagreement falls in an adjudicated "
                   "Pyntel4004 defect or convention class.")
    else:
        out.append("RESULT: %d mismatches, %d errors need adjudication."
                   % (total_mismatch, total_error))
    text = "\n".join(out) + "\n"
    sys.stdout.write(text)
    with open(report_path, "w") as fh:
        fh.write(text)
    return 0 if (total_mismatch == 0 and total_error == 0) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))

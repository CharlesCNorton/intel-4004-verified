# Intel 4004 formal model: build, verify, and differential test.
#
#   make          compile the development (machine, behavior, verification)
#   make check    verify every headline theorem is axiom-free (fails otherwise)
#   make run      extract to OCaml and run the differential test harness
#   make clean    remove build artifacts
#
# Coq sources live under theories/; audit.v carries both the assumption audit
# and the OCaml extraction, so `make check` also refreshes the extracted model
# as a side effect.
#
# Requires the Rocq Prover 9.0 or later (the sources use the Stdlib
# namespace) and, for the harness, OCaml with ocamlfind.

COQC   ?= coqc
QFLAGS  = -Q theories FourK

VOFILES = theories/machine.vo theories/behavior.vo theories/verification.vo \
          theories/control.vo theories/fidelity.vo

.PHONY: all check run crossval clean \
        netlistval netlistval-gen netlistval-run netlistval-check

all: $(VOFILES)

theories/machine.vo: theories/machine.v
	$(COQC) $(QFLAGS) theories/machine.v

theories/behavior.vo: theories/behavior.v theories/machine.vo
	$(COQC) $(QFLAGS) theories/behavior.v

theories/verification.vo: theories/verification.v theories/behavior.vo theories/machine.vo
	$(COQC) $(QFLAGS) theories/verification.v

theories/control.vo: theories/control.v theories/verification.vo theories/behavior.vo theories/machine.vo
	$(COQC) $(QFLAGS) theories/control.v

theories/fidelity.vo: theories/fidelity.v theories/verification.vo theories/behavior.vo theories/machine.vo
	$(COQC) $(QFLAGS) theories/fidelity.v

check: $(VOFILES) theories/audit.v
	@$(COQC) $(QFLAGS) theories/audit.v > check.out 2>&1 || { cat check.out; rm -f check.out; exit 1; }
	@cat check.out
	@if grep -q "Axioms" check.out; then echo "FAIL: an assumption base is nonempty"; rm -f check.out; exit 1; fi
	@n=$$(grep -c "Closed under the global context" check.out); rm -f check.out; \
	 echo "OK: $$n assumption bases closed under the global context"

difftest: $(VOFILES) theories/audit.v driver.ml
	$(COQC) $(QFLAGS) theories/audit.v
	ocamlfind ocamlopt -w -a-31 intel4004_model.mli intel4004_model.ml driver.ml -o difftest

run: difftest
	./difftest

crossval/dump_vectors: $(VOFILES) theories/audit.v crossval/dump_vectors.ml
	$(COQC) $(QFLAGS) theories/audit.v
	ocamlfind ocamlopt -w -a-31 -I . intel4004_model.mli intel4004_model.ml \
	  crossval/dump_vectors.ml -o crossval/dump_vectors

# Dump model vectors and replay them on the third-party Pyntel4004 emulator
# (pip install Pyntel4004).  Known Pyntel defects are adjudicated; any other
# disagreement fails the target.
crossval: crossval/dump_vectors
	./crossval/dump_vectors > crossval/vectors.csv
	python3 crossval/pyntel_crossval.py crossval/vectors.csv crossval/report.txt

# Differential test against a transistor-level simulation of the 4004
# netlist captured from Intel's released mask artwork (see
# netlistval/README.md).  The netlist is fetched pinned by commit; it is
# licensed non-commercially and is not part of this repository.
NETLIST_URL = https://raw.githubusercontent.com/pmonta/FPGA-netlist-tools/6bdbdf93db27e00356f0707dcc04fba3c5d2d865/masks/4004/lajos-4004-layout-netlist.txt

netlistval/lajos-4004-layout-netlist.txt:
	curl -L -o $@ $(NETLIST_URL)

netlistval/gen_netlist: $(VOFILES) theories/audit.v netlistval/gen_netlist.ml
	$(COQC) $(QFLAGS) theories/audit.v
	ocamlfind ocamlopt -w -a-31 -I . intel4004_model.mli intel4004_model.ml \
	  netlistval/gen_netlist.ml -o netlistval/gen_netlist

netlistval-gen: netlistval/gen_netlist
	./netlistval/gen_netlist

netlistval-run: netlistval/lajos-4004-layout-netlist.txt
	python3 netlistval/run_suites.py netlistval/lajos-4004-layout-netlist.txt netlistval/build

netlistval-check:
	python3 netlistval/compare.py netlistval/build \
	  undef alu regs branch_t0 branch_t1 loops pagewrap fetchwrap ring \
	  dcl wpm rand1 rand2 rand3

netlistval: netlistval-gen netlistval-run netlistval-check

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux \
	      intel4004_model.ml intel4004_model.mli *.cmi *.cmx *.cmo *.o difftest check.out \
	      .*.aux .lia.cache .nia.cache \
	      crossval/dump_vectors crossval/*.cmi crossval/*.cmx crossval/*.o \
	      crossval/vectors.csv crossval/report.txt \
	      netlistval/gen_netlist netlistval/*.cmi netlistval/*.cmx netlistval/*.o
	rm -rf netlistval/build

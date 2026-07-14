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

.PHONY: all check run crossval clean

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

clean:
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob theories/.*.aux \
	      intel4004_model.ml intel4004_model.mli *.cmi *.cmx *.cmo *.o difftest check.out \
	      .*.aux .lia.cache .nia.cache \
	      crossval/dump_vectors crossval/*.cmi crossval/*.cmx crossval/*.o \
	      crossval/vectors.csv crossval/report.txt

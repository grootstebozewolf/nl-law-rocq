# Build with: make   (requires Rocq 9.x: `rocq makefile`; falls back to coq_makefile)
ROCQMAKEFILE := $(shell command -v rocq >/dev/null 2>&1 && echo "rocq makefile" || echo coq_makefile)

all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _CoqProject
	$(ROCQMAKEFILE) -f _CoqProject -o Makefile.rocq

check-admits:
	@! grep -nE '\b(Admitted|admit|Axiom|Parameter|Conjecture)\b' theories/*.v && echo "no Admitted/admit/Axiom/Parameter"

clean:
	@if [ -f Makefile.rocq ]; then $(MAKE) -f Makefile.rocq clean; fi
	rm -f Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d

.PHONY: all clean check-admits

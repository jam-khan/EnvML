COQPROJECT := _CoqProject
COQMK      := Makefile.coq

# ---- build ---------------------------------------------------------------
all: $(COQMK)
	@$(MAKE) --no-print-directory -f $(COQMK)

# (re)generate the coq build makefile whenever _CoqProject changes
$(COQMK): $(COQPROJECT)
	coq_makefile -f $(COQPROJECT) -o $(COQMK)

# ---- cleaning ------------------------------------------------------------
clean:
	rm -f *.vo *.vok *.vos *.glob
	rm -f .*.aux *.aux
	rm -f .*.d *.d
	rm -f .lia.cache
	rm -f $(COQMK) $(COQMK).conf .$(COQMK).d
	rm -f Makefile.coq.bak CoqMakefile CoqMakefile.conf
	rm -f Makefile.conf .Makefile.d
	rm -f *~

.PHONY: all clean

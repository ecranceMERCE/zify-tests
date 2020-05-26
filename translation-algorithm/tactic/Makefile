ifeq "$(COQBIN)" ""
  COQBIN=/Users/cloudyhug/Desktop/coq/bin/
endif

all: Makefile.coq

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

tests: all
	@$(MAKE) -C tests -s clean
	@$(MAKE) -C tests -s all

-include Makefile.coq
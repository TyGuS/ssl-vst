all: default doc
default: Makefile.coq
	make -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -C ./examples clean
	$(MAKE) -C ./benchmarks clean
	make -f Makefile.coq clean
	rm -f Makefile.coq

install: Makefile.coq
	make -f Makefile.coq install

examples: default
	$(MAKE) -C ./examples

benchmarks: default
	$(MAKE) -C ./benchmarks


Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: coq clean install doc examples

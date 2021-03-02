default: all

clightfiles = $(patsubst %.c, %.v, $(wildcard *.c))
verif_files = $(wildcard verif_*.v)
compiled_verif_files = $(patsubst %.v, %.vo, $(verif_files))

common.v: common.c
	clightgen -normalize common.c

%.v: %.c common.c
	clightgen -normalize common.c $<

common.vo: common.v
	coqc common.v

common_predicates.vo: common_predicates.v common.vo
	coqc -Q ../../lib SSL_VST $<

verif_%.vo: verif_%.v %.v common_predicates.vo common.vo
	coqc -Q ../../lib SSL_VST $*.v
	coqc -Q ../../lib SSL_VST verif_$*.v

all: $(compiled_verif_files)

clean:
	rm -f $(clightfiles)
	rm -f ./*.vo
	rm -f ./*.vos
	rm -f ./*.vok
	rm -f ./*.glob

.PHONY: all default quick install clean

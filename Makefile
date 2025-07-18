.PHONY: all clean

all: Makefile.coq build

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

build: Makefile.coq
	$(MAKE) -f Makefile.coq
	rm -f Makefile.coq Makefile.coq.conf

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

all: joho.tar.gz joho-aRjL4EK6.tar.gz

SOURCES=engine.mli engine.ml strategy.mli strategy.ml main.ml
ALLSOURCES=$(SOURCES) Makefile
DIST= init run README

run: $(SOURCES)
	ocamlopt -o $@ $^

joho-aRjL4EK6.tar.gz: $(DIST) $(ALLSOURCES)
	mkdir src
	cp init README $(ALLSOURCES) src
	tar -cvzf $@ $(DIST) src
	rm -rf src

joho.tar.gz: init run
	tar -cvzf $@ $^

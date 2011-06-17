all: joho.tar.gz

run: engine.mli engine.ml strategy.mli strategy.ml main.ml
	ocamlopt -o $@ $^


joho.tar.gz: init run
	tar -cvzf $@ init run

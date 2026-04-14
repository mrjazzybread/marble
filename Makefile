.PHONY: all clean bench doc

all:
	@ dune build

clean:
	@ git clean -fdX

bench:
	@ dune exec extracted/main.exe -- --sort 16000

doc:
	@ make -C doc

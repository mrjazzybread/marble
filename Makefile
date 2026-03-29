.PHONY: all clean bench

all:
	@ dune build

clean:
	@ git clean -fdX

bench:
	@ dune exec extracted/main.exe -- --sort 16000

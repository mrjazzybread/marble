.PHONY: all clean

all:
	@ dune build

clean:
	@ git clean -fdX

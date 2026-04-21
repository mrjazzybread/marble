.PHONY: all view clean debug

# The file documentation.md is generated from documentation.md.pre.

# The preprocessor recognizes the syntax (array.v:Lemma foobar),
# uses grep to search for "Lemma foobar" in the file theories/array.v
# and produces a link to this particular line in the repository.

all: documentation.md

view: all
	@ open -a "/Applications/Visual Studio Code.app" documentation.md

clean:
	@ rm -f documentation.md
	@ git clean -fdX

debug:
	./preprocess.sh documentation.md.pre

%.md: %.md.pre $(wildcard ../theories/*.v) preprocess.sh
	@ rm -f $@
	./preprocess.sh $< > $@
	@ chmod u-w $@

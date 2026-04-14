.PHONY: all view clean

# The file documentation.md is generated from documentation.md.pre.

# The preprocessor recognizes the syntax (array.v:Lemma foobar),
# uses grep to search for "Lemma foobar" in the file src/array.v
# and produces a link to this particular line in the repository.

all: documentation.md

view: all
	open -a "/Applications/Visual Studio Code.app" documentation.md

clean:
	git clean -fdX

%.md: %.md.pre $(wildcard ../src/*.v)
	./preprocess.sh $< > $@

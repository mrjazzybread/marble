.PHONY: all
all:
	@ dune build

.PHONY: clean
clean:
	@ git clean -fdX

.PHONY: reinstall
reinstall:
	@ dune uninstall
	@ dune build -p $(ROCQLIB) @install
	@ dune install

# ------------------------------------------------------------------------------

# Benchmark. (OCaml extracted code.)

.PHONY: bench
bench:
	@ dune exec benchmark/main.exe -- --sort 16000

# ------------------------------------------------------------------------------

# Documentation.

.PHONY: doc
doc:
	@ make -C doc

# ------------------------------------------------------------------------------

# [make headache] updates the headers.

HEADACHE := headache
HEADER   := header.txt
FIND     := $(shell if command -v gfind >/dev/null ; then echo gfind ; else echo find ; fi)

.PHONY: headache
headache:
	@ for f in $(shell $(FIND) src -type f -regex ".*\.v") ; do \
	  $(HEADACHE) -c headache.config -h $(HEADER) $$f ; \
	done

# ------------------------------------------------------------------------------

# The version number is automatically set to the current date,
# unless DATE is defined on the command line.
# An example of the date format is 20241208.
DATE      := $(shell /bin/date +%Y%m%d)

# The date with dashes is used in the .opam description file.
DATEDASH  := $(shell /bin/date +%Y-%m-%d)

# The date, with slahes, is used in [make release] to search CHANGES.md.
# An example is 2024/12/08.
DATESLASH := $(shell /bin/date +%Y/%m/%d)

# The project's name.
THIS     := marble

# ------------------------------------------------------------------------------

# The repository's URL (https).
REPO     := https://gitlab.inria.fr/fpottier/($THIS)

# The archive URL (https).
ARCHIVE  := $(REPO)/-/archive/$(DATE)/archive.tar.gz

# Options for opam publish.
OPAM_PUBLISH_OPTIONS := \
  --repo coq/opam-coq-archive \
  --packages-directory released/packages \

# The package name.
ROCQLIB  := rocq-$(THIS)

.PHONY: release
release:
# Check the current package description.
	@ opam lint
# Make sure that the documentation can be built.
	@ make doc
# Make sure the current version can be compiled and installed.
	@ make clean
	@ dune build -p $(ROCQLIB) @install
# Check if this is the main branch.
	@ if [ "$$(git symbolic-ref --short HEAD)" != "main" ] ; then \
	  echo "Error: this is not the main branch." ; \
	  git branch ; \
	  exit 1 ; \
	fi
# Make sure a CHANGES entry with the current date seems to exist.
	@ if ! grep $(DATESLASH) CHANGES.md ; then \
	    echo "Error: CHANGES.md has no entry with date $(DATESLASH)." ; \
	    exit 1 ; \
	  fi
# Check if everything has been committed.
	@ if [ -n "$$(git status --porcelain)" ] ; then \
	    echo "Error: there remain uncommitted changes." ; \
	    git status ; \
	    exit 1 ; \
	  fi
# Create a git tag.
	@ git tag -a $(DATE) -m "Release $(DATE)."
# Push the new tag to gitlab.inria.fr.
	@ git push --tags
# Patch $(ROCQLIB).opam.
# We replace the string DATEDASH with $(DATEDASH).
# We replace the string development with $(DATE).
	@ cat $(ROCQLIB).opam \
	  | sed -e 's/DATEDASH/$(DATEDASH)/g' \
	  | sed -e 's/development/$(DATE)/g' \
	  > $(ROCQLIB).patched.opam
# Publish an opam description.
	@ opam publish -v $(DATE) $(OPAM_PUBLISH_OPTIONS) \
	    $(ROCQLIB).patched.opam $(ARCHIVE)
	@ rm $(ROCQLIB).patched.opam

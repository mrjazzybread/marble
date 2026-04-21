#!/bin/bash
set -euo pipefail

# Usage: ./preprocess.sh <filename>

# This script preprocesses the file <filename>. It interprets my custom syntax
# for links and replaces it with correct Markdown links. The result is printed
# on stdout. There can be at most one custom link per line.

REPO=https://gitlab.inria.fr/fpottier/marble/-/blob/main/theories/
SRC=../theories

echo "<!--- THIS FILE HAS BEEN GENERATED based on documentation.md.pre -->"

while IFS= read -r line; do
  # Identify the custom link syntax: a (short) file name (which must end in .v) and a pattern,
  # separated with a colon, surrounded with parentheses. An example is
  # (array.v:Lemma wp_make)
  if [[ $line =~ ^(.*)\(([^:]*\.v):([^\)]*)\)(.*)$ ]]; then
    leading="${BASH_REMATCH[1]}"
    file="${BASH_REMATCH[2]}"
    pattern="${BASH_REMATCH[3]}"
    trailing="${BASH_REMATCH[4]}"
    # Search for this pattern in this file, and extract the line
    # number of the match. If there are multiple matches, keep only
    # the first match. Construct a URL for this particular file and
    # line number in the repository.
    number=$(grep -n "${pattern}" "${SRC}"/"${file}" | head -n 1 | cut -f 1 -d ':')
    URL="${REPO}${file}?ref_type=heads#L${number}"
    # Print the transformed line, where the trailing and leading material
    # is preserved and a link is printed in the middle.
    echo "${leading}(${URL})${trailing}"
  else
    echo "$line"
  fi
done < "$1"

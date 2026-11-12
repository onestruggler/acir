#!/bin/sh
# Regenerate the Agda code of qcert.tex, as ../../vqupit does: run
# `agda --latex --only-scope-checking' on each literate file here, which
# resolves every name of its code blocks against the library and colours
# it by kind, and writes ../latex/pldi/lagda/<name>.tex, which qcert.tex
# inputs.  Run in WSL from anywhere:  sh pldi/lagda/make.sh [file ...]
# Agda runs from the repository root, where the .agda-lib file is, and
# under the machine-wide Agda lock (one Agda job at a time); the imported
# developments are type-checked first if their interfaces are stale.
set -e
cd "$(dirname "$0")/../.."
AGDA=${AGDA:-$HOME/.local/bin/agda}
[ $# -gt 0 ] || set -- pldi/lagda/*.lagda.tex
exec 9>"$HOME/.agda-job.lock"
flock 9
for f in "$@"; do
  echo "== $f"
  timeout 3600 "$AGDA" +RTS -M6G -RTS --latex --only-scope-checking \
    --latex-dir=pldi/latex "$f"
done

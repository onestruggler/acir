#!/usr/bin/env bash
# Build Lean modules in WSL (dependencies included):
#   ./check.sh QCert/Foo.lean [QCert/Bar.lean ...]     ./check.sh   (whole library)
# At most three builds run at once on this machine (lock files in $HOME).
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
got=
for i in 1 2 3; do
  exec {fd}>"$HOME/.qcert-build-$i.lock"
  if flock -n "$fd"; then got=1; break; fi
  exec {fd}>&-
done
if [ -z "$got" ]; then
  exec {fd}>"$HOME/.qcert-build-$((RANDOM % 3 + 1)).lock"
  flock "$fd"
fi
if [ $# -eq 0 ]; then
  /usr/bin/timeout 7200 lake build
  exit $?
fi
mods=()
for f in "$@"; do m="${f%.lean}"; mods+=("${m//\//.}"); done
/usr/bin/timeout 3600 lake build "${mods[@]}"

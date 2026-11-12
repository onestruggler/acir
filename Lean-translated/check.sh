#!/usr/bin/env bash
# Build Lean modules in WSL (dependencies included), writing their .oleans:
#   ./check.sh EquaCert/Foo.lean [EquaCert/Bar.lean ...]     ./check.sh   (whole library)
# Builds are serialized by a lock file: several agents share this workspace,
# and two Lake processes must not write the same .olean at once.  To check a
# single file without writing anything (no lock needed), use tools/lean1.sh.
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
exec {fd}>"$HOME/.equacert-build.lock"
flock "$fd"
if [ $# -eq 0 ]; then
  /usr/bin/timeout 14400 lake build
  exit $?
fi
mods=()
for f in "$@"; do m="${f%.lean}"; mods+=("${m//\//.}"); done
/usr/bin/timeout 14400 lake build "${mods[@]}"

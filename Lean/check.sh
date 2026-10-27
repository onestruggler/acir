#!/usr/bin/env bash
# Build Lean modules in WSL (dependencies included):
#   ./check.sh QCert/Foo.lean [QCert/Bar.lean ...]     ./check.sh   (whole library)
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
if [ $# -eq 0 ]; then
  exec /usr/bin/timeout 7200 lake build
fi
mods=()
for f in "$@"; do m="${f%.lean}"; mods+=("${m//\//.}"); done
exec /usr/bin/timeout 3600 lake build "${mods[@]}"

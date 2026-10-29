#!/usr/bin/env bash
# Build Lean modules in WSL (dependencies included):
#   ./check.sh QCert/Foo.lean [QCert/Bar.lean ...]     ./check.sh   (whole library)
# Serialize builds: concurrent Lake processes can replace the same .olean
# while another process is importing it. Lake still schedules its own jobs.
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
exec {fd}>"$HOME/.qcert-build-1.lock"
flock "$fd"
if [ $# -eq 0 ]; then
  /usr/bin/timeout 7200 lake build
  exit $?
fi
mods=()
for f in "$@"; do m="${f%.lean}"; mods+=("${m//\//.}"); done
/usr/bin/timeout 14400 lake build "${mods[@]}"

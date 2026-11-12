#!/usr/bin/env bash
# Check one Lean file without writing its .olean (its imports must be built):
#   tools/lean1.sh EquaCert/Foo.lean [--profile]
# Safe to run beside other checks and beside ./check.sh.
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
f="$1"; shift
if [ "$1" = "--profile" ]; then
  exec /usr/bin/timeout 3600 lake env lean --profile -Dprofiler=true -Dprofiler.threshold=500 "$f"
fi
exec /usr/bin/timeout 3600 lake env lean "$f"

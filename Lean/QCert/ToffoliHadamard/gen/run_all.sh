#!/usr/bin/env bash
# Rerun every search and regenerate the four modules (Micro, MacroTable,
# Families, RoundTable).  Run in Linux (WSL here) from this folder:
#   ./run_all.sh            searches, export to data/, emitters
#   ./run_all.sh emit       emitters only, from the recorded data/
set -e
cd "$(dirname "$0")"
export PYTHONHASHSEED=0
if [ "$1" != "emit" ]; then
  gcc -O2 -w -o bfs bfs.c
  gcc -O2 -w -DBITS=7 -o bfs7 bfs.c
  python3 s01_involutions.py
  python3 s02_enum.py
  python3 s03_relators.py
  python3 sat2.py 10 200000 8 4,5,6
  python3 s05_coxeter.py 6 3000000 2
  python3 s06_x34.py 1500000 10
  python3 s07_store.py
  python3 s08_assemble.py
  python3 s09_mfacts.py
  python3 s10_routes.py
  python3 s11_lrs.py
  python3 s12_export.py
fi
python3 emit_micro.py
python3 emit_macro.py
python3 emit_fam.py
python3 emit_round.py

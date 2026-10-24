#!/bin/bash
# codes.sh CHECKOUT TREE OUT : the generators of each macro letter of TREE
# (Four or Five) as their codes, one letter a line in the order of
# TREE/Letters' Mac -- the table reflect4_engine.py writes into
# Four/Reflect.agda (scratchpad/four/codes_Four.txt).  CHECKOUT is a copy
# of the repository in which TREE/Reflect is checked (any version: only
# tableM, codeG and flat are used); Agda normalises the codes through its
# interaction mode.  Four takes seconds; Five, whose letters run to 2,226
# generators, about eleven minutes, most of it printing.
#   AGDA_DIR=... bash codes.sh ~/acir-work Four codes_Four.txt
AGDA=${AGDA:-agda}
cd "$1" || exit 1
T=$2
OUT=$(realpath -m "$3")
mkdir -p Par5Batch
M=Par5Batch/Codes$T.agda
cat > $M <<AG
module Par5Batch.Codes$T where
open import Data.List.Base using (List ; map ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Examples.Groups.Clifford+CS.$T.Reflect using (tableM ; codeG ; flat)
codes : List (List ℕ)
codes = map (λ x → map codeG (flat (x ∷ []))) tableM
AG
$AGDA $M > /dev/null 2>&1 || { echo "codes.sh: $M does not check"; $AGDA $M | tail -5; exit 1; }
F=$(pwd)/$M
printf 'IOTCM "%s" NonInteractive Indirect (Cmd_load "%s" [])\nIOTCM "%s" NonInteractive Indirect (Cmd_compute_toplevel DefaultCompute "codes")\n' "$F" "$F" "$F" \
  | $AGDA +RTS -M6G -RTS --interaction > /tmp/codes$T.raw 2>&1
python3 - /tmp/codes$T.raw "$OUT" <<'PY'
import re, sys
raw = open(sys.argv[1], encoding='utf-8').read()
m = re.search(r'agda2-info-action "\*Normal Form\*" "(.*?)" nil\)', raw, re.S)
if not m:
    sys.exit('codes.sh: no normal form in the output:\n' + raw[-2000:])
t = m.group(1).replace('\\n', ' ')
# (a ∷ b ∷ []) ∷ (c ∷ []) ∷ [] : each letter's list is parenthesised
items, depth, cur = [], 0, ''
for ch in t:
    if ch == '(':
        depth += 1
        if depth == 1:
            cur = ''
            continue
    if ch == ')':
        depth -= 1
        if depth == 0:
            items.append(cur)
            continue
    if depth >= 1:
        cur += ch
rows = [[int(x) for x in re.findall(r'\d+', it)] for it in items]
open(sys.argv[2], 'w').write('\n'.join(' '.join(map(str, r)) for r in rows) + '\n')
print(len(rows), 'letters,', sum(map(len, rows)), 'codes')
PY
rm -f $M

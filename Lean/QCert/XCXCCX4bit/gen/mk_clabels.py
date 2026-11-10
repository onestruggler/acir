"""Writes CLabels.lean: the data of the labels of the controlled A8.

Port of the Agda's gen/mk_clabels.py, writing Lean instead of Agda.  The data
comes from the Agda's gen/clabels.py (imported, as the Agda's generator
imports it): the 105 perfect matchings of the Gray positions (pair lists and
tables), the five base matchings (one per union type with mu0) with the
three-wire circuits Q that place mu0 on them (the Agda generator's
`BASE_PG`) and Coxeter words for Q (`base_words`), and for every matching its
base type and a Coxeter word of the centraliser of mu0 that conjugates the
base matching to it.  The numbering of the labels is the Agda's (later
modules name labels by number), and this script checks that against the
checked-in CLabels.agda.  Like the Agda's, it is untrusted: Lean checks what
it writes.

Run with WSL's python3 from this folder: `python3 mk_clabels.py`.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent                       # Lean/QCert/XCXCCX4bit
REPO = LEAN.parents[2]                   # the repository root
AGDA = REPO / 'Examples' / 'Groups' / 'XCXCCX-4bit'
AGEN = AGDA / 'gen'
OUT = LEAN / 'CLabels.lean'

sys.path.insert(0, str(AGEN))
from clabels import PMS, plist, BASE_IDX, ORBIT, word_of, act_t, MU0, compose, inverse  # noqa: E402
import mk_clabels as ag  # noqa: E402  (the Agda generator, for BASE_PG and base_words)


def letter(d):
    return 's' + '₀₁₂₃₄₅₆'[d]


def wrap(items, indent, first, last, start):
    """`first`, the items separated by ', ', `last`, the first line starting at
    column `start`, wrapped at 100 columns with continuation lines indented by
    `indent`."""
    out, line = [], first
    for k, it in enumerate(items):
        piece = it + (', ' if k + 1 < len(items) else last)
        col = indent if out else start
        if col + len(line) + len(piece) > 100 and line.strip(' [('):
            out.append(line.rstrip())
            line = ''
        line += piece
    out.append(line)
    return ('\n' + ' ' * indent).join(out)


def cw(w, col):
    """A Coxeter word starting at column `col`."""
    if not w:
        return '1'
    first = 'FreeMonoid.ofList ['
    return wrap([letter(d) for d in w], col + len(first), first, ']', col)


def fins(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def pg_letter(l):
    if l[0] == 'X':
        return 'PG.Xₚ %d' % l[1]
    if l[0] == 'CX':
        return 'PG.CXₚ %d %d' % (l[1], l[2])
    return 'PG.CCXₚ %d %d %d' % (l[1], l[2], l[3])


def pg_list(w):
    return '[' + ', '.join(pg_letter(l) for l in w) + ']'


def table(name, typ, doc, rows):
    """A list-valued definition, one row per line."""
    o = ['/-- %s -/' % doc, 'def %s : %s :=' % (name, typ)]
    for i, r in enumerate(rows):
        lead = '  [' if i == 0 else '   '
        tail = ']' if i + 1 == len(rows) else ','
        o.append(lead + r + tail)
    return o


def agda_check():
    """The labels are numbered as in the checked-in CLabels.agda."""
    src = (AGDA / 'CLabels.agda').read_text(encoding='utf-8')
    block = src.split('tblT =', 1)[1].split('frmT', 1)[0]
    digits = {c: i for i, c in enumerate('₀₁₂₃₄₅₆₇')}
    rows = re.findall(r'\(([^()]*)∷ \[\]\)', block)
    tabs = [tuple(digits[x.strip()] for x in r.split('∷') if x.strip()) for r in rows]
    assert tabs == [tuple(m) for m in PMS], 'tblT differs from CLabels.agda'
    base = src.split('baseT =', 1)[1].split('\n', 1)[0]
    assert [int(x) for x in re.findall(r'# (\d+)', base)] == BASE_IDX


def main():
    agda_check()
    QW = ag.base_words()
    from clabels import match_of
    for k, v in enumerate(QW):
        assert match_of(v) == PMS[BASE_IDX[k]], k
    for m, (k, c) in zip(PMS, ORBIT):
        nu = PMS[BASE_IDX[k]]
        a = act_t(c)
        assert compose(compose(a, nu), inverse(a)) == m
        assert all(a[MU0[x]] == MU0[a[x]] for x in range(8))
    frm = []
    for m in PMS:
        w = word_of(tuple(plist(m)))
        assert match_of(w) == m
        frm.append(w)
    o = [HDR]
    o += table('pairsT', 'List (List (Fin 8))', 'The 105 matchings as lists of their pairs.',
               [fins(plist(m)) for m in PMS])
    o.append('')
    o += table('tblT', 'List (List (Fin 8))', 'The 105 matchings as tables.',
               [fins(m) for m in PMS])
    o.append('')
    o += table('frmT', 'List (CW 8)', 'A Coxeter word placing `μ₀` on each matching (its frame).',
               [cw(w, 3) for w in frm])
    o.append('')
    o.append('/-- The base matchings: one per union type with `μ₀`. -/')
    o.append('def baseT : List (Fin 105) := ' + fins(BASE_IDX))
    o.append('')
    o.append('/-- The circuits that place `μ₀` on the base matchings, as placed letters on')
    o.append('wires 0, 1, 2 … -/')
    o.append('def baseQ : Fin 5 → List PG')
    for k, w in enumerate(ag.BASE_PG):
        o.append('  | %d => %s' % (k, pg_list(w)))
    o.append('  | ⟨k + 5, h⟩ => absurd h (by omega)')
    o.append('')
    o.append('/-- … and as Coxeter words. -/')
    o.append('def baseW : Fin 5 → CW 8')
    for k, v in enumerate(QW):
        lead = '  | %d => ' % k
        o.append(lead + cw(v, len(lead)))
    o.append('  | ⟨k + 5, h⟩ => absurd h (by omega)')
    o.append('')
    o.append('/-- The base type of each matching … -/')
    o.append('def orbKT : List (Fin 5) :=')
    o.append('  ' + wrap([str(k) for k, _ in ORBIT], 3, '[', ']', 2))
    o.append('')
    o += table('orbCT', 'List (CW 8)',
               '… and a word of the centraliser of `μ₀` conjugating the base matching to it.',
               [cw(c, 3) for _, c in ORBIT])
    o.append('')
    o.append('end QCert.XCXCCX4bit.CLabels')
    OUT.write_text('\n'.join(o) + '\n', encoding='utf-8', newline='\n')
    print('wrote', OUT)


HDR = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Data of the labels of the controlled A₈

Translation of `CLabels.agda`.  The labels are the 105 perfect matchings of
the eight Gray positions of the lower wires (`pairsT`, `tblT`).  Five of them
(`baseT`) represent the five orbits of the centraliser of
`μ₀ = (0 1)(2 3)(4 5)(6 7)`: `μ₀` itself and the matchings whose union with
`μ₀` has cycles of lengths 2+2, 2+1+1, 3+1 and 4 (in pairs); each is `μ₀`
placed by a short three-wire circuit (`baseQ`, as placed letters, and
`baseW`, as a Coxeter word with the same function).  Every matching is a
base matching conjugated by a word of the centraliser (`orbKT`, `orbCT`).

Generated by `gen/mk_clabels.py` (the port of the Agda's, from the Agda's
`gen/clabels.py`).

**Deviation from the Agda.**  The tables are lists (the Agda's `Vec`s), read
by `CRel`'s lookups; a Coxeter word is `FreeMonoid.ofList` of its letters
(the Agda's `[ s₁ ]ʷ • [ s₂ ]ʷ • …`).
-/
import QCert.XCXCCX4bit.Placed
import QCert.XCXCCX4bit.PFrames

namespace QCert.XCXCCX4bit.CLabels

open Placed (PG)
open PFrames (SG CW)

/-! The generators of `S₈`. -/

def s₀ : SG 8 := ⟨0, by decide⟩
def s₁ : SG 8 := ⟨1, by decide⟩
def s₂ : SG 8 := ⟨2, by decide⟩
def s₃ : SG 8 := ⟨3, by decide⟩
def s₄ : SG 8 := ⟨4, by decide⟩
def s₅ : SG 8 := ⟨5, by decide⟩
def s₆ : SG 8 := ⟨6, by decide⟩
'''

if __name__ == '__main__':
    main()

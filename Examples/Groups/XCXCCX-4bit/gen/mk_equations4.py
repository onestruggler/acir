"""Writes Equations4.agda: the four-wire equations of pg_results.json as
PlacedEngine derivations.

A derivation of pg_search.py is a list of steps, each with the
linearisation `lin` of the current word it acts on (the same word up to
letters on disjoint wires).  Each step becomes `perm lin` (when lin is
not the current list) followed by

  narrow (triple, i, j, new)   narrow i (j - i) new
  rule7 (perm p, fwd, i)       rw i (r7at p0 p1 p2 p3)
  rule7 (perm p, bwd, i)       rw i (sym⁼ (r7at p0 p1 p2 p3))

and a final `perm rhs` when the last word is the right side only up to
interchange.  Letters: ["X", t], ["CX", c, t], ["CCX", a, b, t] with
a > b, read as Xᵖ t, CXᵖ c t, CCXᵖ b a t (PlacedEngine's controls are
increasing).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(HERE), 'Equations4.agda')

W = ['₀', '₁', '₂', '₃']


def letter(j):
    k = j[0]
    if k == 'X':
        return 'Xᵖ ' + W[j[1]]
    if k == 'CX':
        return 'CXᵖ ' + W[j[1]] + ' ' + W[j[2]]
    if k == 'CCX':
        a, b, t = j[1], j[2], j[3]
        lo, hi = min(a, b), max(a, b)
        return 'CCXᵖ ' + W[lo] + ' ' + W[hi] + ' ' + W[t]
    raise ValueError(j)


def norm(j):
    if j[0] == 'CCX':
        return ('CCX', min(j[1], j[2]), max(j[1], j[2]), j[3])
    return tuple(j)


def agda_list(w, indent):
    if not w:
        return '[]'
    items = [letter(j) for j in w]
    # wrap long lists
    out, line = [], ''
    for it in items:
        piece = it + ' ∷ '
        if len(line) + len(piece) > 76 and line:
            out.append(line)
            line = ''
        line += piece
    line += '[]'
    out.append(line)
    if len(out) == 1:
        return '(' + out[0] + ')'
    return '(' + ('\n' + ' ' * (indent + 1)).join(out) + ')'


R7L = [('CCX', 2, 3, 1), ('CX', 1, 0), ('CCX', 2, 3, 1)]
R7R = [('CCX', 2, 3, 0), ('CX', 1, 0)]


def r7_side(p, side):
    out = []
    for j in side:
        if j[0] == 'CX':
            out.append(('CX', p[j[1]], p[j[2]]))
        else:
            a, b = p[j[1]], p[j[2]]
            out.append(('CCX', min(a, b), max(a, b), p[j[3]]))
    return out


def steps_of(t):
    """The PlacedEngine steps, and a replay on normalised letter tuples."""
    cur = [norm(j) for j in t['lhs']]
    rhs = [norm(j) for j in t['rhs']]
    out = []
    for st in t['steps']:
        lin = [norm(j) for j in st['lin']]
        if lin != cur:
            out.append(('perm', st['lin']))
            cur = lin
        if st['kind'] == 'narrow':
            i, j = st['i'], st['j']
            new = [norm(x) for x in st['new']]
            out.append(('narrow', i, j - i, st['new']))
            cur = cur[:i] + new + cur[j:]
        elif st['kind'] == 'rule7':
            p, i = st['perm'], st['i']
            if st['dir'] == 'fwd':
                assert cur[i:i + 3] == r7_side(p, R7L), (t['name'], cur[i:i + 3], r7_side(p, R7L))
                cur = cur[:i] + r7_side(p, R7R) + cur[i + 3:]
            else:
                assert cur[i:i + 2] == r7_side(p, R7R), (t['name'], cur[i:i + 2], r7_side(p, R7R))
                cur = cur[:i] + r7_side(p, R7L) + cur[i + 2:]
            out.append(('rule7', p, st['dir'], i))
        else:
            raise ValueError(st['kind'])
    if cur != rhs:
        out.append(('perm', t['rhs']))
    return out


def emit_step(s, indent):
    if s[0] == 'perm':
        return 'perm ' + agda_list(s[1], indent + 5)
    if s[0] == 'narrow':
        _, i, k, new = s
        return 'narrow %d %d %s' % (i, k, agda_list(new, indent + 7 + len(str(i)) + len(str(k)) + 2))
    _, p, d, i = s
    r = 'r7at %s %s %s %s' % tuple(W[x] for x in p)
    if d == 'fwd':
        return 'rw %d (%s)' % (i, r)
    return 'rw %d (sym⁼ (%s))' % (i, r)


def emit(name, comment, t):
    st = steps_of(t)
    lines = []
    for c in comment:
        lines.append('-- ' + c if c else '--')
    lines.append(name + ' : Eqnᵖ')
    lines.append(name + ' = derive')
    lines.append('  ' + agda_list(t['lhs'], 2))
    lines.append('  ' + agda_list(t['rhs'], 2))
    body = []
    for k, s in enumerate(st):
        lead = '  (' if k == 0 else '   '
        body.append(lead + emit_step(s, 3) + ' ∷')
    body.append('   [])')
    lines.extend(body)
    lines.append('  Eq.refl')
    return '\n'.join(lines)


NAMES = {
    'E1': ('eq8⁼', [
        "Equation (8): the CNOT from wire 1 onto wire 2 conjugates the",
        "Toffoli from wires 3, 2 onto wire 0 into its product with the",
        "Toffoli from wires 3, 1 onto wire 0."]),
    'E2': ('E2⁼', ["Two Toffolis with the same controls commute."]),
    'E3': ('E3⁼', ["Two Toffolis with the same target and a common control commute."]),
    'E4': ('E4⁼', ["A Toffoli and a CNOT with the same target commute."]),
    'E5': ('E5⁼', ["A Toffoli commutes with a CNOT from one of its controls onto a",
                   "wire it does not touch."]),
    'E6a': ('E6a⁼', ["Toffolis that act on disjoint sets of states commute:",
                     "CCX_{3,2̄→1} against CCX_{3,2→0}."]),
    'E6b': ('E6b⁼', ["CCX_{2̄,1̄→3} against CCX_{3,2→0}."]),
    'E6c': ('E6c⁼', ["CCX_{3̄,2̄→1} against CCX_{3,2→0}."]),
    'E6d': ('E6d⁼', ["CCX_{3̄,1→2} against CCX_{3,2→0}."]),
    'E6e': ('E6e⁼', ["CCX_{3̄,2→1} against CCX_{3,2→0}."]),
    'E7': ('E7⁼', ["The commutator of CCX_{3,2→1} and CCX_{3,1→0} is CCX_{3,2→0}",
                   "(the controlled Steinberg relation)."]),
    'E8': ('E8⁼', ["A Toffoli and a CNOT onto its target from the fourth wire",
                   "commute."]),
}

HDR = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- Equations on four wires, among them the paper's equation (8)
--
-- Each is a derivation of PlacedEngine whose steps are rule (7) under a
-- relabelling of the wires and three-wire steps justified by
-- completeness on three wires, found by gen/pg_search.py
-- (gen/pg_results.json) and written out by gen/mk_equations4.py.  A
-- letter CCX_{a,b→t} is the Toffoli with controls a, b and target t; a
-- bar marks a control that is negated (X on both sides of it).  Wire 0
-- is the bottom wire, and words are in diagram order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Equations4 where

open import Data.List.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Placed using (PG ; Xᵖ ; CXᵖ ; CCXᵖ)
open import Examples.Groups.XCXCCX-4bit.PlacedEngine
'''


def main():
    d = json.load(open(os.path.join(HERE, 'pg_results.json'), encoding='utf-8'))
    order = ['E2', 'E4', 'E8', 'E5', 'E6a', 'E6e', 'E6d', 'E6b', 'E6c', 'E7', 'E3', 'E1']
    tg = {t['name']: t for t in d['targets']}
    parts = [HDR]
    for n in order:
        nm, cm = NAMES[n]
        parts.append(emit(nm, cm, tg[n]))
    with open(OUT, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n\n'.join(parts) + '\n')
    print('wrote', OUT)


if __name__ == '__main__':
    main()

"""Writes CLabels.agda: the data of the labels of the controlled A8.

The 105 perfect matchings of the Gray positions (pair lists and tables),
the five base matchings (one per union type with mu0) with the
three-wire circuits Q that place mu0 on them and Coxeter words for Q,
and for every matching its base type and a Coxeter word of the
centraliser of mu0 that conjugates the base matching to it.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from clabels import (PMS, IDX, plist, BASE_IDX, ORBIT, word_of, inverse, GRAY, POS,  # noqa: E402
                     BASE_Q, match_of, act_t, MU0, compose)

OUT = os.path.join(os.path.dirname(HERE), 'CLabels.agda')
F8 = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇']
F5 = ['₀', '₁', '₂', '₃', '₄']


def letter(d):
    return 's' + '₀₁₂₃₄₅₆'[d]


def cw(w):
    if not w:
        return 'ε'
    return ' • '.join('[ %s ]ʷ' % letter(d) for d in w)


def fin_list(xs):
    return '(' + ' ∷ '.join(F8[x] for x in xs) + ' ∷ [])'


def fin_vec(xs):
    return '(' + ' ∷ '.join(F8[x] for x in xs) + ' ∷ [])'


# The base circuits Q as placed letters on wires 0..2, and Coxeter words
# whose circuits have the same function on the lower states.
BASE_PG = [
    [],
    [('CX', 0, 1)],
    [('CCX', 0, 2, 1)],
    [('CCX', 0, 2, 1), ('CCX', 0, 1, 2)],
    [('CX', 0, 1), ('CCX', 0, 1, 2)],
]


def pg_letter(l):
    if l[0] == 'X':
        return 'Xᵖ ' + F8[l[1]]
    if l[0] == 'CX':
        return 'CXᵖ ' + F8[l[1]] + ' ' + F8[l[2]]
    return 'CCXᵖ ' + F8[l[1]] + ' ' + F8[l[2]] + ' ' + F8[l[3]]


def pg_list(w):
    if not w:
        return '[]'
    return '(' + ' ∷ '.join(pg_letter(l) for l in w) + ' ∷ [])'


def state_fun(w):
    def f(x):
        for l in w:
            if l[0] == 'X':
                x ^= 1 << l[1]
            elif l[0] == 'CX':
                x ^= ((x >> l[1]) & 1) << l[2]
            else:
                x ^= (((x >> l[1]) & (x >> l[2])) & 1) << l[3]
        return x
    return f


def base_words():
    out = []
    for w, (nm, q) in zip(BASE_PG, BASE_Q):
        f = state_fun(w)
        for x in range(8):
            assert f(x) == q(x), nm
        # forward permutation of positions realised by the circuit
        fwd = tuple(POS[f(GRAY[i])] for i in range(8))
        # Pc v realises the inverse of act v: act v = fwd^-1
        v = word_of(inverse(fwd))
        out.append(v)
    return out


def main():
    QW = base_words()
    for k, v in enumerate(QW):
        assert match_of(v) == PMS[BASE_IDX[k]], k
    for m, (k, c) in zip(PMS, ORBIT):
        # match (c . frm base) = act c o nu_k o act c^-1
        nu = PMS[BASE_IDX[k]]
        a = act_t(c)
        assert compose(compose(a, nu), inverse(a)) == m
        assert all(a[MU0[x]] == MU0[a[x]] for x in range(8))
    o = [HDR]
    o.append('-- The 105 matchings as lists of their pairs.')
    o.append('pairsT : Vec (List (Fin 8)) 105')
    o.append('pairsT =')
    for i, m in enumerate(PMS):
        o.append('  %s %s' % ('  ' if i == 0 else '∷', fin_list(plist(m))))
    o.append('  ∷ []')
    o.append('')
    o.append('-- The 105 matchings as tables.')
    o.append('tblT : Vec (Vec (Fin 8) 8) 105')
    o.append('tblT =')
    for i, m in enumerate(PMS):
        o.append('  %s %s' % ('  ' if i == 0 else '∷', fin_vec(m)))
    o.append('  ∷ []')
    o.append('')
    o.append('-- The base matchings: one per union type with μ₀.')
    o.append('baseT : Vec (Fin 105) 5')
    o.append('baseT = ' + ' ∷ '.join('# %d' % i for i in BASE_IDX) + ' ∷ []')
    o.append('')
    o.append('-- The circuits that place μ₀ on the base matchings, as placed letters')
    o.append('-- on wires 0, 1, 2, and as Coxeter words.')
    o.append('baseQ : Fin 5 → List PG')
    for k, w in enumerate(BASE_PG):
        o.append('baseQ %s = %s' % (F5[k], pg_list(w)))
    o.append('')
    o.append('baseW : Fin 5 → CW')
    for k, v in enumerate(QW):
        o.append('baseW %s = %s' % (F5[k], cw(v)))
    o.append('')
    o.append('-- The base type of each matching, and a word of the centraliser of μ₀')
    o.append('-- conjugating the base matching to it.')
    o.append('orbKT : Vec (Fin 5) 105')
    o.append('orbKT = ' + ' ∷ '.join(F5[k] for k, _ in ORBIT) + ' ∷ []')
    o.append('')
    o.append('orbCT : Vec CW 105')
    o.append('orbCT =')
    for i, (k, c) in enumerate(ORBIT):
        o.append('  %s %s' % ('  ' if i == 0 else '∷', '(' + cw(c) + ')'))
    o.append('  ∷ []')
    with open(OUT, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write('\n'.join(o) + '\n')
    print('wrote', OUT)


HDR = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- Data of the labels of the controlled A₈
--
-- The labels are the 105 perfect matchings of the eight Gray positions
-- of the lower wires (pairsT, tblT).  Five of them (baseT) represent the
-- five orbits of the centraliser of μ₀ = (0 1)(2 3)(4 5)(6 7): μ₀ itself
-- and the matchings whose union with μ₀ has cycles of lengths 2+2,
-- 2+1+1, 3+1 and 4 (in pairs); each is μ₀ placed by a short three-wire
-- circuit (baseQ, as placed letters, and baseW, as a Coxeter word with
-- the same function).  Every matching is a base matching conjugated by a
-- word of the centraliser (orbKT, orbCT).  Generated by
-- gen/mk_clabels.py from gen/clabels.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.CLabels where

open import Data.Fin.Base using (Fin)
open import Data.Fin using (#_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Vec.Base using (Vec ; [] ; _∷_)

open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

import Examples.Groups.Symmetric.Syntactics as Sym
open import Examples.Groups.XCXCCX-4bit.Placed using (PG ; Xᵖ ; CXᵖ ; CCXᵖ)
open import Examples.Groups.XCXCCX-4bit.PFrames using (SG ; CW)

-- The generators of S₈.
s₀ s₁ s₂ s₃ s₄ s₅ s₆ : SG 8
s₀ = Sym.gate₂ Sym.σ-gate
s₁ = Sym.gate₂ Sym.σ-gate Sym.↥
s₂ = Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥
s₃ = Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥ Sym.↥
s₄ = Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥ Sym.↥ Sym.↥
s₅ = Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥
s₆ = Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥
'''

if __name__ == '__main__':
    main()

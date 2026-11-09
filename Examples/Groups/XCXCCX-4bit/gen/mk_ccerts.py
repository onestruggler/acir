"""Writes CCerts.agda: the symbols of EvenRS 8 as words of labels, the
relations, rev and closure certificates of ccerts.py, and the action
of each symbol's word on the upper half."""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ccerts  # noqa: E402
from ccerts import phiQ, SYMS, MU0_IDX, BASE_SYMS, BASE_MOVES  # noqa: E402

OUT = os.path.join(os.path.dirname(HERE), 'CCerts.agda')


def lab(i):
    return '# %d' % i


def labs(ls):
    if not ls:
        return '[]'
    return '(' + ' ∷ '.join(lab(i) for i in ls) + ' ∷ [])'


def move(m):
    k = m[0]
    if k in ('H', 'Hi', 'C', 'K'):
        return '%s %d' % (k, m[1])
    if k == 'I':
        return 'I %d (%s)' % (m[1], lab(m[2]))
    if k == 'Ki':
        return 'Ki %d (%s) (%s)' % (m[1], lab(m[2]), lab(m[3]))
    raise ValueError(m)


def moves(ms, indent):
    if not ms:
        return '[]'
    items = [move(m) for m in ms]
    out, line = [], ''
    for it in items:
        piece = it + ' ∷ '
        if len(line) + len(piece) > 70 and line:
            out.append(line)
            line = ''
        line += piece
    line += '[]'
    out.append(line)
    return '(' + ('\n' + ' ' * (indent + 1)).join(out) + ')'


def b(c):
    return 'true' if c else 'false'


def suc(n, v):
    s = v
    for _ in range(n):
        s = '(suc ' + s + ')'
    return s


def sym_term(x):
    c, d = x
    return '(sy %s %d)' % (b(c), d)


def cert_call(ms, lw, rw):
    return 'check-sound\n    %s\n    %s\n    %s\n    Eq.refl' % (moves(ms, 4), labs(lw), labs(rw))


def main():
    certs = ccerts.relation_certificates()
    revs = ccerts.rev_certificates()
    par = ccerts.closure()
    o = [HDR]

    o.append('------------------------------------------------------------------------')
    o.append('-- The symbols as words of labels')
    o.append('')
    o.append('Φ : Sch → List L')
    for c, d in SYMS:
        o.append('Φ (γ %s %d _ _) = %s' % (b(c), d, labs(phiQ(c, d))))
    o.append('Φ _ = []')
    o.append('')
    o.append(PHISTAR)

    o.append('------------------------------------------------------------------------')
    o.append('-- The action of each symbol on the upper half')
    o.append('')
    o.append('Φ-act-ok : (x : Sch) →')
    o.append('           allFin 8 (λ i → eqV (mF* (Φ x) (enc8 i)) (enc8 (SymI.⟦ f x ⟧ ⟨$⟩ʳ i))) ≡ true')
    o.append('Φ-act-ok (γ c zero () q)')
    for c, d in SYMS:
        o.append('Φ-act-ok (γ %s %d _ _) = Eq.refl' % (b(c), d))
    o.append('Φ-act-ok (γ c %s p q) = Irr.⊥-elim (ℕP.≤⇒≤ᵇ q)' % suc(7, 'd'))
    o.append('')

    o.append('------------------------------------------------------------------------')
    o.append('-- The relations of EvenRS 8, certified')
    o.append('')
    o.append('R-rel : ∀ {u v} → _RS,_===_ u v → 4 ⊢ Xs (Φ* u) ≈ Xs (Φ* v)')
    for name, l, r, lw, rw, ms in certs:
        k = name[0]
        if k == 'order':
            pat = '(order %s %d _ _)' % (b(name[1]), name[2])
        elif k == 'braid0':
            pat = '(braid₀ %s _)' % b(name[1])
        elif k == 'braid':
            pat = '(braid %s %d _ _)' % (b(name[1]), name[2])
        elif k == 'far0':
            pat = '(far₀ %s %d _ _)' % (b(name[1]), name[2])
        else:
            pat = '(far %s %d %d _ _ _)' % (b(name[1]), name[2], name[3])
        o.append('R-rel %s =' % pat)
        o.append('  ' + cert_call(ms, lw, rw))
    o.append('R-rel (order c zero () q)')
    o.append('R-rel (order c %s p q) = ⊥-elim (ℕP.≤⇒≤ᵇ q)' % suc(7, 'd'))
    o.append('R-rel (braid c zero () q)')
    o.append('R-rel (braid c %s p q) = ⊥-elim (ℕP.≤⇒≤ᵇ q)' % suc(6, 'd'))
    o.append('R-rel (far₀ c zero () q)')
    o.append('R-rel (far₀ c (suc zero) (s≤s ()) q)')
    o.append('R-rel (far₀ c %s p q) = ⊥-elim (ℕP.≤⇒≤ᵇ q)' % suc(7, 'e'))
    o.append('R-rel (far c zero e () q r)')
    for d in range(1, 5):
        for e in range(0, d + 2):
            o.append('R-rel (far c %d %d p q r) = ⊥-elim (ℕP.≤⇒≤ᵇ q)' % (d, e))
        o.append('R-rel (far c %d %s p q r) = ⊥-elim (ℕP.≤⇒≤ᵇ r)' % (d, suc(7, 'e')))
    o.append('R-rel (far c %s e p q r) = ⊥-elim (ℕP.≤⇒≤ᵇ (ℕP.≤-trans (ℕP.+-monoʳ-≤ 2 q) r))'
             % suc(5, 'd'))
    o.append('')

    o.append('------------------------------------------------------------------------')
    o.append('-- A symbol reversed is the inverse symbol')
    o.append('')
    o.append('inv-sym : Sch → Sch')
    o.append('inv-sym (γ c d p q) = γ (not c) d p q')
    o.append('')
    o.append('rev-ok : (x : Sch) → 4 ⊢ Xs (reverse (Φ x)) ≈ Xs (Φ (inv-sym x))')
    o.append('rev-ok (γ c zero () q)')
    for c, d in SYMS:
        a = list(reversed(phiQ(c, d)))
        bb = phiQ(not c, d)
        o.append('rev-ok (γ %s %d _ _) =' % (b(c), d))
        o.append('  ' + cert_call(revs[(c, d)], a, bb))
    o.append('rev-ok (γ c %s p q) = Irr.⊥-elim (ℕP.≤⇒≤ᵇ q)' % suc(7, 'd'))
    o.append('')

    o.append('------------------------------------------------------------------------')
    o.append('-- The closure: every label from μ₀ by symbols')
    o.append('')
    o.append('μ₀ : L')
    o.append('μ₀ = %s' % lab(MU0_IDX))
    o.append('')
    o.append('-- γ₂ γ₄ γ₆ is μ₀: the product of the double transpositions')
    o.append('-- (0 1)(2 3), (0 1)(4 5) and (0 1)(6 7).')
    o.append('base-word : Word Sch')
    o.append('base-word = [ %s ]ʷ • ([ %s ]ʷ • [ %s ]ʷ)' % tuple(sym_term(x) for x in BASE_SYMS))
    o.append('')
    o.append('base-ok : 4 ⊢ Xs (Φ* base-word) ≈ Xs (μ₀ ∷ [])')
    o.append('base-ok =')
    o.append('  ' + cert_call(BASE_MOVES, ccerts.phiQs(BASE_SYMS), [MU0_IDX]))
    o.append('')
    o.append('-- The tree: each label but μ₀ is its parent conjugated by the')
    o.append('-- word of a symbol, one level deeper.')
    o.append('parT : Vec L 105')
    o.append('parT =')
    for m in range(105):
        o.append('  %s %s' % ('  ' if m == 0 else '∷', lab(par[m][0])))
    o.append('  ∷ []')
    o.append('')
    o.append('symT : Vec Sch 105')
    o.append('symT =')
    for m in range(105):
        o.append('  %s %s' % ('  ' if m == 0 else '∷', sym_term(par[m][1])))
    o.append('  ∷ []')
    o.append('')
    o.append('depT : Vec ℕ 105')
    o.append('depT =')
    for m in range(105):
        o.append('  %s %d' % ('  ' if m == 0 else '∷', par[m][2]))
    o.append('  ∷ []')
    o.append('')
    o.append(TAIL)
    with open(OUT, 'w', encoding='utf-8', newline='\n') as fh:
        fh.write('\n'.join(o) + '\n')
    print('wrote', OUT)


HDR = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- Certificates for the controlled A₈
--
-- The controlled matchings generate, on the upper half of the states,
-- the even permutations of the eight Gray positions, which EvenRS 8
-- presents by symbols γ c d.  Each symbol is a word of two or four
-- labels (Φ, after the canonical factorisation of a double
-- transposition into two commuting matchings, with the auxiliary pair
-- (6 7) for d = 1) whose matchings compose to f (γ c d) (Φ-act-ok,
-- decided on the eight positions).  Each relation of EvenRS 8 is a
-- certificate of LabelEngine between the words of its two sides
-- (R-rel; found by gen/c8/certgen.py on double transpositions and
-- expanded), a symbol's word reversed is the word of the inverse
-- symbol (rev-ok), and every label is reached from μ₀ = Φ (γ₂ γ₄ γ₆)
-- by conjugating with the words of symbols, along a breadth-first tree
-- (parT, symT, depT, checked by closure-all).  Generated by
-- gen/mk_ccerts.py from gen/ccerts.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.CCerts where

open import Data.Bool.Base using (Bool ; true ; false ; T ; not ; _∧_)
open import Data.Empty using (⊥-elim)
import Data.Empty.Irrelevant as Irr
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; reverse)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤ᵇ_ ; _≡ᵇ_ ; _+_ ; s≤s ; z≤n)
import Data.Nat.Properties as ℕP
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Examples.Groups.Symmetric.Interpretation as SymI

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (eqV)
open import Examples.Groups.XCXCCX-4bit.CRel
  using (L ; Xm ; c3 ; mul ; _==ᴸ_ ; ==ᴸ-sound ; conj-ok ; klein-ok)
open import Examples.Groups.XCXCCX-4bit.CBC using (X-inv ; X-conj ; X-klein)
open import Examples.Groups.XCXCCX-4bit.CSem using (allFin ; enc8 ; mF*)
import Examples.Groups.XCXCCX-4bit.LabelEngine as LE
open LE _==ᴸ_ c3 conj-ok mul klein-ok public using (Move ; H ; Hi ; C ; I ; K ; Ki ; check)
open LE.Sound _==ᴸ_ c3 conj-ok mul klein-ok (4 VRel,_===_) Xm ==ᴸ-sound X-inv X-conj X-klein public
  using (Xs ; Xs-++ ; check-sound)
import Examples.Groups.XCXCCX-4bit.EvenRS as ERS
open ERS 8 using (Sch ; γ ; f ; _RS,_===_ ; order ; braid₀ ; braid ; far₀ ; far)

-- A symbol with its bounds decided.
sy : Bool → (d : ℕ) → {_ : T (1 ≤ᵇ d)} → {_ : T (2 + d ≤ᵇ 8)} → Sch
sy c d {p} {q} = γ c d (ℕP.≤ᵇ⇒≤ 1 d p) (ℕP.≤ᵇ⇒≤ (2 + d) 8 q)
'''

PHISTAR = r'''-- A word of symbols as a word of labels.
Φ* : Word Sch → List L
Φ* [ x ]ʷ   = Φ x
Φ* ε       = []
Φ* (u • v) = Φ* u ++ Φ* v
'''

TAIL = r'''par : L → L
par μ = lookup parT μ

sym-of : L → Sch
sym-of μ = lookup symT μ

dep : L → ℕ
dep μ = lookup depT μ

-- Conjugation by a word of labels, the last letter innermost, and the
-- side conditions of its steps.
star : List L → L → L
star []       ν = ν
star (w ∷ ws) ν = c3 w (star ws ν)

conjs-ok : List L → L → Bool
conjs-ok []       ν = true
conjs-ok (w ∷ ws) ν = conj-ok w (star ws ν) ∧ conjs-ok ws ν

-- The step of the tree at a label of the given depth.
cstep : L → ℕ → Bool
cstep μ zero    = μ ==ᴸ μ₀
cstep μ (suc n) = (dep (par μ) ≡ᵇ n) ∧ (conjs-ok (Φ (sym-of μ)) (par μ) ∧ (star (Φ (sym-of μ)) (par μ) ==ᴸ μ))

closure-ok : L → Bool
closure-ok μ = cstep μ (dep μ)

closure-all : allFin 105 closure-ok ≡ true
closure-all = Eq.refl'''

if __name__ == '__main__':
    main()

"""Writes CFrame.agda: the frame lemma for G = CX₃₀ at every Coxeter word.

A Coxeter word r whose permutation of the Gray positions commutes with
mu0 = (0 1)(2 3)(4 5)(6 7) is, as a permutation, a flip inside some pairs
followed by a permutation of the pairs (decided by its values on the even
positions); the 24 pair permutations have fixed Coxeter words (pairW),
each checked once against G by CBase.wcore, and the flips are Width3's
T 0, T 2, T 4, T 6.  This module generates the finite tables.
"""
import itertools
import os
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(HERE), 'CFrame.agda')

F8 = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇']
F4 = ['₀', '₁', '₂', '₃']


def sw(d, i):
    return d + 1 if i == d else (d if i == d + 1 else i)


def act(w, i):
    for d in reversed(w):
        i = sw(d, i)
    return i


def pair_words():
    target = {}
    for s in itertools.permutations(range(4)):
        Q = tuple(2 * s[x >> 1] + (x & 1) for x in range(8))
        target[Q] = s
    start = tuple(range(8))
    prev = {start: None}
    dq = deque([start])
    found = {}
    while dq and len(found) < 24:
        t = dq.popleft()
        if t in target and t not in found:
            w = []
            u = t
            while prev[u] is not None:
                p, d = prev[u]
                w.append(d)
                u = p
            found[t] = list(reversed(w))
        for d in range(7):
            nt = tuple(t[sw(d, i)] for i in range(8))
            if nt not in prev:
                prev[nt] = (t, d)
                dq.append(nt)
    out = {}
    for Q, s in target.items():
        w = found[Q]
        assert tuple(act(w, i) for i in range(8)) == Q
        out[s] = w
    return out


def gen_letter(d):
    return 'Sym.gate₂ Sym.σ-gate' + ' Sym.↥' * d


def cw(w):
    if not w:
        return 'ε'
    return ' • '.join('[ %s ]ʷ' % gen_letter(d) for d in w)


def main():
    PW = pair_words()
    o = []
    o.append(HDR)
    # flips
    o.append('flips-act : (b₀ b₁ b₂ b₃ : Bool) (x : Fin 8) →')
    o.append('            act (flips4 b₀ b₁ b₂ b₃) x ≡ mk (half x) (low x xor sel4b b₀ b₁ b₂ b₃ (half x))')
    for bs in itertools.product([0, 1], repeat=4):
        for x in range(8):
            o.append('flips-act %s %s = Eq.refl' % (' '.join('true' if b else 'false' for b in bs), F8[x]))
    o.append('')
    # the fast action: transpositions, and act on a letter
    o.append('-- The transposition of the positions d and d + 1.')
    o.append('swp : ℕ → Fin 8 → Fin 8')
    for d in range(7):
        for x in range(8):
            y = d + 1 if x == d else (d if x == d + 1 else x)
            o.append('swp %d %s = %s' % (d, F8[x], F8[y]))
    o.append('swp _ x = x')
    o.append('')
    o.append('act-letter : (g : SG 8) (x : Fin 8) → act [ g ]ʷ x ≡ swp (CF.tr 0 g) x')
    for k in range(9):
        sh = ' Sym.↥' * k
        if k <= 6:
            for x in range(8):
                o.append('act-letter (Sym.gate₂ Sym.σ-gate%s) %s = Eq.refl' % (sh, F8[x]))
        o.append('act-letter (Sym.gate₀ ()%s) x' % sh)
        if k <= 7:
            o.append('act-letter (Sym.gate₁ ()%s) x' % sh)
    o.append('')
    # pair words
    o.append('pairW : Fin 4 → Fin 4 → Fin 4 → Fin 4 → CW')
    for s, w in sorted(PW.items()):
        o.append('pairW %s = %s' % (' '.join(F4[v] for v in s), cw(w)))
    o.append('pairW _ _ _ _ = ε')
    o.append('')
    # invalid prefixes
    absurd = []
    for a in range(4):
        absurd.append((a, a, None, None))
    for a in range(4):
        for b in range(4):
            if a == b:
                continue
            absurd.append((a, b, a, None))
            absurd.append((a, b, b, None))
    for a, b, c in itertools.permutations(range(4), 3):
        for d in (a, b, c):
            absurd.append((a, b, c, d))

    def pat(t):
        return ' '.join(F4[v] if v is not None else '_' for v in t)

    o.append('pair-act : (a b c d : Fin 4) → valid4 a b c d ≡ true → (x : Fin 8) →')
    o.append('           act (pairW a b c d) x ≡ mk (sel4 a b c d (half x)) (low x)')
    for s in sorted(PW):
        for x in range(8):
            o.append('pair-act %s h %s = Eq.refl' % (' '.join(F4[v] for v in s), F8[x]))
    for t in absurd:
        o.append('pair-act %s ()' % pat(t))
    o.append('')
    o.append('pair-comm : (a b c d : Fin 4) → valid4 a b c d ≡ true → Comm (Pc 0 (pairW a b c d)) G')
    for s in sorted(PW):
        o.append('pair-comm %s h = wcore (pairW %s) Eq.refl' % (' '.join(F4[v] for v in s), ' '.join(F4[v] for v in s)))
    for t in absurd:
        o.append('pair-comm %s ()' % pat(t))
    o.append('')
    o.append(TAIL)
    with open(OUT, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n'.join(o) + '\n')
    print('wrote', OUT)


HDR = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- The frame lemma for G = CX₃₀, at every Coxeter word
--
-- A Coxeter word r of S₈ whose permutation commutes with the matching
-- μ₀ = (0 1)(2 3)(4 5)(6 7) of the Gray positions (InC r) gives a
-- circuit that commutes with G (W-core).  Write a position as 2 v + e
-- (mk v e, a pair v and a side e).  Such a permutation sends 2 v + e to
-- 2 σ v + (e xor β v), where σ v and β v are read off its value at
-- 2 v (the centraliser condition gives the odd positions); σ is
-- injective because the permutation is (valid4).  So r has the same
-- permutation as pairW σ • flipsW β (perm-complete), whose circuit is
-- a pair permutation (one of 24 fixed Coxeter words, each checked
-- against G once by CBase.wcore) after flips inside the pairs (Width3's
-- T 0, T 2, T 4, T 6, CBase.flip-comm).  Hence two frames of G with the
-- same matching are equal (W′, the matchings compared on the eight
-- positions by eqMatch).
--
-- Generated by gen/mk_cframe.py (the 24 pair words, and the tables of
-- refl proofs for their permutations and for the flips).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.CFrame where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∧_ ; _xor_ ; T)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Nat.Base using (ℕ)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

import Examples.Groups.Symmetric.Syntactics as Sym
open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.PFrames
open import Examples.Groups.XCXCCX-4bit.CBase
import Examples.Groups.XCXCCX-4bit.Coxeter as Cox
open Cox 8 using (act-inv)
import Examples.Groups.Symmetric.CoxeterFrames as CF

open PB (4 VRel,_===_) using (_≈_)

------------------------------------------------------------------------
-- Positions as pairs

mk : Fin 4 → Bool → Fin 8
mk ₀ false = ₀
mk ₀ true  = ₁
mk ₁ false = ₂
mk ₁ true  = ₃
mk ₂ false = ₄
mk ₂ true  = ₅
mk ₃ false = ₆
mk ₃ true  = ₇

half : Fin 8 → Fin 4
half ₀ = ₀
half ₁ = ₀
half ₂ = ₁
half ₃ = ₁
half ₄ = ₂
half ₅ = ₂
half ₆ = ₃
half ₇ = ₃

low : Fin 8 → Bool
low ₀ = false
low ₁ = true
low ₂ = false
low ₃ = true
low ₄ = false
low ₅ = true
low ₆ = false
low ₇ = true

mk-hl : (x : Fin 8) → mk (half x) (low x) ≡ x
mk-hl ₀ = Eq.refl
mk-hl ₁ = Eq.refl
mk-hl ₂ = Eq.refl
mk-hl ₃ = Eq.refl
mk-hl ₄ = Eq.refl
mk-hl ₅ = Eq.refl
mk-hl ₆ = Eq.refl
mk-hl ₇ = Eq.refl

half-mk : (v : Fin 4) (e : Bool) → half (mk v e) ≡ v
half-mk ₀ false = Eq.refl
half-mk ₀ true  = Eq.refl
half-mk ₁ false = Eq.refl
half-mk ₁ true  = Eq.refl
half-mk ₂ false = Eq.refl
half-mk ₂ true  = Eq.refl
half-mk ₃ false = Eq.refl
half-mk ₃ true  = Eq.refl

low-mk : (v : Fin 4) (e : Bool) → low (mk v e) ≡ e
low-mk ₀ false = Eq.refl
low-mk ₀ true  = Eq.refl
low-mk ₁ false = Eq.refl
low-mk ₁ true  = Eq.refl
low-mk ₂ false = Eq.refl
low-mk ₂ true  = Eq.refl
low-mk ₃ false = Eq.refl
low-mk ₃ true  = Eq.refl

-- The matching that flips wire 0.
μ₀ : Fin 8 → Fin 8
μ₀ x = mk (half x) (not (low x))

μ₀-mk : (v : Fin 4) → μ₀ (mk v false) ≡ mk v true
μ₀-mk ₀ = Eq.refl
μ₀-mk ₁ = Eq.refl
μ₀-mk ₂ = Eq.refl
μ₀-mk ₃ = Eq.refl

-- Commuting with μ₀.
InC : CW → Set
InC r = ∀ x → act r (μ₀ x) ≡ μ₀ (act r x)

------------------------------------------------------------------------
-- Equality of positions and pair indices

_==₄_ : Fin 4 → Fin 4 → Bool
₀ ==₄ ₀ = true
₁ ==₄ ₁ = true
₂ ==₄ ₂ = true
₃ ==₄ ₃ = true
_ ==₄ _ = false

==₄-sound : (a b : Fin 4) → (a ==₄ b) ≡ true → a ≡ b
==₄-sound ₀ ₀ _ = Eq.refl
==₄-sound ₁ ₁ _ = Eq.refl
==₄-sound ₂ ₂ _ = Eq.refl
==₄-sound ₃ ₃ _ = Eq.refl
==₄-sound ₀ ₁ ()
==₄-sound ₀ ₂ ()
==₄-sound ₀ ₃ ()
==₄-sound ₁ ₀ ()
==₄-sound ₁ ₂ ()
==₄-sound ₁ ₃ ()
==₄-sound ₂ ₀ ()
==₄-sound ₂ ₁ ()
==₄-sound ₂ ₃ ()
==₄-sound ₃ ₀ ()
==₄-sound ₃ ₁ ()
==₄-sound ₃ ₂ ()

-- Four pair indices that are pairwise distinct.
valid4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Bool
valid4 a b c d = not (a ==₄ b) ∧ (not (a ==₄ c) ∧ (not (b ==₄ c) ∧ (not (a ==₄ d) ∧ (not (b ==₄ d) ∧ not (c ==₄ d)))))

sel4 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4
sel4 a b c d ₀ = a
sel4 a b c d ₁ = b
sel4 a b c d ₂ = c
sel4 a b c d ₃ = d

sel4b : Bool → Bool → Bool → Bool → Fin 4 → Bool
sel4b a b c d ₀ = a
sel4b a b c d ₁ = b
sel4b a b c d ₂ = c
sel4b a b c d ₃ = d

------------------------------------------------------------------------
-- Flips inside the pairs: s₀, s₂, s₄, s₆

fw : Bool → SG 8 → CW
fw true  g = [ g ]ʷ
fw false _ = ε

flips4 : Bool → Bool → Bool → Bool → CW
flips4 b₀ b₁ b₂ b₃ =
  fw b₀ (Sym.gate₂ Sym.σ-gate) • fw b₁ (Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥)
  • fw b₂ (Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥ Sym.↥ Sym.↥)
  • fw b₃ (Sym.gate₂ Sym.σ-gate Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥ Sym.↥)

private
  cf : (b : Bool) (k : ℕ) (g : SG 8) → Pc 0 [ g ]ʷ ≡ T₄ k → Comm (T₄ k) G → Comm (Pc 0 (fw b g)) G
  cf true  k g e h = Eq.subst (λ z → Comm z G) (Eq.sym e) h
  cf false k g e h = comm-ε

flips-comm : (b₀ b₁ b₂ b₃ : Bool) → Comm (Pc 0 (flips4 b₀ b₁ b₂ b₃)) G
flips-comm b₀ b₁ b₂ b₃ =
  comm-• (cf b₀ 0 _ Eq.refl flip-comm₀)
  (comm-• (cf b₁ 2 _ Eq.refl flip-comm₂)
  (comm-• (cf b₂ 4 _ Eq.refl flip-comm₄) (cf b₃ 6 _ Eq.refl flip-comm₆)))

'''

TAIL = open(os.path.join(HERE, 'cframe_tail.txt'), encoding='utf-8').read()


if __name__ == '__main__':
    main()

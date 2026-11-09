"""Writes Four.agda: completeness on four wires from the faithfulness of
the circuits that keep wire 3 (the top layer).

The 16 states are numbered by the reflected Gray code g(i) = i xor (i >> 1),
so that s_d exchanges two states that differ in one bit t(d).  The symbol
gamma(c, d) of EvenRS 16 (s_d s_0 or s_0 s_d) is realised by a word whose
letters target only wires 0 and t(d) (found by breadth-first search), so
it keeps every other wire; a relation of A_16 involves at most two values
of t besides 0, so it keeps some wire m in {1, 2, 3} and Faithful m decides
it.  Every placed letter is a word in the symbols: by a Coxeter word inside
the Young subgroup of the positions that preserves some wire m it keeps
(checked by Faithful m), or, for the four letters that lie in no such
subgroup, by a three-wire step into letters that do.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(HERE), 'Four.agda')

N = 16
G = [i ^ (i >> 1) for i in range(N)]
GINV = {s: i for i, s in enumerate(G)}
T = [(G[d] ^ G[d + 1]).bit_length() - 1 for d in range(N - 1)]
W = ['₀', '₁', '₂', '₃']
NUM = ['₀', '₁', '₂', '₃', '₄', '₅', '₆', '₇', '₈', '₉', '₁₀', '₁₁', '₁₂', '₁₃', '₁₄', '₁₅']


# ---------------------------------------------------------------- letters

def all_letters():
    L = []
    for w in range(4):
        L.append(('X', w))
    for c in range(4):
        for w in range(4):
            if c != w:
                L.append(('CX', c, w))
    for a in range(4):
        for b in range(a + 1, 4):
            for w in range(4):
                if w not in (a, b):
                    L.append(('CCX', a, b, w))
    return L


ALL = all_letters()


def target(l):
    return l[-1]


def act(l, x):
    k = l[0]
    if k == 'X':
        return x ^ (1 << l[1])
    if k == 'CX':
        return x ^ (((x >> l[1]) & 1) << l[2])
    a, b, w = l[1], l[2], l[3]
    return x ^ ((((x >> a) & (x >> b)) & 1) << w)


def func(word):
    p = list(range(16))
    for l in word:
        p = [act(l, y) for y in p]
    return tuple(p)


def agda_letter(l):
    if l[0] == 'X':
        return 'Xᵖ ' + W[l[1]]
    if l[0] == 'CX':
        return 'CXᵖ ' + W[l[1]] + ' ' + W[l[2]]
    return 'CCXᵖ ' + W[l[1]] + ' ' + W[l[2]] + ' ' + W[l[3]]


def agda_list(w):
    if not w:
        return '[]'
    return '(' + ' ∷ '.join(agda_letter(l) for l in w) + ' ∷ [])'


# ---------------------------------------------------------------- symbols

def sperm(k, i):
    return k + 1 if i == k else (k if i == k + 1 else i)


def symperm(c, d):
    # f (γ false d) = s d • s 0: s_d first; f (γ true d) = s 0 • s d.
    if c == 0:
        return [sperm(0, sperm(d, i)) for i in range(N)]
    return [sperm(d, sperm(0, i)) for i in range(N)]


def state_fun(perm):
    f = [None] * 16
    for i in range(N):
        f[G[i]] = G[perm[i]]
    return tuple(f)


def bfs(goal, alphabet, maxd=10):
    start = tuple(range(16))
    if start == goal:
        return []
    prev = {start: None}
    frontier = [start]
    for _ in range(maxd):
        nf = []
        for p in frontier:
            for l in alphabet:
                q = tuple(act(l, y) for y in p)
                if q not in prev:
                    prev[q] = (p, l)
                    if q == goal:
                        w = []
                        while prev[q] is not None:
                            p0, l0 = prev[q]
                            w.append(l0)
                            q = p0
                        return w[::-1]
                    nf.append(q)
        frontier = nf
    return None


R = {}
for d in range(1, N - 1):
    alpha = [l for l in ALL if target(l) in (0, T[d])]
    for c in (0, 1):
        goal = state_fun(symperm(c, d))
        w = bfs(goal, alpha)
        assert w is not None and func(w) == goal
        R[(c, d)] = w

# ---------------------------------------------------------------- translations


def blocks(m):
    cuts = [d for d in range(N - 1) if T[d] == m]
    b, cur = [], []
    for i in range(N):
        cur.append(i)
        if i in cuts:
            b.append(cur)
            cur = []
    b.append(cur)
    return b


def posperm(l):
    return [GINV[act(l, G[i])] for i in range(N)]


def perm_of_word(word):
    res = []
    for i in range(N):
        x = i
        for d in word:
            x = sperm(d, x)
        res.append(x)
    return res


def coxeter_word(p, allowed):
    a = list(p)
    word = []
    changed = True
    while changed:
        changed = False
        for d in range(N - 1):
            if a[d] > a[d + 1]:
                assert d in allowed
                a[d], a[d + 1] = a[d + 1], a[d]
                word.append(d)
                changed = True
    for Wd in (word, word[::-1]):
        if perm_of_word(Wd) == p:
            return Wd
    raise Exception('orientation')


def rs(word):
    c, out = 0, []
    for d in word:
        if d > 0:
            out.append((c, d))
        c ^= 1
    assert c == 0
    return out


def R_star(sch):
    w = []
    for x in sch:
        w += R[x]
    return w


BASIC = {}
for l in ALL:
    p = posperm(l)
    best = None
    for m in (3, 2, 1):
        if target(l) == m:
            continue
        bl = blocks(m)
        bid = {i: k for k, b in enumerate(bl) for i in b}
        if not all(bid[p[i]] == bid[i] for i in range(N)):
            continue
        allowed = {d for d in range(N - 1) if T[d] != m}
        sch = rs(coxeter_word(p, allowed))
        rw = R_star(sch)
        assert func(rw) == func([l])
        assert all(target(x) != m for x in rw)
        if best is None or len(rw) < best[0]:
            best = (len(rw), m, sch)
    if best is not None:
        BASIC[l] = (best[1], best[2])

# The letters in no Young subgroup, by a three-wire step (idle wire m)
# into letters translated earlier.
EXC = [
    (('X', 3), 0, [('CX', 2, 3), ('X', 2), ('CX', 2, 3), ('X', 2)]),
    (('CX', 0, 3), 1, [('CCX', 0, 2, 3), ('X', 2), ('CCX', 0, 2, 3), ('X', 2)]),
    (('CX', 1, 3), 0, [('CCX', 1, 2, 3), ('X', 2), ('CCX', 1, 2, 3), ('X', 2)]),
    (('CCX', 0, 1, 3), 2, [('CX', 1, 3), ('CX', 3, 1), ('CX', 1, 3), ('CCX', 0, 3, 1),
                           ('CX', 1, 3), ('CX', 3, 1), ('CX', 1, 3)]),
]
assert set(BASIC) | {e[0] for e in EXC} == set(ALL) and not (set(BASIC) & {e[0] for e in EXC})
done = set(BASIC)
for l, m, us in EXC:
    assert func([l]) == func(us)
    assert all(m not in x[1:] for x in [l] + us)
    assert all(u in done for u in us)
    done.add(l)


def lname(l):
    sub = {0: '₀', 1: '₁', 2: '₂', 3: '₃'}
    return 'ok-' + l[0] + ''.join(sub[x] for x in l[1:])


def sym(cd):
    c, d = cd
    return '[ sy %s %d ]ʷ' % ('false' if c == 0 else 'true', d)


def sch_word(sch):
    if not sch:
        return 'ε'
    return ' • '.join(sym(x) for x in sch)


def fin(i):
    return NUM[i]


def bits(s):
    return '(' + ' ∷ '.join('true' if (s >> w) & 1 else 'false' for w in range(4)) + ' ∷ [])'


def gen():
    out = []
    o = out.append
    o(HDR)
    # numbering
    o('------------------------------------------------------------------------')
    o('-- The states, numbered along the reflected Gray code')
    o('')
    o('enc : Fin 16 → Bits 4')
    for i in range(N):
        o('enc %s = %s' % (fin(i), bits(G[i])))
    o('')
    o('dec : Bits 4 → Fin 16')
    for i in range(N):
        o('dec %s = %s' % (bits(G[i]), fin(i)))
    o('')
    o('dec-enc : ∀ i → dec (enc i) ≡ i')
    for i in range(N):
        o('dec-enc %s = Eq.refl' % fin(i))
    o('')
    o('enc-dec : ∀ x → enc (dec x) ≡ x')
    for i in range(N):
        o('enc-dec %s = Eq.refl' % bits(G[i]))
    o('')
    o('-- The wire on which the states d and d + 1 differ.')
    o('t : ℕ → Wire')
    for d in range(N - 1):
        o('t %d = %s' % (d, W[T[d]]))
    o('t _ = ₀')
    o('')
    # realisations
    o('------------------------------------------------------------------------')
    o('-- The symbols as words of letters that target wires 0 and t d only')
    o('')
    o('R : Sch → List PG')
    for d in range(1, N - 1):
        for c in (0, 1):
            o('R (γ %s %d _ _) = %s' % ('false' if c == 0 else 'true', d, agda_list(R[(c, d)])))
    o('R _ = []')
    o('')
    o('R-act : ∀ (x : Sch) (i : Fin 16) → ⟦ R x ⟧ᵖ* (enc i) ≡ enc (SymI.⟦ f x ⟧ ⟨$⟩ʳ i)')
    o('R-act (γ c zero () q) i')
    for d in range(1, N - 1):
        for c in (0, 1):
            for i in range(N):
                o('R-act (γ %s %d _ _) %s = Eq.refl' % ('false' if c == 0 else 'true', d, fin(i)))
    o('R-act (γ c (%s) p q) i = ⊥-elim (ℕP.≤⇒≤ᵇ q)' % ('suc (' * 15 + 'd' + ')' * 15))
    o('')
    o('R-tgt : (c : Bool) (d : ℕ) .(p : 1 ≤ d) .(q : 2 + d ≤ 16) →')
    o('        every (targets ₀ (t d)) (R (γ c d p q)) ≡ true')
    o('R-tgt c zero () q')
    for d in range(1, N - 1):
        for c in (0, 1):
            o('R-tgt %s %d p q = Eq.refl' % ('false' if c == 0 else 'true', d))
    for c in ('false', 'true'):
        o('R-tgt %s (%s) p q = Eq.refl' % (c, 'suc (' * 15 + 'd' + ')' * 15))
    o('')
    o(MID)
    # translations
    o('------------------------------------------------------------------------')
    o('-- Every letter as a word in the symbols')
    o('')
    o('tw₀ : PG → Word Sch')
    for l, (m, sch) in BASIC.items():
        o('tw₀ (%s) = %s' % (agda_letter(l), sch_word(sch)))
    o('tw₀ _ = ε')
    o('')
    o(TWL)
    o('tw₁ : PG → Word Sch')
    for l, m, us in EXC[:3]:
        o('tw₁ (%s) = twL₀ %s' % (agda_letter(l), agda_list(us)))
    o('tw₁ g = tw₀ g')
    o('')
    o(TWL1)
    o('tw : PG → Word Sch')
    l, m, us = EXC[3]
    o('tw (%s) = twL₁ %s' % (agda_letter(l), agda_list(us)))
    o('tw g = tw₁ g')
    o('')
    for l, (m, sch) in BASIC.items():
        o('%s : 4 ⊢ ι (%s) ≈ ι* (R* (tw₀ (%s)))' % (lname(l), agda_letter(l), agda_letter(l)))
        o('%s = basic (%s) %s Eq.refl Eq.refl Eq.refl' % (lname(l), agda_letter(l), W[m]))
        o('')
    for l, m, us in EXC[:3]:
        oks = ' ∷ '.join(lname(u) for u in us) + ' ∷ []'
        o('%s : 4 ⊢ ι (%s) ≈ ι* (R* (tw₁ (%s)))' % (lname(l), agda_letter(l), agda_letter(l)))
        o('%s = viaN (%s) %s %s (tw₁ (%s)) Eq.refl Eq.refl Eq.refl (okL₀ %s (%s))'
          % (lname(l), agda_letter(l), W[m], agda_list(us), agda_letter(l), agda_list(us), oks))
        o('')
    l, m, us = EXC[3]
    oks = ' ∷ '.join(lname(u) for u in us) + ' ∷ []'
    o('%s : 4 ⊢ ι (%s) ≈ ι* (R* (tw (%s)))' % (lname(l), agda_letter(l), agda_letter(l)))
    o('%s = viaN (%s) %s %s (tw (%s)) Eq.refl Eq.refl Eq.refl (okL₁ %s (%s))'
      % (lname(l), agda_letter(l), W[m], agda_list(us), agda_letter(l), agda_list(us), oks))
    o('')
    o('tw-ok : ∀ g → 4 ⊢ ι g ≈ ι* (R* (tw g))')
    valid = set(ALL)
    for l in ALL:
        o('tw-ok (%s) = %s' % (agda_letter(l), lname(l)))
    for c in range(4):
        o('tw-ok (CXᵖ %s %s {()})' % (W[c], W[c]))
    for a in range(4):
        for b in range(4):
            for w in range(4):
                if ('CCX', a, b, w) not in valid:
                    o('tw-ok (CCXᵖ %s %s %s {()})' % (W[a], W[b], W[w]))
    o('')
    o(END)
    with open(OUT, 'w', encoding='utf-8', newline='\n') as f:
        f.write('\n'.join(out) + '\n')
    print('wrote', OUT)
    print('symbols:', max(len(v) for v in R.values()), 'max letters; translations:',
          sum(len(R_star(s)) for m, s in BASIC.values()), 'letters')


HDR = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness on four wires, from the faithfulness of the circuits
-- that keep wire 3
--
-- ByEvenRS for the numbering of the 16 states along the reflected Gray
-- code, so that the transposition s_d of the states d and d + 1 flips
-- one wire t d.  The symbol γ c d of A₁₆ (s_d s_0 or s_0 s_d) is
-- realised by a word whose letters target wires 0 and t d only (R,
-- found by breadth-first search; R-act checks it state by state), so
-- it keeps the other two wires.  A relation of A₁₆ involves at most two
-- values of t besides 0, so all its symbols keep a wire m in {1, 2, 3}
-- (pick), and Faithful m, from the parameter by relabelling, decides
-- it (R-rel, five generic clauses).  Every placed letter is a word in
-- the symbols (tw): by a Coxeter word inside the Young subgroup of the
-- positions that preserves a wire m that the letter keeps, so that
-- Faithful m decides the translation, or, for the four letters in no
-- such subgroup (X₃, CX₀₃, CX₁₃, CCX₀₁₃), by a three-wire step into
-- letters translated before (viaN).  So two words of placed letters
-- with the same function are equal, and so are two circuits
-- (complete₄).
--
-- Generated by gen/mk_four.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇ ; ₈ ; ₉ ; ₁₀ ; ₁₁ ; ₁₂ ; ₁₃ ; ₁₄ ; ₁₅)
open import Examples.Groups.XCXCCX-4bit.Faithful using (Faithful)

module Examples.Groups.XCXCCX-4bit.Four (f₃ : Faithful ₃) where

open import Data.Bool.Base using (Bool ; true ; false ; T ; not ; _∧_)
open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; _≤ᵇ_ ; _+_ ; s≤s ; z≤n)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB

import Examples.Groups.Symmetric.Interpretation as SymI

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (Bits ; ⟦_⟧ ; _≐_ ; ≐-sym ; ≐-trans ; eqF ; eqF-sound ; sound)
open import Examples.Groups.XCXCCX-4bit.Placed using (PG ; Xᵖ ; CXᵖ ; CCXᵖ ; Wire ; _==_ ; every ; avoids ; ι ; ι* ; ⟦_⟧ᵖ* ; ι*-sem)
open import Examples.Groups.XCXCCX-4bit.Narrow3 using (narrowᵖ)
open import Examples.Groups.XCXCCX-4bit.ToPlaced using (ι*-++ ; pg ; pg-ok)
open import Examples.Groups.XCXCCX-4bit.Faithful using (target ; keeps ; targets ; every-++ ; keeps-from ; faithful)
import Examples.Groups.XCXCCX-4bit.EvenRS as ERS
open ERS 16 using (Sch ; γ ; f ; _RS,_===_ ; order ; braid₀ ; braid ; far₀ ; far ; far-lo ; far-pos)
import Examples.Groups.XCXCCX-4bit.ByEvenRS as BE

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong ; right-unit)

-- A symbol with its bounds decided.
sy : Bool → (d : ℕ) → {_ : T (1 ≤ᵇ d)} → {_ : T (2 + d ≤ᵇ 16)} → Sch
sy c d {p} {q} = γ c d (ℕP.≤ᵇ⇒≤ 1 d p) (ℕP.≤ᵇ⇒≤ (2 + d) 16 q)
'''

MID = r'''------------------------------------------------------------------------
-- The relations

module RL = BE.Realisation enc dec dec-enc enc-dec R R-act
open RL using (R* ; rel-sem)

-- A wire in {1, 2, 3} other than a and b.
pick : Wire → Wire → Wire
pick ₃ ₃ = ₂
pick ₃ ₂ = ₁
pick ₂ ₃ = ₁
pick ₃ _ = ₂
pick _ ₃ = ₂
pick _ _ = ₃

pick-ok : (a b : Wire) → T (not (pick a b == ₀)) × (T (not (pick a b == a)) × T (not (pick a b == b)))
pick-ok ₀ ₀ = tt , tt , tt
pick-ok ₀ ₁ = tt , tt , tt
pick-ok ₀ ₂ = tt , tt , tt
pick-ok ₀ ₃ = tt , tt , tt
pick-ok ₁ ₀ = tt , tt , tt
pick-ok ₁ ₁ = tt , tt , tt
pick-ok ₁ ₂ = tt , tt , tt
pick-ok ₁ ₃ = tt , tt , tt
pick-ok ₂ ₀ = tt , tt , tt
pick-ok ₂ ₁ = tt , tt , tt
pick-ok ₂ ₂ = tt , tt , tt
pick-ok ₂ ₃ = tt , tt , tt
pick-ok ₃ ₀ = tt , tt , tt
pick-ok ₃ ₁ = tt , tt , tt
pick-ok ₃ ₂ = tt , tt , tt
pick-ok ₃ ₃ = tt , tt , tt

-- A symbol keeps every wire other than 0 and t d.
kR : (c : Bool) (d : ℕ) .(p : 1 ≤ d) .(q : 2 + d ≤ 16) (m : Wire) →
     T (not (m == ₀)) → T (not (m == t d)) → every (keeps m) (R (γ c d p q)) ≡ true
kR c d p q m h₀ h = keeps-from m ₀ (t d) (R (γ c d p q)) (R-tgt c d p q) h₀ h

private
  -- The wire a relation keeps, and why each symbol keeps it.
  module Pk (a b : Wire) where
    m = pick a b
    k₀ = proj₁ (pick-ok a b)
    ka = proj₁ (proj₂ (pick-ok a b))
    kb = proj₂ (proj₂ (pick-ok a b))

  ++3 : (m : Wire) (xs ys zs : List PG) → every (keeps m) xs ≡ true → every (keeps m) ys ≡ true →
        every (keeps m) zs ≡ true → every (keeps m) (xs ++ (ys ++ zs)) ≡ true
  ++3 m xs ys zs hx hy hz = every-++ (keeps m) xs (ys ++ zs) hx (every-++ (keeps m) ys zs hy hz)

R-rel : ∀ {u v} → _RS,_===_ u v → 4 ⊢ ι* (R* u) ≈ ι* (R* v)
R-rel {u} {v} r@(order c d p q) =
  faithful f₃ m (R* u) (R* v)
    (every-++ (keeps m) (R (γ c d p q)) (R (γ (not c) d p q)) (kR c d p q m k₀ ka) (kR (not c) d p q m k₀ ka))
    Eq.refl (rel-sem r)
  where open Pk (t d) (t d)
R-rel {u} {v} r@(braid₀ c q) =
  faithful f₃ m (R* u) (R* v)
    (kR (not c) 1 (s≤s z≤n) q m k₀ ka)
    (every-++ (keeps m) (R (γ c 1 (s≤s z≤n) q)) (R (γ c 1 (s≤s z≤n) q))
      (kR c 1 (s≤s z≤n) q m k₀ ka) (kR c 1 (s≤s z≤n) q m k₀ ka))
    (rel-sem r)
  where open Pk (t 1) (t 1)
R-rel {u} {v} r@(braid c d p q) =
  faithful f₃ m (R* u) (R* v)
    (++3 m (R (γ c d p q′)) (R (γ (not c) (suc d) (s≤s z≤n) q)) (R (γ c d p q′))
      (kR c d p q′ m k₀ ka) (kR (not c) (suc d) (s≤s z≤n) q m k₀ kb) (kR c d p q′ m k₀ ka))
    (++3 m (R (γ c (suc d) (s≤s z≤n) q)) (R (γ (not c) d p q′)) (R (γ c (suc d) (s≤s z≤n) q))
      (kR c (suc d) (s≤s z≤n) q m k₀ kb) (kR (not c) d p q′ m k₀ ka) (kR c (suc d) (s≤s z≤n) q m k₀ kb))
    (rel-sem r)
  where
  open Pk (t d) (t (suc d))
  q′ = ℕP.<⇒≤ q
R-rel {u} {v} r@(far₀ c e p q) =
  faithful f₃ m (R* u) (R* v) (kR c e (ℕP.<⇒≤ p) q m k₀ ka) (kR (not c) e (ℕP.<⇒≤ p) q m k₀ ka) (rel-sem r)
  where open Pk (t e) (t e)
R-rel {u} {v} r@(far c d e p q s) =
  faithful f₃ m (R* u) (R* v)
    (every-++ (keeps m) (R (γ c d p lo)) (R (γ (not c) e pe s))
      (kR c d p lo m k₀ ka) (kR (not c) e pe s m k₀ kb))
    (every-++ (keeps m) (R (γ c e pe s)) (R (γ (not c) d p lo))
      (kR c e pe s m k₀ kb) (kR (not c) d p lo m k₀ ka))
    (rel-sem r)
  where
  open Pk (t d) (t e)
  lo = far-lo q s
  pe = far-pos p q
'''

TWL = r'''-- A word of letters, letter by letter.
twL₀ : List PG → Word Sch
twL₀ []      = ε
twL₀ (g ∷ u) = tw₀ g • twL₀ u

data Oks₀ : List PG → Set where
  []  : Oks₀ []
  _∷_ : {g : PG} {u : List PG} → 4 ⊢ ι g ≈ ι* (R* (tw₀ g)) → Oks₀ u → Oks₀ (g ∷ u)

okL₀ : (u : List PG) → Oks₀ u → 4 ⊢ ι* u ≈ ι* (R* (twL₀ u))
okL₀ []      []       = refl
okL₀ (g ∷ u) (e ∷ es) = trans (cong e (okL₀ u es)) (sym (ι*-++ (R* (tw₀ g)) (R* (twL₀ u))))

-- A letter whose translation keeps wire m: Faithful m decides it.
basic : (g : PG) (m : Wire) → every (keeps m) (g ∷ []) ≡ true → every (keeps m) (R* (tw₀ g)) ≡ true →
        eqF 4 ⟦ g ∷ [] ⟧ᵖ* ⟦ R* (tw₀ g) ⟧ᵖ* ≡ true → 4 ⊢ ι g ≈ ι* (R* (tw₀ g))
basic g m hg ht hs =
  trans (sym right-unit) (faithful f₃ m (g ∷ []) (R* (tw₀ g)) hg ht (eqF-sound 4 _ _ hs))

-- A letter that a three-wire step (idle wire m) turns into letters
-- translated before.
viaN : (g : PG) (m : Wire) (us : List PG) (w : Word Sch) → every (avoids m) (g ∷ []) ≡ true →
       every (avoids m) us ≡ true → eqF 4 ⟦ g ∷ [] ⟧ᵖ* ⟦ us ⟧ᵖ* ≡ true → 4 ⊢ ι* us ≈ ι* (R* w) →
       4 ⊢ ι g ≈ ι* (R* w)
viaN g m us w hg hu hs e =
  trans (sym right-unit) (trans (narrowᵖ m (g ∷ []) us hg hu (eqF-sound 4 _ _ hs)) e)
'''

TWL1 = r'''twL₁ : List PG → Word Sch
twL₁ []      = ε
twL₁ (g ∷ u) = tw₁ g • twL₁ u

data Oks₁ : List PG → Set where
  []  : Oks₁ []
  _∷_ : {g : PG} {u : List PG} → 4 ⊢ ι g ≈ ι* (R* (tw₁ g)) → Oks₁ u → Oks₁ (g ∷ u)

okL₁ : (u : List PG) → Oks₁ u → 4 ⊢ ι* u ≈ ι* (R* (twL₁ u))
okL₁ []      []       = refl
okL₁ (g ∷ u) (e ∷ es) = trans (cong e (okL₁ u es)) (sym (ι*-++ (R* (tw₁ g)) (R* (twL₁ u))))
'''

END = r'''------------------------------------------------------------------------
-- Completeness

open RL.Complete R-rel tw tw-ok public using (complete)

-- Two circuits on four wires with the same function are equal.
complete₄ : {u v : Circuit 4} → ⟦ u ⟧ ≐ ⟦ v ⟧ → 4 ⊢ u ≈ v
complete₄ {u} {v} e =
  trans (pg-ok u) (trans (complete (pg u) (pg v) e′) (sym (pg-ok v)))
  where
  at : (w : Circuit 4) → ⟦ pg w ⟧ᵖ* ≐ ⟦ w ⟧
  at w = ≐-trans (≐-sym (ι*-sem (pg w))) (≐-sym (sound (pg-ok w)))
  e′ : ⟦ pg u ⟧ᵖ* ≐ ⟦ pg v ⟧ᵖ*
  e′ = ≐-trans (at u) (≐-trans e (≐-sym (at v)))
'''

if __name__ == '__main__':
    gen()

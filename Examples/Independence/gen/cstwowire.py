"""Write Examples/Independence/Clifford+CS/TwoWire.agda: the decoding of the
two-level generators in dimension 4 on two wires, the push lemmas, the
standard instances, and every instance of every relation as a
relabelling of its standard one (tl2.py has the mathematics).

    python3 cstwowire.py ../Clifford+CS/TwoWire.agda"""
import itertools
import sys
from collections import deque

import cscliff  # noqa: F401  (the spellings)
import tl2
import tlcs

TOKN = {'x0': 'x0ᵗ', 'x1': 'x1ᵗ', 's': 'sᵗ', 'c': 'cᵗ'}
FIN = ['₀', '₁', '₂', '₃']


def toks(ts):
    return '(' + ' ∷ '.join(TOKN[t] for t in ts) + (' ∷ [])' if ts else '[])')


def atom(g):
    if g[0] == 'i':
        return 'dᵃ %s' % FIN[g[1]]
    return '%sᵃ %s %s' % ('k' if g[0] == 'K' else 'x', FIN[g[1]], FIN[g[2]])


def atoms(gs):
    return '(' + ' ∷ '.join(atom(g) for g in gs) + (' ∷ [])' if gs else '[])')


def key(gs):
    return tuple(tl2.norm(g) for g in gs)


def relabel_all(gs, ts):
    for t in ts:
        gs = [tl2.relabel(g, t) for g in gs]
    return gs


def path(sl, sr, il, ir):
    """Tokens relabelling the standard instance to the instance."""
    target = (key(il), key(ir))
    q = deque([()])
    seen = {(key(sl), key(sr))}
    while q:
        ts = q.popleft()
        l, r = relabel_all(sl, ts), relabel_all(sr, ts)
        if (key(l), key(r)) == target and all(a == b or a[0] == 'X' for a, b in zip(l + r, il + ir)):
            return list(ts)
        for t in tl2.TOKS:
            n = ts + (t,)
            k = (key(relabel_all(sl, n)), key(relabel_all(sr, n)))
            if k not in seen:
                seen.add(k)
                q.append(n)
    raise SystemExit('no path to %r' % (il,))


RELS = {name: (l, r) for name, l, r in tlcs.relations(4)}


def by(name):
    fam = tl2.family(name)
    sl, sr = RELS[tl2.STD[fam]]
    il, ir = RELS[name]
    return 'by %s std-%s refl refl' % (toks(path(sl, sr, il, ir)), fam)


def lt(a, b):
    return 'l%d%d' % (a, b)


PAIRS = [(a, b) for a in range(4) for b in range(a + 1, 4)]


def clauses():
    out = []
    w = out.append
    # (1)–(3)
    for j in range(4):
        w('D₂-rel (TL.order-i {j = %s}) = %s' % (FIN[j], by('order-i-%d' % j)))
    for c, fam in [('order-X', 'order-X'), ('order-K', 'order-K')]:
        w('D₂-rel (TL.%s {j = j} {k = k} p) with lt4 j k p' % c)
        for a, b in PAIRS:
            w('... | %s = %s' % (lt(a, b), by('%s-%d%d' % (fam, a, b))))
    # (4)
    for j, k in itertools.product(range(4), repeat=2):
        rhs = '⊥-elim (ne refl)' if j == k else by('comm-ii-%d%d' % (j, k))
        w('D₂-rel (TL.comm-ii {j = %s} {k = %s} ne) = %s' % (FIN[j], FIN[k], rhs))
    # (5), (6)
    for c in ('comm-iX', 'comm-iK'):
        for j in range(4):
            w('D₂-rel (TL.%s {k = k} {l = l} {j = %s} p jk jl) with lt4 k l p' % (c, FIN[j]))
            for a, b in PAIRS:
                rhs = ('⊥-elim (jk refl)' if j == a else '⊥-elim (jl refl)' if j == b
                       else by('%s-%d%d%d' % (c, j, a, b)))
                w('... | %s = %s' % (lt(a, b), rhs))
    # (7)–(9)
    for c in ('comm-XX', 'comm-XK', 'comm-KK'):
        w('D₂-rel (TL.%s {j = j} {k = k} {l = l} {m = m} p q jl jm kl km) with lt4 j k p | lt4 l m q' % c)
        for (a, b), (x, y) in itertools.product(PAIRS, repeat=2):
            if a == x:
                rhs = '⊥-elim (jl refl)'
            elif a == y:
                rhs = '⊥-elim (jm refl)'
            elif b == x:
                rhs = '⊥-elim (kl refl)'
            elif b == y:
                rhs = '⊥-elim (km refl)'
            else:
                rhs = by('%s-%d%d%d%d' % (c, a, b, x, y))
            w('... | %s | %s = %s' % (lt(a, b), lt(x, y), rhs))
    # (10)
    w('D₂-rel (TL.swap-iX {j = j} {k = k} p) with lt4 j k p')
    for a, b in PAIRS:
        w('... | %s = %s' % (lt(a, b), by('swap-iX-%d%d' % (a, b))))
    # (11)–(14)
    for c in ('swap-XX', 'swap-XX′', 'swap-KX', 'swap-KX′'):
        w('D₂-rel (TL.%s {j = j} {k = k} {l = l} p q) with lt4 j k p | lt4 k l q' % c)
        for a, b in PAIRS:
            for x, y in PAIRS:
                if x == b:
                    w('... | %s | %s = %s' % (lt(a, b), lt(x, y), by('%s-%d%d%d' % (c, a, b, y))))
    # (15)–(18)
    for c in ('rel-13', 'rel-14', 'rel-15', 'rel-16'):
        w('D₂-rel (TL.%s {j = j} {k = k} p) with lt4 j k p' % c)
        for a, b in PAIRS:
            w('... | %s = %s' % (lt(a, b), by('%s-%d%d' % (c, a, b))))
    # (19)
    w('D₂-rel (TL.rel-17 {j = j} {k = k} {l = l} {m = m} jk lm jl km k≢l) with lt4 j k jk | lt4 l m lm')
    for (a, b), (x, y) in itertools.product(PAIRS, repeat=2):
        if not a < x:
            rhs = 'bad {a = %s} {b = %s} jl' % (FIN[a], FIN[x])
        elif not b < y:
            rhs = 'bad {a = %s} {b = %s} km' % (FIN[b], FIN[y])
        elif b == x:
            rhs = '⊥-elim (k≢l refl)'
        else:
            rhs = by('rel-17-%d%d%d%d' % (a, b, x, y))
        w('... | %s | %s = %s' % (lt(a, b), lt(x, y), rhs))
    return out


def tables():
    out = []
    w = out.append
    w('π : Tok → Fin 4 → Fin 4')
    for t in tl2.TOKS:
        for a in range(4):
            w('π %s %s = %s' % (TOKN[t], FIN[a], FIN[tl2.PERM[t][a]]))
    w('')
    w('⟦_⟧ᵃ : Atom → Circuit 2')
    for a in range(4):
        w('⟦ dᵃ %s ⟧ᵃ = cj %s zᵇ' % (FIN[a], toks(tl2.ATOM[('i', a)])))
    for a, b in itertools.product(range(4), repeat=2):
        if a == b:
            w('⟦ kᵃ %s %s ⟧ᵃ = ε' % (FIN[a], FIN[b]))
        else:
            w('⟦ kᵃ %s %s ⟧ᵃ = cj %s kᵇ' % (FIN[a], FIN[b], toks(tl2.ATOM[('K', a, b)])))
    for a, b in itertools.product(range(4), repeat=2):
        if a == b:
            w('⟦ xᵃ %s %s ⟧ᵃ = ε' % (FIN[a], FIN[b]))
        else:
            w('⟦ xᵃ %s %s ⟧ᵃ = cj %s cᵇ' % (FIN[a], FIN[b], toks(tl2.ATOM[tl2.norm(('X', a, b))])))
    w('')
    w('push : ∀ t a → 2 ⊢ tok t • ⟦ a ⟧ᵃ ≈ ⟦ a ^ᵃ t ⟧ᵃ • tok t')
    for t in tl2.TOKS:
        for a in range(4):
            w('push %s (dᵃ %s) = via %s refl refl' % (TOKN[t], FIN[a], tl2.pname(t, ('i', a))))
        for kind in ('kᵃ', 'xᵃ'):
            for a, b in itertools.product(range(4), repeat=2):
                if a == b:
                    w('push %s (%s %s %s) = triv' % (TOKN[t], kind, FIN[a], FIN[b]))
                else:
                    g = ('K' if kind == 'kᵃ' else 'X', a, b)
                    w('push %s (%s %s %s) = via %s refl refl' % (TOKN[t], kind, FIN[a], FIN[b],
                                                                 tl2.pname(t, g)))
    return out


def stds():
    out = []
    for fam, inst in tl2.STD.items():
        l, r = RELS[inst]
        out.append('std-%s : Std' % fam)
        out.append('std-%s = std %s %s (via STD-%s⁼ refl refl)' % (fam, atoms(l), atoms(r), fam))
        out.append('')
    return out


HEAD = '''------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level relations in dimension 4, decoded on two wires
--
-- Generated by Examples/Independence/gen (python3 cstwowire.py ...);
-- the mathematics is in tl2.py.  Index a = 2 x₀ + x₁, wire 0 the high
-- bit.  The tokens X₀, X₁, the swap and the CNOT from wire 0 onto
-- wire 1 permute the indices (π); the decoded generators are atoms,
-- conjugates of CS (the phase on index 3), of the controlled K on the
-- indices 2 and 3, and of the CNOT, by token words (cj).  Each token
-- passes each atom (push, from Clifford+CS.Derivations), so every
-- relation holds at every relabelling of its standard instance
-- (Clifford+CS.Transport), and D₂-rel reads each instance of each
-- relation as one.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.TwoWire where

open import Data.Empty using (⊥-elim)
import Data.Empty.Irrelevant as Irr
open import Data.Fin.Base using (Fin ; _<_ ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_ ; reverse)
open import Data.Nat.Base using (ℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Relation.Nullary.Decidable using (True ; toWitness)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

open import Examples.Independence.Clifford+CS.Syntactics
open import Examples.Independence.Clifford+CS.Kit using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf ; σσ⁼)
open import Examples.Independence.Clifford+CS.Derivations
open import Examples.Independence.Clifford+CS.Assemble using (module Decode)

private
  via : {w v : Circuit 2} (e : Eqn 2) →
        Assoc.to-list (2 VRel,_===_) w ≡ Assoc.to-list (2 VRel,_===_) ⟪ lhs⁼ e ⟫ →
        Assoc.to-list (2 VRel,_===_) ⟪ rhs⁼ e ⟫ ≡ Assoc.to-list (2 VRel,_===_) v →
        2 ⊢ w ≈ v
  via e p q =
    PB.trans (PP.by-assoc (2 VRel,_===_) p) (PB.trans (prf e) (PP.by-assoc (2 VRel,_===_) q))

  triv : {w : Circuit 2} → 2 ⊢ w • ε ≈ ε • w
  triv = PB.trans PB.right-unit (PB.sym PB.left-unit)

  -- a ≥ b refutes an irrelevant a < b.
  bad : ∀ {A : Set} {a b : Fin 4} → .(a < b) → {w : True (toℕ b ℕP.≤? toℕ a)} → A
  bad p {w} = Irr.⊥-elim (ℕP.<⇒≱ p (toWitness w))

------------------------------------------------------------------------
-- Tokens, bases and atoms

data Tok : Set where
  x0ᵗ x1ᵗ sᵗ cᵗ : Tok

tok : Tok → Circuit 2
tok x0ᵗ = X
tok x1ᵗ = X ↑
tok sᵗ  = σ
tok cᵗ  = H ↑ • CS • CS • H ↑

toks : List Tok → Circuit 2
toks []       = ε
toks (t ∷ ts) = tok t • toks ts

-- Conjugation by a token word.
cj : List Tok → Circuit 2 → Circuit 2
cj ts b = toks ts • b • toks (reverse ts)

-- CS, the controlled K on the indices 2 and 3, the CNOT.
zᵇ kᵇ cᵇ : Circuit 2
zᵇ = CS
kᵇ = CS • H ↑ • CS • H ↑ • CS • S†
cᵇ = H ↑ • CS • CS • H ↑

data Atom : Set where
  dᵃ    : Fin 4 → Atom
  kᵃ xᵃ : Fin 4 → Fin 4 → Atom

'''

MID = '''
-- An atom relabelled by a token's permutation.
_^ᵃ_ : Atom → Tok → Atom
dᵃ a   ^ᵃ t = dᵃ (π t a)
kᵃ a b ^ᵃ t = kᵃ (π t a) (π t b)
xᵃ a b ^ᵃ t = xᵃ (π t a) (π t b)

'''

TAIL1 = '''
tt : ∀ t → 2 ⊢ tok t • tok t ≈ ε
tt x0ᵗ = via Rx0⁼ refl refl
tt x1ᵗ = via Rx1⁼ refl refl
tt sᵗ  = via σσ⁼ refl refl
tt cᵗ  = via Rc⁼ refl refl

open import Examples.Independence.Clifford+CS.Transport tok ⟦_⟧ᵃ _^ᵃ_ tt push public

------------------------------------------------------------------------
-- The standard instances

'''

TAIL2 = '''------------------------------------------------------------------------
-- The decoding, and every relation decoded

d₂ : TL.Gen 4 → Circuit 2
d₂ (TL.i-gen a)     = ⟦ dᵃ a ⟧ᵃ
d₂ (TL.X-gen a b _) = ⟦ xᵃ a b ⟧ᵃ
d₂ (TL.K-gen a b _) = ⟦ kᵃ a b ⟧ᵃ

open Decode d₂ public renaming (Dʷ to D₂ʷ)

data Lt4 : Fin 4 → Fin 4 → Set where
  l01 : Lt4 ₀ ₁
  l02 : Lt4 ₀ ₂
  l03 : Lt4 ₀ ₃
  l12 : Lt4 ₁ ₂
  l13 : Lt4 ₁ ₃
  l23 : Lt4 ₂ ₃

lt4 : (a b : Fin 4) → .(a < b) → Lt4 a b
lt4 ₀ ₁ _ = l01
lt4 ₀ ₂ _ = l02
lt4 ₀ ₃ _ = l03
lt4 ₁ ₂ _ = l12
lt4 ₁ ₃ _ = l13
lt4 ₂ ₃ _ = l23
lt4 ₀ ₀ p = bad {a = ₀} {b = ₀} p
lt4 ₁ ₀ p = bad {a = ₁} {b = ₀} p
lt4 ₁ ₁ p = bad {a = ₁} {b = ₁} p
lt4 ₂ ₀ p = bad {a = ₂} {b = ₀} p
lt4 ₂ ₁ p = bad {a = ₂} {b = ₁} p
lt4 ₂ ₂ p = bad {a = ₂} {b = ₂} p
lt4 ₃ ₀ p = bad {a = ₃} {b = ₀} p
lt4 ₃ ₁ p = bad {a = ₃} {b = ₁} p
lt4 ₃ ₂ p = bad {a = ₃} {b = ₂} p
lt4 ₃ ₃ p = bad {a = ₃} {b = ₃} p

D₂-rel : ∀ {w v} → w TL.=== v → 2 ⊢ D₂ʷ w ≈ D₂ʷ v
'''


def main(path):
    src = HEAD + '\n'.join(tables()[:tables().index('') + 1]) + '\n'
    tb = tables()
    i1 = tb.index('')
    i2 = tb.index('', i1 + 1)
    src = (HEAD + '\n'.join(tb[:i1]) + '\n' + MID + '\n'.join(tb[i1 + 1:i2]) + '\n\n' +
           '\n'.join(tb[i2 + 1:]) + '\n' + TAIL1 + '\n'.join(stds()) + TAIL2 +
           '\n'.join(clauses()) + '\n')
    with open(path, 'w', encoding='utf-8', newline='\n') as f:
        f.write(src)
    print('written', path, src.count('\n'), 'lines')


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    main(sys.argv[1] if len(sys.argv) > 1 else '../Clifford+CS/TwoWire.agda')

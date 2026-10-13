"""Emit Tables.agda from tables.py's typed box relations."""
import sys
import tables as T

HEADER = r'''------------------------------------------------------------------------
-- Presentations of groups
--
-- The box relations of Appendix C as rewriting tables
--
-- A dirty gate in front of the clean boxes of a normal form is rewritten
-- into clean boxes followed by dirty gates (Lemma 4.2).  Each table
-- sends the boxes and the dirty gate to the new boxes and the dirty
-- gates that come out, listed in operator order (the head leaves last).
-- The dirty gates that come out are sorted by where they go next, which
-- is the label Definition 4.1 gives their wire:
--
--   W0      a gate on the lower input of a ladder (label 2): S, X, Z;
--   Post    what follows a clean box on wires 0 and 1 whose wire 1 goes
--           on into a ladder: H or S on wire 0 (label 1), which is done,
--           an input of the ladder, or CZ on wires 0 and 1, which
--           straddles it;
--   Post2   the same after clean boxes reaching wire 2, where wires 0 and
--           1 are done and wire 2 goes on;
--   CO, SCO what follows a C box, and the CZ that meets it: S or Z on
--           its wire (label 3), CZ below it, H or S below that;
--   O2, O3  what follows a D box, or two: gates on the wires above,
--           which are done (label 1), and S or Z on wire 0 (label 4),
--           which go on to the next D box or the E and F boxes.
--
-- Every kind also carries the scalar −ω, which commutes with everything.
-- An X or Z on a wire of label 1 is written out in H and S.  The tables
-- and the relations they stand for are generated from the transcription
-- of Appendix C (tables.py, emit_tables.py), which checks every typed
-- entry against the matrices.  One relation is misprinted in the paper:
-- Figure 25, third row (CZ through A₀₂ and B₀₂), has a single CZ in its
-- residual, not two; with two it is unsound.
--
-- The relations themselves are the fields of three records, by the
-- number of qutrits they act on, so that normalisation on n wires needs
-- only those on at most n: BoxRelations₁, BoxRelations₂, BoxRelations₃.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Tables where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine using (⟪_⟫)
open import Examples.Groups.Qutrit-Clifford.Axioms
  using (𝕟 ; h₀ ; h₁ ; h₂ ; s₀ ; s₁ ; s₂ ; c₀ ; c₁)
open import Examples.Groups.Qutrit-Clifford.NormalForm

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Dirty gates

-- Gates on a wire labelled 1 that the tables take as input.
data HS : Set where
  gH gS : HS

HSl : HS → List (Gen (₁₊ n))
HSl gH = h₀ ∷ []
HSl gS = s₀ ∷ []

data W0 : Set where
  iS iX iZ iν : W0

W0l : W0 → List (Gen (₁₊ n))
W0l iS = s₀ ∷ []
W0l iX = Xˡ
W0l iZ = Zˡ
W0l iν = 𝕟 ∷ []

W0ls : List W0 → List (Gen (₁₊ n))
W0ls = concatMap W0l

-- The input of a one-B rule: on its lower wire, or H, S on its upper.
data In1 : Set where
  w0 : W0 → In1
  w1 : HS → In1

In1l : In1 → List (Gen (₂₊ n))
In1l (w0 w) = W0l w
In1l (w1 h) = map _↥ (HSl h)

data Post : Set where
  pH pS : Post
  pin   : W0 → Post
  pstr  : Post
  pν    : Post

Pl : Post → List (Gen (₂₊ n))
Pl pH      = h₀ ∷ []
Pl pS      = s₀ ∷ []
Pl (pin w) = map _↥ (W0l w)
Pl pstr    = c₀ ∷ []
Pl pν      = 𝕟 ∷ []

Pls : List Post → List (Gen (₂₊ n))
Pls = concatMap Pl

-- Letters on wires 0 and 1.
data Q01 : Set where
  qh₀ qs₀ qh₁ qs₁ qc₀ : Q01

Ql : Q01 → Gen (₂₊ n)
Ql qh₀ = h₀
Ql qs₀ = s₀
Ql qh₁ = h₁
Ql qs₁ = s₁
Ql qc₀ = c₀

data Post2 : Set where
  qd   : Q01 → Post2
  qin  : W0 → Post2
  qstr : Post2
  qν   : Post2

P2l : Post2 → List (Gen (₃₊ n))
P2l (qd q)  = Ql q ∷ []
P2l (qin w) = map _↥ (map _↥ (W0l w))
P2l qstr    = c₁ ∷ []
P2l qν      = 𝕟 ∷ []

P2ls : List Post2 → List (Gen (₃₊ n))
P2ls = concatMap P2l

-- After a C box on its wire, and after the CZ that meets it.
data CO : Set where
  coS coZ coν : CO

COl : CO → List (Gen (₁₊ n))
COl coS = s₀ ∷ []
COl coZ = Zˡ
COl coν = 𝕟 ∷ []

COls : List CO → List (Gen (₁₊ n))
COls = concatMap COl

data SCO : Set where
  scC scH scS scν : SCO

SCOl : SCO → List (Gen (₂₊ n))
SCOl scC = c₀ ∷ []
SCOl scH = h₀ ∷ []
SCOl scS = s₀ ∷ []
SCOl scν = 𝕟 ∷ []

SCOls : List SCO → List (Gen (₂₊ n))
SCOls = concatMap SCOl

-- After a D box on wires 0, 1, and after two on wires 0 to 2.
data O2 : Set where
  oh₁ os₁ oS₀ oZ₀ oν : O2

O2l : O2 → List (Gen (₂₊ n))
O2l oh₁ = h₁ ∷ []
O2l os₁ = s₁ ∷ []
O2l oS₀ = s₀ ∷ []
O2l oZ₀ = Zˡ
O2l oν  = 𝕟 ∷ []

O2ls : List O2 → List (Gen (₂₊ n))
O2ls = concatMap O2l

data O3 : Set where
  o3h₁ o3s₁ o3h₂ o3s₂ o3c₁ o3S₀ o3Z₀ o3ν : O3

O3l : O3 → List (Gen (₃₊ n))
O3l o3h₁ = h₁ ∷ []
O3l o3s₁ = s₁ ∷ []
O3l o3h₂ = h₂ ∷ []
O3l o3s₂ = s₂ ∷ []
O3l o3c₁ = c₁ ∷ []
O3l o3S₀ = s₀ ∷ []
O3l o3Z₀ = Zˡ
O3l o3ν  = 𝕟 ∷ []

O3ls : List O3 → List (Gen (₃₊ n))
O3ls = concatMap O3l

------------------------------------------------------------------------
-- The tables

-- H or S in front of an A box (Figures 18, 19).
ruleA : AT → HS → AT × List W0
-- S, X or Z in front of the C box (Figure 20), and the scalar.
ruleC : CT → W0 → CT × List CO
-- S in front of the E box (Figure 21 (1)); Z passes it (Figure 21 (2)).
ruleE : ET → ET
-- Z in front of the F box (Figure 22).
ruleF : FT → FT
-- CZ with an A box on its upper wire (Figure 23): the A box stays, or
-- moves down a wire and a B box appears.
ruleAup : AT → (AT × List Post) ⊎ (AT × BT × List Post)
-- CZ in front of an A box and the B box after it (Figures 24-27): a new
-- A and B box, or the A box moves up a wire and the B box goes.
ruleAB : AT → BT → (AT × BT × List Post) ⊎ (AT × List Post)
-- An input of a B box (Figures 28-32), and the scalar.
ruleB : BT → In1 → BT × List Post
-- CZ straddling the C box's wire and the wire below (Figure 33).
ruleSC : CT → CT × List SCO
-- H or S on the lower input of a D box (Figures 34, 35).
ruleD : DT → HS → DT × List O2
-- CZ on the inputs of a D box (Figure 37).
ruleCD : DT → DT × List O2
-- CZ on the upper inputs of two B boxes (Figures 38-42).
ruleBB : BT → BT → BT × BT × List Post2
-- CZ straddling a B box's lower input and the wire below (Figure 43).
ruleS : BT → BT × List Post2
-- CZ on the lower inputs of two D boxes (Figure 44).
ruleDD : DT → DT → DT × DT × List O3

-- The right-hand sides.
Aupr : (AT × List Post) ⊎ (AT × BT × List Post) → List (Gen (₂₊ n))
Aupr (inj₁ (a , ps))     = Pls ps ++ map _↥ (Al a)
Aupr (inj₂ (a , b , ps)) = Pls ps ++ Bl b ++ Al a

ABr : (AT × BT × List Post) ⊎ (AT × List Post) → List (Gen (₂₊ n))
ABr (inj₁ (a , b , ps)) = Pls ps ++ Bl b ++ Al a
ABr (inj₂ (a , ps))     = Pls ps ++ map _↥ (Al a)

BBr : BT × BT × List Post2 → List (Gen (₃₊ n))
BBr (b₀ , b₁ , qs) = P2ls qs ++ map _↥ (Bl b₁) ++ Bl b₀

DDr : DT × DT × List O3 → List (Gen (₃₊ n))
DDr (d₁ , d₀ , os) = O3ls os ++ Dl d₀ ++ map _↥ (Dl d₁)'''

RECORDS = r'''
------------------------------------------------------------------------
-- The box relations

-- On one qutrit (Appendix C.2).
record BoxRelations₁ : Set where
  field
    ruleA-ok  : ∀ {n} (a : AT) (h : HS) →
      (₁₊ n) ⊢ ⟪ Al a ++ HSl h ⟫ ≈ ⟪ W0ls (proj₂ (ruleA a h)) ++ Al (proj₁ (ruleA a h)) ⟫
    ruleC-ok  : ∀ {n} (c : CT) (g : W0) →
      (₁₊ n) ⊢ ⟪ Cl c ++ W0l g ⟫ ≈ ⟪ COls (proj₂ (ruleC c g)) ++ Cl (proj₁ (ruleC c g)) ⟫
    ruleE-ok  : ∀ {n} (e : ET) → (₁₊ n) ⊢ ⟪ El e ++ s₀ ∷ [] ⟫ ≈ ⟪ El (ruleE e) ⟫
    ruleEZ-ok : ∀ {n} (e : ET) → (₁₊ n) ⊢ ⟪ El e ++ Zˡ ⟫ ≈ ⟪ Zˡ ++ El e ⟫
    ruleF-ok  : ∀ {n} (f : FT) → (₁₊ n) ⊢ ⟪ Fl f ++ Zˡ ⟫ ≈ ⟪ Fl (ruleF f) ⟫

-- On two qutrits (Appendix C.3), and the second equation of (4), which
-- writes the identity on two wires as a normal form's boxes.
record BoxRelations₂ : Set where
  field
    ruleAup-ok : ∀ {n} (a : AT) →
      (₂₊ n) ⊢ ⟪ map _↥ (Al a) ++ c₀ ∷ [] ⟫ ≈ ⟪ Aupr (ruleAup a) ⟫
    ruleAB-ok  : ∀ {n} (a : AT) (b : BT) →
      (₂₊ n) ⊢ ⟪ Bl b ++ Al a ++ c₀ ∷ [] ⟫ ≈ ⟪ ABr (ruleAB a b) ⟫
    ruleB-ok   : ∀ {n} (b : BT) (g : In1) →
      (₂₊ n) ⊢ ⟪ Bl b ++ In1l g ⟫ ≈ ⟪ Pls (proj₂ (ruleB b g)) ++ Bl (proj₁ (ruleB b g)) ⟫
    ruleSC-ok  : ∀ {n} (c : CT) →
      (₂₊ n) ⊢ ⟪ map _↥ (Cl c) ++ c₀ ∷ [] ⟫ ≈ ⟪ SCOls (proj₂ (ruleSC c)) ++ map _↥ (Cl (proj₁ (ruleSC c))) ⟫
    ruleD-ok   : ∀ {n} (d : DT) (h : HS) →
      (₂₊ n) ⊢ ⟪ Dl d ++ HSl h ⟫ ≈ ⟪ O2ls (proj₂ (ruleD d h)) ++ Dl (proj₁ (ruleD d h)) ⟫
    -- S or Z on the upper input of a D box (Figure 36).
    ruleS1D-ok : ∀ {n} (d : DT) → (₂₊ n) ⊢ ⟪ Dl d ++ s₁ ∷ [] ⟫ ≈ ⟪ s₀ ∷ Dl d ⟫
    ruleZ1D-ok : ∀ {n} (d : DT) → (₂₊ n) ⊢ ⟪ Dl d ++ map _↥ Zˡ ⟫ ≈ ⟪ Zˡ ++ Dl d ⟫
    ruleCD-ok  : ∀ {n} (d : DT) →
      (₂₊ n) ⊢ ⟪ Dl d ++ c₀ ∷ [] ⟫ ≈ ⟪ O2ls (proj₂ (ruleCD d)) ++ Dl (proj₁ (ruleCD d)) ⟫
    id₂-ok     : ∀ {n} → (₂₊ n) ⊢ ⟪ Dl D₀₁ ++ Bl B₀₀ ⟫ ≈ ⟪ [] ⟫

-- On three qutrits (Appendix C.4).
record BoxRelations₃ : Set where
  field
    ruleS-ok  : ∀ {n} (b : BT) →
      (₃₊ n) ⊢ ⟪ map _↥ (Bl b) ++ c₀ ∷ [] ⟫ ≈ ⟪ P2ls (proj₂ (ruleS b)) ++ map _↥ (Bl (proj₁ (ruleS b))) ⟫
    ruleBB-ok : ∀ {n} (b₀ b₁ : BT) →
      (₃₊ n) ⊢ ⟪ map _↥ (Bl b₁) ++ Bl b₀ ++ c₁ ∷ [] ⟫ ≈ ⟪ BBr (ruleBB b₀ b₁) ⟫
    ruleDD-ok : ∀ {n} (d₁ d₀ : DT) →
      (₃₊ n) ⊢ ⟪ Dl d₀ ++ map _↥ (Dl d₁) ++ c₀ ∷ [] ⟫ ≈ ⟪ DDr (ruleDD d₁ d₀) ⟫
'''

SUB = T.SUB

def emit(path):
    T.build()
    out = [HEADER]
    extra = {
        'ruleC': [(f'C{SUB[b]} iν', f'C{SUB[b]} , coν ∷ []') for b in range(3)],
        'ruleB': [(f'{b} (w0 iν)', f'{b} , pν ∷ []') for b in
                  ['B' + SUB[a] + SUB[c] for a in range(3) for c in range(3)]],
    }
    order = ['ruleA', 'ruleC', 'ruleE', 'ruleF', 'ruleAup', 'ruleAB', 'ruleB', 'ruleSC',
             'ruleD', 'ruleCD', 'ruleBB', 'ruleS', 'ruleDD']
    for fam in order:
        out.append('')
        for key, val in T.ENTRIES[fam] + extra.get(fam, []):
            out.append(f'{fam} {key} = {val}')
    out.append(RECORDS)
    open(path, 'w', encoding='utf-8').write('\n'.join(out))

if __name__ == '__main__':
    emit(sys.argv[1])
    print('wrote', sys.argv[1])

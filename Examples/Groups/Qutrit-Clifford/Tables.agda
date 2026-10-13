------------------------------------------------------------------------
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
DDr (d₁ , d₀ , os) = O3ls os ++ Dl d₀ ++ map _↥ (Dl d₁)

ruleA A₀₁ gH = A₁₀ , []
ruleA A₀₂ gH = A₂₀ , []
ruleA A₁₀ gH = A₀₂ , []
ruleA A₁₁ gH = A₁₂ , iν ∷ iν ∷ iν ∷ iν ∷ iν ∷ iX ∷ iX ∷ iS ∷ iS ∷ []
ruleA A₁₂ gH = A₂₂ , iν ∷ iS ∷ iX ∷ []
ruleA A₂₀ gH = A₀₁ , []
ruleA A₂₁ gH = A₁₁ , iν ∷ iS ∷ iX ∷ []
ruleA A₂₂ gH = A₂₁ , iν ∷ iν ∷ iν ∷ iν ∷ iν ∷ iX ∷ iX ∷ iS ∷ iS ∷ []
ruleA A₀₁ gS = A₀₁ , iS ∷ []
ruleA A₀₂ gS = A₀₂ , iZ ∷ iZ ∷ iS ∷ []
ruleA A₁₀ gS = A₁₁ , []
ruleA A₂₀ gS = A₂₂ , iX ∷ []
ruleA A₁₁ gS = A₁₂ , []
ruleA A₂₁ gS = A₂₀ , iX ∷ []
ruleA A₁₂ gS = A₁₀ , []
ruleA A₂₂ gS = A₂₁ , iX ∷ []

ruleC C₀ iS = C₀ , coS ∷ []
ruleC C₀ iZ = C₀ , coZ ∷ []
ruleC C₀ iX = C₁ , []
ruleC C₁ iS = C₁ , coν ∷ coν ∷ coZ ∷ coS ∷ []
ruleC C₁ iZ = C₁ , coν ∷ coν ∷ coZ ∷ []
ruleC C₁ iX = C₂ , []
ruleC C₂ iS = C₂ , coZ ∷ coZ ∷ coS ∷ []
ruleC C₂ iZ = C₂ , coν ∷ coν ∷ coν ∷ coν ∷ coZ ∷ []
ruleC C₂ iX = C₀ , []
ruleC C₀ iν = C₀ , coν ∷ []
ruleC C₁ iν = C₁ , coν ∷ []
ruleC C₂ iν = C₂ , coν ∷ []

ruleE E₀ = E₁
ruleE E₁ = E₂
ruleE E₂ = E₀

ruleF F₀ = F₂
ruleF F₁ = F₀
ruleF F₂ = F₁

ruleAup A₀₁ = inj₁ (A₀₁ , pstr ∷ [])
ruleAup A₀₂ = inj₁ (A₀₂ , pstr ∷ pstr ∷ [])
ruleAup A₁₀ = inj₂ (A₀₂ , B₁₀ , pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pS ∷ (pin iS) ∷ [])
ruleAup A₂₀ = inj₂ (A₀₁ , B₂₀ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pS ∷ (pin iS) ∷ [])
ruleAup A₁₁ = inj₂ (A₀₂ , B₁₁ , pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pS ∷ (pin iS) ∷ [])
ruleAup A₂₁ = inj₂ (A₀₁ , B₂₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pS ∷ (pin iS) ∷ [])
ruleAup A₁₂ = inj₂ (A₀₂ , B₁₂ , pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pS ∷ (pin iS) ∷ [])
ruleAup A₂₂ = inj₂ (A₀₁ , B₂₂ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pS ∷ (pin iS) ∷ [])

ruleAB A₀₁ B₀₀ = inj₁ (A₀₁ , B₀₀ , pstr ∷ [])
ruleAB A₀₁ B₀₁ = inj₁ (A₀₁ , B₀₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pstr ∷ [])
ruleAB A₀₁ B₀₂ = inj₁ (A₀₁ , B₀₂ , pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pstr ∷ pstr ∷ [])
ruleAB A₀₁ B₁₀ = inj₂ (A₁₀ , pν ∷ pν ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ (pin iS) ∷ (pin iS) ∷ [])
ruleAB A₀₁ B₂₀ = inj₁ (A₀₂ , B₂₀ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ [])
ruleAB A₀₁ B₁₁ = inj₂ (A₁₁ , pν ∷ pν ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ (pin iS) ∷ (pin iS) ∷ [])
ruleAB A₀₁ B₂₁ = inj₁ (A₀₂ , B₂₁ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ [])
ruleAB A₀₁ B₁₂ = inj₂ (A₁₂ , pν ∷ pν ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ (pin iS) ∷ (pin iS) ∷ [])
ruleAB A₀₁ B₂₂ = inj₁ (A₀₂ , B₂₂ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ [])
ruleAB A₀₂ B₀₀ = inj₁ (A₀₂ , B₀₀ , pstr ∷ pstr ∷ [])
ruleAB A₀₂ B₀₁ = inj₁ (A₀₂ , B₀₁ , pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pstr ∷ pstr ∷ [])
ruleAB A₀₂ B₀₂ = inj₁ (A₀₂ , B₀₂ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ [])
ruleAB A₀₂ B₁₀ = inj₁ (A₀₁ , B₁₀ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ [])
ruleAB A₀₂ B₂₀ = inj₂ (A₂₀ , pν ∷ pν ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iS) ∷ [])
ruleAB A₀₂ B₁₁ = inj₁ (A₀₁ , B₁₁ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ [])
ruleAB A₀₂ B₂₁ = inj₂ (A₂₁ , pν ∷ pν ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iS) ∷ [])
ruleAB A₀₂ B₁₂ = inj₁ (A₀₁ , B₁₂ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ [])
ruleAB A₀₂ B₂₂ = inj₂ (A₂₂ , pν ∷ pν ∷ pS ∷ pH ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iS) ∷ [])
ruleAB A₁₀ B₀₀ = inj₁ (A₁₀ , B₀₂ , pH ∷ pH ∷ pstr ∷ pstr ∷ [])
ruleAB A₁₀ B₀₁ = inj₁ (A₁₀ , B₀₀ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ [])
ruleAB A₁₀ B₀₂ = inj₁ (A₁₀ , B₀₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pstr ∷ [])
ruleAB A₁₀ B₁₀ = inj₁ (A₁₂ , B₁₂ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₀ B₂₀ = inj₁ (A₁₁ , B₂₂ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₁₀ B₁₁ = inj₁ (A₁₂ , B₁₀ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₀ B₂₁ = inj₁ (A₁₁ , B₂₀ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₁₀ B₁₂ = inj₁ (A₁₂ , B₁₁ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₀ B₂₂ = inj₁ (A₁₁ , B₂₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₁₁ B₀₀ = inj₁ (A₁₁ , B₀₂ , pH ∷ pH ∷ pstr ∷ pstr ∷ [])
ruleAB A₁₁ B₀₁ = inj₁ (A₁₁ , B₀₀ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ [])
ruleAB A₁₁ B₀₂ = inj₁ (A₁₁ , B₀₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pstr ∷ [])
ruleAB A₁₁ B₁₀ = inj₁ (A₁₀ , B₁₂ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₁ B₂₀ = inj₁ (A₁₂ , B₂₂ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₁₁ B₁₁ = inj₁ (A₁₀ , B₁₀ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₁ B₂₁ = inj₁ (A₁₂ , B₂₀ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₁₁ B₁₂ = inj₁ (A₁₀ , B₁₁ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₁ B₂₂ = inj₁ (A₁₂ , B₂₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₁₂ B₀₀ = inj₁ (A₁₂ , B₀₂ , pH ∷ pH ∷ pstr ∷ pstr ∷ [])
ruleAB A₁₂ B₀₁ = inj₁ (A₁₂ , B₀₀ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ [])
ruleAB A₁₂ B₀₂ = inj₁ (A₁₂ , B₀₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pstr ∷ [])
ruleAB A₁₂ B₁₀ = inj₁ (A₁₁ , B₁₂ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₂ B₂₀ = inj₁ (A₁₀ , B₂₂ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₁₂ B₁₁ = inj₁ (A₁₁ , B₁₀ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₂ B₂₁ = inj₁ (A₁₀ , B₂₀ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₁₂ B₁₂ = inj₁ (A₁₁ , B₁₁ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₁₂ B₂₂ = inj₁ (A₁₀ , B₂₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₀ B₀₀ = inj₁ (A₂₀ , B₀₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ [])
ruleAB A₂₀ B₀₁ = inj₁ (A₂₀ , B₀₂ , pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ [])
ruleAB A₂₀ B₀₂ = inj₁ (A₂₀ , B₀₀ , pH ∷ pH ∷ pstr ∷ pstr ∷ [])
ruleAB A₂₀ B₁₀ = inj₁ (A₂₂ , B₁₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₀ B₂₀ = inj₁ (A₂₁ , B₂₁ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₂₀ B₁₁ = inj₁ (A₂₂ , B₁₂ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₀ B₂₁ = inj₁ (A₂₁ , B₂₂ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₂₀ B₁₂ = inj₁ (A₂₂ , B₁₀ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₀ B₂₂ = inj₁ (A₂₁ , B₂₀ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₂₁ B₀₀ = inj₁ (A₂₁ , B₀₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ [])
ruleAB A₂₁ B₀₁ = inj₁ (A₂₁ , B₀₂ , pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ [])
ruleAB A₂₁ B₀₂ = inj₁ (A₂₁ , B₀₀ , pH ∷ pH ∷ pstr ∷ pstr ∷ [])
ruleAB A₂₁ B₁₀ = inj₁ (A₂₀ , B₁₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₁ B₂₀ = inj₁ (A₂₂ , B₂₁ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₂₁ B₁₁ = inj₁ (A₂₀ , B₁₂ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₁ B₂₁ = inj₁ (A₂₂ , B₂₂ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₂₁ B₁₂ = inj₁ (A₂₀ , B₁₀ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₁ B₂₂ = inj₁ (A₂₂ , B₂₀ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₂₂ B₀₀ = inj₁ (A₂₂ , B₀₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ [])
ruleAB A₂₂ B₀₁ = inj₁ (A₂₂ , B₀₂ , pν ∷ pν ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ [])
ruleAB A₂₂ B₀₂ = inj₁ (A₂₂ , B₀₀ , pH ∷ pH ∷ pstr ∷ pstr ∷ [])
ruleAB A₂₂ B₁₀ = inj₁ (A₂₁ , B₁₁ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₂ B₂₀ = inj₁ (A₂₀ , B₂₁ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₂₂ B₁₁ = inj₁ (A₂₁ , B₁₂ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₂ B₂₁ = inj₁ (A₂₀ , B₂₂ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])
ruleAB A₂₂ B₁₂ = inj₁ (A₂₁ , B₁₀ , pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ (pin iX) ∷ (pin iS) ∷ [])
ruleAB A₂₂ B₂₂ = inj₁ (A₂₀ , B₂₀ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ (pin iX) ∷ (pin iX) ∷ (pin iS) ∷ pstr ∷ pstr ∷ pH ∷ pS ∷ [])

ruleB B₀₀ (w1 gH) = B₀₀ , pstr ∷ pH ∷ pstr ∷ pstr ∷ []
ruleB B₀₁ (w1 gH) = B₁₀ , pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ pstr ∷ []
ruleB B₀₂ (w1 gH) = B₂₀ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ []
ruleB B₁₀ (w1 gH) = B₀₂ , pν ∷ pν ∷ pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ pstr ∷ []
ruleB B₁₁ (w1 gH) = B₁₂ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pS ∷ pS ∷ (pin iZ) ∷ (pin iZ) ∷ (pin iX) ∷ (pin iX) ∷ []
ruleB B₁₂ (w1 gH) = B₂₂ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pS ∷ (pin iZ) ∷ (pin iX) ∷ []
ruleB B₂₀ (w1 gH) = B₀₁ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pstr ∷ pstr ∷ []
ruleB B₂₁ (w1 gH) = B₁₁ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pS ∷ (pin iZ) ∷ (pin iX) ∷ []
ruleB B₂₂ (w1 gH) = B₂₁ , pν ∷ pν ∷ pν ∷ pν ∷ pν ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pS ∷ pS ∷ (pin iZ) ∷ (pin iZ) ∷ (pin iX) ∷ (pin iX) ∷ []
ruleB B₀₀ (w1 gS) = B₀₀ , pS ∷ []
ruleB B₀₁ (w1 gS) = B₀₁ , pS ∷ []
ruleB B₀₂ (w1 gS) = B₀₂ , pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ []
ruleB B₁₀ (w1 gS) = B₁₁ , []
ruleB B₂₀ (w1 gS) = B₂₂ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ (pin iZ) ∷ (pin iX) ∷ []
ruleB B₁₁ (w1 gS) = B₁₂ , []
ruleB B₂₁ (w1 gS) = B₂₀ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ (pin iZ) ∷ (pin iX) ∷ []
ruleB B₁₂ (w1 gS) = B₁₀ , []
ruleB B₂₂ (w1 gS) = B₂₁ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ (pin iZ) ∷ (pin iX) ∷ []
ruleB B₀₀ (w0 iS) = B₀₀ , (pin iS) ∷ []
ruleB B₀₀ (w0 iX) = B₀₀ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ (pin iX) ∷ []
ruleB B₀₁ (w0 iX) = B₀₁ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iX) ∷ []
ruleB B₀₂ (w0 iX) = B₀₂ , (pin iX) ∷ []
ruleB B₀₀ (w0 iZ) = B₀₀ , (pin iZ) ∷ []
ruleB B₀₁ (w0 iS) = B₀₁ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ pstr ∷ []
ruleB B₀₁ (w0 iZ) = B₀₁ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iZ) ∷ []
ruleB B₀₂ (w0 iS) = B₀₂ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ pstr ∷ []
ruleB B₀₂ (w0 iZ) = B₀₂ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iZ) ∷ []
ruleB B₁₀ (w0 iS) = B₁₀ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ pstr ∷ []
ruleB B₁₀ (w0 iZ) = B₁₀ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iZ) ∷ []
ruleB B₁₀ (w0 iX) = B₁₀ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ (pin iX) ∷ []
ruleB B₁₁ (w0 iS) = B₁₁ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ pstr ∷ []
ruleB B₁₁ (w0 iZ) = B₁₁ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iZ) ∷ []
ruleB B₁₁ (w0 iX) = B₁₁ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ (pin iX) ∷ []
ruleB B₁₂ (w0 iS) = B₁₂ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ pstr ∷ []
ruleB B₁₂ (w0 iZ) = B₁₂ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iZ) ∷ []
ruleB B₁₂ (w0 iX) = B₁₂ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ (pin iX) ∷ []
ruleB B₂₀ (w0 iS) = B₂₀ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ pstr ∷ []
ruleB B₂₀ (w0 iZ) = B₂₀ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iZ) ∷ []
ruleB B₂₀ (w0 iX) = B₂₀ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ (pin iX) ∷ []
ruleB B₂₁ (w0 iS) = B₂₁ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ pstr ∷ []
ruleB B₂₁ (w0 iZ) = B₂₁ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iZ) ∷ []
ruleB B₂₁ (w0 iX) = B₂₁ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ (pin iX) ∷ []
ruleB B₂₂ (w0 iS) = B₂₂ , pν ∷ pν ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iS) ∷ pstr ∷ []
ruleB B₂₂ (w0 iZ) = B₂₂ , pS ∷ pS ∷ pH ∷ pH ∷ pS ∷ pH ∷ pH ∷ (pin iZ) ∷ []
ruleB B₂₂ (w0 iX) = B₂₂ , pS ∷ pH ∷ pH ∷ pS ∷ pS ∷ pH ∷ pH ∷ (pin iX) ∷ []
ruleB B₀₀ (w0 iν) = B₀₀ , pν ∷ []
ruleB B₀₁ (w0 iν) = B₀₁ , pν ∷ []
ruleB B₀₂ (w0 iν) = B₀₂ , pν ∷ []
ruleB B₁₀ (w0 iν) = B₁₀ , pν ∷ []
ruleB B₁₁ (w0 iν) = B₁₁ , pν ∷ []
ruleB B₁₂ (w0 iν) = B₁₂ , pν ∷ []
ruleB B₂₀ (w0 iν) = B₂₀ , pν ∷ []
ruleB B₂₁ (w0 iν) = B₂₁ , pν ∷ []
ruleB B₂₂ (w0 iν) = B₂₂ , pν ∷ []

ruleSC C₀ = C₀ , scC ∷ []
ruleSC C₁ = C₁ , scS ∷ scS ∷ scH ∷ scH ∷ scS ∷ scH ∷ scH ∷ scC ∷ []
ruleSC C₂ = C₂ , scS ∷ scH ∷ scH ∷ scS ∷ scS ∷ scH ∷ scH ∷ scC ∷ []

ruleD D₀₀ gH = D₀₀ , oh₁ ∷ []
ruleD D₀₁ gH = D₁₀ , []
ruleD D₀₂ gH = D₂₀ , oh₁ ∷ oh₁ ∷ []
ruleD D₁₀ gH = D₀₂ , oh₁ ∷ oh₁ ∷ []
ruleD D₁₁ gH = D₁₂ , oν ∷ oν ∷ oν ∷ oν ∷ oν ∷ oZ₀ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ []
ruleD D₁₂ gH = D₂₂ , oν ∷ oZ₀ ∷ oZ₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ []
ruleD D₂₀ gH = D₀₁ , []
ruleD D₂₁ gH = D₁₁ , oν ∷ oZ₀ ∷ oZ₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ []
ruleD D₂₂ gH = D₂₁ , oν ∷ oν ∷ oν ∷ oν ∷ oν ∷ oZ₀ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ []
ruleD D₀₀ gS = D₀₀ , os₁ ∷ []
ruleD D₁₀ gS = D₁₁ , []
ruleD D₂₀ gS = D₂₂ , oZ₀ ∷ oZ₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ []
ruleD D₀₁ gS = D₀₁ , os₁ ∷ []
ruleD D₁₁ gS = D₁₂ , []
ruleD D₂₁ gS = D₂₀ , oZ₀ ∷ oZ₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ []
ruleD D₀₂ gS = D₀₂ , os₁ ∷ []
ruleD D₁₂ gS = D₁₀ , []
ruleD D₂₂ gS = D₂₁ , oZ₀ ∷ oZ₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ []

ruleCD D₀₀ = D₀₂ , []
ruleCD D₁₀ = D₁₂ , oν ∷ oν ∷ oν ∷ oν ∷ oZ₀ ∷ oS₀ ∷ oS₀ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ oh₁ ∷ []
ruleCD D₂₀ = D₂₂ , oν ∷ oν ∷ oZ₀ ∷ oZ₀ ∷ oS₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ oh₁ ∷ []
ruleCD D₀₁ = D₀₀ , []
ruleCD D₁₁ = D₁₀ , oν ∷ oν ∷ oν ∷ oν ∷ oZ₀ ∷ oS₀ ∷ oS₀ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ oh₁ ∷ []
ruleCD D₂₁ = D₂₀ , oν ∷ oν ∷ oZ₀ ∷ oZ₀ ∷ oS₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ oh₁ ∷ []
ruleCD D₀₂ = D₀₁ , []
ruleCD D₁₂ = D₁₁ , oν ∷ oν ∷ oν ∷ oν ∷ oZ₀ ∷ oS₀ ∷ oS₀ ∷ oh₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ oh₁ ∷ []
ruleCD D₂₂ = D₂₁ , oν ∷ oν ∷ oZ₀ ∷ oZ₀ ∷ oS₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ oh₁ ∷ oh₁ ∷ oh₁ ∷ []

ruleBB B₀₀ B₀₀ = B₀₀ , B₀₀ , (qd qc₀) ∷ []
ruleBB B₀₀ B₀₁ = B₀₀ , B₀₁ , (qd qc₀) ∷ []
ruleBB B₀₀ B₀₂ = B₀₀ , B₀₂ , (qd qc₀) ∷ (qd qc₀) ∷ []
ruleBB B₀₀ B₁₀ = B₀₂ , B₁₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₀ B₂₀ = B₀₁ , B₂₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₀ B₁₁ = B₀₂ , B₁₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₀ B₂₁ = B₀₁ , B₂₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₀ B₁₂ = B₀₂ , B₁₂ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₀ B₂₂ = B₀₁ , B₂₂ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₁ B₀₀ = B₀₁ , B₀₀ , (qd qc₀) ∷ []
ruleBB B₀₁ B₀₁ = B₀₁ , B₀₁ , (qd qc₀) ∷ []
ruleBB B₀₁ B₀₂ = B₀₁ , B₀₂ , (qd qc₀) ∷ (qd qc₀) ∷ []
ruleBB B₀₁ B₁₀ = B₀₀ , B₁₀ , qν ∷ qν ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ []
ruleBB B₀₁ B₂₀ = B₀₂ , B₂₀ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₁ B₁₁ = B₀₀ , B₁₁ , qν ∷ qν ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ []
ruleBB B₀₁ B₂₁ = B₀₂ , B₂₁ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₁ B₁₂ = B₀₀ , B₁₂ , qν ∷ qν ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ []
ruleBB B₀₁ B₂₂ = B₀₂ , B₂₂ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₂ B₀₀ = B₀₂ , B₀₀ , (qd qc₀) ∷ (qd qc₀) ∷ []
ruleBB B₀₂ B₀₁ = B₀₂ , B₀₁ , (qd qc₀) ∷ (qd qc₀) ∷ []
ruleBB B₀₂ B₀₂ = B₀₂ , B₀₂ , (qd qc₀) ∷ []
ruleBB B₀₂ B₁₀ = B₀₁ , B₁₀ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₂ B₂₀ = B₀₀ , B₂₀ , qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ []
ruleBB B₀₂ B₁₁ = B₀₁ , B₁₁ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₂ B₂₁ = B₀₀ , B₂₁ , qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ []
ruleBB B₀₂ B₁₂ = B₀₁ , B₁₂ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₀₂ B₂₂ = B₀₀ , B₂₂ , qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ []
ruleBB B₁₀ B₀₀ = B₁₀ , B₀₂ , qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₀ B₀₁ = B₁₀ , B₀₀ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₀ B₀₂ = B₁₀ , B₀₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₀ B₁₀ = B₁₂ , B₁₂ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₀ B₂₀ = B₁₁ , B₂₂ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₁₀ B₁₁ = B₁₂ , B₁₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₀ B₂₁ = B₁₁ , B₂₀ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₁₀ B₁₂ = B₁₂ , B₁₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₀ B₂₂ = B₁₁ , B₂₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₁₁ B₀₀ = B₁₁ , B₀₂ , qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₁ B₀₁ = B₁₁ , B₀₀ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₁ B₀₂ = B₁₁ , B₀₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₁ B₁₀ = B₁₀ , B₁₂ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₁ B₂₀ = B₁₂ , B₂₂ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₁₁ B₁₁ = B₁₀ , B₁₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₁ B₂₁ = B₁₂ , B₂₀ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₁₁ B₁₂ = B₁₀ , B₁₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₁ B₂₂ = B₁₂ , B₂₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₁₂ B₀₀ = B₁₂ , B₀₂ , qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₂ B₀₁ = B₁₂ , B₀₀ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₂ B₀₂ = B₁₂ , B₀₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₁₂ B₁₀ = B₁₁ , B₁₂ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₂ B₂₀ = B₁₀ , B₂₂ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₁₂ B₁₁ = B₁₁ , B₁₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₂ B₂₁ = B₁₀ , B₂₀ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₁₂ B₁₂ = B₁₁ , B₁₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₁₂ B₂₂ = B₁₀ , B₂₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₀ B₀₀ = B₂₀ , B₀₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ []
ruleBB B₂₀ B₀₁ = B₂₀ , B₀₂ , qν ∷ qν ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₂₀ B₀₂ = B₂₀ , B₀₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₂₀ B₁₀ = B₂₂ , B₁₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₀ B₂₀ = B₂₁ , B₂₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₂₀ B₁₁ = B₂₂ , B₁₂ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₀ B₂₁ = B₂₁ , B₂₂ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₂₀ B₁₂ = B₂₂ , B₁₀ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₀ B₂₂ = B₂₁ , B₂₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₂₁ B₀₀ = B₂₁ , B₀₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ []
ruleBB B₂₁ B₀₁ = B₂₁ , B₀₂ , qν ∷ qν ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₂₁ B₀₂ = B₂₁ , B₀₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₂₁ B₁₀ = B₂₀ , B₁₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₁ B₂₀ = B₂₂ , B₂₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₂₁ B₁₁ = B₂₀ , B₁₂ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₁ B₂₁ = B₂₂ , B₂₂ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₂₁ B₁₂ = B₂₀ , B₁₀ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₁ B₂₂ = B₂₂ , B₂₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₂₂ B₀₀ = B₂₂ , B₀₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ []
ruleBB B₂₂ B₀₁ = B₂₂ , B₀₂ , qν ∷ qν ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₂₂ B₀₂ = B₂₂ , B₀₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ []
ruleBB B₂₂ B₁₀ = B₂₁ , B₁₁ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₂ B₂₀ = B₂₀ , B₂₁ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₂₂ B₁₁ = B₂₁ , B₁₂ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₂ B₂₁ = B₂₀ , B₂₂ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []
ruleBB B₂₂ B₁₂ = B₂₁ , B₁₀ , (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qin iZ) ∷ (qin iX) ∷ []
ruleBB B₂₂ B₂₂ = B₂₀ , B₂₀ , qν ∷ qν ∷ qν ∷ qν ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qs₁) ∷ (qin iZ) ∷ (qin iZ) ∷ (qin iX) ∷ (qin iX) ∷ []

ruleS B₀₀ = B₀₀ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₀₁ = B₀₁ , (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₀₂ = B₀₂ , (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₁₀ = B₁₀ , (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₁₁ = B₁₁ , (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₁₂ = B₁₂ , (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₂₀ = B₂₀ , (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₂₁ = B₂₁ , (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₂₂ = B₂₂ , (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []

ruleDD D₀₀ D₀₀ = D₀₀ , D₀₀ , o3c₁ ∷ []
ruleDD D₀₀ D₁₀ = D₀₂ , D₁₀ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₀ D₂₀ = D₀₁ , D₂₀ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₀ D₀₀ = D₁₀ , D₀₂ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₀ D₁₀ = D₁₂ , D₁₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₀ D₂₀ = D₁₁ , D₂₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₀₀ = D₂₀ , D₀₁ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₁₀ = D₂₂ , D₁₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₂₀ = D₂₁ , D₂₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₀₀ D₀₁ = D₀₀ , D₀₁ , o3c₁ ∷ []
ruleDD D₀₀ D₁₁ = D₀₂ , D₁₁ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₀ D₂₁ = D₀₁ , D₂₁ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₀ D₀₁ = D₁₀ , D₀₀ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₀ D₁₁ = D₁₂ , D₁₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₀ D₂₁ = D₁₁ , D₂₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₀₁ = D₂₀ , D₀₂ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₁₁ = D₂₂ , D₁₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₂₁ = D₂₁ , D₂₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₀₀ D₀₂ = D₀₀ , D₀₂ , o3c₁ ∷ []
ruleDD D₀₀ D₁₂ = D₀₂ , D₁₂ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₀ D₂₂ = D₀₁ , D₂₂ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₀ D₀₂ = D₁₀ , D₀₁ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₀ D₁₂ = D₁₂ , D₁₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₀ D₂₂ = D₁₁ , D₂₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₀₂ = D₂₀ , D₀₀ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₁₂ = D₂₂ , D₁₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₀ D₂₂ = D₂₁ , D₂₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₀₁ D₀₀ = D₀₁ , D₀₀ , o3c₁ ∷ []
ruleDD D₀₁ D₁₀ = D₀₀ , D₁₀ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₁ D₂₀ = D₀₂ , D₂₀ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₁ D₀₀ = D₁₁ , D₀₂ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₁ D₁₀ = D₁₀ , D₁₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₁ D₂₀ = D₁₂ , D₂₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₀₀ = D₂₁ , D₀₁ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₁₀ = D₂₀ , D₁₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₂₀ = D₂₂ , D₂₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₀₁ D₀₁ = D₀₁ , D₀₁ , o3c₁ ∷ []
ruleDD D₀₁ D₁₁ = D₀₀ , D₁₁ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₁ D₂₁ = D₀₂ , D₂₁ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₁ D₀₁ = D₁₁ , D₀₀ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₁ D₁₁ = D₁₀ , D₁₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₁ D₂₁ = D₁₂ , D₂₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₀₁ = D₂₁ , D₀₂ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₁₁ = D₂₀ , D₁₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₂₁ = D₂₂ , D₂₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₀₁ D₀₂ = D₀₁ , D₀₂ , o3c₁ ∷ []
ruleDD D₀₁ D₁₂ = D₀₀ , D₁₂ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₁ D₂₂ = D₀₂ , D₂₂ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₁ D₀₂ = D₁₁ , D₀₁ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₁ D₁₂ = D₁₀ , D₁₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₁ D₂₂ = D₁₂ , D₂₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₀₂ = D₂₁ , D₀₀ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₁₂ = D₂₀ , D₁₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₁ D₂₂ = D₂₂ , D₂₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₀₂ D₀₀ = D₀₂ , D₀₀ , o3c₁ ∷ []
ruleDD D₀₂ D₁₀ = D₀₁ , D₁₀ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₂ D₂₀ = D₀₀ , D₂₀ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₂ D₀₀ = D₁₂ , D₀₂ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₂ D₁₀ = D₁₁ , D₁₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₂ D₂₀ = D₁₀ , D₂₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₀₀ = D₂₂ , D₀₁ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₁₀ = D₂₁ , D₁₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₂₀ = D₂₀ , D₂₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₀₂ D₀₁ = D₀₂ , D₀₁ , o3c₁ ∷ []
ruleDD D₀₂ D₁₁ = D₀₁ , D₁₁ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₂ D₂₁ = D₀₀ , D₂₁ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₂ D₀₁ = D₁₂ , D₀₀ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₂ D₁₁ = D₁₁ , D₁₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₂ D₂₁ = D₁₀ , D₂₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₀₁ = D₂₂ , D₀₂ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₁₁ = D₂₁ , D₁₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₂₁ = D₂₀ , D₂₂ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₀₂ D₀₂ = D₀₂ , D₀₂ , o3c₁ ∷ []
ruleDD D₀₂ D₁₂ = D₀₁ , D₁₂ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₀₂ D₂₂ = D₀₀ , D₂₂ , o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₁₂ D₀₂ = D₁₂ , D₀₁ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁₂ D₁₂ = D₁₁ , D₁₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₁₂ D₂₂ = D₁₀ , D₂₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₀₂ = D₂₂ , D₀₀ , o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₁₂ = D₂₁ , D₁₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3c₁ ∷ o3Z₀ ∷ o3Z₀ ∷ o3s₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []
ruleDD D₂₂ D₂₂ = D₂₀ , D₂₀ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3Z₀ ∷ o3s₁ ∷ o3h₁ ∷ o3h₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3h₂ ∷ o3h₂ ∷ []

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

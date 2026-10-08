------------------------------------------------------------------------
-- Presentations of groups
--
-- The rewrite rules of Figures 3 to 7 as rewriting tables
--
-- A dirty gate in front of clean gates of a normal form is rewritten
-- into clean gates followed by dirty gates (Lemma 5.2).  Each table
-- below sends the clean gates and the dirty gate to the new clean gates
-- and the dirty gates that come out, listed in operator order (the head
-- leaves last), and its companion `-ok` is the relation, one of the
-- supplement's equations (3.3) to (3.101).  The dirty gates that come
-- out are sorted by where they go next, which is the label the paper
-- gives their wire:
--
--   W0      a gate on the lower input of a ladder (label 2): S and X;
--   Post    what follows a clean gate on wires 0 and 1 whose wire 1
--           goes on into a ladder: H or S on wire 0 (label 1), which is
--           done, an input of the ladder, or CZ on wires 0 and 1, which
--           straddles it;
--   Post2   the same after clean gates reaching wire 2, where wires 0
--           and 1 are done and wire 2 goes on;
--   CO, SCO what follows a C gate, and the CZ that meets it: S on its
--           wire (label 3), CZ below it, S below that;
--   O2, O3  what follows a D gate, or two: gates on the wires above,
--           which are done (label 1), and S on wire 0 (label 4), which
--           goes on to the next D gate or the E gate.
--
-- Every kind also carries the scalar ω, which commutes with everything.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Tables where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Engine using (⟪_⟫ ; prf)
open import Examples.Groups.Qubit-Clifford.Axioms
  using (𝕨 ; h₀ ; h₁ ; h₂ ; s₀ ; s₁ ; s₂ ; c₀ ; c₁)
open import Examples.Groups.Qubit-Clifford.NormalForm
open import Examples.Groups.Qubit-Clifford.Relations.Rules

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The scalar passes a list of letters

ω-pass : (xs : List (Gen n)) → n ⊢ ⟪ xs ++ 𝕨 ∷ [] ⟫ ≈ ⟪ 𝕨 ∷ xs ⟫
ω-pass []       = PB.refl
ω-pass (x ∷ xs) = PB.trans (PB.cong PB.refl (ω-pass xs))
  (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong (PB.axiom (comm₀ ω-gate x)) PB.refl) PB.assoc))

------------------------------------------------------------------------
-- Dirty gates

-- Gates on a wire labelled 1.
data HS : Set where
  gH gS : HS

HSl : HS → List (Gen (₁₊ n))
HSl gH = h₀ ∷ []
HSl gS = s₀ ∷ []

-- The Pauli X = HSSH.
Xl : List (Gen (₁₊ n))
Xl = h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ []

data W0 : Set where
  iS iX iω : W0

W0l : W0 → List (Gen (₁₊ n))
W0l iS = s₀ ∷ []
W0l iX = Xl
W0l iω = 𝕨 ∷ []

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
  pω    : Post

Pl : Post → List (Gen (₂₊ n))
Pl pH      = h₀ ∷ []
Pl pS      = s₀ ∷ []
Pl (pin w) = map _↥ (W0l w)
Pl pstr    = c₀ ∷ []
Pl pω      = 𝕨 ∷ []

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
  qω   : Post2

P2l : Post2 → List (Gen (₃₊ n))
P2l (qd q)  = Ql q ∷ []
P2l (qin w) = map _↥ (map _↥ (W0l w))
P2l qstr    = c₁ ∷ []
P2l qω      = 𝕨 ∷ []

P2ls : List Post2 → List (Gen (₃₊ n))
P2ls = concatMap P2l

-- After a C gate on its wire, and after the CZ that meets it.
data CO : Set where
  coS coω : CO

COl : CO → List (Gen (₁₊ n))
COl coS = s₀ ∷ []
COl coω = 𝕨 ∷ []

data SCO : Set where
  scC scS scω : SCO

SCOl : SCO → List (Gen (₂₊ n))
SCOl scC = c₀ ∷ []
SCOl scS = s₀ ∷ []
SCOl scω = 𝕨 ∷ []

-- After a D gate on wires 0, 1, and after two on wires 0 to 2.
data O2 : Set where
  oh₁ os₁ oS₀ oω : O2

O2l : O2 → List (Gen (₂₊ n))
O2l oh₁ = h₁ ∷ []
O2l os₁ = s₁ ∷ []
O2l oS₀ = s₀ ∷ []
O2l oω  = 𝕨 ∷ []

data O3 : Set where
  o3h₁ o3s₁ o3h₂ o3s₂ o3c₁ o3S₀ o3ω : O3

O3l : O3 → List (Gen (₃₊ n))
O3l o3h₁ = h₁ ∷ []
O3l o3s₁ = s₁ ∷ []
O3l o3h₂ = h₂ ∷ []
O3l o3s₂ = s₂ ∷ []
O3l o3c₁ = c₁ ∷ []
O3l o3S₀ = s₀ ∷ []
O3l o3ω  = 𝕨 ∷ []

------------------------------------------------------------------------
-- The tables

-- H or S in front of an A gate (3.3)–(3.8).
ruleA : AT → HS → AT × List W0
-- CZ with an A gate on its upper wire (3.9)–(3.11): the A gate stays, or
-- moves down a wire and a B gate appears.
ruleAup : AT → (AT × List Post) ⊎ (AT × BT × List Post)
-- CZ in front of an A gate and the B gate after it (3.12)–(3.23): a new
-- A and B gate, or the A gate moves up a wire and the B gate goes.
ruleAB : AT → BT → (AT × BT × List Post) ⊎ (AT × List Post)
-- An input of a B gate (3.24)–(3.39).
ruleB : BT → In1 → BT × List Post
-- CZ straddling a B gate's lower input and the wire below (3.40)–(3.43).
ruleS : BT → BT × List Post2
-- An input of the C gate (3.44)–(3.47).
ruleC : CT → W0 → CT × List CO
-- CZ straddling the C gate's wire and the wire below (3.48), (3.49).
ruleSC : CT → CT × List SCO
-- CZ on the upper inputs of two B gates (3.50)–(3.65).
ruleBB : BT → BT → BT × BT × List Post2
-- H or S on the lower input of a D gate (3.66)–(3.73).
ruleD : DT → HS → DT × List O2
-- CZ on the inputs of a D gate (3.78)–(3.81).
ruleCD : DT → DT × List O2
-- CZ on the lower inputs of two D gates (3.86)–(3.101).
ruleDD : DT → DT → DT × DT × List O3
-- S in front of the E gate (3.82)–(3.85).
ruleE : ET → ET

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
DDr (d₁ , d₀ , os) = concatMap O3l os ++ Dl d₀ ++ map _↥ (Dl d₁)

ruleA-ok : (a : AT) (h : HS) →
  (₁₊ n) ⊢ ⟪ Al a ++ HSl h ⟫ ≈ ⟪ W0ls (proj₂ (ruleA a h)) ++ Al (proj₁ (ruleA a h)) ⟫
ruleAup-ok : (a : AT) →
  (₂₊ n) ⊢ ⟪ map _↥ (Al a) ++ c₀ ∷ [] ⟫ ≈ ⟪ Aupr (ruleAup a) ⟫
ruleAB-ok : (a : AT) (b : BT) →
  (₂₊ n) ⊢ ⟪ Bl b ++ Al a ++ c₀ ∷ [] ⟫ ≈ ⟪ ABr (ruleAB a b) ⟫
ruleB-ok : (b : BT) (g : In1) →
  (₂₊ n) ⊢ ⟪ Bl b ++ In1l g ⟫ ≈ ⟪ Pls (proj₂ (ruleB b g)) ++ Bl (proj₁ (ruleB b g)) ⟫
ruleS-ok : (b : BT) →
  (₃₊ n) ⊢ ⟪ map _↥ (Bl b) ++ c₀ ∷ [] ⟫ ≈ ⟪ P2ls (proj₂ (ruleS b)) ++ map _↥ (Bl (proj₁ (ruleS b))) ⟫
ruleC-ok : (c : CT) (g : W0) →
  (₁₊ n) ⊢ ⟪ Cl c ++ W0l g ⟫ ≈ ⟪ concatMap COl (proj₂ (ruleC c g)) ++ Cl (proj₁ (ruleC c g)) ⟫
ruleSC-ok : (c : CT) →
  (₂₊ n) ⊢ ⟪ map _↥ (Cl c) ++ c₀ ∷ [] ⟫ ≈ ⟪ concatMap SCOl (proj₂ (ruleSC c)) ++ map _↥ (Cl (proj₁ (ruleSC c))) ⟫
ruleBB-ok : (b₀ b₁ : BT) →
  (₃₊ n) ⊢ ⟪ map _↥ (Bl b₁) ++ Bl b₀ ++ c₁ ∷ [] ⟫ ≈ ⟪ BBr (ruleBB b₀ b₁) ⟫
ruleD-ok : (d : DT) (h : HS) →
  (₂₊ n) ⊢ ⟪ Dl d ++ HSl h ⟫ ≈ ⟪ concatMap O2l (proj₂ (ruleD d h)) ++ Dl (proj₁ (ruleD d h)) ⟫
-- S on the upper input of a D gate (3.74)–(3.77).
ruleS1D-ok : (d : DT) →
  (₂₊ n) ⊢ ⟪ Dl d ++ s₁ ∷ [] ⟫ ≈ ⟪ s₀ ∷ Dl d ⟫
ruleCD-ok : (d : DT) →
  (₂₊ n) ⊢ ⟪ Dl d ++ c₀ ∷ [] ⟫ ≈ ⟪ concatMap O2l (proj₂ (ruleCD d)) ++ Dl (proj₁ (ruleCD d)) ⟫
ruleDD-ok : (d₁ d₀ : DT) →
  (₃₊ n) ⊢ ⟪ Dl d₀ ++ map _↥ (Dl d₁) ++ c₀ ∷ [] ⟫ ≈ ⟪ DDr (ruleDD d₁ d₀) ⟫
ruleE-ok : (e : ET) →
  (₁₊ n) ⊢ ⟪ El e ++ s₀ ∷ [] ⟫ ≈ ⟪ El (ruleE e) ⟫

ruleA A₁ gH = A₂ , []
ruleA A₂ gH = A₁ , []
ruleA A₃ gH = A₃ , iω ∷ iS ∷ iS ∷ iS ∷ iX ∷ []
ruleA A₁ gS = A₁ , iS ∷ []
ruleA A₂ gS = A₃ , iω ∷ iS ∷ iS ∷ iS ∷ iX ∷ []
ruleA A₃ gS = A₂ , iω ∷ iS ∷ iS ∷ iS ∷ []

ruleAup A₁ = inj₁ (A₁ , pstr ∷ [])
ruleAup A₂ = inj₂ (A₁ , B₂ , pH ∷ pstr ∷ [])
ruleAup A₃ = inj₂ (A₁ , B₃ , pH ∷ (pin iS) ∷ (pin iS) ∷ (pin iS) ∷ pstr ∷ pH ∷ pS ∷ pH ∷ [])

ruleAB A₁ B₁ = inj₁ (A₁ , B₁ , pH ∷ pstr ∷ pH ∷ [])
ruleAB A₁ B₂ = inj₂ (A₂ , pstr ∷ pH ∷ [])
ruleAB A₁ B₃ = inj₂ (A₃ , pω ∷ pω ∷ pω ∷ pω ∷ pω ∷ pω ∷ pω ∷ pS ∷ pH ∷ pS ∷ (pin iS) ∷ pstr ∷ pH ∷ [])
ruleAB A₁ B₄ = inj₁ (A₁ , B₄ , pH ∷ pS ∷ pS ∷ pstr ∷ pH ∷ [])
ruleAB A₂ B₁ = inj₁ (A₂ , B₄ , [])
ruleAB A₂ B₂ = inj₁ (A₃ , B₃ , pω ∷ pω ∷ pω ∷ pω ∷ pω ∷ pω ∷ pS ∷ pH ∷ pS ∷ pS ∷ (pin iS) ∷ pstr ∷ pH ∷ [])
ruleAB A₂ B₃ = inj₁ (A₃ , B₂ , pω ∷ (pin iS) ∷ (pin iS) ∷ (pin iS) ∷ pstr ∷ pH ∷ (pin iX) ∷ [])
ruleAB A₂ B₄ = inj₁ (A₂ , B₁ , [])
ruleAB A₃ B₁ = inj₁ (A₃ , B₄ , pH ∷ pS ∷ pstr ∷ pH ∷ [])
ruleAB A₃ B₂ = inj₁ (A₂ , B₃ , pω ∷ pH ∷ pS ∷ pS ∷ (pin iS) ∷ (pin iS) ∷ (pin iS) ∷ pstr ∷ (pin iX) ∷ [])
ruleAB A₃ B₃ = inj₁ (A₂ , B₂ , pω ∷ pH ∷ pS ∷ pS ∷ pS ∷ (pin iS) ∷ (pin iS) ∷ (pin iS) ∷ pstr ∷ pH ∷ pS ∷ pH ∷ [])
ruleAB A₃ B₄ = inj₁ (A₃ , B₁ , pH ∷ pS ∷ pS ∷ pS ∷ pstr ∷ pH ∷ [])

ruleB B₁ (w1 gH) = B₁ , pH ∷ []
ruleB B₂ (w1 gH) = B₄ , []
ruleB B₃ (w1 gH) = B₃ , pS ∷ pH ∷ pS ∷ pS ∷ pS ∷ (pin iX) ∷ []
ruleB B₄ (w1 gH) = B₂ , []
ruleB B₁ (w1 gS) = B₁ , pH ∷ pS ∷ pH ∷ []
ruleB B₂ (w1 gS) = B₃ , pS ∷ pH ∷ pS ∷ pS ∷ pS ∷ (pin iX) ∷ []
ruleB B₃ (w1 gS) = B₂ , pS ∷ pH ∷ pS ∷ []
ruleB B₄ (w1 gS) = B₄ , pH ∷ pS ∷ pH ∷ []
ruleB B₁ (w0 iS) = B₁ , (pin iS) ∷ []
ruleB B₂ (w0 iS) = B₂ , pH ∷ pS ∷ (pin iS) ∷ pstr ∷ pH ∷ []
ruleB B₃ (w0 iS) = B₃ , pH ∷ pS ∷ (pin iS) ∷ pstr ∷ pH ∷ []
ruleB B₄ (w0 iS) = B₄ , pH ∷ pS ∷ (pin iS) ∷ pstr ∷ pH ∷ []
ruleB B₁ (w0 iX) = B₁ , (pin iX) ∷ []
ruleB B₂ (w0 iX) = B₂ , (pin iX) ∷ []
ruleB B₃ (w0 iX) = B₃ , (pin iX) ∷ []
ruleB B₄ (w0 iX) = B₄ , (pin iX) ∷ []
ruleB b (w0 iω) = b , pω ∷ []

ruleS B₁ = B₁ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₂ = B₂ , qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₃ = B₃ , qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []
ruleS B₄ = B₄ , qstr ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ qstr ∷ []

ruleC C₁ iX = C₂ , []
ruleC C₂ iX = C₁ , []
ruleC C₁ iS = C₁ , coS ∷ []
ruleC C₂ iS = C₂ , coω ∷ coω ∷ coS ∷ coS ∷ coS ∷ []
ruleC c iω = c , coω ∷ []

ruleSC C₁ = C₁ , scC ∷ []
ruleSC C₂ = C₂ , scS ∷ scS ∷ scC ∷ []

ruleBB B₁ B₁ = B₁ , B₁ , (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ []
ruleBB B₁ B₂ = B₄ , B₂ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₁ B₃ = B₄ , B₃ , qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₁ B₄ = B₁ , B₄ , (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ []
ruleBB B₂ B₁ = B₂ , B₄ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₂ B₂ = B₃ , B₃ , qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ []
ruleBB B₂ B₃ = B₃ , B₂ , qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ (qd qs₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qin iX) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ []
ruleBB B₂ B₄ = B₂ , B₁ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₃ B₁ = B₃ , B₄ , qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ []
ruleBB B₃ B₂ = B₂ , B₃ , qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qin iX) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ []
ruleBB B₃ B₃ = B₂ , B₂ , (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qc₀) ∷ []
ruleBB B₃ B₄ = B₃ , B₁ , qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qs₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ []
ruleBB B₄ B₁ = B₄ , B₁ , (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ []
ruleBB B₄ B₂ = B₁ , B₂ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₄ B₃ = B₁ , B₃ , qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ qω ∷ (qd qh₀) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qs₁) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₄ B₄ = B₄ , B₄ , (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ []

ruleD D₁ gH = D₁ , oh₁ ∷ []
ruleD D₂ gH = D₄ , []
ruleD D₃ gH = D₃ , oS₀ ∷ oS₀ ∷ os₁ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ os₁ ∷ []
ruleD D₄ gH = D₂ , []
ruleD D₁ gS = D₁ , oh₁ ∷ os₁ ∷ oh₁ ∷ []
ruleD D₂ gS = D₃ , oS₀ ∷ oS₀ ∷ os₁ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ os₁ ∷ []
ruleD D₃ gS = D₂ , os₁ ∷ oh₁ ∷ os₁ ∷ []
ruleD D₄ gS = D₄ , oh₁ ∷ os₁ ∷ oh₁ ∷ []

ruleCD D₁ = D₄ , []
ruleCD D₂ = D₃ , oS₀ ∷ oS₀ ∷ oS₀ ∷ oh₁ ∷ os₁ ∷ os₁ ∷ os₁ ∷ []
ruleCD D₃ = D₂ , oS₀ ∷ os₁ ∷ oh₁ ∷ []
ruleCD D₄ = D₁ , []

ruleE E₁ = E₂
ruleE E₂ = E₃
ruleE E₃ = E₄
ruleE E₄ = E₁

ruleDD D₁ D₁ = D₁ , D₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₁ D₂ = D₄ , D₂ , o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁ D₃ = D₄ , D₃ , o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3s₁ ∷ o3h₁ ∷ o3s₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₁ D₄ = D₁ , D₄ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₂ D₁ = D₂ , D₄ , o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₂ D₂ = D₃ , D₃ , o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3s₁ ∷ o3s₂ ∷ o3c₁ ∷ o3h₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₂ ∷ o3s₂ ∷ o3h₂ ∷ []
ruleDD D₂ D₃ = D₃ , D₂ , o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3S₀ ∷ o3S₀ ∷ o3s₁ ∷ o3h₁ ∷ o3s₂ ∷ o3c₁ ∷ o3h₂ ∷ o3s₂ ∷ o3h₂ ∷ []
ruleDD D₂ D₄ = D₂ , D₁ , o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₃ D₁ = D₃ , D₄ , o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3s₂ ∷ o3c₁ ∷ o3h₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₁ ∷ []
ruleDD D₃ D₂ = D₂ , D₃ , o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3S₀ ∷ o3S₀ ∷ o3s₁ ∷ o3s₂ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3s₁ ∷ o3h₁ ∷ []
ruleDD D₃ D₃ = D₂ , D₂ , o3s₁ ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3c₁ ∷ []
ruleDD D₃ D₄ = D₃ , D₁ , o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3h₁ ∷ o3s₂ ∷ o3h₂ ∷ o3s₂ ∷ o3c₁ ∷ o3h₂ ∷ o3s₂ ∷ o3h₂ ∷ o3h₁ ∷ []
ruleDD D₄ D₁ = D₄ , D₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₄ D₂ = D₁ , D₂ , o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₄ D₃ = D₁ , D₃ , o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3ω ∷ o3s₁ ∷ o3h₁ ∷ o3s₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3s₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₄ D₄ = D₄ , D₄ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3h₂ ∷ []

ruleA-ok A₁ gH = prf Eq3-3
ruleA-ok A₂ gH = prf Eq3-4
ruleA-ok A₃ gH = prf Eq3-5
ruleA-ok A₁ gS = prf Eq3-6
ruleA-ok A₂ gS = prf Eq3-7
ruleA-ok A₃ gS = prf Eq3-8

ruleAup-ok A₁ = prf Eq3-9
ruleAup-ok A₂ = prf Eq3-10
ruleAup-ok A₃ = prf Eq3-11

ruleAB-ok A₁ B₁ = prf Eq3-12
ruleAB-ok A₁ B₂ = prf Eq3-13
ruleAB-ok A₁ B₃ = prf Eq3-14
ruleAB-ok A₁ B₄ = prf Eq3-15
ruleAB-ok A₂ B₁ = prf Eq3-16
ruleAB-ok A₂ B₂ = prf Eq3-17
ruleAB-ok A₂ B₃ = prf Eq3-18
ruleAB-ok A₂ B₄ = prf Eq3-19
ruleAB-ok A₃ B₁ = prf Eq3-20
ruleAB-ok A₃ B₂ = prf Eq3-21
ruleAB-ok A₃ B₃ = prf Eq3-22
ruleAB-ok A₃ B₄ = prf Eq3-23

ruleB-ok B₁ (w1 gH) = prf Eq3-24
ruleB-ok B₂ (w1 gH) = prf Eq3-25
ruleB-ok B₃ (w1 gH) = prf Eq3-26
ruleB-ok B₄ (w1 gH) = prf Eq3-27
ruleB-ok B₁ (w1 gS) = prf Eq3-28
ruleB-ok B₂ (w1 gS) = prf Eq3-29
ruleB-ok B₃ (w1 gS) = prf Eq3-30
ruleB-ok B₄ (w1 gS) = prf Eq3-31
ruleB-ok B₁ (w0 iS) = prf Eq3-32
ruleB-ok B₂ (w0 iS) = prf Eq3-33
ruleB-ok B₃ (w0 iS) = prf Eq3-34
ruleB-ok B₄ (w0 iS) = prf Eq3-35
ruleB-ok B₁ (w0 iX) = prf Eq3-36
ruleB-ok B₂ (w0 iX) = prf Eq3-37
ruleB-ok B₃ (w0 iX) = prf Eq3-38
ruleB-ok B₄ (w0 iX) = prf Eq3-39
ruleB-ok B₁ (w0 iω) = ω-pass (Bl B₁)
ruleB-ok B₂ (w0 iω) = ω-pass (Bl B₂)
ruleB-ok B₃ (w0 iω) = ω-pass (Bl B₃)
ruleB-ok B₄ (w0 iω) = ω-pass (Bl B₄)

ruleS-ok B₁ = prf Eq3-40
ruleS-ok B₂ = prf Eq3-41
ruleS-ok B₃ = prf Eq3-42
ruleS-ok B₄ = prf Eq3-43

ruleC-ok C₁ iX = prf Eq3-44
ruleC-ok C₂ iX = prf Eq3-45
ruleC-ok C₁ iS = prf Eq3-46
ruleC-ok C₂ iS = prf Eq3-47
ruleC-ok C₁ iω = ω-pass (Cl C₁)
ruleC-ok C₂ iω = ω-pass (Cl C₂)

ruleSC-ok C₁ = prf Eq3-48
ruleSC-ok C₂ = prf Eq3-49

ruleBB-ok B₁ B₁ = prf Eq3-50
ruleBB-ok B₁ B₂ = prf Eq3-51
ruleBB-ok B₁ B₃ = prf Eq3-52
ruleBB-ok B₁ B₄ = prf Eq3-53
ruleBB-ok B₂ B₁ = prf Eq3-54
ruleBB-ok B₂ B₂ = prf Eq3-55
ruleBB-ok B₂ B₃ = prf Eq3-56
ruleBB-ok B₂ B₄ = prf Eq3-57
ruleBB-ok B₃ B₁ = prf Eq3-58
ruleBB-ok B₃ B₂ = prf Eq3-59
ruleBB-ok B₃ B₃ = prf Eq3-60
ruleBB-ok B₃ B₄ = prf Eq3-61
ruleBB-ok B₄ B₁ = prf Eq3-62
ruleBB-ok B₄ B₂ = prf Eq3-63
ruleBB-ok B₄ B₃ = prf Eq3-64
ruleBB-ok B₄ B₄ = prf Eq3-65

ruleD-ok D₁ gH = prf Eq3-66
ruleD-ok D₂ gH = prf Eq3-67
ruleD-ok D₃ gH = prf Eq3-68
ruleD-ok D₄ gH = prf Eq3-69
ruleD-ok D₁ gS = prf Eq3-70
ruleD-ok D₂ gS = prf Eq3-71
ruleD-ok D₃ gS = prf Eq3-72
ruleD-ok D₄ gS = prf Eq3-73

ruleS1D-ok D₁ = prf Eq3-74
ruleS1D-ok D₂ = prf Eq3-75
ruleS1D-ok D₃ = prf Eq3-76
ruleS1D-ok D₄ = prf Eq3-77

ruleCD-ok D₁ = prf Eq3-78
ruleCD-ok D₂ = prf Eq3-79
ruleCD-ok D₃ = prf Eq3-80
ruleCD-ok D₄ = prf Eq3-81

ruleE-ok E₁ = prf Eq3-82
ruleE-ok E₂ = prf Eq3-83
ruleE-ok E₃ = prf Eq3-84
ruleE-ok E₄ = prf Eq3-85

ruleDD-ok D₁ D₁ = prf Eq3-86
ruleDD-ok D₁ D₂ = prf Eq3-87
ruleDD-ok D₁ D₃ = prf Eq3-88
ruleDD-ok D₁ D₄ = prf Eq3-89
ruleDD-ok D₂ D₁ = prf Eq3-90
ruleDD-ok D₂ D₂ = prf Eq3-91
ruleDD-ok D₂ D₃ = prf Eq3-92
ruleDD-ok D₂ D₄ = prf Eq3-93
ruleDD-ok D₃ D₁ = prf Eq3-94
ruleDD-ok D₃ D₂ = prf Eq3-95
ruleDD-ok D₃ D₃ = prf Eq3-96
ruleDD-ok D₃ D₄ = prf Eq3-97
ruleDD-ok D₄ D₁ = prf Eq3-98
ruleDD-ok D₄ D₂ = prf Eq3-99
ruleDD-ok D₄ D₃ = prf Eq3-100
ruleDD-ok D₄ D₄ = prf Eq3-101

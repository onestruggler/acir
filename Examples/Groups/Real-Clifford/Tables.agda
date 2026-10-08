------------------------------------------------------------------------
-- Presentations of groups
--
-- The typed relations (Appendix B) as rewriting tables
--
-- A dirty gate in front of clean gates of a normal form is rewritten
-- into clean gates followed by dirty gates (Section 5.1).  Each table
-- below sends the types of the clean gates and the dirty gate to the
-- new types and the dirty gates that come out, listed in operator order
-- (the head leaves last), and its companion `-ok` is the relation,
-- taken from Relations.Rules.  The dirty gates that come out are sorted
-- by where they go next:
--
--   W0 t    a gate on the lower input of a ladder of type t: Z, X, and
--           H on a double wire;
--   SIn t   a gate on wires 0 and 1 that enters a ladder starting on
--           wire 1: CZ into a single ladder, CXZ into a double one;
--   Post u  what follows a clean gate on wires 0 and 1 whose wire 1
--           goes on into a ladder of type u: H or Z on wire 0, which is
--           done, an input of the ladder, or a straddling gate;
--   Post2 u the same after clean gates reaching wire 2, where wires 0
--           and 1 are done and wire 2 goes on;
--   O2, O3  what follows a D gate, or two: gates on the wires above,
--           which are done, and Z on wire 0, which meets the E gate.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Tables where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine using (⟪_⟫ ; prf)
open import Examples.Groups.Real-Clifford.Axioms
  using (𝕞 ; h₀ ; h₁ ; h₂ ; z₀ ; z₁ ; z₂ ; c₀ ; c₁)
open import Examples.Groups.Real-Clifford.NormalForm
open import Examples.Groups.Real-Clifford.Relations.Rules

private
  variable
    n : ℕ
    t u v : Ty

------------------------------------------------------------------------
-- Dirty gates

data HZ : Set where
  gH gZ : HZ

HZl : HZ → List (Gen (₁₊ n))
HZl gH = h₀ ∷ []
HZl gZ = z₀ ∷ []

data W0 : Ty → Set where
  iZ iX : W0 t
  iH    : W0 db

W0l : W0 t → List (Gen (₁₊ n))
W0l iZ = z₀ ∷ []
W0l iX = Xl
W0l iH = h₀ ∷ []

W0ls : List (W0 t) → List (Gen (₁₊ n))
W0ls = concatMap W0l

-- The input of a one-B rule: on its lower wire, or H, Z on its upper.
data In1 (t : Ty) : Set where
  w0 : W0 t → In1 t
  w1 : HZ → In1 t

In1l : In1 t → List (Gen (₂₊ n))
In1l (w0 w) = W0l w
In1l (w1 h) = map _↥ (HZl h)

data SIn : Ty → Set where
  sCZ  : SIn sg
  sXZC : SIn db

Sl : SIn t → List (Gen (₂₊ n))
Sl sCZ  = c₀ ∷ []
Sl sXZC = XZCl

data Post (u : Ty) : Set where
  pH pZ : Post u
  pin   : W0 u → Post u
  pstr  : SIn u → Post u
  pneg  : Post u

Pl : Post u → List (Gen (₂₊ n))
Pl pH       = h₀ ∷ []
Pl pZ       = z₀ ∷ []
Pl (pin w)  = map _↥ (W0l w)
Pl (pstr s) = Sl s
Pl pneg     = 𝕞 ∷ []

Pls : List (Post u) → List (Gen (₂₊ n))
Pls = concatMap Pl

-- Letters on wires 0 and 1.
data Q01 : Set where
  qh₀ qz₀ qh₁ qz₁ qc₀ : Q01

Ql : Q01 → Gen (₂₊ n)
Ql qh₀ = h₀
Ql qz₀ = z₀
Ql qh₁ = h₁
Ql qz₁ = z₁
Ql qc₀ = c₀

data Post2 (u : Ty) : Set where
  qd   : Q01 → Post2 u
  qin  : W0 u → Post2 u
  qstr : SIn u → Post2 u
  qneg : Post2 u

P2l : Post2 u → List (Gen (₃₊ n))
P2l (qd q)   = Ql q ∷ []
P2l (qin w)  = map _↥ (map _↥ (W0l w))
P2l (qstr s) = map _↥ (Sl s)
P2l qneg     = 𝕞 ∷ []

P2ls : List (Post2 u) → List (Gen (₃₊ n))
P2ls = concatMap P2l

-- After a C gate on its wire, and after the CZ that meets it.
data CO : Set where
  coZ coneg : CO

COl : CO → List (Gen (₁₊ n))
COl coZ   = z₀ ∷ []
COl coneg = 𝕞 ∷ []

data SCO : Set where
  scC scZ scneg : SCO

SCOl : SCO → List (Gen (₂₊ n))
SCOl scC   = c₀ ∷ []
SCOl scZ   = z₀ ∷ []
SCOl scneg = 𝕞 ∷ []

-- After a D gate on wires 0, 1, and after two on wires 0 to 2.
data O2 : Set where
  oh₁ oz₁ oZ₀ oneg : O2

O2l : O2 → List (Gen (₂₊ n))
O2l oh₁  = h₁ ∷ []
O2l oz₁  = z₁ ∷ []
O2l oZ₀  = z₀ ∷ []
O2l oneg = 𝕞 ∷ []

data O3 : Set where
  o3h₁ o3z₁ o3h₂ o3z₂ o3c₁ o3Z₀ o3neg : O3

O3l : O3 → List (Gen (₃₊ n))
O3l o3h₁  = h₁ ∷ []
O3l o3z₁  = z₁ ∷ []
O3l o3h₂  = h₂ ∷ []
O3l o3z₂  = z₂ ∷ []
O3l o3c₁  = c₁ ∷ []
O3l o3Z₀  = z₀ ∷ []
O3l o3neg = 𝕞 ∷ []

------------------------------------------------------------------------
-- The tables

ruleA : AT t → HZ → AT t × List (W0 t)
ruleAup : AT t → (AT t × List (Post t)) ⊎ (Σ Ty λ t' → AT t' × BT t' t × List (Post t))
ruleAB : AT t → BT t u → (Σ Ty λ t' → AT t' × BT t' u × List (Post u)) ⊎ (AT u × List (Post u))
ruleB : BT t u → In1 t → BT t u × List (Post u)
ruleBB : BT t v → BT v u → Σ Ty λ v' → BT t v' × BT v' u × List (Post2 u)
ruleS : SIn t → BT t u → BT t u × List (Post2 u)
ruleC : CT → W0 sg → CT × List CO
ruleSC : CT → CT × List SCO
ruleD : DT → HZ → DT × List O2
ruleCD : DT → DT × List O2
ruleDD : DT → DT → DT × DT × List O3
ruleE : ET → ET

-- The right-hand sides.
Aupr : (AT t × List (Post t)) ⊎ (Σ Ty λ t' → AT t' × BT t' t × List (Post t)) → List (Gen (₂₊ n))
Aupr (inj₁ (a , ps))         = Pls ps ++ map _↥ (Al a)
Aupr (inj₂ (_ , a , b , ps)) = Pls ps ++ Bl b ++ Al a

ABr : (Σ Ty λ t' → AT t' × BT t' u × List (Post u)) ⊎ (AT u × List (Post u)) → List (Gen (₂₊ n))
ABr (inj₁ (_ , a , b , ps)) = Pls ps ++ Bl b ++ Al a
ABr (inj₂ (a , ps))         = Pls ps ++ map _↥ (Al a)

BBr : (Σ Ty λ v' → BT t v' × BT v' u × List (Post2 u)) → List (Gen (₃₊ n))
BBr (_ , b₀ , b₁ , qs) = P2ls qs ++ map _↥ (Bl b₁) ++ Bl b₀

DDr : DT × DT × List O3 → List (Gen (₃₊ n))
DDr (d₁ , d₀ , os) = concatMap O3l os ++ Dl d₀ ++ map _↥ (Dl d₁)

ruleA-ok : (a : AT t) (h : HZ) →
  (₁₊ n) ⊢ ⟪ Al a ++ HZl h ⟫ ≈ ⟪ W0ls (proj₂ (ruleA a h)) ++ Al (proj₁ (ruleA a h)) ⟫
ruleAup-ok : (a : AT t) →
  (₂₊ n) ⊢ ⟪ map _↥ (Al a) ++ c₀ ∷ [] ⟫ ≈ ⟪ Aupr (ruleAup a) ⟫
ruleAB-ok : (a : AT t) (b : BT t u) →
  (₂₊ n) ⊢ ⟪ Bl b ++ Al a ++ c₀ ∷ [] ⟫ ≈ ⟪ ABr (ruleAB a b) ⟫
ruleB-ok : (b : BT t u) (g : In1 t) →
  (₂₊ n) ⊢ ⟪ Bl b ++ In1l g ⟫ ≈ ⟪ Pls (proj₂ (ruleB b g)) ++ Bl (proj₁ (ruleB b g)) ⟫
ruleBB-ok : (b₀ : BT t v) (b₁ : BT v u) →
  (₃₊ n) ⊢ ⟪ map _↥ (Bl b₁) ++ Bl b₀ ++ c₁ ∷ [] ⟫ ≈ ⟪ BBr (ruleBB b₀ b₁) ⟫
ruleS-ok : (s : SIn t) (b : BT t u) →
  (₃₊ n) ⊢ ⟪ map _↥ (Bl b) ++ Sl s ⟫ ≈ ⟪ P2ls (proj₂ (ruleS s b)) ++ map _↥ (Bl (proj₁ (ruleS s b))) ⟫
ruleC-ok : (c : CT) (g : W0 sg) →
  (₁₊ n) ⊢ ⟪ Cl c ++ W0l g ⟫ ≈ ⟪ concatMap COl (proj₂ (ruleC c g)) ++ Cl (proj₁ (ruleC c g)) ⟫
ruleSC-ok : (c : CT) →
  (₂₊ n) ⊢ ⟪ map _↥ (Cl c) ++ c₀ ∷ [] ⟫ ≈ ⟪ concatMap SCOl (proj₂ (ruleSC c)) ++ map _↥ (Cl (proj₁ (ruleSC c))) ⟫
ruleZ1D-ok : (d : DT) →
  (₂₊ n) ⊢ ⟪ Dl d ++ z₁ ∷ [] ⟫ ≈ ⟪ z₀ ∷ Dl d ⟫
ruleD-ok : (d : DT) (h : HZ) →
  (₂₊ n) ⊢ ⟪ Dl d ++ HZl h ⟫ ≈ ⟪ concatMap O2l (proj₂ (ruleD d h)) ++ Dl (proj₁ (ruleD d h)) ⟫
ruleCD-ok : (d : DT) →
  (₂₊ n) ⊢ ⟪ Dl d ++ c₀ ∷ [] ⟫ ≈ ⟪ concatMap O2l (proj₂ (ruleCD d)) ++ Dl (proj₁ (ruleCD d)) ⟫
ruleDD-ok : (d₁ d₀ : DT) →
  (₃₊ n) ⊢ ⟪ Dl d₀ ++ map _↥ (Dl d₁) ++ c₀ ∷ [] ⟫ ≈ ⟪ DDr (ruleDD d₁ d₀) ⟫
ruleE-ok : (e : ET) →
  (₁₊ n) ⊢ ⟪ El e ++ z₀ ∷ [] ⟫ ≈ ⟪ El (ruleE e) ⟫

ruleA A₁ gH = A₂ , []
ruleA A₁ gZ = A₁ , iZ ∷ []
ruleA A₂ gH = A₁ , []
ruleA A₂ gZ = A₂ , iX ∷ []
ruleA A₃ gH = A₃ , iH ∷ []
ruleA A₃ gZ = A₃ , iZ ∷ []

ruleAup A₁ = inj₁ (A₁ , (pstr sCZ) ∷ [])
ruleAup A₂ = inj₂ (_ , A₁ , B₂ , pH ∷ (pstr sCZ) ∷ [])
ruleAup A₃ = inj₂ (_ , A₁ , B₄ , (pin iZ) ∷ pH ∷ (pstr sXZC) ∷ (pin iH) ∷ [])

ruleAB A₁ B₁ = inj₁ (_ , A₁ , B₁ , pH ∷ (pstr sCZ) ∷ pH ∷ [])
ruleAB A₂ B₁ = inj₁ (_ , A₂ , B₃ , [])
ruleAB A₁ B₂ = inj₂ (A₂ , (pstr sCZ) ∷ pH ∷ [])
ruleAB A₂ B₂ = inj₁ (_ , A₃ , B₈ , pZ ∷ (pin iX) ∷ (pstr sCZ) ∷ pH ∷ (pstr sCZ) ∷ [])
ruleAB A₁ B₃ = inj₁ (_ , A₁ , B₃ , pH ∷ pZ ∷ pH ∷ pH ∷ (pstr sCZ) ∷ pH ∷ [])
ruleAB A₂ B₃ = inj₁ (_ , A₂ , B₁ , [])
ruleAB A₁ B₄ = inj₂ (A₃ , (pin iH) ∷ (pin iZ) ∷ (pstr sXZC) ∷ pH ∷ [])
ruleAB A₂ B₄ = inj₁ (_ , A₃ , B₆ , pH ∷ pZ ∷ pH ∷ (pin iZ) ∷ (pstr sXZC) ∷ pH ∷ (pstr sXZC) ∷ [])
ruleAB A₃ B₅ = inj₁ (_ , A₃ , B₇ , pH ∷ (pstr sXZC) ∷ pH ∷ [])
ruleAB A₃ B₆ = inj₁ (_ , A₂ , B₄ , (pin iH) ∷ pH ∷ (pstr sXZC) ∷ pH ∷ [])
ruleAB A₃ B₇ = inj₁ (_ , A₃ , B₅ , pH ∷ pZ ∷ pH ∷ pH ∷ (pstr sXZC) ∷ pH ∷ [])
ruleAB A₃ B₈ = inj₁ (_ , A₂ , B₂ , pZ ∷ (pin iX) ∷ (pstr sCZ) ∷ pH ∷ (pstr sCZ) ∷ [])

ruleB B₅ (w0 iH) = B₅ , (pin iH) ∷ []
ruleB B₆ (w0 iH) = B₆ , (pin iH) ∷ pH ∷ (pstr sXZC) ∷ pH ∷ []
ruleB B₇ (w0 iH) = B₇ , (pin iH) ∷ pH ∷ (pstr sXZC) ∷ pH ∷ []
ruleB B₈ (w0 iH) = B₈ , (pstr sCZ) ∷ (pin iX) ∷ pH ∷ (pstr sCZ) ∷ []
ruleB B₁ (w0 iX) = B₁ , (pin iX) ∷ []
ruleB B₂ (w0 iX) = B₂ , (pin iX) ∷ []
ruleB B₃ (w0 iX) = B₃ , (pin iX) ∷ []
ruleB B₄ (w0 iX) = B₄ , (pin iX) ∷ []
ruleB B₅ (w0 iX) = B₅ , (pin iX) ∷ []
ruleB B₆ (w0 iX) = B₆ , (pin iX) ∷ []
ruleB B₇ (w0 iX) = B₇ , (pin iX) ∷ []
ruleB B₈ (w0 iX) = B₈ , (pin iX) ∷ []
ruleB B₁ (w1 gH) = B₁ , pH ∷ []
ruleB B₂ (w1 gH) = B₃ , []
ruleB B₃ (w1 gH) = B₂ , []
ruleB B₄ (w1 gH) = B₄ , (pin iX) ∷ pH ∷ []
ruleB B₅ (w1 gH) = B₅ , pH ∷ []
ruleB B₆ (w1 gH) = B₇ , []
ruleB B₇ (w1 gH) = B₆ , []
ruleB B₈ (w1 gH) = B₈ , (pin iX) ∷ pH ∷ []
ruleB B₁ (w1 gZ) = B₁ , pH ∷ pZ ∷ pH ∷ []
ruleB B₂ (w1 gZ) = B₂ , pZ ∷ (pin iX) ∷ []
ruleB B₃ (w1 gZ) = B₃ , pH ∷ pZ ∷ pH ∷ []
ruleB B₄ (w1 gZ) = B₄ , pZ ∷ (pin iX) ∷ []
ruleB B₅ (w1 gZ) = B₅ , pH ∷ pZ ∷ pH ∷ []
ruleB B₆ (w1 gZ) = B₆ , pZ ∷ (pin iX) ∷ []
ruleB B₇ (w1 gZ) = B₇ , pH ∷ pZ ∷ pH ∷ []
ruleB B₈ (w1 gZ) = B₈ , pZ ∷ (pin iX) ∷ []
ruleB B₁ (w0 iZ) = B₁ , (pin iZ) ∷ []
ruleB B₂ (w0 iZ) = B₂ , pH ∷ pZ ∷ pH ∷ (pin iZ) ∷ []
ruleB B₃ (w0 iZ) = B₃ , pH ∷ pZ ∷ pH ∷ (pin iZ) ∷ []
ruleB B₄ (w0 iZ) = B₄ , pH ∷ pZ ∷ pH ∷ (pin iZ) ∷ (pin iX) ∷ pZ ∷ []
ruleB B₅ (w0 iZ) = B₅ , (pin iZ) ∷ []
ruleB B₆ (w0 iZ) = B₆ , pH ∷ pZ ∷ pH ∷ (pin iZ) ∷ []
ruleB B₇ (w0 iZ) = B₇ , pH ∷ pZ ∷ pH ∷ (pin iZ) ∷ []
ruleB B₈ (w0 iZ) = B₈ , pH ∷ pZ ∷ pH ∷ (pin iZ) ∷ (pin iX) ∷ pZ ∷ []

ruleBB B₁ B₁ = _ , B₁ , B₁ , (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₁ B₂ = _ , B₃ , B₂ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₁ B₃ = _ , B₁ , B₃ , (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₁ B₄ = _ , B₃ , B₄ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₂ B₁ = _ , B₂ , B₃ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₂ B₂ = _ , B₄ , B₈ , (qd qc₀) ∷ (qin iX) ∷ []
ruleBB B₂ B₃ = _ , B₂ , B₁ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₂ B₄ = _ , B₄ , B₆ , (qd qc₀) ∷ (qin iX) ∷ []
ruleBB B₃ B₁ = _ , B₃ , B₁ , (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₃ B₂ = _ , B₁ , B₂ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₃ B₃ = _ , B₃ , B₃ , (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₃ B₄ = _ , B₁ , B₄ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₄ B₅ = _ , B₄ , B₇ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₄ B₆ = _ , B₂ , B₄ , (qd qc₀) ∷ (qin iX) ∷ []
ruleBB B₄ B₇ = _ , B₄ , B₅ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₄ B₈ = _ , B₂ , B₂ , (qd qc₀) ∷ (qin iX) ∷ []
ruleBB B₅ B₅ = _ , B₅ , B₅ , (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₅ B₆ = _ , B₇ , B₆ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₅ B₇ = _ , B₅ , B₇ , (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₅ B₈ = _ , B₇ , B₈ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₆ B₅ = _ , B₆ , B₇ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₆ B₆ = _ , B₈ , B₄ , (qd qc₀) ∷ (qin iX) ∷ []
ruleBB B₆ B₇ = _ , B₆ , B₅ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₆ B₈ = _ , B₈ , B₂ , (qd qc₀) ∷ (qin iX) ∷ []
ruleBB B₇ B₅ = _ , B₇ , B₅ , (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₇ B₆ = _ , B₅ , B₆ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₇ B₇ = _ , B₇ , B₇ , (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ []
ruleBB B₇ B₈ = _ , B₅ , B₈ , (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleBB B₈ B₁ = _ , B₈ , B₃ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₈ B₂ = _ , B₆ , B₈ , (qd qc₀) ∷ (qin iX) ∷ []
ruleBB B₈ B₃ = _ , B₈ , B₁ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ []
ruleBB B₈ B₄ = _ , B₆ , B₆ , (qd qc₀) ∷ (qin iX) ∷ []

ruleS sCZ B₁ = B₁ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sCZ) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sCZ) ∷ []
ruleS sCZ B₂ = B₂ , (qstr sCZ) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sCZ) ∷ []
ruleS sCZ B₃ = B₃ , (qstr sCZ) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sCZ) ∷ []
ruleS sCZ B₄ = B₄ , (qd qz₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sXZC) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleS sXZC B₅ = B₅ , (qd qz₀) ∷ (qd qz₀) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sXZC) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleS sXZC B₆ = B₆ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sXZC) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleS sXZC B₇ = B₇ , (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sXZC) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []
ruleS sXZC B₈ = B₈ , (qd qz₀) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qstr sCZ) ∷ (qd qh₁) ∷ (qd qc₀) ∷ (qd qh₁) ∷ (qd qh₀) ∷ (qd qc₀) ∷ (qd qh₀) ∷ []

ruleC C₁ iZ = C₁ , coZ ∷ []
ruleC C₁ iX = C₂ , []
ruleC C₂ iZ = C₂ , coneg ∷ coZ ∷ []
ruleC C₂ iX = C₁ , []

ruleSC C₁ = C₁ , scC ∷ []
ruleSC C₂ = C₂ , scZ ∷ scC ∷ []

ruleD D₁ gH = D₁ , oh₁ ∷ []
ruleD D₁ gZ = D₁ , oh₁ ∷ oz₁ ∷ oh₁ ∷ []
ruleD D₂ gH = D₃ , []
ruleD D₂ gZ = D₂ , oZ₀ ∷ oz₁ ∷ []
ruleD D₃ gH = D₂ , []
ruleD D₃ gZ = D₃ , oh₁ ∷ oz₁ ∷ oh₁ ∷ []
ruleD D₄ gH = D₄ , oh₁ ∷ oZ₀ ∷ []
ruleD D₄ gZ = D₄ , oz₁ ∷ oZ₀ ∷ []

ruleCD D₁ = D₃ , []
ruleCD D₂ = D₄ , oZ₀ ∷ []
ruleCD D₃ = D₁ , []
ruleCD D₄ = D₂ , oZ₀ ∷ []

ruleDD D₁ D₁ = D₁ , D₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₁ D₂ = D₃ , D₂ , o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₁ D₃ = D₁ , D₃ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₁ D₄ = D₃ , D₄ , o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₂ D₁ = D₂ , D₃ , o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₂ D₂ = D₄ , D₄ , o3Z₀ ∷ o3c₁ ∷ []
ruleDD D₂ D₃ = D₂ , D₁ , o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₂ D₄ = D₄ , D₂ , o3Z₀ ∷ o3c₁ ∷ []
ruleDD D₃ D₁ = D₃ , D₁ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₃ D₂ = D₁ , D₂ , o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₃ D₃ = D₃ , D₃ , o3h₁ ∷ o3h₂ ∷ o3c₁ ∷ o3h₁ ∷ o3h₂ ∷ []
ruleDD D₃ D₄ = D₁ , D₄ , o3h₂ ∷ o3c₁ ∷ o3h₂ ∷ []
ruleDD D₄ D₁ = D₄ , D₃ , o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₄ D₂ = D₂ , D₄ , o3Z₀ ∷ o3c₁ ∷ []
ruleDD D₄ D₃ = D₄ , D₁ , o3h₁ ∷ o3c₁ ∷ o3h₁ ∷ []
ruleDD D₄ D₄ = D₂ , D₂ , o3Z₀ ∷ o3c₁ ∷ []

ruleE E₁ = E₂
ruleE E₂ = E₁

ruleA-ok A₁ gH = prf Rule-HA-1
ruleA-ok A₁ gZ = prf Rule-ZA-1
ruleA-ok A₂ gH = prf Rule-HA-2
ruleA-ok A₂ gZ = prf Rule-ZA-2
ruleA-ok A₃ gH = prf Rule-HA-3
ruleA-ok A₃ gZ = prf Rule-ZA-3

ruleAup-ok A₁ = prf Rule-CZA^-1
ruleAup-ok A₂ = prf Rule-CZA^-2
ruleAup-ok A₃ = prf Rule-CZA^-3

ruleAB-ok A₁ B₁ = prf Rule-CZAB-1-1
ruleAB-ok A₂ B₁ = prf Rule-CZAB-2-1
ruleAB-ok A₁ B₂ = prf Rule-CZAB-1-2
ruleAB-ok A₂ B₂ = prf Rule-CZAB-2-2
ruleAB-ok A₁ B₃ = prf Rule-CZAB-1-3
ruleAB-ok A₂ B₃ = prf Rule-CZAB-2-3
ruleAB-ok A₁ B₄ = prf Rule-CZAB-1-4
ruleAB-ok A₂ B₄ = prf Rule-CZAB-2-4
ruleAB-ok A₃ B₅ = prf Rule-CZAB-3-5
ruleAB-ok A₃ B₆ = prf Rule-CZAB-3-6
ruleAB-ok A₃ B₇ = prf Rule-CZAB-3-7
ruleAB-ok A₃ B₈ = prf Rule-CZAB-3-8

ruleB-ok B₅ (w0 iH) = prf Rule-H0B-5
ruleB-ok B₆ (w0 iH) = prf Rule-H0B-6
ruleB-ok B₇ (w0 iH) = prf Rule-H0B-7
ruleB-ok B₈ (w0 iH) = prf Rule-H0B-8
ruleB-ok B₁ (w0 iX) = prf Rule-X0B-1
ruleB-ok B₂ (w0 iX) = prf Rule-X0B-2
ruleB-ok B₃ (w0 iX) = prf Rule-X0B-3
ruleB-ok B₄ (w0 iX) = prf Rule-X0B-4
ruleB-ok B₅ (w0 iX) = prf Rule-X0B-5
ruleB-ok B₆ (w0 iX) = prf Rule-X0B-6
ruleB-ok B₇ (w0 iX) = prf Rule-X0B-7
ruleB-ok B₈ (w0 iX) = prf Rule-X0B-8
ruleB-ok B₁ (w1 gH) = prf Rule-H1B-1
ruleB-ok B₂ (w1 gH) = prf Rule-H1B-2
ruleB-ok B₃ (w1 gH) = prf Rule-H1B-3
ruleB-ok B₄ (w1 gH) = prf Rule-H1B-4
ruleB-ok B₅ (w1 gH) = prf Rule-H1B-5
ruleB-ok B₆ (w1 gH) = prf Rule-H1B-6
ruleB-ok B₇ (w1 gH) = prf Rule-H1B-7
ruleB-ok B₈ (w1 gH) = prf Rule-H1B-8
ruleB-ok B₁ (w1 gZ) = prf Rule-Z1B-1
ruleB-ok B₂ (w1 gZ) = prf Rule-Z1B-2
ruleB-ok B₃ (w1 gZ) = prf Rule-Z1B-3
ruleB-ok B₄ (w1 gZ) = prf Rule-Z1B-4
ruleB-ok B₅ (w1 gZ) = prf Rule-Z1B-5
ruleB-ok B₆ (w1 gZ) = prf Rule-Z1B-6
ruleB-ok B₇ (w1 gZ) = prf Rule-Z1B-7
ruleB-ok B₈ (w1 gZ) = prf Rule-Z1B-8
ruleB-ok B₁ (w0 iZ) = prf Rule-Z0B-1
ruleB-ok B₂ (w0 iZ) = prf Rule-Z0B-2
ruleB-ok B₃ (w0 iZ) = prf Rule-Z0B-3
ruleB-ok B₄ (w0 iZ) = prf Rule-Z0B-4
ruleB-ok B₅ (w0 iZ) = prf Rule-Z0B-5
ruleB-ok B₆ (w0 iZ) = prf Rule-Z0B-6
ruleB-ok B₇ (w0 iZ) = prf Rule-Z0B-7
ruleB-ok B₈ (w0 iZ) = prf Rule-Z0B-8

ruleBB-ok B₁ B₁ = prf Rule-CZBB-1-1
ruleBB-ok B₁ B₂ = prf Rule-CZBB-1-2
ruleBB-ok B₁ B₃ = prf Rule-CZBB-1-3
ruleBB-ok B₁ B₄ = prf Rule-CZBB-1-4
ruleBB-ok B₂ B₁ = prf Rule-CZBB-2-1
ruleBB-ok B₂ B₂ = prf Rule-CZBB-2-2
ruleBB-ok B₂ B₃ = prf Rule-CZBB-2-3
ruleBB-ok B₂ B₄ = prf Rule-CZBB-2-4
ruleBB-ok B₃ B₁ = prf Rule-CZBB-3-1
ruleBB-ok B₃ B₂ = prf Rule-CZBB-3-2
ruleBB-ok B₃ B₃ = prf Rule-CZBB-3-3
ruleBB-ok B₃ B₄ = prf Rule-CZBB-3-4
ruleBB-ok B₄ B₅ = prf Rule-CZBB-4-5
ruleBB-ok B₄ B₆ = prf Rule-CZBB-4-6
ruleBB-ok B₄ B₇ = prf Rule-CZBB-4-7
ruleBB-ok B₄ B₈ = prf Rule-CZBB-4-8
ruleBB-ok B₅ B₅ = prf Rule-CZBB-5-5
ruleBB-ok B₅ B₆ = prf Rule-CZBB-5-6
ruleBB-ok B₅ B₇ = prf Rule-CZBB-5-7
ruleBB-ok B₅ B₈ = prf Rule-CZBB-5-8
ruleBB-ok B₆ B₅ = prf Rule-CZBB-6-5
ruleBB-ok B₆ B₆ = prf Rule-CZBB-6-6
ruleBB-ok B₆ B₇ = prf Rule-CZBB-6-7
ruleBB-ok B₆ B₈ = prf Rule-CZBB-6-8
ruleBB-ok B₇ B₅ = prf Rule-CZBB-7-5
ruleBB-ok B₇ B₆ = prf Rule-CZBB-7-6
ruleBB-ok B₇ B₇ = prf Rule-CZBB-7-7
ruleBB-ok B₇ B₈ = prf Rule-CZBB-7-8
ruleBB-ok B₈ B₁ = prf Rule-CZBB-8-1
ruleBB-ok B₈ B₂ = prf Rule-CZBB-8-2
ruleBB-ok B₈ B₃ = prf Rule-CZBB-8-3
ruleBB-ok B₈ B₄ = prf Rule-CZBB-8-4

ruleS-ok sCZ B₁ = prf Rule-SCZB-1
ruleS-ok sCZ B₂ = prf Rule-SCZB-2
ruleS-ok sCZ B₃ = prf Rule-SCZB-3
ruleS-ok sCZ B₄ = prf Rule-SCZB-4
ruleS-ok sXZC B₅ = prf Rule-SXZCB-5
ruleS-ok sXZC B₆ = prf Rule-SXZCB-6
ruleS-ok sXZC B₇ = prf Rule-SXZCB-7
ruleS-ok sXZC B₈ = prf Rule-SXZCB-8

ruleC-ok C₁ iZ = prf Rule-ZC-1
ruleC-ok C₁ iX = prf Rule-XC-1
ruleC-ok C₂ iZ = prf Rule-ZC-2
ruleC-ok C₂ iX = prf Rule-XC-2

ruleSC-ok C₁ = prf Rule-SCZC-1
ruleSC-ok C₂ = prf Rule-SCZC-2

ruleZ1D-ok D₁ = prf Rule-Z1D-1
ruleZ1D-ok D₂ = prf Rule-Z1D-2
ruleZ1D-ok D₃ = prf Rule-Z1D-3
ruleZ1D-ok D₄ = prf Rule-Z1D-4

ruleD-ok D₁ gH = prf Rule-H0D-1
ruleD-ok D₁ gZ = prf Rule-Z0D-1
ruleD-ok D₂ gH = prf Rule-H0D-2
ruleD-ok D₂ gZ = prf Rule-Z0D-2
ruleD-ok D₃ gH = prf Rule-H0D-3
ruleD-ok D₃ gZ = prf Rule-Z0D-3
ruleD-ok D₄ gH = prf Rule-H0D-4
ruleD-ok D₄ gZ = prf Rule-Z0D-4

ruleCD-ok D₁ = prf Rule-CZD-1
ruleCD-ok D₂ = prf Rule-CZD-2
ruleCD-ok D₃ = prf Rule-CZD-3
ruleCD-ok D₄ = prf Rule-CZD-4

ruleDD-ok D₁ D₁ = prf Rule-CZDD-1-1
ruleDD-ok D₁ D₂ = prf Rule-CZDD-1-2
ruleDD-ok D₁ D₃ = prf Rule-CZDD-1-3
ruleDD-ok D₁ D₄ = prf Rule-CZDD-1-4
ruleDD-ok D₂ D₁ = prf Rule-CZDD-2-1
ruleDD-ok D₂ D₂ = prf Rule-CZDD-2-2
ruleDD-ok D₂ D₃ = prf Rule-CZDD-2-3
ruleDD-ok D₂ D₄ = prf Rule-CZDD-2-4
ruleDD-ok D₃ D₁ = prf Rule-CZDD-3-1
ruleDD-ok D₃ D₂ = prf Rule-CZDD-3-2
ruleDD-ok D₃ D₃ = prf Rule-CZDD-3-3
ruleDD-ok D₃ D₄ = prf Rule-CZDD-3-4
ruleDD-ok D₄ D₁ = prf Rule-CZDD-4-1
ruleDD-ok D₄ D₂ = prf Rule-CZDD-4-2
ruleDD-ok D₄ D₃ = prf Rule-CZDD-4-3
ruleDD-ok D₄ D₄ = prf Rule-CZDD-4-4

ruleE-ok E₁ = prf Rule-ZE-1
ruleE-ok E₂ = prf Rule-ZE-2

------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoded relations on two wires, over macro letters
-- (machine-generated)
--
-- The decoding of the two-level generators on four indices is a word
-- in a few circuits: the Paulis X and X↑, the CNOTs CX₀₁ and CX₁₀, CS,
-- the controlled K gates CK₀₁ and CK₁₀, and the one-wire gates.  Read
-- as letters (M, read back by μ), the decoded relations are short
-- words, and a Knuth–Bendix completion derives them from some eighty
-- equations between those letters, each an equation of circuits:
-- derived on the gates in Lemmas.TwoWire, or from the others here.
-- An equation of macro words is an equation of their circuits (_∼_),
-- so a derivation over the letters is one of circuits (lift); `inst`
-- turns it into an equation of any two circuits with the same letters.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Lemmas.TwoWireMacro where

open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; WRel ; _•_ ; _ʷ)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+CS.Syntactics
import Examples.Groups.Clifford+CS.Engine as Engine
import Examples.Groups.Clifford+CS.Lemmas.TwoWire as TW

private
  module B = Assoc (2 VRel,_===_)

------------------------------------------------------------------------
-- The macro letters

data M : Set where
  ι s₀ s₁ cs x₀ x₁ cx cx′ ck ck′ k₀ k₁ : M

μ : M → Circuit 2
μ ι   = iI
μ s₀  = S
μ s₁  = S ↑
μ cs  = CS
μ x₀  = X
μ x₁  = K ↑ • S ↑ • S ↑ • K ↑ • iI
μ cx  = CX₀₁
μ cx′ = CX₁₀
μ ck  = CS • K ↑ • CS • K ↑ • CS • S • S • S • iI
μ ck′ = CS • K • CS • K • CS • S ↑ • S ↑ • S ↑ • iI
μ k₀  = K
μ k₁  = K ↑

private
  code : M → ℕ
  code ι = 0 ; code s₀ = 1 ; code s₁ = 2 ; code cs = 3 ; code x₀ = 4 ; code x₁ = 5
  code cx = 6 ; code cx′ = 7 ; code ck = 8 ; code ck′ = 9 ; code k₀ = 10 ; code k₁ = 11

  decode : ℕ → M
  decode 1 = s₀ ; decode 2 = s₁ ; decode 3 = cs ; decode 4 = x₀ ; decode 5 = x₁
  decode 6 = cx ; decode 7 = cx′ ; decode 8 = ck ; decode 9 = ck′ ; decode 10 = k₀
  decode 11 = k₁ ; decode _ = ι

  decode-code : ∀ x → decode (code x) ≡ x
  decode-code ι = refl ; decode-code s₀ = refl ; decode-code s₁ = refl
  decode-code cs = refl ; decode-code x₀ = refl ; decode-code x₁ = refl
  decode-code cx = refl ; decode-code cx′ = refl ; decode-code ck = refl
  decode-code ck′ = refl ; decode-code k₀ = refl ; decode-code k₁ = refl

-- An equation of macro words is one of their circuits.
_∼_ : WRel M
u ∼ v = 2 ⊢ (μ ʷ) u ≈ (μ ʷ) v

module EM = Engine _∼_ code decode decode-code
open EM public using (Eqn ; lhs ; rhs ; prf ; from-list)
open EM using (eqn ; sym⁼ ; derive ; rw ; rw⁻)

-- So a derivation over the letters is one of circuits.
lift : (e : Eqn) → 2 ⊢ (μ ʷ) (from-list (lhs e)) ≈ (μ ʷ) (from-list (rhs e))
lift e = fʷ-cong (prf e)
  where open PP.StarCongruence _∼_ (2 VRel,_===_) μ (λ e → e) using (fʷ-cong)

-- Two circuits whose letters are those of the two sides.
inst : ∀ {w v : Circuit 2} (e : Eqn) →
       B.to-list w ≡ B.to-list ((μ ʷ) (from-list (lhs e))) →
       B.to-list v ≡ B.to-list ((μ ʷ) (from-list (rhs e))) → 2 ⊢ w ≈ v
inst e p q = PB.trans (B.by-assoc p) (PB.trans (lift e) (B.by-assoc (Eq.sym q)))

------------------------------------------------------------------------
-- The equations between the letters, from Lemmas.TwoWire

private
  ax-K0 : Eqn
  ax-K0 = eqn (x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ []) (k₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-K0) (B.by-assoc refl))))

  ax-K1 : Eqn
  ax-K1 = eqn (x₀ ∷ ck ∷ x₀ ∷ ck ∷ []) (k₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-K1) (B.by-assoc refl))))

  ax-aka : Eqn
  ax-aka = eqn (cx ∷ k₀ ∷ cx ∷ []) (cx′ ∷ cx ∷ k₁ ∷ cx ∷ cx′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-aka) (B.by-assoc refl))))

  ax-aqa-C : Eqn
  ax-aqa-C = eqn (cs ∷ cx ∷ ck′ ∷ cx ∷ []) (cx ∷ ck′ ∷ cx ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-aqa-C) (B.by-assoc refl))))

  ax-k-I : Eqn
  ax-k-I = eqn (k₀ ∷ ι ∷ []) (ι ∷ k₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-k-I) (B.by-assoc refl))))

  ax-k-l : Eqn
  ax-k-l = eqn (k₁ ∷ k₀ ∷ []) (k₀ ∷ k₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-k-l) (B.by-assoc refl))))

  ax-k-t : Eqn
  ax-k-t = eqn (s₁ ∷ k₀ ∷ []) (k₀ ∷ s₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-k-t) (B.by-assoc refl))))

  ax-k2 : Eqn
  ax-k2 = eqn (k₀ ∷ k₀ ∷ []) (ι ∷ ι ∷ ι ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-k2) (B.by-assoc refl))))

  ax-l-I : Eqn
  ax-l-I = eqn (k₁ ∷ ι ∷ []) (ι ∷ k₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-l-I) (B.by-assoc refl))))

  ax-l-s : Eqn
  ax-l-s = eqn (k₁ ∷ s₀ ∷ []) (s₀ ∷ k₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-l-s) (B.by-assoc refl))))

  ax-l2 : Eqn
  ax-l2 = eqn (k₁ ∷ k₁ ∷ []) (ι ∷ ι ∷ ι ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-l2) (B.by-assoc refl))))

  ax-m-C4 : Eqn
  ax-m-C4 = eqn (cs ∷ cs ∷ cs ∷ cs ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-C4) (B.by-assoc refl))))

  ax-m-I4 : Eqn
  ax-m-I4 = eqn (ι ∷ ι ∷ ι ∷ ι ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-I4) (B.by-assoc refl))))

  ax-m-IC : Eqn
  ax-m-IC = eqn (cs ∷ ι ∷ []) (ι ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-IC) (B.by-assoc refl))))

  ax-m-Ia : Eqn
  ax-m-Ia = eqn (cx ∷ ι ∷ []) (ι ∷ cx ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-Ia) (B.by-assoc refl))))

  ax-m-Ib : Eqn
  ax-m-Ib = eqn (cx′ ∷ ι ∷ []) (ι ∷ cx′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-Ib) (B.by-assoc refl))))

  ax-m-Is : Eqn
  ax-m-Is = eqn (s₀ ∷ ι ∷ []) (ι ∷ s₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-Is) (B.by-assoc refl))))

  ax-m-It : Eqn
  ax-m-It = eqn (s₁ ∷ ι ∷ []) (ι ∷ s₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-It) (B.by-assoc refl))))

  ax-m-Ix : Eqn
  ax-m-Ix = eqn (x₀ ∷ ι ∷ []) (ι ∷ x₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-Ix) (B.by-assoc refl))))

  ax-m-Iy : Eqn
  ax-m-Iy = eqn (x₁ ∷ ι ∷ []) (ι ∷ x₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-Iy) (B.by-assoc refl))))

  ax-m-a2 : Eqn
  ax-m-a2 = eqn (cx ∷ cx ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-a2) (B.by-assoc refl))))

  ax-m-aC : Eqn
  ax-m-aC = eqn (cx ∷ cs ∷ cx ∷ []) (cs ∷ cs ∷ cs ∷ s₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-aC) (B.by-assoc refl))))

  ax-m-ab : Eqn
  ax-m-ab = eqn (cx ∷ cx′ ∷ cx ∷ []) (cx′ ∷ cx ∷ cx′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-ab) (B.by-assoc refl))))

  ax-m-as : Eqn
  ax-m-as = eqn (cx ∷ s₀ ∷ []) (s₀ ∷ cx ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-as) (B.by-assoc refl))))

  ax-m-at : Eqn
  ax-m-at = eqn (cx ∷ s₁ ∷ cx ∷ []) (s₀ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-at) (B.by-assoc refl))))

  ax-m-ax : Eqn
  ax-m-ax = eqn (cx ∷ x₀ ∷ cx ∷ []) (x₀ ∷ x₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-ax) (B.by-assoc refl))))

  ax-m-ay : Eqn
  ax-m-ay = eqn (cx ∷ x₁ ∷ []) (x₁ ∷ cx ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-ay) (B.by-assoc refl))))

  ax-m-b2 : Eqn
  ax-m-b2 = eqn (cx′ ∷ cx′ ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-b2) (B.by-assoc refl))))

  ax-m-bC : Eqn
  ax-m-bC = eqn (cx′ ∷ cs ∷ cx′ ∷ []) (cs ∷ cs ∷ cs ∷ s₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-bC) (B.by-assoc refl))))

  ax-m-bs : Eqn
  ax-m-bs = eqn (cx′ ∷ s₀ ∷ cx′ ∷ []) (s₀ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-bs) (B.by-assoc refl))))

  ax-m-bt : Eqn
  ax-m-bt = eqn (cx′ ∷ s₁ ∷ []) (s₁ ∷ cx′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-bt) (B.by-assoc refl))))

  ax-m-bx : Eqn
  ax-m-bx = eqn (cx′ ∷ x₀ ∷ []) (x₀ ∷ cx′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-bx) (B.by-assoc refl))))

  ax-m-by : Eqn
  ax-m-by = eqn (cx′ ∷ x₁ ∷ cx′ ∷ []) (x₀ ∷ x₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-by) (B.by-assoc refl))))

  ax-m-s4 : Eqn
  ax-m-s4 = eqn (s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-s4) (B.by-assoc refl))))

  ax-m-sC : Eqn
  ax-m-sC = eqn (cs ∷ s₀ ∷ []) (s₀ ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-sC) (B.by-assoc refl))))

  ax-m-st : Eqn
  ax-m-st = eqn (s₁ ∷ s₀ ∷ []) (s₀ ∷ s₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-st) (B.by-assoc refl))))

  ax-m-t4 : Eqn
  ax-m-t4 = eqn (s₁ ∷ s₁ ∷ s₁ ∷ s₁ ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-t4) (B.by-assoc refl))))

  ax-m-tC : Eqn
  ax-m-tC = eqn (cs ∷ s₁ ∷ []) (s₁ ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-tC) (B.by-assoc refl))))

  ax-m-x2 : Eqn
  ax-m-x2 = eqn (x₀ ∷ x₀ ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-x2) (B.by-assoc refl))))

  ax-m-xC : Eqn
  ax-m-xC = eqn (x₀ ∷ cs ∷ x₀ ∷ []) (cs ∷ cs ∷ cs ∷ s₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-xC) (B.by-assoc refl))))

  ax-m-xs : Eqn
  ax-m-xs = eqn (x₀ ∷ s₀ ∷ x₀ ∷ []) (ι ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-xs) (B.by-assoc refl))))

  ax-m-xt : Eqn
  ax-m-xt = eqn (x₀ ∷ s₁ ∷ []) (s₁ ∷ x₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-xt) (B.by-assoc refl))))

  ax-m-xy : Eqn
  ax-m-xy = eqn (x₁ ∷ x₀ ∷ []) (x₀ ∷ x₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-xy) (B.by-assoc refl))))

  ax-m-y2 : Eqn
  ax-m-y2 = eqn (x₁ ∷ x₁ ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-y2) (B.by-assoc refl))))

  ax-m-yC : Eqn
  ax-m-yC = eqn (x₁ ∷ cs ∷ x₁ ∷ []) (cs ∷ cs ∷ cs ∷ s₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-yC) (B.by-assoc refl))))

  ax-m-ys : Eqn
  ax-m-ys = eqn (x₁ ∷ s₀ ∷ []) (s₀ ∷ x₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-ys) (B.by-assoc refl))))

  ax-m-yt : Eqn
  ax-m-yt = eqn (x₁ ∷ s₁ ∷ x₁ ∷ []) (ι ∷ s₁ ∷ s₁ ∷ s₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-m-yt) (B.by-assoc refl))))

  ax-p-13 : Eqn
  ax-p-13 = eqn (ck ∷ cs ∷ cs ∷ []) (cx ∷ ck ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-p-13) (B.by-assoc refl))))

  ax-p-14 : Eqn
  ax-p-14 = eqn (ck ∷ cs ∷ cs ∷ cs ∷ []) (cs ∷ ck ∷ cs ∷ ck ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-p-14) (B.by-assoc refl))))

  ax-p-15 : Eqn
  ax-p-15 = eqn (ck ∷ s₀ ∷ []) (s₀ ∷ ck ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-p-15) (B.by-assoc refl))))

  ax-p-16 : Eqn
  ax-p-16 = eqn (ck ∷ ck ∷ s₀ ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-p-16) (B.by-assoc refl))))

  ax-p-a : Eqn
  ax-p-a = eqn (cx ∷ ck ∷ cx ∷ []) (s₀ ∷ s₀ ∷ cs ∷ cs ∷ ck ∷ cs ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-p-a) (B.by-assoc refl))))

  ax-p-i1 : Eqn
  ax-p-i1 = eqn (ck ∷ cs ∷ cs ∷ cs ∷ s₁ ∷ []) (cs ∷ cs ∷ cs ∷ s₁ ∷ ck ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-p-i1) (B.by-assoc refl))))

  ax-p-xpx : Eqn
  ax-p-xpx = eqn (x₀ ∷ ck ∷ x₀ ∷ ck ∷ []) (ck ∷ x₀ ∷ ck ∷ x₀ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-p-xpx) (B.by-assoc refl))))

  ax-p-y : Eqn
  ax-p-y = eqn (x₁ ∷ ck ∷ x₁ ∷ []) (s₀ ∷ s₀ ∷ cs ∷ cs ∷ ck ∷ cs ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-p-y) (B.by-assoc refl))))

  ax-pq-sw : Eqn
  ax-pq-sw = eqn (cx ∷ cx′ ∷ cx ∷ ck ∷ cx ∷ cx′ ∷ cx ∷ []) (ck′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-pq-sw) (B.by-assoc refl))))

  ax-q-13 : Eqn
  ax-q-13 = eqn (ck′ ∷ cs ∷ cs ∷ []) (cx′ ∷ ck′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-13) (B.by-assoc refl))))

  ax-q-14 : Eqn
  ax-q-14 = eqn (ck′ ∷ cs ∷ cs ∷ cs ∷ []) (cs ∷ ck′ ∷ cs ∷ ck′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-14) (B.by-assoc refl))))

  ax-q-15 : Eqn
  ax-q-15 = eqn (ck′ ∷ s₁ ∷ []) (s₁ ∷ ck′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-15) (B.by-assoc refl))))

  ax-q-16 : Eqn
  ax-q-16 = eqn (ck′ ∷ ck′ ∷ s₁ ∷ []) ([])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-16) (B.by-assoc refl))))

  ax-q-I : Eqn
  ax-q-I = eqn (ck′ ∷ ι ∷ []) (ι ∷ ck′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-I) (B.by-assoc refl))))

  ax-q-b : Eqn
  ax-q-b = eqn (cx′ ∷ ck′ ∷ cx′ ∷ []) (s₁ ∷ s₁ ∷ cs ∷ cs ∷ ck′ ∷ cs ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-b) (B.by-assoc refl))))

  ax-q-i2 : Eqn
  ax-q-i2 = eqn (ck′ ∷ cs ∷ cs ∷ cs ∷ s₀ ∷ []) (cs ∷ cs ∷ cs ∷ s₀ ∷ ck′ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-i2) (B.by-assoc refl))))

  ax-q-x : Eqn
  ax-q-x = eqn (x₀ ∷ ck′ ∷ x₀ ∷ []) (s₁ ∷ s₁ ∷ cs ∷ cs ∷ ck′ ∷ cs ∷ cs ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-x) (B.by-assoc refl))))

  ax-q-yqy : Eqn
  ax-q-yqy = eqn (x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ []) (ck′ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-q-yqy) (B.by-assoc refl))))

  ax-sw-x : Eqn
  ax-sw-x = eqn (cx ∷ cx′ ∷ cx ∷ x₀ ∷ []) (x₁ ∷ cx ∷ cx′ ∷ cx ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-sw-x) (B.by-assoc refl))))

  ax-sw-y : Eqn
  ax-sw-y = eqn (cx ∷ cx′ ∷ cx ∷ x₁ ∷ []) (x₀ ∷ cx ∷ cx′ ∷ cx ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-sw-y) (B.by-assoc refl))))

  ax-x-def : Eqn
  ax-x-def = eqn (x₀ ∷ []) (k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ ι ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-x-def) (B.by-assoc refl))))

  ax-y-def : Eqn
  ax-y-def = eqn (x₁ ∷ []) (k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ ι ∷ [])
    (PB.axiom (PB.trans (B.by-assoc refl)
      (PB.trans (TW.prf TW.ax-y-def) (B.by-assoc refl))))

------------------------------------------------------------------------
-- Equations between the letters that follow from the others

private
  rt2a-1 : Eqn
  rt2a-1 = ax-m-s4

  rt2a-2 : Eqn
  rt2a-2 = ax-m-t4

  rt2a-3 : Eqn
  rt2a-3 = ax-m-C4

  rt2a-4 : Eqn
  rt2a-4 = ax-m-x2

  rt2a-5 : Eqn
  rt2a-5 = ax-m-y2

  rt2a-6 : Eqn
  rt2a-6 = ax-m-a2

  rt2a-7 : Eqn
  rt2a-7 = ax-m-b2

  rt2a-9 : Eqn
  rt2a-9 = ax-m-It

  rt2a-10 : Eqn
  rt2a-10 = ax-m-IC

  rt2a-11 : Eqn
  rt2a-11 = ax-m-st

  rt2a-12 : Eqn
  rt2a-12 = ax-m-sC

  rt2a-13 : Eqn
  rt2a-13 = ax-m-tC

  rt2a-15 : Eqn
  rt2a-15 = ax-m-Iy

  rt2a-18 : Eqn
  rt2a-18 = ax-m-xy

  rt2a-21 : Eqn
  rt2a-21 = sym⁼ (ax-m-xC)

  rt2a-22 : Eqn
  rt2a-22 = ax-m-ys

  rt2a-23 : Eqn
  rt2a-23 = sym⁼ (ax-m-yt)

  rt2a-24 : Eqn
  rt2a-24 = sym⁼ (ax-m-yC)

  rt2a-27 : Eqn
  rt2a-27 = sym⁼ (ax-m-aC)

  rt2a-30 : Eqn
  rt2a-30 = sym⁼ (ax-m-bC)

  rt2a-31 : Eqn
  rt2a-31 = ax-m-ax

  rt2a-32 : Eqn
  rt2a-32 = ax-m-ay

  rt2a-33 : Eqn
  rt2a-33 = ax-m-by

  rt2a-35 : Eqn
  rt2a-35 = sym⁼ (ax-m-ab)

  rt2a-37 : Eqn
  rt2a-37 = ax-q-15

  rt2a-39 : Eqn
  rt2a-39 = ax-q-I

  rt2a-44 : Eqn
  rt2a-44 = ax-pq-sw

  rt2a-46 : Eqn
  rt2a-46 = ax-q-i2

  rt2a-47 : Eqn
  rt2a-47 = derive (s₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (x₀ ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 0 rt2a-13 ∷ rw⁻ 1 rt2a-13 ∷ rw⁻ 2 rt2a-13 ∷ rw 0 rt2a-21 ∷ []) refl

  rt2a-48 : Eqn
  rt2a-48 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2a-12 ∷ rw⁻ 1 rt2a-12 ∷ rw⁻ 2 rt2a-12 ∷ rw 0 rt2a-24 ∷ []) refl

  rt2a-49 : Eqn
  rt2a-49 = derive (cx ∷ cs ∷ cx ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2a-27 ∷ rw 2 rt2a-12 ∷ rw 1 rt2a-12 ∷ rw 0 rt2a-12 ∷ rw 0 rt2a-48 ∷ []) refl

  rt2a-50 : Eqn
  rt2a-50 = derive (cx′ ∷ cs ∷ cx′ ∷ [])
    (x₀ ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 0 rt2a-30 ∷ rw 2 rt2a-13 ∷ rw 1 rt2a-13 ∷ rw 0 rt2a-13 ∷ rw 0 rt2a-47 ∷ []) refl

  rt2a-52 : Eqn
  rt2a-52 = derive (ck′ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ ck′ ∷ [])
    (rw⁻ 1 rt2a-48 ∷ rw⁻ 1 rt2a-12 ∷ rw⁻ 2 rt2a-12 ∷ rw⁻ 3 rt2a-12 ∷ rw 0 rt2a-46 ∷ rw 2 rt2a-12 ∷
       rw 1 rt2a-12 ∷ rw 0 rt2a-12 ∷ rw 0 rt2a-48 ∷ []) refl

  rt2a-54 : Eqn
  rt2a-54 = derive (x₁ ∷ s₁ ∷ x₁ ∷ s₁ ∷ [])
    (ι ∷ [])
    (rw⁻ 0 rt2a-23 ∷ rw⁻ 0 rt2a-9 ∷ rw⁻ 1 rt2a-9 ∷ rw⁻ 2 rt2a-9 ∷ rw⁻ 3 rt2a-9 ∷ rw 0 rt2a-2 ∷ []) refl

  rt2a-55 : Eqn
  rt2a-55 = derive (x₁ ∷ cs ∷ x₁ ∷ cs ∷ [])
    (s₀ ∷ [])
    (rw⁻ 0 rt2a-48 ∷ rw⁻ 0 rt2a-12 ∷ rw⁻ 1 rt2a-12 ∷ rw⁻ 2 rt2a-12 ∷ rw⁻ 3 rt2a-12 ∷ rw 0 rt2a-3 ∷ []) refl

  rt2a-60 : Eqn
  rt2a-60 = derive (cx ∷ x₀ ∷ x₁ ∷ [])
    (x₁ ∷ cx ∷ x₀ ∷ [])
    (rw⁻ 1 rt2a-18 ∷ rw 0 rt2a-32 ∷ []) refl

  rt2a-62 : Eqn
  rt2a-62 = derive (x₀ ∷ x₁ ∷ cx ∷ [])
    (cx ∷ x₀ ∷ [])
    (rw⁻ 0 rt2a-31 ∷ rw 2 rt2a-6 ∷ []) refl

  rt2a-63 : Eqn
  rt2a-63 = derive (x₁ ∷ cx ∷ x₀ ∷ [])
    (x₀ ∷ cx ∷ [])
    (rw⁻ 0 rt2a-60 ∷ rw⁻ 1 rt2a-31 ∷ rw 0 rt2a-6 ∷ []) refl

  rt2a-64 : Eqn
  rt2a-64 = derive (cx ∷ x₀ ∷ x₁ ∷ [])
    (x₀ ∷ cx ∷ [])
    (rw 0 rt2a-60 ∷ rw 0 rt2a-63 ∷ []) refl

  rt2a-66 : Eqn
  rt2a-66 = derive (x₀ ∷ x₁ ∷ cx′ ∷ [])
    (cx′ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2a-33 ∷ rw 2 rt2a-7 ∷ []) refl

  rt2a-71 : Eqn
  rt2a-71 = derive (s₁ ∷ x₁ ∷ s₁ ∷ [])
    (ι ∷ x₁ ∷ [])
    (rw⁻ 0 rt2a-5 ∷ rw 1 rt2a-54 ∷ rw 0 rt2a-15 ∷ []) refl

  rt2a-72 : Eqn
  rt2a-72 = derive (cs ∷ x₁ ∷ cs ∷ [])
    (s₀ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2a-5 ∷ rw 1 rt2a-55 ∷ rw 0 rt2a-22 ∷ []) refl

  rt2a-74 : Eqn
  rt2a-74 = derive (x₀ ∷ cx ∷ x₀ ∷ [])
    (x₁ ∷ cx ∷ [])
    (rw⁻ 1 rt2a-62 ∷ rw 0 rt2a-4 ∷ []) refl

  rt2a-81 : Eqn
  rt2a-81 = derive (cx ∷ cx′ ∷ x₁ ∷ [])
    (x₀ ∷ cx ∷ cx′ ∷ [])
    (rw⁻ 1 rt2a-66 ∷ rw 0 rt2a-64 ∷ []) refl

  rt2a-93 : Eqn
  rt2a-93 = derive (s₁ ∷ ck′ ∷ x₁ ∷ s₁ ∷ [])
    (ι ∷ ck′ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2a-37 ∷ rw 1 rt2a-71 ∷ rw 0 rt2a-39 ∷ []) refl

  rt2a-94 : Eqn
  rt2a-94 = derive (s₀ ∷ x₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2a-72 ∷ rw 2 rt2a-3 ∷ []) refl

  rt2a-104 : Eqn
  rt2a-104 = derive (x₁ ∷ cs ∷ x₁ ∷ cx ∷ [])
    (cx ∷ cs ∷ [])
    (rw⁻ 0 rt2a-49 ∷ rw 2 rt2a-6 ∷ []) refl

  rt2a-111 : Eqn
  rt2a-111 = derive (x₀ ∷ cs ∷ x₀ ∷ cx′ ∷ [])
    (cx′ ∷ cs ∷ [])
    (rw⁻ 0 rt2a-50 ∷ rw 2 rt2a-7 ∷ []) refl

  rt2a-133 : Eqn
  rt2a-133 = derive (x₁ ∷ cx ∷ cs ∷ [])
    (cs ∷ x₁ ∷ cx ∷ [])
    (rw⁻ 1 rt2a-104 ∷ rw 0 rt2a-5 ∷ []) refl

  rt2a-141 : Eqn
  rt2a-141 = derive (x₀ ∷ cx ∷ cx′ ∷ cs ∷ x₁ ∷ cx ∷ [])
    (cx ∷ cx′ ∷ cx ∷ cs ∷ [])
    (rw⁻ 0 rt2a-81 ∷ rw 2 rt2a-104 ∷ []) refl

  rt2a-158 : Eqn
  rt2a-158 = derive (x₀ ∷ cx ∷ cx′ ∷ cs ∷ [])
    (cs ∷ x₀ ∷ cx ∷ cx′ ∷ [])
    (rw⁻ 2 rt2a-111 ∷ rw 0 rt2a-74 ∷ rw 0 rt2a-133 ∷ rw 1 rt2a-63 ∷ []) refl

  rt2a-159 : Eqn
  rt2a-159 = derive (cx ∷ cx′ ∷ cx ∷ cs ∷ [])
    (cs ∷ cx ∷ cx′ ∷ cx ∷ [])
    (rw⁻ 0 rt2a-141 ∷ rw 0 rt2a-158 ∷ rw 2 rt2a-81 ∷ rw 1 rt2a-4 ∷ []) refl

  rt2a-193 : Eqn
  rt2a-193 = derive (x₁ ∷ s₁ ∷ x₁ ∷ cs ∷ [])
    (cs ∷ x₁ ∷ s₁ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2a-23 ∷ rw⁻ 3 rt2a-13 ∷ rw⁻ 2 rt2a-13 ∷ rw⁻ 1 rt2a-13 ∷ rw⁻ 0 rt2a-10 ∷ rw 1 rt2a-23 ∷ []) refl

  rt2a-438 : Eqn
  rt2a-438 = derive (x₁ ∷ s₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
    (ck′ ∷ x₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rt2a-23 ∷ rw⁻ 0 rt2a-9 ∷ rw⁻ 1 rt2a-9 ∷ rw⁻ 2 rt2a-9 ∷ rw⁻ 3 rt2a-93 ∷ rw 0 rt2a-2 ∷ []) refl

  rt2a-455 : Eqn
  rt2a-455 = derive (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ x₁ ∷ [])
    (x₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 rt2a-94 ∷ rw 0 rt2a-1 ∷ []) refl

  rt2a-743 : Eqn
  rt2a-743 = derive (cx ∷ cx′ ∷ cx ∷ ck ∷ cx ∷ cx′ ∷ [])
    (ck′ ∷ cx ∷ [])
    (rw⁻ 6 rt2a-6 ∷ rw 0 rt2a-44 ∷ []) refl

  rt2a-864 : Eqn
  rt2a-864 = derive (x₁ ∷ cs ∷ x₁ ∷ ck′ ∷ cs ∷ [])
    (ck′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2a-52 ∷ rw 2 rt2a-72 ∷ rw 1 rt2a-22 ∷ rw 2 rt2a-5 ∷ []) refl

  rt2a-870 : Eqn
  rt2a-870 = derive (cs ∷ x₁ ∷ ck′ ∷ cs ∷ [])
    (x₁ ∷ ck′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2a-5 ∷ rw 1 rt2a-864 ∷ []) refl

  rt2a-879 : Eqn
  rt2a-879 = derive (cs ∷ ck′ ∷ s₀ ∷ [])
    (s₀ ∷ ck′ ∷ cs ∷ [])
    (rw⁻ 1 rt2a-5 ∷ rw⁻ 2 rt2a-870 ∷ rw 0 rt2a-72 ∷ rw 1 rt2a-5 ∷ []) refl

  rt2a-919 : Eqn
  rt2a-919 = derive (s₀ ∷ ck′ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ [])
    (cs ∷ ck′ ∷ [])
    (rw⁻ 4 rt2a-12 ∷ rw⁻ 3 rt2a-12 ∷ rw⁻ 2 rt2a-12 ∷ rw⁻ 0 rt2a-879 ∷ rw 2 rt2a-1 ∷ []) refl

  rt2a-2052 : Eqn
  rt2a-2052 = derive (cx′ ∷ cx ∷ ck ∷ cx ∷ cx′ ∷ [])
    (cx ∷ ck′ ∷ cx ∷ [])
    (rw⁻ 0 rt2a-6 ∷ rw 1 rt2a-743 ∷ []) refl

  rt2a-2447 : Eqn
  rt2a-2447 = derive (ck′ ∷ s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ ck′ ∷ [])
    (rw⁻ 0 rt2a-1 ∷ rw 3 rt2a-919 ∷ []) refl

  rt2a-2730 : Eqn
  rt2a-2730 = derive (cx′ ∷ cx ∷ ck ∷ cx ∷ [])
    (cx ∷ ck′ ∷ cx ∷ cx′ ∷ [])
    (rw⁻ 4 rt2a-7 ∷ rw 0 rt2a-2052 ∷ []) refl

  rt2a-3150 : Eqn
  rt2a-3150 = derive (cx′ ∷ cx ∷ ck′ ∷ cx ∷ cx′ ∷ [])
    (cx ∷ ck ∷ cx ∷ [])
    (rw⁻ 1 rt2a-2730 ∷ rw 0 rt2a-7 ∷ []) refl

  rt2a-3155 : Eqn
  rt2a-3155 = derive (cx′ ∷ ck′ ∷ cx ∷ cx′ ∷ [])
    (cx ∷ cx′ ∷ ck ∷ cx ∷ [])
    (rw⁻ 1 rt2a-6 ∷ rw⁻ 2 rt2a-2730 ∷ rw 0 rt2a-35 ∷ rw 2 rt2a-6 ∷ []) refl

  rt2a-3207 : Eqn
  rt2a-3207 = derive (cx′ ∷ cx ∷ ck′ ∷ cx ∷ [])
    (cx ∷ ck ∷ cx ∷ cx′ ∷ [])
    (rw⁻ 4 rt2a-7 ∷ rw 0 rt2a-3150 ∷ []) refl

  rt2a-3212 : Eqn
  rt2a-3212 = derive (cx′ ∷ ck′ ∷ cx′ ∷ cx ∷ [])
    (cx ∷ cx′ ∷ ck ∷ cx′ ∷ [])
    (rw⁻ 2 rt2a-6 ∷ rw⁻ 3 rt2a-35 ∷ rw 0 rt2a-3155 ∷ rw 3 rt2a-6 ∷ []) refl

  rt2a-3276 : Eqn
  rt2a-3276 = derive (cx ∷ ck ∷ cx ∷ cx′ ∷ cx ∷ [])
    (cx′ ∷ cx ∷ ck′ ∷ [])
    (rw⁻ 0 rt2a-3207 ∷ rw 3 rt2a-6 ∷ []) refl

  rt2a-3389 : Eqn
  rt2a-3389 = derive (ck ∷ cx ∷ cx′ ∷ cx ∷ [])
    (cx ∷ cx′ ∷ cx ∷ ck′ ∷ [])
    (rw⁻ 0 rt2a-6 ∷ rw 1 rt2a-3276 ∷ []) refl

  rt2a-5946 : Eqn
  rt2a-5946 = derive (x₁ ∷ cs ∷ cs ∷ cs ∷ x₁ ∷ [])
    (s₀ ∷ s₀ ∷ s₀ ∷ cs ∷ [])
    (rw⁻ 0 rt2a-455 ∷ rw 4 rt2a-5 ∷ []) refl

  rt2a-13347 : Eqn
  rt2a-13347 = derive (ck′ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
    (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ ck′ ∷ [])
    (rw⁻ 1 rt2a-18 ∷ rw⁻ 2 rt2a-47 ∷ rw⁻ 0 rt2a-438 ∷ rw 4 rt2a-5946 ∷ rw 3 rt2a-2447 ∷ rw 2 rt2a-22 ∷
       rw 1 rt2a-11 ∷ rw 0 rt2a-22 ∷ rw 3 rt2a-22 ∷ rw 2 rt2a-11 ∷ rw 1 rt2a-22 ∷ rw 4 rt2a-22 ∷
       rw 3 rt2a-11 ∷ rw 2 rt2a-22 ∷ rw 3 rt2a-193 ∷ rw 0 rt2a-455 ∷ rw 3 rt2a-13 ∷ rw 2 rt2a-13 ∷
       rw 1 rt2a-13 ∷ rw 1 rt2a-47 ∷ rw 0 rt2a-18 ∷ []) refl

private
  ax-p-b : Eqn
  ax-p-b = derive (cx′ ∷ ck ∷ cx′ ∷ [])
    (cx ∷ cx′ ∷ ck′ ∷ cx′ ∷ cx ∷ [])
    (rw⁻ 0 rt2a-6 ∷ rw⁻ 1 rt2a-3212 ∷ []) refl

  ax-sw-pq : Eqn
  ax-sw-pq = derive (ck ∷ cx ∷ cx′ ∷ cx ∷ [])
    (cx ∷ cx′ ∷ cx ∷ ck′ ∷ [])
    (rw 0 rt2a-3389 ∷ []) refl

  ax-sw-C : Eqn
  ax-sw-C = derive (cx ∷ cx′ ∷ cx ∷ cs ∷ [])
    (cs ∷ cx ∷ cx′ ∷ cx ∷ [])
    (rw 0 rt2a-159 ∷ []) refl

  ax-q-i0 : Eqn
  ax-q-i0 = derive (ck′ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
    (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ ck′ ∷ [])
    (rw 0 rt2a-13347 ∷ []) refl

------------------------------------------------------------------------
-- The derived rules

private
  rt2f-6 : Eqn
  rt2f-6 = ax-m-a2

  rt2f-12 : Eqn
  rt2f-12 = ax-m-sC

  rt2f-18 : Eqn
  rt2f-18 = ax-m-xy

  rt2f-24 : Eqn
  rt2f-24 = sym⁼ (ax-m-yC)

  rt2f-27 : Eqn
  rt2f-27 = sym⁼ (ax-m-aC)

  rt2f-31 : Eqn
  rt2f-31 = ax-m-ax

  rt2f-76 : Eqn
  rt2f-76 = ax-q-i0

  rt2f-79 : Eqn
  rt2f-79 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2f-12 ∷ rw⁻ 1 rt2f-12 ∷ rw⁻ 2 rt2f-12 ∷ rw 0 rt2f-24 ∷ []) refl

  rt2f-80 : Eqn
  rt2f-80 = derive (cx ∷ cs ∷ cx ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2f-27 ∷ rw 2 rt2f-12 ∷ rw 1 rt2f-12 ∷ rw 0 rt2f-12 ∷ rw 0 rt2f-79 ∷ []) refl

  rt2f-138 : Eqn
  rt2f-138 = derive (x₀ ∷ x₁ ∷ cx ∷ [])
    (cx ∷ x₀ ∷ [])
    (rw⁻ 0 rt2f-31 ∷ rw 2 rt2f-6 ∷ []) refl

  rt2f-139 : Eqn
  rt2f-139 = derive (cx ∷ x₀ ∷ x₁ ∷ [])
    (x₀ ∷ cx ∷ [])
    (rw⁻ 1 rt2f-31 ∷ rw 0 rt2f-6 ∷ []) refl

  rt2f-245 : Eqn
  rt2f-245 = derive (cx ∷ cs ∷ x₀ ∷ x₁ ∷ [])
    (x₁ ∷ cs ∷ cx ∷ x₀ ∷ [])
    (rw⁻ 2 rt2f-31 ∷ rw 0 rt2f-80 ∷ rw 2 rt2f-18 ∷ rw 2 rt2f-138 ∷ []) refl

  rt2f-524 : Eqn
  rt2f-524 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ ck′ ∷ cx ∷ [])
    (ck′ ∷ x₀ ∷ x₁ ∷ cs ∷ cx ∷ x₀ ∷ [])
    (rw⁻ 0 rt2f-76 ∷ rw 4 rt2f-138 ∷ []) refl

  rt2f-3721 : Eqn
  rt2f-3721 = derive (cx ∷ ck′ ∷ x₀ ∷ x₁ ∷ cs ∷ cx ∷ x₀ ∷ [])
    (x₀ ∷ x₁ ∷ cs ∷ cx ∷ x₀ ∷ ck′ ∷ cx ∷ [])
    (rw⁻ 1 rt2f-524 ∷ rw 0 rt2f-139 ∷ rw 1 rt2f-245 ∷ []) refl

  rt2s-0 : Eqn
  rt2s-0 = ax-m-I4

  rt2s-1 : Eqn
  rt2s-1 = ax-m-s4

  rt2s-2 : Eqn
  rt2s-2 = ax-m-t4

  rt2s-3 : Eqn
  rt2s-3 = ax-m-C4

  rt2s-4 : Eqn
  rt2s-4 = ax-m-x2

  rt2s-5 : Eqn
  rt2s-5 = ax-m-y2

  rt2s-6 : Eqn
  rt2s-6 = ax-m-a2

  rt2s-7 : Eqn
  rt2s-7 = ax-m-b2

  rt2s-8 : Eqn
  rt2s-8 = ax-m-Is

  rt2s-9 : Eqn
  rt2s-9 = ax-m-It

  rt2s-10 : Eqn
  rt2s-10 = ax-m-IC

  rt2s-11 : Eqn
  rt2s-11 = ax-m-st

  rt2s-12 : Eqn
  rt2s-12 = ax-m-sC

  rt2s-13 : Eqn
  rt2s-13 = ax-m-tC

  rt2s-14 : Eqn
  rt2s-14 = ax-m-Ix

  rt2s-15 : Eqn
  rt2s-15 = ax-m-Iy

  rt2s-16 : Eqn
  rt2s-16 = ax-m-Ia

  rt2s-17 : Eqn
  rt2s-17 = ax-m-Ib

  rt2s-18 : Eqn
  rt2s-18 = ax-m-xy

  rt2s-19 : Eqn
  rt2s-19 = sym⁼ (ax-m-xs)

  rt2s-20 : Eqn
  rt2s-20 = ax-m-xt

  rt2s-21 : Eqn
  rt2s-21 = sym⁼ (ax-m-xC)

  rt2s-22 : Eqn
  rt2s-22 = ax-m-ys

  rt2s-23 : Eqn
  rt2s-23 = sym⁼ (ax-m-yt)

  rt2s-24 : Eqn
  rt2s-24 = sym⁼ (ax-m-yC)

  rt2s-25 : Eqn
  rt2s-25 = ax-m-as

  rt2s-26 : Eqn
  rt2s-26 = sym⁼ (ax-m-at)

  rt2s-27 : Eqn
  rt2s-27 = sym⁼ (ax-m-aC)

  rt2s-28 : Eqn
  rt2s-28 = ax-m-bt

  rt2s-29 : Eqn
  rt2s-29 = sym⁼ (ax-m-bs)

  rt2s-30 : Eqn
  rt2s-30 = sym⁼ (ax-m-bC)

  rt2s-31 : Eqn
  rt2s-31 = ax-m-ax

  rt2s-32 : Eqn
  rt2s-32 = ax-m-ay

  rt2s-33 : Eqn
  rt2s-33 = ax-m-by

  rt2s-34 : Eqn
  rt2s-34 = ax-m-bx

  rt2s-35 : Eqn
  rt2s-35 = sym⁼ (ax-m-ab)

  rt2s-36 : Eqn
  rt2s-36 = ax-p-13

  rt2s-37 : Eqn
  rt2s-37 = ax-p-14

  rt2s-38 : Eqn
  rt2s-38 = ax-p-15

  rt2s-39 : Eqn
  rt2s-39 = ax-p-16

  rt2s-40 : Eqn
  rt2s-40 = ax-q-13

  rt2s-41 : Eqn
  rt2s-41 = ax-q-14

  rt2s-42 : Eqn
  rt2s-42 = ax-q-15

  rt2s-43 : Eqn
  rt2s-43 = ax-q-16

  rt2s-45 : Eqn
  rt2s-45 = ax-q-I

  rt2s-46 : Eqn
  rt2s-46 = sym⁼ (ax-p-y)

  rt2s-47 : Eqn
  rt2s-47 = sym⁼ (ax-p-a)

  rt2s-48 : Eqn
  rt2s-48 = sym⁼ (ax-q-x)

  rt2s-49 : Eqn
  rt2s-49 = sym⁼ (ax-q-b)

  rt2s-51 : Eqn
  rt2s-51 = sym⁼ (ax-p-xpx)

  rt2s-52 : Eqn
  rt2s-52 = sym⁼ (ax-q-yqy)

  rt2s-53 : Eqn
  rt2s-53 = ax-p-i1

  rt2s-54 : Eqn
  rt2s-54 = ax-q-i2

  rt2s-55 : Eqn
  rt2s-55 = sym⁼ (ax-p-b)

  rt2s-56 : Eqn
  rt2s-56 = ax-sw-pq

  rt2s-57 : Eqn
  rt2s-57 = ax-K1

  rt2s-58 : Eqn
  rt2s-58 = ax-K0

  rt2s-59 : Eqn
  rt2s-59 = ax-k-l

  rt2s-60 : Eqn
  rt2s-60 = sym⁼ (ax-k2)

  rt2s-61 : Eqn
  rt2s-61 = sym⁼ (ax-l2)

  rt2s-64 : Eqn
  rt2s-64 = ax-k-I

  rt2s-65 : Eqn
  rt2s-65 = ax-l-I

  rt2s-66 : Eqn
  rt2s-66 = sym⁼ (ax-k-t)

  rt2s-67 : Eqn
  rt2s-67 = ax-l-s

  rt2s-68 : Eqn
  rt2s-68 = sym⁼ (ax-x-def)

  rt2s-69 : Eqn
  rt2s-69 = sym⁼ (ax-y-def)

  rt2s-70 : Eqn
  rt2s-70 = ax-sw-x

  rt2s-71 : Eqn
  rt2s-71 = ax-sw-y

  rt2s-72 : Eqn
  rt2s-72 = ax-sw-C

  rt2s-74 : Eqn
  rt2s-74 = sym⁼ (ax-aqa-C)

  rt2s-75 : Eqn
  rt2s-75 = sym⁼ (ax-aka)

  rt2s-76 : Eqn
  rt2s-76 = ax-q-i0

  rt2s-77 : Eqn
  rt2s-77 = derive (ι ∷ k₁ ∷ k₁ ∷ [])
    ([])
    (rw⁻ 0 rt2s-65 ∷ rw⁻ 1 rt2s-65 ∷ rw⁻ 0 rt2s-61 ∷ rw 0 rt2s-0 ∷ []) refl

  rt2s-78 : Eqn
  rt2s-78 = derive (s₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (x₀ ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-13 ∷ rw⁻ 1 rt2s-13 ∷ rw⁻ 2 rt2s-13 ∷ rw 0 rt2s-21 ∷ []) refl

  rt2s-79 : Eqn
  rt2s-79 = derive (s₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-12 ∷ rw⁻ 1 rt2s-12 ∷ rw⁻ 2 rt2s-12 ∷ rw 0 rt2s-24 ∷ []) refl

  rt2s-80 : Eqn
  rt2s-80 = derive (cx ∷ cs ∷ cx ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-27 ∷ rw 2 rt2s-12 ∷ rw 1 rt2s-12 ∷ rw 0 rt2s-12 ∷ rw 0 rt2s-79 ∷ []) refl

  rt2s-81 : Eqn
  rt2s-81 = derive (cx′ ∷ cs ∷ cx′ ∷ [])
    (x₀ ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-30 ∷ rw 2 rt2s-13 ∷ rw 1 rt2s-13 ∷ rw 0 rt2s-13 ∷ rw 0 rt2s-78 ∷ []) refl

  rt2s-82 : Eqn
  rt2s-82 = derive (cs ∷ ck ∷ cs ∷ ck ∷ [])
    (cx ∷ ck ∷ cs ∷ [])
    (rw⁻ 0 rt2s-37 ∷ rw 0 rt2s-36 ∷ []) refl

  rt2s-83 : Eqn
  rt2s-83 = derive (s₀ ∷ ck ∷ ck ∷ [])
    ([])
    (rw⁻ 0 rt2s-38 ∷ rw⁻ 1 rt2s-38 ∷ rw 0 rt2s-39 ∷ []) refl

  rt2s-84 : Eqn
  rt2s-84 = derive (cs ∷ ck′ ∷ cs ∷ ck′ ∷ [])
    (cx′ ∷ ck′ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-41 ∷ rw 0 rt2s-40 ∷ []) refl

  rt2s-85 : Eqn
  rt2s-85 = derive (s₁ ∷ ck′ ∷ ck′ ∷ [])
    ([])
    (rw⁻ 0 rt2s-42 ∷ rw⁻ 1 rt2s-42 ∷ rw 0 rt2s-43 ∷ []) refl

  rt2s-86 : Eqn
  rt2s-86 = derive (s₀ ∷ s₀ ∷ cs ∷ cs ∷ cx ∷ ck ∷ [])
    (x₁ ∷ ck ∷ x₁ ∷ [])
    (rw⁻ 4 rt2s-36 ∷ rw 0 rt2s-46 ∷ []) refl

  rt2s-87 : Eqn
  rt2s-87 = derive (cx ∷ ck ∷ cx ∷ [])
    (x₁ ∷ ck ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-47 ∷ rw 4 rt2s-36 ∷ rw 0 rt2s-86 ∷ []) refl

  rt2s-88 : Eqn
  rt2s-88 = derive (s₁ ∷ s₁ ∷ cs ∷ cs ∷ cx′ ∷ ck′ ∷ [])
    (x₀ ∷ ck′ ∷ x₀ ∷ [])
    (rw⁻ 4 rt2s-40 ∷ rw 0 rt2s-48 ∷ []) refl

  rt2s-89 : Eqn
  rt2s-89 = derive (cx′ ∷ ck′ ∷ cx′ ∷ [])
    (x₀ ∷ ck′ ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-49 ∷ rw 4 rt2s-40 ∷ rw 0 rt2s-88 ∷ []) refl

  rt2s-91 : Eqn
  rt2s-91 = derive (cx ∷ ck ∷ s₁ ∷ cs ∷ [])
    (x₀ ∷ cs ∷ x₀ ∷ ck ∷ [])
    (rw⁻ 2 rt2s-13 ∷ rw⁻ 0 rt2s-36 ∷ rw 0 rt2s-53 ∷ rw 2 rt2s-13 ∷ rw 1 rt2s-13 ∷ rw 0 rt2s-13 ∷
       rw 0 rt2s-78 ∷ []) refl

  rt2s-92 : Eqn
  rt2s-92 = derive (cx′ ∷ ck′ ∷ s₀ ∷ cs ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ ck′ ∷ [])
    (rw⁻ 2 rt2s-12 ∷ rw⁻ 0 rt2s-40 ∷ rw 0 rt2s-54 ∷ rw 2 rt2s-12 ∷ rw 1 rt2s-12 ∷ rw 0 rt2s-12 ∷
       rw 0 rt2s-79 ∷ []) refl

  rt2s-93 : Eqn
  rt2s-93 = derive (ι ∷ k₀ ∷ s₀ ∷ s₀ ∷ k₀ ∷ [])
    (x₀ ∷ [])
    (rw⁻ 0 rt2s-64 ∷ rw⁻ 1 rt2s-8 ∷ rw⁻ 2 rt2s-8 ∷ rw⁻ 3 rt2s-64 ∷ rw 0 rt2s-68 ∷ []) refl

  rt2s-94 : Eqn
  rt2s-94 = derive (ι ∷ k₁ ∷ s₁ ∷ s₁ ∷ k₁ ∷ [])
    (x₁ ∷ [])
    (rw⁻ 0 rt2s-65 ∷ rw⁻ 1 rt2s-9 ∷ rw⁻ 2 rt2s-9 ∷ rw⁻ 3 rt2s-65 ∷ rw 0 rt2s-69 ∷ []) refl

  rt2s-95 : Eqn
  rt2s-95 = derive (cx ∷ cx′ ∷ x₁ ∷ cx ∷ [])
    (x₀ ∷ cx ∷ cx′ ∷ cx ∷ [])
    (rw⁻ 2 rt2s-32 ∷ rw 0 rt2s-71 ∷ []) refl

  rt2s-97 : Eqn
  rt2s-97 = derive (cx ∷ x₀ ∷ ck′ ∷ x₀ ∷ cx ∷ [])
    (cx′ ∷ ck ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-89 ∷ rw 0 rt2s-55 ∷ []) refl

  rt2s-98 : Eqn
  rt2s-98 = derive (s₀ ∷ s₀ ∷ s₀ ∷ [])
    (ck ∷ ck ∷ [])
    (rw⁻ 3 rt2s-83 ∷ rw 0 rt2s-1 ∷ []) refl

  rt2s-99 : Eqn
  rt2s-99 = derive (x₀ ∷ s₀ ∷ x₀ ∷ [])
    (ι ∷ ck ∷ ck ∷ [])
    (rw⁻ 0 rt2s-19 ∷ rw 1 rt2s-98 ∷ []) refl

  rt2s-100 : Eqn
  rt2s-100 = derive (s₁ ∷ s₁ ∷ s₁ ∷ [])
    (ck′ ∷ ck′ ∷ [])
    (rw⁻ 3 rt2s-85 ∷ rw 0 rt2s-2 ∷ []) refl

  rt2s-101 : Eqn
  rt2s-101 = derive (x₁ ∷ s₁ ∷ x₁ ∷ [])
    (ι ∷ ck′ ∷ ck′ ∷ [])
    (rw⁻ 0 rt2s-23 ∷ rw 1 rt2s-100 ∷ []) refl

  rt2s-102 : Eqn
  rt2s-102 = derive (ι ∷ s₀ ∷ k₁ ∷ k₁ ∷ [])
    (s₀ ∷ [])
    (rw⁻ 0 rt2s-8 ∷ rw 1 rt2s-77 ∷ []) refl

  rt2s-103 : Eqn
  rt2s-103 = derive (ι ∷ s₁ ∷ k₁ ∷ k₁ ∷ [])
    (s₁ ∷ [])
    (rw⁻ 0 rt2s-9 ∷ rw 1 rt2s-77 ∷ []) refl

  rt2s-104 : Eqn
  rt2s-104 = derive (ι ∷ cs ∷ k₁ ∷ k₁ ∷ [])
    (cs ∷ [])
    (rw⁻ 0 rt2s-10 ∷ rw 1 rt2s-77 ∷ []) refl

  rt2s-105 : Eqn
  rt2s-105 = derive (s₀ ∷ s₁ ∷ ck ∷ ck ∷ [])
    (s₁ ∷ [])
    (rw⁻ 0 rt2s-11 ∷ rw 1 rt2s-83 ∷ []) refl

  rt2s-106 : Eqn
  rt2s-106 = derive (x₁ ∷ cs ∷ x₁ ∷ cs ∷ [])
    (s₀ ∷ [])
    (rw⁻ 0 rt2s-79 ∷ rw⁻ 0 rt2s-12 ∷ rw⁻ 1 rt2s-12 ∷ rw⁻ 2 rt2s-12 ∷ rw⁻ 3 rt2s-12 ∷ rw 0 rt2s-3 ∷ []) refl

  rt2s-107 : Eqn
  rt2s-107 = derive (s₀ ∷ cs ∷ ck ∷ ck ∷ [])
    (cs ∷ [])
    (rw⁻ 0 rt2s-12 ∷ rw 1 rt2s-83 ∷ []) refl

  rt2s-108 : Eqn
  rt2s-108 = derive (x₀ ∷ cs ∷ x₀ ∷ cs ∷ [])
    (s₁ ∷ [])
    (rw⁻ 0 rt2s-78 ∷ rw⁻ 0 rt2s-13 ∷ rw⁻ 1 rt2s-13 ∷ rw⁻ 2 rt2s-13 ∷ rw⁻ 3 rt2s-13 ∷ rw 0 rt2s-3 ∷ []) refl

  rt2s-109 : Eqn
  rt2s-109 = derive (s₁ ∷ cs ∷ ck′ ∷ ck′ ∷ [])
    (cs ∷ [])
    (rw⁻ 0 rt2s-13 ∷ rw 1 rt2s-85 ∷ []) refl

  rt2s-110 : Eqn
  rt2s-110 = derive (ι ∷ x₀ ∷ k₁ ∷ k₁ ∷ [])
    (x₀ ∷ [])
    (rw⁻ 0 rt2s-14 ∷ rw 1 rt2s-77 ∷ []) refl

  rt2s-111 : Eqn
  rt2s-111 = derive (ι ∷ x₁ ∷ k₁ ∷ k₁ ∷ [])
    (x₁ ∷ [])
    (rw⁻ 0 rt2s-15 ∷ rw 1 rt2s-77 ∷ []) refl

  rt2s-113 : Eqn
  rt2s-113 = derive (ι ∷ cx′ ∷ k₁ ∷ k₁ ∷ [])
    (cx′ ∷ [])
    (rw⁻ 0 rt2s-17 ∷ rw 1 rt2s-77 ∷ []) refl

  rt2s-115 : Eqn
  rt2s-115 = derive (x₁ ∷ s₁ ∷ x₀ ∷ [])
    (x₀ ∷ x₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-20 ∷ rw 0 rt2s-18 ∷ []) refl

  rt2s-117 : Eqn
  rt2s-117 = derive (s₀ ∷ x₁ ∷ ck ∷ ck ∷ [])
    (x₁ ∷ [])
    (rw⁻ 0 rt2s-22 ∷ rw 1 rt2s-83 ∷ []) refl

  rt2s-118 : Eqn
  rt2s-118 = derive (s₀ ∷ cx ∷ ck ∷ ck ∷ [])
    (cx ∷ [])
    (rw⁻ 0 rt2s-25 ∷ rw 1 rt2s-83 ∷ []) refl

  rt2s-119 : Eqn
  rt2s-119 = derive (cx′ ∷ s₀ ∷ s₁ ∷ [])
    (s₁ ∷ cx′ ∷ s₀ ∷ [])
    (rw⁻ 1 rt2s-11 ∷ rw 0 rt2s-28 ∷ []) refl

  rt2s-120 : Eqn
  rt2s-120 = derive (s₁ ∷ cx′ ∷ ck′ ∷ ck′ ∷ [])
    (cx′ ∷ [])
    (rw⁻ 0 rt2s-28 ∷ rw 1 rt2s-85 ∷ []) refl

  rt2s-121 : Eqn
  rt2s-121 = derive (cx ∷ x₀ ∷ x₁ ∷ [])
    (x₁ ∷ cx ∷ x₀ ∷ [])
    (rw⁻ 1 rt2s-18 ∷ rw 0 rt2s-32 ∷ []) refl

  rt2s-122 : Eqn
  rt2s-122 = derive (ck′ ∷ s₀ ∷ s₁ ∷ [])
    (s₁ ∷ ck′ ∷ s₀ ∷ [])
    (rw⁻ 1 rt2s-11 ∷ rw 0 rt2s-42 ∷ []) refl

  rt2s-124 : Eqn
  rt2s-124 = derive (ι ∷ ck′ ∷ k₁ ∷ k₁ ∷ [])
    (ck′ ∷ [])
    (rw⁻ 0 rt2s-45 ∷ rw 1 rt2s-77 ∷ []) refl

  rt2s-130 : Eqn
  rt2s-130 = derive (x₀ ∷ x₁ ∷ cx ∷ [])
    (cx ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-31 ∷ rw 2 rt2s-6 ∷ []) refl

  rt2s-131 : Eqn
  rt2s-131 = derive (x₁ ∷ cx ∷ x₀ ∷ [])
    (x₀ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-121 ∷ rw⁻ 1 rt2s-31 ∷ rw 0 rt2s-6 ∷ []) refl

  rt2s-132 : Eqn
  rt2s-132 = derive (cx ∷ x₀ ∷ x₁ ∷ [])
    (x₀ ∷ cx ∷ [])
    (rw 0 rt2s-121 ∷ rw 0 rt2s-131 ∷ []) refl

  rt2s-134 : Eqn
  rt2s-134 = derive (x₀ ∷ x₁ ∷ cx′ ∷ [])
    (cx′ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-33 ∷ rw 2 rt2s-7 ∷ []) refl

  rt2s-135 : Eqn
  rt2s-135 = derive (x₀ ∷ cx′ ∷ x₁ ∷ [])
    (x₁ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-34 ∷ rw⁻ 1 rt2s-33 ∷ rw 0 rt2s-7 ∷ []) refl

  rt2s-137 : Eqn
  rt2s-137 = derive (x₁ ∷ cx′ ∷ x₁ ∷ [])
    (x₀ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-135 ∷ rw⁻ 0 rt2s-34 ∷ rw⁻ 1 rt2s-18 ∷ rw⁻ 2 rt2s-33 ∷ rw 0 rt2s-33 ∷ rw 1 rt2s-5 ∷ []) refl

  rt2s-138 : Eqn
  rt2s-138 = derive (ck ∷ s₁ ∷ cs ∷ cs ∷ [])
    (cx ∷ ck ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-13 ∷ rw⁻ 2 rt2s-13 ∷ rw 0 rt2s-36 ∷ []) refl

  rt2s-139 : Eqn
  rt2s-139 = derive (s₀ ∷ ck ∷ cx ∷ ck ∷ [])
    (cs ∷ cs ∷ [])
    (rw⁻ 2 rt2s-36 ∷ rw 0 rt2s-83 ∷ []) refl

  rt2s-140 : Eqn
  rt2s-140 = derive (ck′ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (cx′ ∷ ck′ ∷ s₀ ∷ [])
    (rw⁻ 1 rt2s-12 ∷ rw⁻ 2 rt2s-12 ∷ rw 0 rt2s-40 ∷ []) refl

  rt2s-141 : Eqn
  rt2s-141 = derive (s₁ ∷ ck′ ∷ cx′ ∷ ck′ ∷ [])
    (cs ∷ cs ∷ [])
    (rw⁻ 2 rt2s-40 ∷ rw 0 rt2s-85 ∷ []) refl

  rt2s-142 : Eqn
  rt2s-142 = derive (ck ∷ x₀ ∷ ck ∷ [])
    (x₀ ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-4 ∷ rw 1 rt2s-57 ∷ []) refl

  rt2s-143 : Eqn
  rt2s-143 = derive (x₀ ∷ k₁ ∷ x₀ ∷ [])
    (k₁ ∷ [])
    (rw⁻ 0 rt2s-142 ∷ rw 0 rt2s-51 ∷ rw 1 rt2s-142 ∷ rw 0 rt2s-4 ∷ []) refl

  rt2s-144 : Eqn
  rt2s-144 = derive (k₁ ∷ x₀ ∷ [])
    (x₀ ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-143 ∷ rw 2 rt2s-4 ∷ []) refl

  rt2s-145 : Eqn
  rt2s-145 = derive (k₁ ∷ s₁ ∷ x₀ ∷ [])
    (x₀ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-20 ∷ rw 0 rt2s-144 ∷ []) refl

  rt2s-146 : Eqn
  rt2s-146 = derive (ck′ ∷ x₁ ∷ ck′ ∷ [])
    (x₁ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-5 ∷ rw 1 rt2s-58 ∷ []) refl

  rt2s-147 : Eqn
  rt2s-147 = derive (x₁ ∷ k₀ ∷ x₁ ∷ [])
    (k₀ ∷ [])
    (rw⁻ 0 rt2s-146 ∷ rw 0 rt2s-52 ∷ rw 1 rt2s-146 ∷ rw 0 rt2s-5 ∷ []) refl

  rt2s-148 : Eqn
  rt2s-148 = derive (k₀ ∷ x₁ ∷ [])
    (x₁ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-147 ∷ rw 2 rt2s-5 ∷ []) refl

  rt2s-149 : Eqn
  rt2s-149 = derive (k₀ ∷ x₀ ∷ x₁ ∷ [])
    (x₁ ∷ k₀ ∷ x₀ ∷ [])
    (rw⁻ 1 rt2s-18 ∷ rw 0 rt2s-148 ∷ []) refl

  rt2s-150 : Eqn
  rt2s-150 = derive (k₀ ∷ s₀ ∷ x₁ ∷ [])
    (x₁ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 1 rt2s-22 ∷ rw 0 rt2s-148 ∷ []) refl

  rt2s-152 : Eqn
  rt2s-152 = derive (s₀ ∷ k₁ ∷ k₁ ∷ [])
    (s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-67 ∷ rw⁻ 1 rt2s-67 ∷ rw⁻ 0 rt2s-61 ∷ rw⁻ 2 rt2s-8 ∷ rw⁻ 1 rt2s-8 ∷ rw⁻ 0 rt2s-8 ∷
       rw 1 rt2s-60 ∷ []) refl

  rt2s-153 : Eqn
  rt2s-153 = derive (ι ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ [])
    (rw⁻ 1 rt2s-152 ∷ rw 0 rt2s-102 ∷ []) refl

  rt2s-154 : Eqn
  rt2s-154 = derive (k₁ ∷ k₁ ∷ s₁ ∷ [])
    (s₁ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-61 ∷ rw⁻ 2 rt2s-9 ∷ rw⁻ 1 rt2s-9 ∷ rw⁻ 0 rt2s-9 ∷ rw 1 rt2s-60 ∷ []) refl

  rt2s-155 : Eqn
  rt2s-155 = derive (k₁ ∷ k₁ ∷ cs ∷ [])
    (cs ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-61 ∷ rw⁻ 2 rt2s-10 ∷ rw⁻ 1 rt2s-10 ∷ rw⁻ 0 rt2s-10 ∷ rw 1 rt2s-60 ∷ []) refl

  rt2s-156 : Eqn
  rt2s-156 = derive (x₀ ∷ k₁ ∷ k₁ ∷ [])
    (x₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-144 ∷ rw⁻ 1 rt2s-144 ∷ rw⁻ 0 rt2s-61 ∷ rw⁻ 2 rt2s-14 ∷ rw⁻ 1 rt2s-14 ∷ rw⁻ 0 rt2s-14 ∷
       rw 1 rt2s-60 ∷ []) refl

  rt2s-157 : Eqn
  rt2s-157 = derive (ι ∷ x₀ ∷ k₀ ∷ k₀ ∷ [])
    (x₀ ∷ [])
    (rw⁻ 1 rt2s-156 ∷ rw 0 rt2s-110 ∷ []) refl

  rt2s-158 : Eqn
  rt2s-158 = derive (k₁ ∷ k₁ ∷ x₁ ∷ [])
    (x₁ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-61 ∷ rw⁻ 2 rt2s-15 ∷ rw⁻ 1 rt2s-15 ∷ rw⁻ 0 rt2s-15 ∷ rw 1 rt2s-60 ∷ []) refl

  rt2s-159 : Eqn
  rt2s-159 = derive (k₁ ∷ k₁ ∷ cx ∷ [])
    (cx ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-61 ∷ rw⁻ 2 rt2s-16 ∷ rw⁻ 1 rt2s-16 ∷ rw⁻ 0 rt2s-16 ∷ rw 1 rt2s-60 ∷ []) refl

  rt2s-160 : Eqn
  rt2s-160 = derive (k₁ ∷ k₁ ∷ cx′ ∷ [])
    (cx′ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-61 ∷ rw⁻ 2 rt2s-17 ∷ rw⁻ 1 rt2s-17 ∷ rw⁻ 0 rt2s-17 ∷ rw 1 rt2s-60 ∷ []) refl

  rt2s-162 : Eqn
  rt2s-162 = derive (k₁ ∷ k₁ ∷ ck′ ∷ [])
    (ck′ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-61 ∷ rw⁻ 2 rt2s-45 ∷ rw⁻ 1 rt2s-45 ∷ rw⁻ 0 rt2s-45 ∷ rw 1 rt2s-60 ∷ []) refl

  rt2s-167 : Eqn
  rt2s-167 = derive (s₁ ∷ k₁ ∷ k₁ ∷ [])
    (s₁ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rt2s-61 ∷ rw 0 rt2s-9 ∷ rw 1 rt2s-9 ∷ rw 2 rt2s-9 ∷ rw 0 rt2s-61 ∷ rw 0 rt2s-154 ∷ []) refl

  rt2s-168 : Eqn
  rt2s-168 = derive (ι ∷ s₁ ∷ k₀ ∷ k₀ ∷ [])
    (s₁ ∷ [])
    (rw⁻ 1 rt2s-167 ∷ rw 0 rt2s-103 ∷ []) refl

  rt2s-169 : Eqn
  rt2s-169 = derive (cs ∷ k₁ ∷ k₁ ∷ [])
    (cs ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rt2s-61 ∷ rw 0 rt2s-10 ∷ rw 1 rt2s-10 ∷ rw 2 rt2s-10 ∷ rw 0 rt2s-61 ∷ rw 0 rt2s-155 ∷ []) refl

  rt2s-170 : Eqn
  rt2s-170 = derive (ι ∷ cs ∷ k₀ ∷ k₀ ∷ [])
    (cs ∷ [])
    (rw⁻ 1 rt2s-169 ∷ rw 0 rt2s-104 ∷ []) refl

  rt2s-171 : Eqn
  rt2s-171 = derive (x₁ ∷ k₁ ∷ k₁ ∷ [])
    (x₁ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rt2s-61 ∷ rw 0 rt2s-15 ∷ rw 1 rt2s-15 ∷ rw 2 rt2s-15 ∷ rw 0 rt2s-61 ∷ rw 0 rt2s-158 ∷ []) refl

  rt2s-172 : Eqn
  rt2s-172 = derive (ι ∷ x₁ ∷ k₀ ∷ k₀ ∷ [])
    (x₁ ∷ [])
    (rw⁻ 1 rt2s-171 ∷ rw 0 rt2s-111 ∷ []) refl

  rt2s-175 : Eqn
  rt2s-175 = derive (cx′ ∷ k₁ ∷ k₁ ∷ [])
    (cx′ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rt2s-61 ∷ rw 0 rt2s-17 ∷ rw 1 rt2s-17 ∷ rw 2 rt2s-17 ∷ rw 0 rt2s-61 ∷ rw 0 rt2s-160 ∷ []) refl

  rt2s-176 : Eqn
  rt2s-176 = derive (ι ∷ cx′ ∷ k₀ ∷ k₀ ∷ [])
    (cx′ ∷ [])
    (rw⁻ 1 rt2s-175 ∷ rw 0 rt2s-113 ∷ []) refl

  rt2s-179 : Eqn
  rt2s-179 = derive (ck′ ∷ k₁ ∷ k₁ ∷ [])
    (ck′ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rt2s-61 ∷ rw 0 rt2s-45 ∷ rw 1 rt2s-45 ∷ rw 2 rt2s-45 ∷ rw 0 rt2s-61 ∷ rw 0 rt2s-162 ∷ []) refl

  rt2s-180 : Eqn
  rt2s-180 = derive (ι ∷ ck′ ∷ k₀ ∷ k₀ ∷ [])
    (ck′ ∷ [])
    (rw⁻ 1 rt2s-179 ∷ rw 0 rt2s-124 ∷ []) refl

  rt2s-182 : Eqn
  rt2s-182 = derive (ι ∷ k₀ ∷ k₀ ∷ [])
    ([])
    (rw⁻ 1 rt2s-60 ∷ rw 0 rt2s-61 ∷ rw 1 rt2s-65 ∷ rw 0 rt2s-65 ∷ rw 0 rt2s-77 ∷ []) refl

  rt2s-183 : Eqn
  rt2s-183 = derive (k₁ ∷ k₁ ∷ [])
    (k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-61 ∷ rw 0 rt2s-60 ∷ []) refl

  rt2s-185 : Eqn
  rt2s-185 = derive (k₀ ∷ k₀ ∷ cs ∷ [])
    (cs ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-183 ∷ rw 0 rt2s-155 ∷ []) refl

  rt2s-186 : Eqn
  rt2s-186 = derive (k₀ ∷ k₀ ∷ cx ∷ [])
    (cx ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-183 ∷ rw 0 rt2s-159 ∷ []) refl

  rt2s-187 : Eqn
  rt2s-187 = derive (k₀ ∷ k₀ ∷ cx′ ∷ [])
    (cx′ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-183 ∷ rw 0 rt2s-160 ∷ []) refl

  rt2s-192 : Eqn
  rt2s-192 = derive (ck ∷ ck ∷ s₁ ∷ [])
    (s₁ ∷ ck ∷ ck ∷ [])
    (rw⁻ 0 rt2s-98 ∷ rw⁻ 2 rt2s-11 ∷ rw⁻ 1 rt2s-11 ∷ rw⁻ 0 rt2s-11 ∷ rw 1 rt2s-98 ∷ []) refl

  rt2s-193 : Eqn
  rt2s-193 = derive (ck ∷ ck ∷ cs ∷ [])
    (cs ∷ ck ∷ ck ∷ [])
    (rw⁻ 0 rt2s-98 ∷ rw⁻ 2 rt2s-12 ∷ rw⁻ 1 rt2s-12 ∷ rw⁻ 0 rt2s-12 ∷ rw 1 rt2s-98 ∷ []) refl

  rt2s-194 : Eqn
  rt2s-194 = derive (ck ∷ ck ∷ x₁ ∷ [])
    (x₁ ∷ ck ∷ ck ∷ [])
    (rw⁻ 0 rt2s-98 ∷ rw⁻ 2 rt2s-22 ∷ rw⁻ 1 rt2s-22 ∷ rw⁻ 0 rt2s-22 ∷ rw 1 rt2s-98 ∷ []) refl

  rt2s-195 : Eqn
  rt2s-195 = derive (ck ∷ ck ∷ cx ∷ [])
    (cx ∷ ck ∷ ck ∷ [])
    (rw⁻ 0 rt2s-98 ∷ rw⁻ 2 rt2s-25 ∷ rw⁻ 1 rt2s-25 ∷ rw⁻ 0 rt2s-25 ∷ rw 1 rt2s-98 ∷ []) refl

  rt2s-197 : Eqn
  rt2s-197 = derive (ck ∷ ck ∷ ck ∷ ck ∷ [])
    (s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-98 ∷ rw 2 rt2s-83 ∷ []) refl

  rt2s-198 : Eqn
  rt2s-198 = derive (ck′ ∷ ck′ ∷ s₀ ∷ [])
    (s₀ ∷ ck′ ∷ ck′ ∷ [])
    (rw⁻ 0 rt2s-100 ∷ rw 2 rt2s-11 ∷ rw 1 rt2s-11 ∷ rw 0 rt2s-11 ∷ rw 1 rt2s-100 ∷ []) refl

  rt2s-199 : Eqn
  rt2s-199 = derive (ck′ ∷ ck′ ∷ cs ∷ [])
    (cs ∷ ck′ ∷ ck′ ∷ [])
    (rw⁻ 0 rt2s-100 ∷ rw⁻ 2 rt2s-13 ∷ rw⁻ 1 rt2s-13 ∷ rw⁻ 0 rt2s-13 ∷ rw 1 rt2s-100 ∷ []) refl

  rt2s-200 : Eqn
  rt2s-200 = derive (ck′ ∷ ck′ ∷ x₀ ∷ [])
    (x₀ ∷ ck′ ∷ ck′ ∷ [])
    (rw⁻ 0 rt2s-100 ∷ rw⁻ 2 rt2s-20 ∷ rw⁻ 1 rt2s-20 ∷ rw⁻ 0 rt2s-20 ∷ rw 1 rt2s-100 ∷ []) refl

  rt2s-203 : Eqn
  rt2s-203 = derive (ck′ ∷ ck′ ∷ ck′ ∷ ck′ ∷ [])
    (s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-100 ∷ rw 2 rt2s-85 ∷ []) refl

  rt2s-206 : Eqn
  rt2s-206 = derive (s₀ ∷ x₁ ∷ s₁ ∷ ck ∷ ck ∷ [])
    (x₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-22 ∷ rw 1 rt2s-105 ∷ []) refl

  rt2s-207 : Eqn
  rt2s-207 = derive (s₀ ∷ cx ∷ s₁ ∷ ck ∷ ck ∷ [])
    (cx ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-25 ∷ rw 1 rt2s-105 ∷ []) refl

  rt2s-208 : Eqn
  rt2s-208 = derive (s₀ ∷ s₁ ∷ ck ∷ cx ∷ ck ∷ [])
    (s₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 rt2s-36 ∷ rw 0 rt2s-105 ∷ []) refl

  rt2s-209 : Eqn
  rt2s-209 = derive (s₀ ∷ ck ∷ s₁ ∷ ck ∷ ck ∷ [])
    (ck ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-38 ∷ rw 1 rt2s-105 ∷ []) refl

  rt2s-211 : Eqn
  rt2s-211 = derive (cs ∷ x₁ ∷ cs ∷ [])
    (s₀ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-5 ∷ rw 1 rt2s-106 ∷ rw 0 rt2s-22 ∷ []) refl

  rt2s-213 : Eqn
  rt2s-213 = derive (s₀ ∷ x₁ ∷ cs ∷ ck ∷ ck ∷ [])
    (x₁ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-22 ∷ rw 1 rt2s-107 ∷ []) refl

  rt2s-214 : Eqn
  rt2s-214 = derive (s₀ ∷ cx ∷ cs ∷ ck ∷ ck ∷ [])
    (cx ∷ cs ∷ [])
    (rw⁻ 0 rt2s-25 ∷ rw 1 rt2s-107 ∷ []) refl

  rt2s-215 : Eqn
  rt2s-215 = derive (s₀ ∷ cs ∷ ck ∷ cx ∷ ck ∷ [])
    (cs ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 rt2s-36 ∷ rw 0 rt2s-107 ∷ []) refl

  rt2s-216 : Eqn
  rt2s-216 = derive (s₀ ∷ ck ∷ cs ∷ ck ∷ ck ∷ [])
    (ck ∷ cs ∷ [])
    (rw⁻ 0 rt2s-38 ∷ rw 1 rt2s-107 ∷ []) refl

  rt2s-218 : Eqn
  rt2s-218 = derive (cs ∷ x₀ ∷ cs ∷ [])
    (s₁ ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-4 ∷ rw 1 rt2s-108 ∷ rw 0 rt2s-20 ∷ []) refl

  rt2s-220 : Eqn
  rt2s-220 = derive (s₁ ∷ x₀ ∷ cs ∷ ck′ ∷ ck′ ∷ [])
    (x₀ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-20 ∷ rw 1 rt2s-109 ∷ []) refl

  rt2s-221 : Eqn
  rt2s-221 = derive (s₁ ∷ cx′ ∷ cs ∷ ck′ ∷ ck′ ∷ [])
    (cx′ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-28 ∷ rw 1 rt2s-109 ∷ []) refl

  rt2s-222 : Eqn
  rt2s-222 = derive (s₁ ∷ cs ∷ ck′ ∷ cx′ ∷ ck′ ∷ [])
    (cs ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 rt2s-40 ∷ rw 0 rt2s-109 ∷ []) refl

  rt2s-234 : Eqn
  rt2s-234 = derive (s₀ ∷ ck ∷ x₁ ∷ ck ∷ ck ∷ [])
    (ck ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-38 ∷ rw 1 rt2s-117 ∷ []) refl

  rt2s-239 : Eqn
  rt2s-239 = derive (cs ∷ cs ∷ ck ∷ [])
    (ck ∷ cx ∷ [])
    (rw⁻ 0 rt2s-139 ∷ rw⁻ 0 rt2s-38 ∷ rw 1 rt2s-118 ∷ []) refl

  rt2s-243 : Eqn
  rt2s-243 = derive (cs ∷ cs ∷ ck′ ∷ [])
    (ck′ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-141 ∷ rw⁻ 0 rt2s-42 ∷ rw 1 rt2s-120 ∷ []) refl

  rt2s-245 : Eqn
  rt2s-245 = derive (x₀ ∷ cx ∷ x₀ ∷ [])
    (x₁ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-130 ∷ rw 0 rt2s-4 ∷ []) refl

  rt2s-247 : Eqn
  rt2s-247 = derive (cx′ ∷ cx ∷ x₀ ∷ [])
    (x₁ ∷ cx′ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-130 ∷ rw 0 rt2s-34 ∷ rw 0 rt2s-135 ∷ []) refl

  rt2s-249 : Eqn
  rt2s-249 = derive (x₁ ∷ cx ∷ s₁ ∷ x₀ ∷ [])
    (x₀ ∷ cx ∷ s₁ ∷ [])
    (rw⁻ 2 rt2s-20 ∷ rw 0 rt2s-131 ∷ []) refl

  rt2s-252 : Eqn
  rt2s-252 = derive (x₀ ∷ x₁ ∷ s₁ ∷ cx′ ∷ [])
    (cx′ ∷ x₁ ∷ s₁ ∷ [])
    (rw⁻ 2 rt2s-28 ∷ rw 0 rt2s-134 ∷ []) refl

  rt2s-254 : Eqn
  rt2s-254 = derive (cx ∷ cx′ ∷ x₁ ∷ [])
    (x₀ ∷ cx ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-134 ∷ rw 0 rt2s-132 ∷ []) refl

  rt2s-257 : Eqn
  rt2s-257 = derive (x₀ ∷ cx′ ∷ s₀ ∷ x₁ ∷ [])
    (x₁ ∷ cx′ ∷ s₀ ∷ [])
    (rw⁻ 2 rt2s-22 ∷ rw 0 rt2s-135 ∷ []) refl

  rt2s-263 : Eqn
  rt2s-263 = derive (s₀ ∷ ck ∷ x₀ ∷ k₁ ∷ [])
    (x₀ ∷ ck ∷ [])
    (rw⁻ 2 rt2s-142 ∷ rw 0 rt2s-83 ∷ []) refl

  rt2s-268 : Eqn
  rt2s-268 = derive (k₁ ∷ ck ∷ [])
    (ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-144 ∷ rw⁻ 0 rt2s-142 ∷ rw 2 rt2s-142 ∷ rw 1 rt2s-4 ∷ []) refl

  rt2s-269 : Eqn
  rt2s-269 = derive (ck ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ cx ∷ ck ∷ [])
    (rw⁻ 0 rt2s-268 ∷ rw 1 rt2s-36 ∷ []) refl

  rt2s-272 : Eqn
  rt2s-272 = derive (s₁ ∷ ck′ ∷ x₁ ∷ k₀ ∷ [])
    (x₁ ∷ ck′ ∷ [])
    (rw⁻ 2 rt2s-146 ∷ rw 0 rt2s-85 ∷ []) refl

  rt2s-276 : Eqn
  rt2s-276 = derive (k₀ ∷ ck′ ∷ [])
    (ck′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-5 ∷ rw⁻ 1 rt2s-148 ∷ rw⁻ 0 rt2s-146 ∷ rw 2 rt2s-146 ∷ rw 1 rt2s-5 ∷ []) refl

  rt2s-277 : Eqn
  rt2s-277 = derive (ck′ ∷ k₀ ∷ cs ∷ cs ∷ [])
    (k₀ ∷ cx′ ∷ ck′ ∷ [])
    (rw⁻ 0 rt2s-276 ∷ rw 1 rt2s-40 ∷ []) refl

  rt2s-279 : Eqn
  rt2s-279 = derive (ι ∷ s₀ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-8 ∷ rw 1 rt2s-153 ∷ []) refl

  rt2s-280 : Eqn
  rt2s-280 = derive (ι ∷ s₀ ∷ s₁ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-11 ∷ rw⁻ 0 rt2s-9 ∷ rw 1 rt2s-153 ∷ rw 0 rt2s-11 ∷ []) refl

  rt2s-283 : Eqn
  rt2s-283 = derive (ι ∷ s₀ ∷ x₁ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ x₁ ∷ [])
    (rw⁻ 1 rt2s-22 ∷ rw⁻ 0 rt2s-15 ∷ rw 1 rt2s-153 ∷ rw 0 rt2s-22 ∷ []) refl

  rt2s-300 : Eqn
  rt2s-300 = derive (ι ∷ s₁ ∷ s₁ ∷ k₀ ∷ k₀ ∷ [])
    (s₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-9 ∷ rw 1 rt2s-168 ∷ []) refl

  rt2s-308 : Eqn
  rt2s-308 = derive (ι ∷ cs ∷ cs ∷ k₀ ∷ k₀ ∷ [])
    (cs ∷ cs ∷ [])
    (rw⁻ 0 rt2s-10 ∷ rw 1 rt2s-170 ∷ []) refl

  rt2s-339 : Eqn
  rt2s-339 = derive (ι ∷ k₀ ∷ cx′ ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-64 ∷ rw 1 rt2s-176 ∷ []) refl

  rt2s-341 : Eqn
  rt2s-341 = derive (ι ∷ cx′ ∷ ck′ ∷ k₀ ∷ k₀ ∷ [])
    (cx′ ∷ ck′ ∷ [])
    (rw⁻ 2 rt2s-276 ∷ rw⁻ 3 rt2s-276 ∷ rw 0 rt2s-176 ∷ []) refl

  rt2s-354 : Eqn
  rt2s-354 = derive (cs ∷ x₁ ∷ s₁ ∷ cs ∷ [])
    (s₀ ∷ x₁ ∷ s₁ ∷ [])
    (rw⁻ 2 rt2s-13 ∷ rw 0 rt2s-211 ∷ []) refl

  rt2s-363 : Eqn
  rt2s-363 = derive (ck ∷ cx ∷ cs ∷ cs ∷ [])
    (cs ∷ cs ∷ cx ∷ ck ∷ [])
    (rw⁻ 0 rt2s-239 ∷ rw 2 rt2s-36 ∷ []) refl

  rt2s-364 : Eqn
  rt2s-364 = derive (ck ∷ cs ∷ ck ∷ cx ∷ [])
    (cx ∷ ck ∷ cs ∷ ck ∷ [])
    (rw⁻ 2 rt2s-239 ∷ rw 0 rt2s-36 ∷ []) refl

  rt2s-366 : Eqn
  rt2s-366 = derive (ck′ ∷ ck ∷ cx ∷ [])
    (cx′ ∷ ck′ ∷ ck ∷ [])
    (rw⁻ 1 rt2s-239 ∷ rw 0 rt2s-40 ∷ []) refl

  rt2s-369 : Eqn
  rt2s-369 = derive (cs ∷ x₀ ∷ ck ∷ cx ∷ [])
    (s₁ ∷ x₀ ∷ cs ∷ ck ∷ [])
    (rw⁻ 2 rt2s-239 ∷ rw 0 rt2s-218 ∷ []) refl

  rt2s-371 : Eqn
  rt2s-371 = derive (ck ∷ ck′ ∷ cx′ ∷ [])
    (cx ∷ ck ∷ ck′ ∷ [])
    (rw⁻ 1 rt2s-243 ∷ rw 0 rt2s-36 ∷ []) refl

  rt2s-377 : Eqn
  rt2s-377 = derive (x₀ ∷ cx ∷ s₁ ∷ x₀ ∷ [])
    (x₁ ∷ cx ∷ s₁ ∷ [])
    (rw⁻ 2 rt2s-20 ∷ rw 0 rt2s-245 ∷ []) refl

  rt2s-382 : Eqn
  rt2s-382 = derive (x₁ ∷ cs ∷ x₁ ∷ cx ∷ [])
    (cx ∷ cs ∷ [])
    (rw⁻ 0 rt2s-80 ∷ rw 2 rt2s-6 ∷ []) refl

  rt2s-383 : Eqn
  rt2s-383 = derive (x₁ ∷ cx ∷ cs ∷ x₁ ∷ [])
    (cs ∷ cx ∷ [])
    (rw⁻ 0 rt2s-32 ∷ rw⁻ 1 rt2s-80 ∷ rw 0 rt2s-6 ∷ []) refl

  rt2s-384 : Eqn
  rt2s-384 = derive (cx ∷ cs ∷ x₀ ∷ x₁ ∷ [])
    (x₁ ∷ cs ∷ cx ∷ x₀ ∷ [])
    (rw⁻ 2 rt2s-31 ∷ rw 0 rt2s-80 ∷ rw 2 rt2s-18 ∷ rw 2 rt2s-130 ∷ []) refl

  rt2s-387 : Eqn
  rt2s-387 = derive (cx ∷ x₀ ∷ cs ∷ cx ∷ [])
    (x₀ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-130 ∷ rw 2 rt2s-80 ∷ rw 1 rt2s-5 ∷ []) refl

  rt2s-388 : Eqn
  rt2s-388 = derive (cx ∷ cs ∷ x₀ ∷ cx ∷ [])
    (x₁ ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 2 rt2s-132 ∷ rw 0 rt2s-80 ∷ rw 2 rt2s-18 ∷ rw 3 rt2s-5 ∷ []) refl

  rt2s-389 : Eqn
  rt2s-389 = derive (x₀ ∷ cs ∷ x₀ ∷ cx′ ∷ [])
    (cx′ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-81 ∷ rw 2 rt2s-7 ∷ []) refl

  rt2s-390 : Eqn
  rt2s-390 = derive (x₀ ∷ cx′ ∷ cs ∷ x₀ ∷ [])
    (cs ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-34 ∷ rw⁻ 1 rt2s-81 ∷ rw 0 rt2s-7 ∷ []) refl

  rt2s-392 : Eqn
  rt2s-392 = derive (x₁ ∷ cx′ ∷ cs ∷ x₀ ∷ [])
    (x₀ ∷ x₁ ∷ cs ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-135 ∷ rw⁻ 0 rt2s-34 ∷ rw⁻ 1 rt2s-18 ∷ rw⁻ 2 rt2s-81 ∷ rw 0 rt2s-33 ∷ []) refl

  rt2s-397 : Eqn
  rt2s-397 = derive (x₁ ∷ ck ∷ x₁ ∷ cx ∷ [])
    (cx ∷ ck ∷ [])
    (rw⁻ 0 rt2s-87 ∷ rw 2 rt2s-6 ∷ []) refl

  rt2s-405 : Eqn
  rt2s-405 = derive (cx ∷ x₀ ∷ ck ∷ cx ∷ [])
    (x₀ ∷ ck ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-130 ∷ rw 2 rt2s-87 ∷ rw 1 rt2s-5 ∷ []) refl

  rt2s-407 : Eqn
  rt2s-407 = derive (x₀ ∷ ck′ ∷ x₀ ∷ cx′ ∷ [])
    (cx′ ∷ ck′ ∷ [])
    (rw⁻ 0 rt2s-89 ∷ rw 2 rt2s-7 ∷ []) refl

  rt2s-428 : Eqn
  rt2s-428 = derive (s₀ ∷ s₀ ∷ k₀ ∷ [])
    (k₀ ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-182 ∷ rw⁻ 0 rt2s-64 ∷ rw 1 rt2s-93 ∷ []) refl

  rt2s-429 : Eqn
  rt2s-429 = derive (ι ∷ k₀ ∷ x₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₀ ∷ [])
    (rw⁻ 1 rt2s-428 ∷ rw 0 rt2s-279 ∷ []) refl

  rt2s-450 : Eqn
  rt2s-450 = derive (s₁ ∷ s₁ ∷ k₁ ∷ [])
    (k₁ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-182 ∷ rw⁻ 1 rt2s-183 ∷ rw⁻ 0 rt2s-65 ∷ rw 1 rt2s-94 ∷ []) refl

  rt2s-457 : Eqn
  rt2s-457 = derive (s₁ ∷ s₁ ∷ k₀ ∷ k₀ ∷ [])
    (k₁ ∷ x₁ ∷ k₁ ∷ [])
    (rw⁻ 2 rt2s-183 ∷ rw 0 rt2s-450 ∷ []) refl

  rt2s-458 : Eqn
  rt2s-458 = derive (ι ∷ k₁ ∷ x₁ ∷ k₁ ∷ [])
    (s₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-457 ∷ rw 0 rt2s-300 ∷ []) refl

  rt2s-460 : Eqn
  rt2s-460 = derive (ι ∷ ck ∷ ck ∷ x₀ ∷ [])
    (x₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-99 ∷ rw 2 rt2s-4 ∷ []) refl

  rt2s-462 : Eqn
  rt2s-462 = derive (x₀ ∷ cx′ ∷ s₀ ∷ x₀ ∷ [])
    (ι ∷ cx′ ∷ ck ∷ ck ∷ [])
    (rw⁻ 0 rt2s-34 ∷ rw 1 rt2s-99 ∷ rw 0 rt2s-17 ∷ []) refl

  rt2s-468 : Eqn
  rt2s-468 = derive (ι ∷ ck′ ∷ ck′ ∷ x₁ ∷ [])
    (x₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-101 ∷ rw 2 rt2s-5 ∷ []) refl

  rt2s-470 : Eqn
  rt2s-470 = derive (x₁ ∷ cx ∷ s₁ ∷ x₁ ∷ [])
    (ι ∷ cx ∷ ck′ ∷ ck′ ∷ [])
    (rw⁻ 0 rt2s-32 ∷ rw 1 rt2s-101 ∷ rw 0 rt2s-16 ∷ []) refl

  rt2s-492 : Eqn
  rt2s-492 = derive (s₁ ∷ ck′ ∷ s₀ ∷ ck′ ∷ ck′ ∷ [])
    (ck′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-122 ∷ rw 2 rt2s-85 ∷ []) refl

  rt2s-512 : Eqn
  rt2s-512 = derive (s₁ ∷ ck′ ∷ k₀ ∷ cx′ ∷ ck′ ∷ [])
    (k₀ ∷ cs ∷ cs ∷ [])
    (rw⁻ 1 rt2s-276 ∷ rw⁻ 0 rt2s-66 ∷ rw 1 rt2s-141 ∷ []) refl

  rt2s-549 : Eqn
  rt2s-549 = derive (k₁ ∷ cx ∷ k₀ ∷ k₀ ∷ [])
    (k₀ ∷ k₀ ∷ k₁ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-186 ∷ rw 0 rt2s-59 ∷ rw 1 rt2s-59 ∷ []) refl

  rt2s-573 : Eqn
  rt2s-573 = derive (ι ∷ ck′ ∷ k₀ ∷ cx′ ∷ k₀ ∷ k₀ ∷ [])
    (ck′ ∷ k₀ ∷ cx′ ∷ [])
    (rw⁻ 3 rt2s-187 ∷ rw 0 rt2s-180 ∷ []) refl

  rt2s-606 : Eqn
  rt2s-606 = derive (s₁ ∷ ck ∷ ck ∷ ck′ ∷ ck′ ∷ [])
    (ck ∷ ck ∷ [])
    (rw⁻ 0 rt2s-192 ∷ rw 2 rt2s-85 ∷ []) refl

  rt2s-613 : Eqn
  rt2s-613 = derive (s₀ ∷ cx ∷ ck ∷ s₁ ∷ ck ∷ ck ∷ [])
    (cx ∷ ck ∷ s₁ ∷ [])
    (rw⁻ 3 rt2s-192 ∷ rw 0 rt2s-118 ∷ []) refl

  rt2s-621 : Eqn
  rt2s-621 = derive (s₀ ∷ s₁ ∷ ck ∷ cs ∷ ck ∷ ck ∷ [])
    (s₁ ∷ ck ∷ cs ∷ [])
    (rw⁻ 3 rt2s-193 ∷ rw 0 rt2s-105 ∷ []) refl

  rt2s-622 : Eqn
  rt2s-622 = derive (s₀ ∷ cx ∷ ck ∷ cs ∷ ck ∷ [])
    (cs ∷ ck ∷ cs ∷ [])
    (rw⁻ 1 rt2s-82 ∷ rw⁻ 3 rt2s-193 ∷ rw 0 rt2s-107 ∷ []) refl

  rt2s-654 : Eqn
  rt2s-654 = derive (s₁ ∷ cx′ ∷ ck′ ∷ cs ∷ ck′ ∷ [])
    (cs ∷ ck′ ∷ cs ∷ [])
    (rw⁻ 1 rt2s-84 ∷ rw⁻ 3 rt2s-199 ∷ rw 0 rt2s-109 ∷ []) refl

  rt2s-687 : Eqn
  rt2s-687 = derive (x₀ ∷ ck ∷ x₀ ∷ [])
    (s₀ ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-263 ∷ rw 3 rt2s-144 ∷ rw 2 rt2s-4 ∷ []) refl

  rt2s-688 : Eqn
  rt2s-688 = derive (x₀ ∷ ck ∷ s₁ ∷ x₀ ∷ [])
    (s₀ ∷ ck ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-263 ∷ rw 3 rt2s-145 ∷ rw 2 rt2s-4 ∷ []) refl

  rt2s-698 : Eqn
  rt2s-698 = derive (x₁ ∷ ck′ ∷ x₁ ∷ [])
    (s₁ ∷ ck′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-272 ∷ rw 3 rt2s-148 ∷ rw 2 rt2s-5 ∷ []) refl

  rt2s-700 : Eqn
  rt2s-700 = derive (x₁ ∷ ck′ ∷ s₀ ∷ x₁ ∷ [])
    (s₁ ∷ ck′ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-272 ∷ rw 3 rt2s-150 ∷ rw 2 rt2s-5 ∷ []) refl

  rt2s-736 : Eqn
  rt2s-736 = derive (x₁ ∷ cx ∷ cs ∷ [])
    (cs ∷ x₁ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-382 ∷ rw 0 rt2s-5 ∷ []) refl

  rt2s-737 : Eqn
  rt2s-737 = derive (cx ∷ cs ∷ x₁ ∷ [])
    (x₁ ∷ cs ∷ cx ∷ [])
    (rw⁻ 0 rt2s-382 ∷ rw 3 rt2s-32 ∷ rw 2 rt2s-5 ∷ []) refl

  rt2s-742 : Eqn
  rt2s-742 = derive (x₁ ∷ cs ∷ x₀ ∷ cx ∷ [])
    (cx ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 2 rt2s-131 ∷ rw 0 rt2s-382 ∷ []) refl

  rt2s-748 : Eqn
  rt2s-748 = derive (cs ∷ cx ∷ cs ∷ [])
    (s₀ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-382 ∷ rw 0 rt2s-211 ∷ rw 1 rt2s-5 ∷ []) refl

  rt2s-752 : Eqn
  rt2s-752 = derive (cs ∷ cx ∷ s₁ ∷ cs ∷ [])
    (s₀ ∷ cx ∷ s₁ ∷ [])
    (rw⁻ 2 rt2s-13 ∷ rw 0 rt2s-748 ∷ []) refl

  rt2s-758 : Eqn
  rt2s-758 = derive (cs ∷ x₁ ∷ ck ∷ x₁ ∷ [])
    (s₀ ∷ cx ∷ cs ∷ ck ∷ [])
    (rw⁻ 1 rt2s-87 ∷ rw⁻ 2 rt2s-239 ∷ rw 0 rt2s-748 ∷ []) refl

  rt2s-760 : Eqn
  rt2s-760 = derive (x₀ ∷ cx′ ∷ cs ∷ [])
    (cs ∷ x₀ ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-389 ∷ rw 0 rt2s-4 ∷ []) refl

  rt2s-763 : Eqn
  rt2s-763 = derive (cx′ ∷ cs ∷ x₁ ∷ cx′ ∷ [])
    (x₀ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-389 ∷ rw 3 rt2s-33 ∷ rw 2 rt2s-4 ∷ []) refl

  rt2s-764 : Eqn
  rt2s-764 = derive (cx′ ∷ cs ∷ x₀ ∷ [])
    (x₀ ∷ cs ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-389 ∷ rw 3 rt2s-34 ∷ rw 2 rt2s-4 ∷ []) refl

  rt2s-775 : Eqn
  rt2s-775 = derive (cs ∷ cx′ ∷ cs ∷ [])
    (s₁ ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-389 ∷ rw 0 rt2s-218 ∷ rw 1 rt2s-4 ∷ []) refl

  rt2s-779 : Eqn
  rt2s-779 = derive (cs ∷ cx′ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ cx′ ∷ s₀ ∷ [])
    (rw⁻ 2 rt2s-12 ∷ rw 0 rt2s-775 ∷ []) refl

  rt2s-781 : Eqn
  rt2s-781 = derive (x₀ ∷ ck′ ∷ x₀ ∷ cs ∷ [])
    (s₁ ∷ ck′ ∷ cs ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-89 ∷ rw⁻ 0 rt2s-40 ∷ rw 2 rt2s-775 ∷ rw 1 rt2s-13 ∷ rw 0 rt2s-42 ∷ []) refl

  rt2s-789 : Eqn
  rt2s-789 = derive (ck ∷ x₁ ∷ cx ∷ [])
    (x₁ ∷ cx ∷ ck ∷ [])
    (rw⁻ 0 rt2s-5 ∷ rw 1 rt2s-397 ∷ []) refl

  rt2s-794 : Eqn
  rt2s-794 = derive (ck′ ∷ x₀ ∷ cx′ ∷ [])
    (x₀ ∷ cx′ ∷ ck′ ∷ [])
    (rw⁻ 0 rt2s-4 ∷ rw 1 rt2s-407 ∷ []) refl

  rt2s-807 : Eqn
  rt2s-807 = derive (k₀ ∷ s₀ ∷ s₀ ∷ [])
    (x₀ ∷ k₀ ∷ [])
    (rw⁻ 1 rt2s-429 ∷ rw 0 rt2s-64 ∷ rw 0 rt2s-182 ∷ []) refl

  rt2s-854 : Eqn
  rt2s-854 = derive (k₁ ∷ s₁ ∷ s₁ ∷ [])
    (x₁ ∷ k₁ ∷ [])
    (rw⁻ 1 rt2s-458 ∷ rw 0 rt2s-65 ∷ rw 1 rt2s-183 ∷ rw 0 rt2s-182 ∷ []) refl

  rt2s-857 : Eqn
  rt2s-857 = derive (k₁ ∷ ck′ ∷ ck′ ∷ [])
    (x₁ ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-100 ∷ rw 0 rt2s-854 ∷ []) refl

  rt2s-870 : Eqn
  rt2s-870 = derive (ι ∷ cx′ ∷ ck ∷ ck ∷ x₀ ∷ [])
    (x₀ ∷ cx′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-17 ∷ rw 1 rt2s-460 ∷ rw 0 rt2s-34 ∷ []) refl

  rt2s-906 : Eqn
  rt2s-906 = derive (s₁ ∷ x₁ ∷ s₁ ∷ [])
    (ι ∷ x₁ ∷ [])
    (rw⁻ 1 rt2s-468 ∷ rw 0 rt2s-9 ∷ rw 1 rt2s-85 ∷ []) refl

  rt2s-921 : Eqn
  rt2s-921 = derive (s₁ ∷ cx′ ∷ x₁ ∷ s₁ ∷ [])
    (ι ∷ cx′ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-28 ∷ rw 1 rt2s-906 ∷ rw 0 rt2s-17 ∷ []) refl

  rt2s-947 : Eqn
  rt2s-947 = derive (x₀ ∷ s₀ ∷ ck ∷ k₁ ∷ [])
    (ck ∷ x₀ ∷ [])
    (rw⁻ 1 rt2s-687 ∷ rw 0 rt2s-4 ∷ []) refl

  rt2s-948 : Eqn
  rt2s-948 = derive (x₀ ∷ x₁ ∷ ck ∷ x₀ ∷ [])
    (s₀ ∷ x₁ ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-18 ∷ rw 1 rt2s-687 ∷ rw 0 rt2s-22 ∷ []) refl

  rt2s-949 : Eqn
  rt2s-949 = derive (cx′ ∷ s₀ ∷ ck ∷ k₁ ∷ [])
    (x₀ ∷ cx′ ∷ ck ∷ x₀ ∷ [])
    (rw⁻ 1 rt2s-687 ∷ rw 0 rt2s-34 ∷ []) refl

  rt2s-975 : Eqn
  rt2s-975 = derive (x₁ ∷ s₁ ∷ ck′ ∷ x₁ ∷ [])
    (ι ∷ ck′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-468 ∷ rw 3 rt2s-698 ∷ rw 2 rt2s-42 ∷ rw 1 rt2s-42 ∷ rw 1 rt2s-85 ∷ []) refl

  rt2s-976 : Eqn
  rt2s-976 = derive (x₁ ∷ cx ∷ s₁ ∷ cs ∷ [])
    (cs ∷ x₁ ∷ cx ∷ s₁ ∷ [])
    (rw⁻ 2 rt2s-13 ∷ rw 0 rt2s-736 ∷ []) refl

  rt2s-977 : Eqn
  rt2s-977 = derive (x₀ ∷ cs ∷ x₁ ∷ cx ∷ [])
    (cx ∷ x₀ ∷ cs ∷ [])
    (rw⁻ 1 rt2s-736 ∷ rw 0 rt2s-130 ∷ []) refl

  rt2s-980 : Eqn
  rt2s-980 = derive (cs ∷ x₀ ∷ cx ∷ cs ∷ [])
    (x₀ ∷ cx ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-131 ∷ rw⁻ 0 rt2s-736 ∷ rw 2 rt2s-218 ∷ rw 0 rt2s-249 ∷ []) refl

  rt2s-993 : Eqn
  rt2s-993 = derive (x₁ ∷ cs ∷ x₀ ∷ cx′ ∷ [])
    (cx′ ∷ x₁ ∷ cs ∷ [])
    (rw⁻ 1 rt2s-760 ∷ rw 0 rt2s-18 ∷ rw 0 rt2s-134 ∷ []) refl

  rt2s-997 : Eqn
  rt2s-997 = derive (cs ∷ x₁ ∷ cx′ ∷ cs ∷ [])
    (x₁ ∷ cx′ ∷ s₀ ∷ [])
    (rw⁻ 1 rt2s-135 ∷ rw⁻ 0 rt2s-760 ∷ rw 2 rt2s-211 ∷ rw 0 rt2s-257 ∷ []) refl

  rt2s-1005 : Eqn
  rt2s-1005 = derive (cx′ ∷ x₁ ∷ cs ∷ x₀ ∷ [])
    (x₁ ∷ cs ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-134 ∷ rw 2 rt2s-764 ∷ rw 1 rt2s-18 ∷ rw 0 rt2s-4 ∷ []) refl

  rt2s-1008 : Eqn
  rt2s-1008 = derive (cx′ ∷ s₀ ∷ cs ∷ ck ∷ k₁ ∷ [])
    (x₀ ∷ cs ∷ cx′ ∷ ck ∷ x₀ ∷ [])
    (rw⁻ 1 rt2s-12 ∷ rw⁻ 2 rt2s-687 ∷ rw 0 rt2s-764 ∷ []) refl

  rt2s-1012 : Eqn
  rt2s-1012 = derive (x₁ ∷ cx ∷ ck ∷ x₀ ∷ [])
    (ck ∷ x₀ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-789 ∷ rw 1 rt2s-131 ∷ []) refl

  rt2s-1014 : Eqn
  rt2s-1014 = derive (cs ∷ cs ∷ x₁ ∷ cx ∷ [])
    (s₀ ∷ ck ∷ x₁ ∷ ck ∷ [])
    (rw⁻ 0 rt2s-139 ∷ rw 3 rt2s-789 ∷ rw 2 rt2s-32 ∷ rw 1 rt2s-789 ∷ rw 2 rt2s-87 ∷ rw 1 rt2s-5 ∷ []) refl

  rt2s-1033 : Eqn
  rt2s-1033 = derive (x₀ ∷ cx′ ∷ ck′ ∷ x₁ ∷ [])
    (ck′ ∷ x₁ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-794 ∷ rw 1 rt2s-135 ∷ []) refl

  rt2s-1040 : Eqn
  rt2s-1040 = derive (k₀ ∷ x₀ ∷ cx′ ∷ ck′ ∷ [])
    (ck′ ∷ k₀ ∷ x₀ ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-794 ∷ rw 0 rt2s-276 ∷ []) refl

  rt2s-1071 : Eqn
  rt2s-1071 = derive (k₁ ∷ cs ∷ ck′ ∷ ck′ ∷ [])
    (x₁ ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (rw⁻ 1 rt2s-199 ∷ rw 0 rt2s-857 ∷ []) refl

  rt2s-1097 : Eqn
  rt2s-1097 = derive (x₀ ∷ ck ∷ ck ∷ x₀ ∷ [])
    (s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 2 rt2s-947 ∷ rw 0 rt2s-687 ∷ rw 2 rt2s-67 ∷ rw 1 rt2s-38 ∷ rw 3 rt2s-268 ∷ rw 1 rt2s-83 ∷
       rw 1 rt2s-183 ∷ []) refl

  rt2s-1104 : Eqn
  rt2s-1104 = derive (cx′ ∷ s₀ ∷ cx′ ∷ cs ∷ [])
    (cs ∷ cx ∷ s₁ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-29 ∷ rw⁻ 1 rt2s-13 ∷ rw⁻ 0 rt2s-12 ∷ rw 1 rt2s-26 ∷ []) refl

  rt2s-1106 : Eqn
  rt2s-1106 = derive (s₀ ∷ x₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (x₁ ∷ cx ∷ s₁ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-22 ∷ rw 1 rt2s-26 ∷ []) refl

  rt2s-1107 : Eqn
  rt2s-1107 = derive (s₀ ∷ cx ∷ s₁ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-25 ∷ rw 1 rt2s-26 ∷ rw 0 rt2s-6 ∷ []) refl

  rt2s-1112 : Eqn
  rt2s-1112 = derive (s₁ ∷ cx′ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (cx′ ∷ cx ∷ s₁ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-119 ∷ rw 1 rt2s-26 ∷ []) refl

  rt2s-1132 : Eqn
  rt2s-1132 = derive (cx′ ∷ s₀ ∷ cx′ ∷ [])
    (cx ∷ s₁ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-29 ∷ rw 0 rt2s-26 ∷ []) refl

  rt2s-1133 : Eqn
  rt2s-1133 = derive (s₀ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (cx ∷ s₁ ∷ cx ∷ [])
    (rw 0 rt2s-29 ∷ rw 0 rt2s-1132 ∷ []) refl

  rt2s-1134 : Eqn
  rt2s-1134 = derive (cx ∷ s₁ ∷ cx ∷ cs ∷ [])
    (cs ∷ cx ∷ s₁ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-1132 ∷ rw 0 rt2s-1104 ∷ []) refl

  rt2s-1136 : Eqn
  rt2s-1136 = derive (cx ∷ s₁ ∷ cx ∷ cx′ ∷ [])
    (cx′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-1132 ∷ rw 2 rt2s-7 ∷ []) refl

  rt2s-1138 : Eqn
  rt2s-1138 = derive (cx′ ∷ cx ∷ s₁ ∷ cx ∷ [])
    (s₀ ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-1132 ∷ rw 0 rt2s-7 ∷ []) refl

  rt2s-1139 : Eqn
  rt2s-1139 = derive (s₁ ∷ cx′ ∷ s₀ ∷ cs ∷ cs ∷ [])
    (s₀ ∷ cx′ ∷ [])
    (rw 0 rt2s-1112 ∷ rw 0 rt2s-1138 ∷ []) refl

  rt2s-1145 : Eqn
  rt2s-1145 = derive (cx′ ∷ s₀ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
    (cs ∷ cx′ ∷ s₀ ∷ [])
    (rw⁻ 2 rt2s-81 ∷ rw 0 rt2s-1132 ∷ rw 0 rt2s-1134 ∷ rw 1 rt2s-1136 ∷ []) refl

  rt2s-1156 : Eqn
  rt2s-1156 = derive (cx ∷ cx′ ∷ s₀ ∷ [])
    (s₁ ∷ cx ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-1136 ∷ rw 0 rt2s-6 ∷ []) refl

  rt2s-1158 : Eqn
  rt2s-1158 = derive (cx ∷ s₁ ∷ cx ∷ x₀ ∷ cx′ ∷ [])
    (cx′ ∷ s₀ ∷ x₀ ∷ [])
    (rw⁻ 3 rt2s-34 ∷ rw 0 rt2s-1136 ∷ []) refl

  rt2s-1173 : Eqn
  rt2s-1173 = derive (cx′ ∷ cx ∷ s₁ ∷ [])
    (s₀ ∷ cx′ ∷ cx ∷ [])
    (rw⁻ 3 rt2s-6 ∷ rw 0 rt2s-1138 ∷ []) refl

  rt2s-1198 : Eqn
  rt2s-1198 = derive (s₀ ∷ cx ∷ cx′ ∷ cx ∷ ck′ ∷ ck′ ∷ [])
    (cx ∷ cx′ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-35 ∷ rw⁻ 0 rt2s-1173 ∷ rw 2 rt2s-120 ∷ rw 0 rt2s-35 ∷ []) refl

  rt2s-1218 : Eqn
  rt2s-1218 = derive (s₁ ∷ k₀ ∷ cs ∷ cs ∷ cs ∷ [])
    (k₀ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-66 ∷ rw 1 rt2s-78 ∷ []) refl

  rt2s-1220 : Eqn
  rt2s-1220 = derive (cs ∷ cx′ ∷ s₀ ∷ [])
    (s₀ ∷ cx′ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-1145 ∷ rw⁻ 2 rt2s-78 ∷ rw 0 rt2s-119 ∷ rw 0 rt2s-1139 ∷ []) refl

  rt2s-1224 : Eqn
  rt2s-1224 = derive (s₀ ∷ cx′ ∷ cs ∷ cs ∷ [])
    (s₁ ∷ cx′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-1220 ∷ rw 0 rt2s-779 ∷ []) refl

  rt2s-1231 : Eqn
  rt2s-1231 = derive (x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ [])
    (cx ∷ s₁ ∷ x₁ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-78 ∷ rw 3 rt2s-211 ∷ rw 2 rt2s-12 ∷ rw 1 rt2s-12 ∷ rw 0 rt2s-11 ∷ rw 0 rt2s-1133 ∷
       rw 2 rt2s-32 ∷ []) refl

  rt2s-1233 : Eqn
  rt2s-1233 = derive (x₀ ∷ cs ∷ x₀ ∷ ck ∷ [])
    (s₁ ∷ cs ∷ ck ∷ cx ∷ [])
    (rw⁻ 0 rt2s-78 ∷ rw 2 rt2s-239 ∷ []) refl

  rt2s-1234 : Eqn
  rt2s-1234 = derive (cx ∷ ck ∷ s₁ ∷ cs ∷ [])
    (s₁ ∷ cs ∷ ck ∷ cx ∷ [])
    (rw 0 rt2s-91 ∷ rw 0 rt2s-1233 ∷ []) refl

  rt2s-1235 : Eqn
  rt2s-1235 = derive (x₀ ∷ cs ∷ x₀ ∷ ck′ ∷ [])
    (s₁ ∷ cs ∷ ck′ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-78 ∷ rw 2 rt2s-243 ∷ []) refl

  rt2s-1260 : Eqn
  rt2s-1260 = derive (s₀ ∷ k₁ ∷ cs ∷ cs ∷ cs ∷ [])
    (k₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-67 ∷ rw 1 rt2s-79 ∷ []) refl

  rt2s-1264 : Eqn
  rt2s-1264 = derive (x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ [])
    (cx ∷ s₁ ∷ cx ∷ x₀ ∷ [])
    (rw⁻ 2 rt2s-18 ∷ rw⁻ 0 rt2s-79 ∷ rw 3 rt2s-218 ∷ rw 2 rt2s-13 ∷ rw 1 rt2s-13 ∷ rw 0 rt2s-1133 ∷ []) refl

  rt2s-1265 : Eqn
  rt2s-1265 = derive (x₁ ∷ cs ∷ x₁ ∷ ck ∷ [])
    (s₀ ∷ cs ∷ ck ∷ cx ∷ [])
    (rw⁻ 0 rt2s-79 ∷ rw 2 rt2s-239 ∷ []) refl

  rt2s-1266 : Eqn
  rt2s-1266 = derive (x₁ ∷ cs ∷ x₁ ∷ ck′ ∷ [])
    (s₀ ∷ cs ∷ ck′ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-79 ∷ rw 2 rt2s-243 ∷ []) refl

  rt2s-1267 : Eqn
  rt2s-1267 = derive (cx′ ∷ ck′ ∷ s₀ ∷ cs ∷ [])
    (s₀ ∷ cs ∷ ck′ ∷ cx′ ∷ [])
    (rw 0 rt2s-92 ∷ rw 0 rt2s-1266 ∷ []) refl

  rt2s-1293 : Eqn
  rt2s-1293 = derive (cs ∷ x₀ ∷ cx′ ∷ ck ∷ cs ∷ ck ∷ [])
    (x₀ ∷ cx′ ∷ cx ∷ ck ∷ cs ∷ [])
    (rw⁻ 0 rt2s-760 ∷ rw 2 rt2s-82 ∷ []) refl

  rt2s-1298 : Eqn
  rt2s-1298 = derive (cs ∷ ck′ ∷ cs ∷ cx′ ∷ ck′ ∷ [])
    (ck′ ∷ cs ∷ [])
    (rw⁻ 3 rt2s-40 ∷ rw 0 rt2s-84 ∷ rw 1 rt2s-40 ∷ rw 0 rt2s-7 ∷ []) refl

  rt2s-1332 : Eqn
  rt2s-1332 = derive (x₀ ∷ cs ∷ x₀ ∷ cx ∷ ck ∷ [])
    (ck ∷ s₁ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-78 ∷ rw⁻ 2 rt2s-363 ∷ rw⁻ 0 rt2s-1234 ∷ rw⁻ 0 rt2s-138 ∷ rw 3 rt2s-3 ∷ []) refl

  rt2s-1333 : Eqn
  rt2s-1333 = derive (s₁ ∷ cs ∷ ck ∷ cx ∷ cs ∷ [])
    (ck ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-1234 ∷ rw⁻ 0 rt2s-138 ∷ rw 2 rt2s-3 ∷ []) refl

  rt2s-1335 : Eqn
  rt2s-1335 = derive (ck ∷ x₀ ∷ cs ∷ x₀ ∷ [])
    (s₁ ∷ cs ∷ ck ∷ cx ∷ [])
    (rw⁻ 1 rt2s-78 ∷ rw 0 rt2s-138 ∷ rw 0 rt2s-1234 ∷ []) refl

  rt2s-1349 : Eqn
  rt2s-1349 = derive (s₀ ∷ cs ∷ ck′ ∷ cx′ ∷ cs ∷ [])
    (ck′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-1267 ∷ rw⁻ 0 rt2s-140 ∷ rw 2 rt2s-3 ∷ []) refl

  rt2s-1351 : Eqn
  rt2s-1351 = derive (ck′ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
    (s₀ ∷ cs ∷ ck′ ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-79 ∷ rw 0 rt2s-140 ∷ rw 0 rt2s-1267 ∷ []) refl

  rt2s-1400 : Eqn
  rt2s-1400 = derive (s₀ ∷ x₁ ∷ s₁ ∷ ck ∷ cx ∷ ck ∷ [])
    (x₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 4 rt2s-36 ∷ rw 0 rt2s-206 ∷ []) refl

  rt2s-1419 : Eqn
  rt2s-1419 = derive (s₀ ∷ cx ∷ s₁ ∷ ck ∷ cs ∷ ck ∷ ck ∷ [])
    (cx ∷ s₁ ∷ ck ∷ cs ∷ [])
    (rw⁻ 4 rt2s-193 ∷ rw 0 rt2s-207 ∷ []) refl

  rt2s-1430 : Eqn
  rt2s-1430 = derive (s₀ ∷ ck ∷ s₁ ∷ ck ∷ cs ∷ ck ∷ ck ∷ [])
    (ck ∷ s₁ ∷ ck ∷ cs ∷ [])
    (rw⁻ 4 rt2s-193 ∷ rw 0 rt2s-209 ∷ []) refl

  rt2s-1454 : Eqn
  rt2s-1454 = derive (cs ∷ cx′ ∷ x₁ ∷ cs ∷ [])
    (s₀ ∷ cx′ ∷ x₁ ∷ [])
    (rw⁻ 2 rt2s-213 ∷ rw 0 rt2s-1220 ∷ rw 2 rt2s-211 ∷ rw 2 rt2s-117 ∷ []) refl

  rt2s-1460 : Eqn
  rt2s-1460 = derive (cx ∷ cs ∷ ck ∷ cs ∷ [])
    (s₀ ∷ ck ∷ cs ∷ ck ∷ [])
    (rw⁻ 0 rt2s-214 ∷ rw 4 rt2s-193 ∷ rw 2 rt2s-82 ∷ rw 1 rt2s-6 ∷ []) refl

  rt2s-1470 : Eqn
  rt2s-1470 = derive (ck ∷ cs ∷ ck ∷ cs ∷ [])
    (cs ∷ ck ∷ cx ∷ [])
    (rw⁻ 0 rt2s-216 ∷ rw 4 rt2s-193 ∷ rw 2 rt2s-82 ∷ rw 0 rt2s-139 ∷ rw 1 rt2s-239 ∷ []) refl

  rt2s-1503 : Eqn
  rt2s-1503 = derive (s₁ ∷ cx′ ∷ cs ∷ ck′ ∷ s₀ ∷ ck′ ∷ ck′ ∷ [])
    (cx′ ∷ cs ∷ ck′ ∷ s₀ ∷ [])
    (rw⁻ 4 rt2s-198 ∷ rw 0 rt2s-221 ∷ []) refl

  rt2s-1677 : Eqn
  rt2s-1677 = derive (x₀ ∷ cx ∷ s₁ ∷ cx ∷ x₀ ∷ [])
    (ι ∷ cx ∷ ck′ ∷ ck′ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-249 ∷ rw 3 rt2s-245 ∷ rw 0 rt2s-470 ∷ []) refl

  rt2s-1836 : Eqn
  rt2s-1836 = derive (s₀ ∷ cx ∷ ck ∷ k₁ ∷ cx ∷ ck ∷ [])
    (cx ∷ k₁ ∷ cs ∷ cs ∷ [])
    (rw⁻ 3 rt2s-269 ∷ rw 0 rt2s-118 ∷ []) refl

  rt2s-1913 : Eqn
  rt2s-1913 = derive (ι ∷ s₀ ∷ s₁ ∷ k₀ ∷ cx′ ∷ k₀ ∷ k₀ ∷ [])
    (s₀ ∷ s₁ ∷ k₀ ∷ cx′ ∷ [])
    (rw⁻ 4 rt2s-187 ∷ rw 0 rt2s-280 ∷ []) refl

  rt2s-1958 : Eqn
  rt2s-1958 = derive (ι ∷ s₀ ∷ x₁ ∷ k₀ ∷ x₀ ∷ k₀ ∷ [])
    (x₁ ∷ ck ∷ ck ∷ [])
    (rw⁻ 4 rt2s-807 ∷ rw 0 rt2s-283 ∷ rw 1 rt2s-22 ∷ rw 2 rt2s-22 ∷ rw 0 rt2s-98 ∷ rw 0 rt2s-194 ∷ []) refl

  rt2s-2754 : Eqn
  rt2s-2754 = derive (cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ [])
    (x₁ ∷ cx ∷ s₁ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-18 ∷ rw⁻ 2 rt2s-78 ∷ rw 0 rt2s-354 ∷ rw 0 rt2s-1106 ∷ []) refl

  rt2s-2815 : Eqn
  rt2s-2815 = derive (cx ∷ x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
    (x₀ ∷ cs ∷ cx ∷ x₀ ∷ [])
    (rw⁻ 3 rt2s-31 ∷ rw 0 rt2s-387 ∷ rw 2 rt2s-18 ∷ rw 2 rt2s-130 ∷ []) refl

  rt2s-2825 : Eqn
  rt2s-2825 = derive (cx′ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
    (x₁ ∷ cs ∷ x₁ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-993 ∷ rw⁻ 0 rt2s-388 ∷ rw 3 rt2s-254 ∷ rw 2 rt2s-4 ∷ rw 0 rt2s-80 ∷ []) refl

  rt2s-2844 : Eqn
  rt2s-2844 = derive (s₀ ∷ cx ∷ ck ∷ k₁ ∷ cx ∷ [])
    (s₀ ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-25 ∷ rw⁻ 1 rt2s-687 ∷ rw⁻ 3 rt2s-132 ∷ rw 0 rt2s-405 ∷ rw 2 rt2s-18 ∷ rw 0 rt2s-687 ∷
       rw 3 rt2s-5 ∷ []) refl

  rt2s-2845 : Eqn
  rt2s-2845 = derive (cx ∷ k₁ ∷ cs ∷ cs ∷ [])
    (k₁ ∷ [])
    (rw⁻ 0 rt2s-1836 ∷ rw 0 rt2s-2844 ∷ rw 2 rt2s-268 ∷ rw 0 rt2s-83 ∷ []) refl

  rt2s-2860 : Eqn
  rt2s-2860 = derive (k₁ ∷ cs ∷ cs ∷ [])
    (cx ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-2845 ∷ rw 2 rt2s-3 ∷ []) refl

  rt2s-2881 : Eqn
  rt2s-2881 = derive (k₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
    (s₀ ∷ cx ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-1260 ∷ rw 1 rt2s-2860 ∷ []) refl

  rt2s-2882 : Eqn
  rt2s-2882 = derive (k₁ ∷ cx ∷ ck ∷ [])
    (ck ∷ cx ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-269 ∷ rw 1 rt2s-2860 ∷ []) refl

  rt2s-2895 : Eqn
  rt2s-2895 = derive (k₁ ∷ s₁ ∷ cs ∷ cs ∷ [])
    (cx ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-13 ∷ rw⁻ 2 rt2s-13 ∷ rw 0 rt2s-2860 ∷ []) refl

  rt2s-2901 : Eqn
  rt2s-2901 = derive (k₁ ∷ cs ∷ cx ∷ ck ∷ cs ∷ [])
    (cx ∷ ck ∷ k₁ ∷ cs ∷ ck ∷ [])
    (rw⁻ 2 rt2s-82 ∷ rw 0 rt2s-2860 ∷ rw 1 rt2s-268 ∷ []) refl

  rt2s-2903 : Eqn
  rt2s-2903 = derive (cs ∷ cs ∷ k₀ ∷ k₀ ∷ [])
    (k₁ ∷ cx ∷ k₁ ∷ [])
    (rw⁻ 1 rt2s-185 ∷ rw⁻ 0 rt2s-185 ∷ rw⁻ 0 rt2s-183 ∷ rw 1 rt2s-2860 ∷ []) refl

  rt2s-2905 : Eqn
  rt2s-2905 = derive (ι ∷ k₁ ∷ cx ∷ k₁ ∷ [])
    (cs ∷ cs ∷ [])
    (rw⁻ 1 rt2s-2903 ∷ rw 0 rt2s-308 ∷ []) refl

  rt2s-2914 : Eqn
  rt2s-2914 = derive (k₁ ∷ s₁ ∷ cs ∷ x₀ ∷ [])
    (cx ∷ x₀ ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 1 rt2s-13 ∷ rw⁻ 2 rt2s-218 ∷ rw 0 rt2s-2860 ∷ rw 1 rt2s-144 ∷ []) refl

  rt2s-2918 : Eqn
  rt2s-2918 = derive (ck ∷ k₁ ∷ cx ∷ [])
    (cx ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-268 ∷ rw⁻ 1 rt2s-239 ∷ rw 0 rt2s-2860 ∷ rw 1 rt2s-268 ∷ []) refl

  rt2s-2951 : Eqn
  rt2s-2951 = derive (cs ∷ cs ∷ k₁ ∷ [])
    (k₁ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-2905 ∷ rw 3 rt2s-183 ∷ rw 1 rt2s-549 ∷ rw 0 rt2s-182 ∷ []) refl

  rt2s-3361 : Eqn
  rt2s-3361 = derive (cs ∷ cx ∷ s₁ ∷ [])
    (s₁ ∷ cx ∷ cs ∷ [])
    (rw⁻ 3 rt2s-3 ∷ rw 0 rt2s-752 ∷ rw 0 rt2s-1107 ∷ []) refl

  rt2s-3407 : Eqn
  rt2s-3407 = derive (cx ∷ x₀ ∷ cs ∷ x₀ ∷ [])
    (x₀ ∷ cs ∷ x₀ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-977 ∷ rw⁻ 0 rt2s-763 ∷ rw 3 rt2s-247 ∷ rw 2 rt2s-5 ∷ rw 0 rt2s-81 ∷ []) refl

  rt2s-3642 : Eqn
  rt2s-3642 = derive (s₁ ∷ k₀ ∷ cx′ ∷ x₁ ∷ s₁ ∷ [])
    (ι ∷ k₀ ∷ cx′ ∷ x₁ ∷ [])
    (rw⁻ 0 rt2s-66 ∷ rw 1 rt2s-921 ∷ rw 0 rt2s-64 ∷ []) refl

  rt2s-3743 : Eqn
  rt2s-3743 = derive (x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ ck ∷ x₁ ∷ [])
    (ck ∷ s₁ ∷ cs ∷ cx ∷ [])
    (rw⁻ 2 rt2s-18 ∷ rw⁻ 3 rt2s-405 ∷ rw 0 rt2s-977 ∷ rw 0 rt2s-3407 ∷ rw 0 rt2s-1332 ∷ []) refl

  rt2s-3758 : Eqn
  rt2s-3758 = derive (x₀ ∷ cx ∷ s₁ ∷ ck ∷ cs ∷ ck ∷ [])
    (cs ∷ x₀ ∷ ck ∷ cs ∷ [])
    (rw⁻ 0 rt2s-980 ∷ rw 3 rt2s-82 ∷ rw 2 rt2s-6 ∷ []) refl

  rt2s-3817 : Eqn
  rt2s-3817 = derive (x₁ ∷ cx′ ∷ s₀ ∷ ck′ ∷ cs ∷ ck′ ∷ [])
    (cs ∷ x₁ ∷ ck′ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-997 ∷ rw 3 rt2s-84 ∷ rw 2 rt2s-7 ∷ []) refl

  rt2s-3848 : Eqn
  rt2s-3848 = derive (x₁ ∷ cx′ ∷ cx ∷ ck ∷ x₀ ∷ [])
    (x₀ ∷ cx′ ∷ ck ∷ x₀ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-135 ∷ rw 2 rt2s-1012 ∷ []) refl

  rt2s-3927 : Eqn
  rt2s-3927 = derive (s₁ ∷ ck′ ∷ k₀ ∷ cx′ ∷ [])
    (s₁ ∷ cx′ ∷ ck′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-698 ∷ rw⁻ 1 rt2s-1033 ∷ rw 0 rt2s-18 ∷ rw 0 rt2s-134 ∷ rw 1 rt2s-698 ∷ rw 0 rt2s-28 ∷ []) refl

  rt2s-3928 : Eqn
  rt2s-3928 = derive (k₀ ∷ cs ∷ cs ∷ [])
    (cx′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-512 ∷ rw 0 rt2s-3927 ∷ rw 3 rt2s-276 ∷ rw 0 rt2s-120 ∷ []) refl

  rt2s-3949 : Eqn
  rt2s-3949 = derive (k₀ ∷ cx′ ∷ ck′ ∷ [])
    (ck′ ∷ cx′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-277 ∷ rw 1 rt2s-3928 ∷ []) refl

  rt2s-3952 : Eqn
  rt2s-3952 = derive (k₀ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
    (s₁ ∷ cx′ ∷ k₀ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-1218 ∷ rw 1 rt2s-3928 ∷ []) refl

  rt2s-3973 : Eqn
  rt2s-3973 = derive (ι ∷ ck′ ∷ k₀ ∷ cx′ ∷ [])
    (ι ∷ cx′ ∷ ck′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-975 ∷ rw⁻ 2 rt2s-1033 ∷ rw 0 rt2s-115 ∷ rw 0 rt2s-252 ∷ rw 1 rt2s-975 ∷ rw 0 rt2s-17 ∷ []) refl

  rt2s-3974 : Eqn
  rt2s-3974 = derive (ck′ ∷ k₀ ∷ cx′ ∷ [])
    (cx′ ∷ ck′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-573 ∷ rw 0 rt2s-3973 ∷ rw 0 rt2s-341 ∷ []) refl

  rt2s-4034 : Eqn
  rt2s-4034 = derive (ι ∷ k₀ ∷ cx′ ∷ k₀ ∷ [])
    (cs ∷ cs ∷ [])
    (rw⁻ 2 rt2s-3928 ∷ rw 0 rt2s-182 ∷ []) refl

  rt2s-4035 : Eqn
  rt2s-4035 = derive (cs ∷ cs ∷ k₀ ∷ [])
    (k₀ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-4034 ∷ rw 0 rt2s-339 ∷ []) refl

  rt2s-4062 : Eqn
  rt2s-4062 = derive (ι ∷ s₀ ∷ s₁ ∷ k₀ ∷ cx′ ∷ k₀ ∷ [])
    (cx ∷ s₁ ∷ cx ∷ [])
    (rw⁻ 4 rt2s-3928 ∷ rw 0 rt2s-280 ∷ rw 0 rt2s-1133 ∷ []) refl

  rt2s-4063 : Eqn
  rt2s-4063 = derive (cx ∷ s₁ ∷ cx ∷ k₀ ∷ [])
    (s₀ ∷ s₁ ∷ k₀ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-4062 ∷ rw 0 rt2s-1913 ∷ []) refl

  rt2s-4236 : Eqn
  rt2s-4236 = derive (ck′ ∷ k₀ ∷ x₀ ∷ cx′ ∷ [])
    (cx′ ∷ ck′ ∷ k₀ ∷ x₀ ∷ [])
    (rw⁻ 2 rt2s-34 ∷ rw 0 rt2s-3974 ∷ []) refl

  rt2s-4237 : Eqn
  rt2s-4237 = derive (k₀ ∷ x₀ ∷ cx′ ∷ ck′ ∷ [])
    (cx′ ∷ ck′ ∷ k₀ ∷ x₀ ∷ [])
    (rw 0 rt2s-1040 ∷ rw 0 rt2s-4236 ∷ []) refl

  rt2s-4618 : Eqn
  rt2s-4618 = derive (x₀ ∷ cx′ ∷ ck ∷ ck ∷ x₀ ∷ [])
    (cx′ ∷ s₀ ∷ k₀ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-34 ∷ rw 1 rt2s-1097 ∷ []) refl

  rt2s-4713 : Eqn
  rt2s-4713 = derive (s₁ ∷ cx′ ∷ s₀ ∷ ck′ ∷ [])
    (s₀ ∷ x₀ ∷ ck′ ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-1224 ∷ rw 2 rt2s-243 ∷ rw 1 rt2s-89 ∷ []) refl

  rt2s-4759 : Eqn
  rt2s-4759 = derive (ck′ ∷ cs ∷ cx′ ∷ ck′ ∷ [])
    (cs ∷ ck′ ∷ cx′ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-3 ∷ rw 3 rt2s-1298 ∷ rw 1 rt2s-243 ∷ []) refl

  rt2s-4765 : Eqn
  rt2s-4765 = derive (cs ∷ ck ∷ s₁ ∷ [])
    (s₁ ∷ ck ∷ cs ∷ [])
    (rw⁻ 1 rt2s-1333 ∷ rw 0 rt2s-13 ∷ rw 1 rt2s-239 ∷ rw 2 rt2s-6 ∷ []) refl

  rt2s-4774 : Eqn
  rt2s-4774 = derive (ck ∷ s₁ ∷ ck ∷ cs ∷ ck ∷ [])
    (s₁ ∷ ck ∷ cx ∷ ck ∷ [])
    (rw⁻ 0 rt2s-1333 ∷ rw 4 rt2s-82 ∷ rw 3 rt2s-6 ∷ rw 2 rt2s-193 ∷ rw 1 rt2s-239 ∷ []) refl

  rt2s-4775 : Eqn
  rt2s-4775 = derive (ck ∷ s₁ ∷ ck ∷ cs ∷ [])
    (s₁ ∷ ck ∷ cx ∷ [])
    (rw⁻ 0 rt2s-1430 ∷ rw 1 rt2s-4774 ∷ rw 0 rt2s-208 ∷ rw 1 rt2s-239 ∷ []) refl

  rt2s-4819 : Eqn
  rt2s-4819 = derive (s₁ ∷ ck ∷ cs ∷ ck′ ∷ ck′ ∷ [])
    (cs ∷ ck ∷ [])
    (rw⁻ 0 rt2s-4765 ∷ rw 2 rt2s-85 ∷ []) refl

  rt2s-4858 : Eqn
  rt2s-4858 = derive (s₀ ∷ s₁ ∷ ck ∷ cs ∷ ck ∷ [])
    (s₀ ∷ cx ∷ ck ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-11 ∷ rw⁻ 1 rt2s-1460 ∷ rw⁻ 0 rt2s-3361 ∷ rw⁻ 2 rt2s-4765 ∷ rw 0 rt2s-748 ∷ []) refl

  rt2s-4859 : Eqn
  rt2s-4859 = derive (s₀ ∷ cx ∷ ck ∷ s₁ ∷ ck ∷ [])
    (s₁ ∷ ck ∷ cs ∷ [])
    (rw⁻ 0 rt2s-4858 ∷ rw 0 rt2s-621 ∷ []) refl

  rt2s-4860 : Eqn
  rt2s-4860 = derive (s₁ ∷ ck ∷ cs ∷ ck ∷ [])
    (cx ∷ ck ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-4859 ∷ rw 0 rt2s-613 ∷ []) refl

  rt2s-4864 : Eqn
  rt2s-4864 = derive (cx ∷ s₁ ∷ ck ∷ cs ∷ [])
    (s₀ ∷ ck ∷ s₁ ∷ ck ∷ [])
    (rw⁻ 0 rt2s-1419 ∷ rw 2 rt2s-4860 ∷ rw 1 rt2s-6 ∷ []) refl

  rt2s-4865 : Eqn
  rt2s-4865 = derive (cs ∷ x₀ ∷ ck ∷ cs ∷ [])
    (x₀ ∷ ck ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-3758 ∷ rw 1 rt2s-4864 ∷ rw 1 rt2s-209 ∷ []) refl

  rt2s-4882 : Eqn
  rt2s-4882 = derive (s₀ ∷ s₁ ∷ cs ∷ ck′ ∷ cx′ ∷ cs ∷ [])
    (s₁ ∷ ck′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-11 ∷ rw 1 rt2s-1349 ∷ []) refl

  rt2s-4884 : Eqn
  rt2s-4884 = derive (cs ∷ ck′ ∷ s₀ ∷ [])
    (s₀ ∷ ck′ ∷ cs ∷ [])
    (rw⁻ 1 rt2s-1349 ∷ rw 0 rt2s-12 ∷ rw 1 rt2s-243 ∷ rw 2 rt2s-7 ∷ []) refl

  rt2s-4888 : Eqn
  rt2s-4888 = derive (cx′ ∷ s₀ ∷ ck′ ∷ cs ∷ [])
    (s₁ ∷ ck′ ∷ s₀ ∷ ck′ ∷ [])
    (rw⁻ 1 rt2s-4884 ∷ rw⁻ 0 rt2s-1503 ∷ rw 2 rt2s-4884 ∷ rw 0 rt2s-4713 ∷ rw 1 rt2s-781 ∷ rw 2 rt2s-4759 ∷
       rw 0 rt2s-4882 ∷ []) refl

  rt2s-4891 : Eqn
  rt2s-4891 = derive (cs ∷ x₁ ∷ ck′ ∷ cs ∷ [])
    (x₁ ∷ ck′ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-3817 ∷ rw 1 rt2s-4888 ∷ rw 1 rt2s-492 ∷ []) refl

  rt2s-4956 : Eqn
  rt2s-4956 = derive (cs ∷ ck′ ∷ x₁ ∷ cs ∷ [])
    (s₀ ∷ ck′ ∷ x₁ ∷ [])
    (rw⁻ 2 rt2s-213 ∷ rw 0 rt2s-4884 ∷ rw 2 rt2s-211 ∷ rw 2 rt2s-117 ∷ []) refl

  rt2s-5237 : Eqn
  rt2s-5237 = derive (cx ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (x₀ ∷ k₁ ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-2895 ∷ rw 1 rt2s-78 ∷ rw 0 rt2s-144 ∷ []) refl

  rt2s-5242 : Eqn
  rt2s-5242 = derive (k₁ ∷ s₁ ∷ ck ∷ cx ∷ [])
    (cx ∷ k₁ ∷ s₁ ∷ ck ∷ [])
    (rw⁻ 2 rt2s-239 ∷ rw 0 rt2s-2895 ∷ []) refl

  rt2s-5516 : Eqn
  rt2s-5516 = derive (ck ∷ k₁ ∷ s₁ ∷ ck ∷ cs ∷ [])
    (cx ∷ k₁ ∷ s₁ ∷ ck ∷ [])
    (rw⁻ 0 rt2s-268 ∷ rw 1 rt2s-4775 ∷ rw 0 rt2s-5242 ∷ []) refl

  rt2s-5747 : Eqn
  rt2s-5747 = derive (s₀ ∷ ck ∷ k₁ ∷ s₁ ∷ cs ∷ [])
    (s₀ ∷ cs ∷ ck ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-688 ∷ rw⁻ 0 rt2s-4865 ∷ rw 3 rt2s-218 ∷ rw 1 rt2s-688 ∷ rw 0 rt2s-12 ∷ []) refl

  rt2s-5775 : Eqn
  rt2s-5775 = derive (s₀ ∷ cx ∷ k₁ ∷ s₁ ∷ ck ∷ [])
    (cs ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 1 rt2s-5516 ∷ rw⁻ 0 rt2s-688 ∷ rw⁻ 0 rt2s-4865 ∷ rw 3 rt2s-4865 ∷ rw 1 rt2s-687 ∷ rw 0 rt2s-12 ∷
       rw 3 rt2s-268 ∷ rw 0 rt2s-107 ∷ []) refl

  rt2s-5791 : Eqn
  rt2s-5791 = derive (s₁ ∷ ck′ ∷ k₀ ∷ s₀ ∷ cs ∷ [])
    (s₁ ∷ cs ∷ ck′ ∷ k₀ ∷ s₀ ∷ [])
    (rw⁻ 0 rt2s-700 ∷ rw⁻ 0 rt2s-4891 ∷ rw 3 rt2s-211 ∷ rw 1 rt2s-700 ∷ rw 0 rt2s-13 ∷ []) refl

  rt2s-5901 : Eqn
  rt2s-5901 = derive (s₀ ∷ cs ∷ ck′ ∷ cx′ ∷ x₁ ∷ [])
    (ck′ ∷ x₁ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-1266 ∷ rw⁻ 0 rt2s-79 ∷ rw⁻ 0 rt2s-12 ∷ rw⁻ 1 rt2s-12 ∷ rw⁻ 2 rt2s-12 ∷ rw⁻ 3 rt2s-4956 ∷
       rw 0 rt2s-3 ∷ []) refl

  rt2s-6197 : Eqn
  rt2s-6197 = derive (ck ∷ x₀ ∷ cx ∷ cx′ ∷ ck ∷ x₁ ∷ [])
    (cx′ ∷ cx ∷ ck′ ∷ ck ∷ [])
    (rw⁻ 1 rt2s-254 ∷ rw⁻ 3 rt2s-87 ∷ rw 0 rt2s-56 ∷ rw 3 rt2s-366 ∷ rw 1 rt2s-35 ∷ rw 0 rt2s-6 ∷ []) refl

  rt2s-6307 : Eqn
  rt2s-6307 = derive (cx′ ∷ cx ∷ k₁ ∷ cx ∷ [])
    (cx ∷ k₀ ∷ cx ∷ cx′ ∷ [])
    (rw⁻ 4 rt2s-7 ∷ rw 0 rt2s-75 ∷ []) refl

  rt2s-6314 : Eqn
  rt2s-6314 = derive (cx ∷ cx′ ∷ ck ∷ cx′ ∷ [])
    (x₀ ∷ ck′ ∷ x₀ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-97 ∷ rw 0 rt2s-6 ∷ []) refl

  rt2s-6317 : Eqn
  rt2s-6317 = derive (cx′ ∷ ck ∷ x₀ ∷ cx′ ∷ cx ∷ [])
    (cx ∷ x₀ ∷ ck′ ∷ x₁ ∷ [])
    (rw⁻ 2 rt2s-34 ∷ rw⁻ 0 rt2s-97 ∷ rw 4 rt2s-31 ∷ rw 3 rt2s-4 ∷ []) refl

  rt2s-6328 : Eqn
  rt2s-6328 = derive (cx′ ∷ x₁ ∷ ck ∷ cx′ ∷ [])
    (cx ∷ ck′ ∷ x₀ ∷ cx ∷ [])
    (rw⁻ 0 rt2s-134 ∷ rw⁻ 2 rt2s-97 ∷ rw 0 rt2s-130 ∷ rw 1 rt2s-4 ∷ []) refl

  rt2s-6331 : Eqn
  rt2s-6331 = derive (cx′ ∷ ck ∷ x₁ ∷ cx′ ∷ [])
    (cx ∷ x₀ ∷ ck′ ∷ cx ∷ [])
    (rw⁻ 2 rt2s-135 ∷ rw⁻ 2 rt2s-34 ∷ rw⁻ 0 rt2s-97 ∷ rw 4 rt2s-132 ∷ rw 3 rt2s-4 ∷ []) refl

  rt2s-6339 : Eqn
  rt2s-6339 = derive (cx ∷ x₀ ∷ ck′ ∷ cx ∷ cx′ ∷ [])
    (cx′ ∷ ck ∷ x₁ ∷ [])
    (rw⁻ 3 rt2s-4 ∷ rw⁻ 4 rt2s-254 ∷ rw 0 rt2s-97 ∷ rw 2 rt2s-7 ∷ []) refl

  rt2s-6361 : Eqn
  rt2s-6361 = derive (cs ∷ k₁ ∷ s₁ ∷ ck ∷ [])
    (cx ∷ k₁ ∷ s₁ ∷ [])
    (rw⁻ 0 rt2s-5775 ∷ rw⁻ 1 rt2s-5242 ∷ rw⁻ 0 rt2s-67 ∷ rw 1 rt2s-208 ∷ rw 0 rt2s-2895 ∷ []) refl

  rt2s-6405 : Eqn
  rt2s-6405 = derive (cx ∷ k₁ ∷ s₁ ∷ ck ∷ ck′ ∷ ck′ ∷ [])
    (cs ∷ ck ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-6361 ∷ rw 2 rt2s-606 ∷ rw 1 rt2s-268 ∷ rw 2 rt2s-268 ∷ []) refl

  rt2s-6433 : Eqn
  rt2s-6433 = derive (x₀ ∷ k₁ ∷ cs ∷ x₀ ∷ ck′ ∷ ck′ ∷ [])
    (cs ∷ k₁ ∷ cs ∷ ck ∷ [])
    (rw⁻ 0 rt2s-5237 ∷ rw⁻ 0 rt2s-6361 ∷ rw 2 rt2s-4819 ∷ []) refl

  rt2s-6493 : Eqn
  rt2s-6493 = derive (cs ∷ cx ∷ ck ∷ cs ∷ [])
    (s₁ ∷ ck ∷ ck′ ∷ ck′ ∷ [])
    (rw⁻ 1 rt2s-36 ∷ rw⁻ 2 rt2s-222 ∷ rw 0 rt2s-4765 ∷ rw 1 rt2s-36 ∷ rw 2 rt2s-371 ∷ rw 1 rt2s-6 ∷ []) refl

  rt2s-6499 : Eqn
  rt2s-6499 = derive (k₁ ∷ s₁ ∷ ck ∷ ck′ ∷ ck′ ∷ [])
    (cx ∷ ck ∷ k₁ ∷ cs ∷ ck ∷ [])
    (rw⁻ 1 rt2s-6493 ∷ rw 0 rt2s-2901 ∷ []) refl

  rt2s-6511 : Eqn
  rt2s-6511 = derive (ck ∷ k₁ ∷ cs ∷ ck ∷ [])
    (cs ∷ ck ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-6 ∷ rw⁻ 1 rt2s-6499 ∷ rw 0 rt2s-6405 ∷ []) refl

  rt2s-6865 : Eqn
  rt2s-6865 = derive (x₁ ∷ s₁ ∷ cs ∷ ck ∷ cx ∷ [])
    (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ ck ∷ [])
    (rw⁻ 0 rt2s-206 ∷ rw 4 rt2s-364 ∷ rw 0 rt2s-1400 ∷ rw 1 rt2s-78 ∷ rw 0 rt2s-18 ∷ []) refl

  rt2s-6869 : Eqn
  rt2s-6869 = derive (ck ∷ cx ∷ k₁ ∷ cs ∷ ck ∷ [])
    (cs ∷ ck ∷ cx ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-2882 ∷ rw⁻ 1 rt2s-364 ∷ rw 0 rt2s-268 ∷ rw 0 rt2s-6511 ∷ rw 2 rt2s-2918 ∷ []) refl

  rt2s-6952 : Eqn
  rt2s-6952 = derive (s₁ ∷ x₀ ∷ cs ∷ ck ∷ x₁ ∷ [])
    (cs ∷ cx ∷ x₀ ∷ ck ∷ [])
    (rw⁻ 0 rt2s-369 ∷ rw 3 rt2s-32 ∷ rw 2 rt2s-789 ∷ rw 1 rt2s-130 ∷ []) refl

  rt2s-8135 : Eqn
  rt2s-8135 = derive (k₁ ∷ cs ∷ ck ∷ cs ∷ [])
    (cs ∷ k₁ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-622 ∷ rw 0 rt2s-67 ∷ rw 1 rt2s-2882 ∷ rw 1 rt2s-6869 ∷ rw 0 rt2s-215 ∷ rw 1 rt2s-2951 ∷ []) refl

  rt2s-8160 : Eqn
  rt2s-8160 = derive (ck ∷ cx ∷ k₁ ∷ cs ∷ [])
    (cs ∷ ck ∷ cx ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-2882 ∷ rw⁻ 1 rt2s-82 ∷ rw 0 rt2s-8135 ∷ rw 1 rt2s-2882 ∷ []) refl

  rt2s-8370 : Eqn
  rt2s-8370 = derive (s₁ ∷ ck′ ∷ cx′ ∷ k₀ ∷ cs ∷ ck′ ∷ [])
    (k₀ ∷ cs ∷ ck′ ∷ cs ∷ [])
    (rw⁻ 1 rt2s-3949 ∷ rw⁻ 0 rt2s-66 ∷ rw 1 rt2s-654 ∷ []) refl

  rt2s-8558 : Eqn
  rt2s-8558 = derive (s₀ ∷ ck ∷ k₁ ∷ cs ∷ [])
    (s₀ ∷ cs ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-687 ∷ rw⁻ 2 rt2s-220 ∷ rw 0 rt2s-688 ∷ rw 0 rt2s-5747 ∷ rw 4 rt2s-85 ∷ []) refl

  rt2s-8630 : Eqn
  rt2s-8630 = derive (s₁ ∷ ck′ ∷ k₀ ∷ cs ∷ [])
    (s₁ ∷ cs ∷ ck′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-698 ∷ rw⁻ 2 rt2s-213 ∷ rw 0 rt2s-700 ∷ rw 0 rt2s-5791 ∷ rw 4 rt2s-83 ∷ []) refl

  rt2s-8888 : Eqn
  rt2s-8888 = derive (ck ∷ s₁ ∷ cs ∷ cx ∷ [])
    (cx ∷ s₁ ∷ cs ∷ ck ∷ [])
    (rw⁻ 0 rt2s-3743 ∷ rw⁻ 0 rt2s-78 ∷ rw 3 rt2s-758 ∷ rw 2 rt2s-12 ∷ rw 1 rt2s-12 ∷ rw 0 rt2s-11 ∷
       rw 0 rt2s-1133 ∷ rw 2 rt2s-6 ∷ []) refl

  rt2s-11161 : Eqn
  rt2s-11161 = derive (x₁ ∷ cx ∷ cx′ ∷ cx ∷ ck ∷ x₀ ∷ [])
    (s₁ ∷ cx ∷ cx′ ∷ cx ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 1 rt2s-35 ∷ rw⁻ 0 rt2s-247 ∷ rw⁻ 2 rt2s-949 ∷ rw 0 rt2s-35 ∷ rw 2 rt2s-25 ∷ rw 0 rt2s-1156 ∷ []) refl

  rt2s-11178 : Eqn
  rt2s-11178 = derive (cx ∷ x₀ ∷ cx′ ∷ ck ∷ x₀ ∷ [])
    (s₁ ∷ cx ∷ cx′ ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 1 rt2s-949 ∷ rw 0 rt2s-1156 ∷ []) refl

  rt2s-11297 : Eqn
  rt2s-11297 = derive (s₀ ∷ ck ∷ x₁ ∷ ck ∷ s₁ ∷ cs ∷ [])
    (x₀ ∷ cx ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-1014 ∷ rw⁻ 1 rt2s-976 ∷ rw⁻ 0 rt2s-976 ∷ rw 2 rt2s-78 ∷ rw 0 rt2s-131 ∷ []) refl

  rt2s-11956 : Eqn
  rt2s-11956 = derive (k₁ ∷ cs ∷ x₀ ∷ ck′ ∷ ck′ ∷ [])
    (x₀ ∷ cx ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 2 rt2s-200 ∷ rw 0 rt2s-1071 ∷ rw 1 rt2s-2914 ∷ rw 0 rt2s-131 ∷ []) refl

  rt2s-11957 : Eqn
  rt2s-11957 = derive (cs ∷ k₁ ∷ cs ∷ ck ∷ [])
    (cx ∷ k₁ ∷ cs ∷ [])
    (rw⁻ 0 rt2s-6433 ∷ rw 1 rt2s-11956 ∷ rw 0 rt2s-4 ∷ []) refl

  rt2s-12035 : Eqn
  rt2s-12035 = derive (ck ∷ k₁ ∷ cs ∷ [])
    (cs ∷ ck ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-268 ∷ rw⁻ 0 rt2s-6 ∷ rw⁻ 1 rt2s-2860 ∷ rw⁻ 0 rt2s-11957 ∷ rw 3 rt2s-1470 ∷ rw 1 rt2s-2860 ∷
       rw 2 rt2s-268 ∷ rw 2 rt2s-2918 ∷ rw 1 rt2s-6 ∷ []) refl

  rt2s-12181 : Eqn
  rt2s-12181 = derive (x₀ ∷ cx′ ∷ ck ∷ x₀ ∷ cs ∷ [])
    (x₀ ∷ cs ∷ cx′ ∷ ck ∷ x₀ ∷ [])
    (rw⁻ 0 rt2s-949 ∷ rw 2 rt2s-12035 ∷ rw 0 rt2s-1008 ∷ []) refl

  rt2s-13847 : Eqn
  rt2s-13847 = derive (ck ∷ x₀ ∷ cx ∷ cs ∷ x₀ ∷ ck ∷ [])
    (x₀ ∷ cx ∷ cs ∷ x₀ ∷ ck ∷ ck ∷ [])
    (rw⁻ 0 rt2s-1012 ∷ rw 3 rt2s-1233 ∷ rw 1 rt2s-1234 ∷ rw 0 rt2s-6865 ∷ rw 4 rt2s-195 ∷ rw 1 rt2s-742 ∷ []) refl

  rt2s-14335 : Eqn
  rt2s-14335 = derive (ck′ ∷ x₁ ∷ cs ∷ ck′ ∷ [])
    (x₁ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-5901 ∷ rw⁻ 0 rt2s-1266 ∷ rw 3 rt2s-146 ∷ rw 2 rt2s-5 ∷ []) refl

  rt2s-14389 : Eqn
  rt2s-14389 = derive (k₀ ∷ cs ∷ ck′ ∷ [])
    (ck′ ∷ cs ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-5 ∷ rw⁻ 1 rt2s-148 ∷ rw⁻ 0 rt2s-146 ∷ rw 2 rt2s-14335 ∷ rw 1 rt2s-5 ∷ []) refl

  rt2s-14421 : Eqn
  rt2s-14421 = derive (ck′ ∷ cs ∷ k₀ ∷ cs ∷ [])
    (cs ∷ k₀ ∷ cx′ ∷ [])
    (rw⁻ 0 rt2s-14389 ∷ rw⁻ 0 rt2s-8370 ∷ rw 3 rt2s-14389 ∷ rw 0 rt2s-141 ∷ rw 1 rt2s-4035 ∷ []) refl

  rt2s-14534 : Eqn
  rt2s-14534 = derive (ck′ ∷ cx′ ∷ k₀ ∷ cs ∷ [])
    (cs ∷ ck′ ∷ cx′ ∷ k₀ ∷ [])
    (rw⁻ 0 rt2s-3949 ∷ rw⁻ 1 rt2s-84 ∷ rw 0 rt2s-14389 ∷ rw 0 rt2s-14421 ∷ rw 1 rt2s-3949 ∷ []) refl

  rt2s-15164 : Eqn
  rt2s-15164 = derive (x₀ ∷ cx ∷ cs ∷ x₀ ∷ ck ∷ [])
    (x₁ ∷ ck ∷ s₁ ∷ cs ∷ [])
    (rw⁻ 1 rt2s-742 ∷ rw⁻ 0 rt2s-18 ∷ rw 1 rt2s-1332 ∷ []) refl

  rt2s-15169 : Eqn
  rt2s-15169 = derive (ck ∷ x₁ ∷ ck ∷ s₁ ∷ cs ∷ [])
    (x₁ ∷ ck ∷ s₁ ∷ cs ∷ ck ∷ [])
    (rw⁻ 1 rt2s-15164 ∷ rw 0 rt2s-13847 ∷ rw 0 rt2s-15164 ∷ []) refl

  rt2s-15170 : Eqn
  rt2s-15170 = derive (s₀ ∷ x₁ ∷ ck ∷ s₁ ∷ cs ∷ ck ∷ [])
    (x₀ ∷ cx ∷ cs ∷ x₀ ∷ [])
    (rw⁻ 1 rt2s-15169 ∷ rw 0 rt2s-11297 ∷ []) refl

  rt2s-15215 : Eqn
  rt2s-15215 = derive (ck ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ [])
    (cs ∷ x₁ ∷ cx ∷ s₁ ∷ ck ∷ [])
    (rw⁻ 1 rt2s-18 ∷ rw⁻ 0 rt2s-234 ∷ rw 4 rt2s-1335 ∷ rw 1 rt2s-15169 ∷ rw 0 rt2s-15170 ∷ rw 0 rt2s-15164 ∷
       rw 1 rt2s-8888 ∷ rw 0 rt2s-976 ∷ []) refl

  rt2s-26713 : Eqn
  rt2s-26713 = derive (cx ∷ k₀ ∷ cx ∷ cx′ ∷ cx ∷ [])
    (cx′ ∷ cx ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-6307 ∷ rw 3 rt2s-6 ∷ []) refl

  rt2s-26726 : Eqn
  rt2s-26726 = derive (cx′ ∷ k₀ ∷ cx ∷ cx′ ∷ [])
    (cx ∷ cx′ ∷ k₁ ∷ cx ∷ [])
    (rw⁻ 1 rt2s-6 ∷ rw⁻ 2 rt2s-6307 ∷ rw 0 rt2s-35 ∷ rw 2 rt2s-6 ∷ []) refl

  rt2s-27025 : Eqn
  rt2s-27025 = derive (cx ∷ cx′ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
    (x₀ ∷ ck′ ∷ x₁ ∷ cx ∷ [])
    (rw⁻ 3 rt2s-34 ∷ rw 0 rt2s-6314 ∷ rw 2 rt2s-245 ∷ []) refl

  rt2s-27140 : Eqn
  rt2s-27140 = derive (cx′ ∷ x₁ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
    (cx ∷ ck′ ∷ x₁ ∷ cx ∷ [])
    (rw⁻ 3 rt2s-34 ∷ rw 0 rt2s-6328 ∷ rw 2 rt2s-245 ∷ []) refl

  rt2s-27351 : Eqn
  rt2s-27351 = derive (cx ∷ cx′ ∷ ck ∷ x₁ ∷ [])
    (x₀ ∷ ck′ ∷ cx ∷ cx′ ∷ [])
    (rw⁻ 1 rt2s-6339 ∷ rw 0 rt2s-6 ∷ []) refl

  rt2s-27355 : Eqn
  rt2s-27355 = derive (ck ∷ ck′ ∷ cx ∷ cx′ ∷ [])
    (cx′ ∷ cx ∷ ck′ ∷ ck ∷ [])
    (rw⁻ 1 rt2s-4 ∷ rw⁻ 2 rt2s-27351 ∷ rw 0 rt2s-6197 ∷ []) refl

  rt2s-37830 : Eqn
  rt2s-37830 = derive (k₀ ∷ cx ∷ cx′ ∷ cx ∷ [])
    (cx ∷ cx′ ∷ cx ∷ k₁ ∷ [])
    (rw⁻ 0 rt2s-6 ∷ rw 1 rt2s-26713 ∷ []) refl

  rt2s-37915 : Eqn
  rt2s-37915 = derive (cx′ ∷ k₀ ∷ cx′ ∷ cx ∷ [])
    (cx ∷ cx′ ∷ k₁ ∷ cx′ ∷ [])
    (rw⁻ 2 rt2s-6 ∷ rw⁻ 3 rt2s-35 ∷ rw 0 rt2s-26726 ∷ rw 3 rt2s-6 ∷ []) refl

  rt2s-38594 : Eqn
  rt2s-38594 = derive (ck′ ∷ cx ∷ cx′ ∷ cx ∷ [])
    (cx ∷ cx′ ∷ cx ∷ ck ∷ [])
    (rw⁻ 1 rt2s-35 ∷ rw⁻ 0 rt2s-243 ∷ rw⁻ 0 rt2s-139 ∷ rw 3 rt2s-27355 ∷ rw 1 rt2s-56 ∷ rw 0 rt2s-1198 ∷ []) refl

  rt2s-40309 : Eqn
  rt2s-40309 = derive (cx ∷ cx′ ∷ ck ∷ k₁ ∷ cx′ ∷ [])
    (ck′ ∷ k₀ ∷ cx ∷ [])
    (rw⁻ 2 rt2s-268 ∷ rw⁻ 3 rt2s-7 ∷ rw⁻ 0 rt2s-37915 ∷ rw 3 rt2s-6314 ∷ rw 2 rt2s-34 ∷ rw 1 rt2s-4237 ∷
       rw 0 rt2s-7 ∷ rw 2 rt2s-4 ∷ []) refl

  rt2s-97458 : Eqn
  rt2s-97458 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ ck ∷ [])
    (cs ∷ x₁ ∷ cx ∷ s₁ ∷ ck ∷ x₁ ∷ [])
    (rw⁻ 3 rt2s-18 ∷ rw⁻ 1 rt2s-80 ∷ rw⁻ 2 rt2s-6952 ∷ rw 0 rt2s-377 ∷ rw 0 rt2s-976 ∷ []) refl

------------------------------------------------------------------------
-- The decoded relations, and the decoded encodings of the generators

order-i-0 : Eqn
order-i-0 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  ([])
  (rw 4 rt2s-18 ∷ rw 3 rt2s-4 ∷ rw 3 rt2s-5 ∷ rw 5 rt2s-18 ∷ rw 4 rt2s-4 ∷ rw 4 rt2s-5 ∷
     rw 6 rt2s-18 ∷ rw 5 rt2s-4 ∷ rw 5 rt2s-5 ∷ rw 2 rt2s-3 ∷ rw 1 rt2s-18 ∷ rw 0 rt2s-4 ∷
     rw 0 rt2s-5 ∷ []) refl

order-i-1 : Eqn
order-i-1 = derive (x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  ([])
  (rw 2 rt2s-4 ∷ rw 3 rt2s-4 ∷ rw 4 rt2s-4 ∷ rw 1 rt2s-3 ∷ rw 0 rt2s-4 ∷ []) refl

order-i-2 : Eqn
order-i-2 = derive (x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  ([])
  (rw 2 rt2s-5 ∷ rw 3 rt2s-5 ∷ rw 4 rt2s-5 ∷ rw 1 rt2s-3 ∷ rw 0 rt2s-5 ∷ []) refl

order-i-3 : Eqn
order-i-3 = derive (cs ∷ cs ∷ cs ∷ cs ∷ [])
  ([])
  (rw 0 rt2s-3 ∷ []) refl

order-X-01 : Eqn
order-X-01 = derive (x₀ ∷ cx ∷ x₀ ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  ([])
  (rw 2 rt2s-4 ∷ rw 1 rt2s-6 ∷ rw 0 rt2s-4 ∷ []) refl

order-K-01 : Eqn
order-K-01 = derive (x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  ([])
  (rw 2 rt2s-4 ∷ rw 3 rt2s-4 ∷ rw 4 rt2s-4 ∷ rw 1 rt2s-197 ∷ rw 3 rt2s-4 ∷ rw 4 rt2s-4 ∷
     rw 2 rt2s-83 ∷ rw 0 rt2s-99 ∷ rw 2 rt2s-142 ∷ rw 3 rt2s-144 ∷ rw 2 rt2s-4 ∷ rw 2 rt2s-144 ∷
     rw 3 rt2s-268 ∷ rw 1 rt2s-142 ∷ rw 2 rt2s-183 ∷ rw 0 rt2s-157 ∷ rw 0 rt2s-4 ∷ []) refl

swap-iX-01 : Eqn
swap-iX-01 = derive (x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 2 rt2s-4 ∷ rw⁻ 0 rt2s-2815 ∷ rw⁻ 0 rt2s-130 ∷ rw⁻ 1 rt2s-32 ∷ rw⁻ 0 rt2s-131 ∷ rw⁻ 0 rt2s-245 ∷ []) refl

rel-13-01 : Eqn
rel-13-01 = derive (x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (rw 2 rt2s-4 ∷ rw 3 rt2s-4 ∷ rw 1 rt2s-36 ∷ rw⁻ 2 rt2s-4 ∷ []) refl

rel-14-01 : Eqn
rel-14-01 = derive (x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (rw 2 rt2s-4 ∷ rw 3 rt2s-4 ∷ rw 1 rt2s-36 ∷ rw 3 rt2s-4 ∷ rw⁻ 1 rt2s-82 ∷ rw⁻ 4 rt2s-4 ∷
     rw⁻ 3 rt2s-4 ∷ rw⁻ 2 rt2s-4 ∷ []) refl

rel-15-01 : Eqn
rel-15-01 = derive (x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (rw 2 rt2s-4 ∷ rw 5 rt2s-18 ∷ rw 4 rt2s-4 ∷ rw 3 rt2s-211 ∷ rw 2 rt2s-22 ∷ rw 1 rt2s-38 ∷
     rw 3 rt2s-5 ∷ rw⁻ 0 rt2s-460 ∷ rw⁻ 0 rt2s-99 ∷ rw⁻ 2 rt2s-5 ∷ rw⁻ 1 rt2s-22 ∷ rw⁻ 2 rt2s-211 ∷
     rw⁻ 3 rt2s-4 ∷ rw⁻ 4 rt2s-18 ∷ []) refl

rel-16-01 : Eqn
rel-16-01 = derive (x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ ck ∷ x₀ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  ([])
  (rw 2 rt2s-4 ∷ rw 3 rt2s-4 ∷ rw 6 rt2s-18 ∷ rw 5 rt2s-4 ∷ rw 3 rt2s-106 ∷ rw 2 rt2s-38 ∷
     rw 1 rt2s-38 ∷ rw 1 rt2s-83 ∷ rw 0 rt2s-4 ∷ []) refl

order-X-02 : Eqn
order-X-02 = derive (x₁ ∷ cx′ ∷ x₁ ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  ([])
  (rw 2 rt2s-5 ∷ rw 1 rt2s-7 ∷ rw 0 rt2s-5 ∷ []) refl

order-K-02 : Eqn
order-K-02 = derive (x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  ([])
  (rw 2 rt2s-5 ∷ rw 3 rt2s-5 ∷ rw 4 rt2s-5 ∷ rw 1 rt2s-203 ∷ rw 3 rt2s-5 ∷ rw 4 rt2s-5 ∷
     rw 2 rt2s-85 ∷ rw 0 rt2s-101 ∷ rw 2 rt2s-146 ∷ rw 3 rt2s-148 ∷ rw 2 rt2s-5 ∷ rw 2 rt2s-148 ∷
     rw 3 rt2s-276 ∷ rw 1 rt2s-146 ∷ rw 0 rt2s-172 ∷ rw 0 rt2s-5 ∷ []) refl

swap-iX-02 : Eqn
swap-iX-02 = derive (x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (x₁ ∷ cx′ ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 2 rt2s-5 ∷ rw⁻ 0 rt2s-1005 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-34 ∷ rw⁻ 0 rt2s-137 ∷ []) refl

rel-13-02 : Eqn
rel-13-02 = derive (x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (x₁ ∷ cx′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (rw 2 rt2s-5 ∷ rw 3 rt2s-5 ∷ rw 1 rt2s-40 ∷ rw⁻ 2 rt2s-5 ∷ []) refl

rel-14-02 : Eqn
rel-14-02 = derive (x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (rw 2 rt2s-5 ∷ rw 3 rt2s-5 ∷ rw 1 rt2s-40 ∷ rw 3 rt2s-5 ∷ rw⁻ 1 rt2s-84 ∷ rw⁻ 4 rt2s-5 ∷
     rw⁻ 3 rt2s-5 ∷ rw⁻ 2 rt2s-5 ∷ []) refl

rel-15-02 : Eqn
rel-15-02 = derive (x₁ ∷ ck′ ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (rw 2 rt2s-18 ∷ rw 3 rt2s-5 ∷ rw 5 rt2s-5 ∷ rw 3 rt2s-218 ∷ rw 2 rt2s-20 ∷ rw 1 rt2s-42 ∷
     rw 3 rt2s-4 ∷ rw⁻ 0 rt2s-468 ∷ rw⁻ 0 rt2s-101 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-115 ∷ rw⁻ 2 rt2s-218 ∷
     rw⁻ 4 rt2s-5 ∷ []) refl

rel-16-02 : Eqn
rel-16-02 = derive (x₁ ∷ ck′ ∷ x₁ ∷ x₁ ∷ ck′ ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  ([])
  (rw 2 rt2s-5 ∷ rw 3 rt2s-18 ∷ rw 4 rt2s-5 ∷ rw 6 rt2s-5 ∷ rw 3 rt2s-108 ∷ rw 2 rt2s-42 ∷
     rw 1 rt2s-42 ∷ rw 1 rt2s-85 ∷ rw 0 rt2s-5 ∷ []) refl

order-X-03 : Eqn
order-X-03 = derive (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  ([])
  (rw 0 rt2s-70 ∷ rw 3 rt2s-32 ∷ rw 1 rt2s-95 ∷ rw 0 rt2s-18 ∷ rw 4 rt2s-6 ∷ rw 3 rt2s-7 ∷
     rw 2 rt2s-6 ∷ rw 1 rt2s-18 ∷ rw 0 rt2s-4 ∷ rw 0 rt2s-5 ∷ []) refl

order-K-03 : Eqn
order-K-03 = derive (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  ([])
  (rw 0 rt2s-34 ∷ rw 4 rt2s-7 ∷ rw 3 rt2s-4 ∷ rw 5 rt2s-7 ∷ rw 4 rt2s-4 ∷ rw 6 rt2s-7 ∷
     rw 5 rt2s-4 ∷ rw 2 rt2s-197 ∷ rw 5 rt2s-7 ∷ rw 4 rt2s-4 ∷ rw 6 rt2s-7 ∷ rw 5 rt2s-4 ∷
     rw 3 rt2s-83 ∷ rw 4 rt2s-7 ∷ rw 3 rt2s-4 ∷ rw 5 rt2s-7 ∷ rw 4 rt2s-4 ∷ rw 2 rt2s-83 ∷
     rw 1 rt2s-34 ∷ rw 0 rt2s-4 ∷ rw 0 rt2s-7 ∷ []) refl

swap-iX-03 : Eqn
swap-iX-03 = derive (cs ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 1 rt2s-70 ∷ rw 4 rt2s-32 ∷ rw 2 rt2s-95 ∷ rw 1 rt2s-18 ∷ rw⁻ 1 rt2s-18 ∷ rw⁻ 2 rt2s-95 ∷
     rw⁻ 4 rt2s-32 ∷ rw⁻ 1 rt2s-70 ∷ rw⁻ 0 rt2s-72 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-95 ∷ rw⁻ 3 rt2s-32 ∷
     rw⁻ 1 rt2s-5 ∷ rw⁻ 2 rt2s-70 ∷ rw⁻ 0 rt2s-18 ∷ rw⁻ 1 rt2s-95 ∷ rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-70 ∷ []) refl

rel-13-03 : Eqn
rel-13-03 = derive (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cs ∷ cs ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (rw 0 rt2s-34 ∷ rw 3 rt2s-760 ∷ rw 4 rt2s-760 ∷ rw 2 rt2s-36 ∷ rw⁻ 0 rt2s-34 ∷ rw⁻ 1 rt2s-131 ∷
     rw⁻ 0 rt2s-134 ∷ rw⁻ 0 rt2s-31 ∷ rw⁻ 2 rt2s-35 ∷ rw⁻ 0 rt2s-130 ∷ rw⁻ 0 rt2s-18 ∷ rw⁻ 1 rt2s-254 ∷
     rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-32 ∷ rw⁻ 1 rt2s-247 ∷ []) refl

rel-14-03 : Eqn
rel-14-03 = derive (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cs ∷ cs ∷ cs ∷ [])
  (cs ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cs ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (rw 0 rt2s-34 ∷ rw 3 rt2s-760 ∷ rw 4 rt2s-760 ∷ rw 2 rt2s-36 ∷ rw 4 rt2s-760 ∷ rw⁻ 0 rt2s-1293 ∷
     rw⁻ 5 rt2s-4 ∷ rw⁻ 6 rt2s-7 ∷ rw⁻ 4 rt2s-760 ∷ rw⁻ 1 rt2s-34 ∷ []) refl

rel-15-03 : Eqn
rel-15-03 = derive (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ [])
  (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (rw 0 rt2s-34 ∷ rw 4 rt2s-34 ∷ rw 3 rt2s-4 ∷ rw 3 rt2s-1005 ∷ rw 4 rt2s-1454 ∷ rw 3 rt2s-22 ∷
     rw 2 rt2s-38 ∷ rw 4 rt2s-137 ∷ rw⁻ 0 rt2s-870 ∷ rw⁻ 0 rt2s-462 ∷ rw⁻ 1 rt2s-1158 ∷ rw⁻ 1 rt2s-1264 ∷ []) refl

rel-16-03 : Eqn
rel-16-03 = derive (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ [])
  ([])
  (rw 0 rt2s-34 ∷ rw 4 rt2s-7 ∷ rw 3 rt2s-4 ∷ rw 0 rt2s-4618 ∷ rw 2 rt2s-187 ∷ rw 0 rt2s-1132 ∷
     rw 0 rt2s-4063 ∷ rw 4 rt2s-149 ∷ rw 5 rt2s-3952 ∷ rw 1 rt2s-3642 ∷ rw 0 rt2s-8 ∷ rw 3 rt2s-33 ∷
     rw 2 rt2s-149 ∷ rw 0 rt2s-1958 ∷ rw 1 rt2s-193 ∷ rw 2 rt2s-194 ∷ rw 0 rt2s-1265 ∷ rw 0 rt2s-215 ∷
     rw 0 rt2s-3 ∷ []) refl

order-X-12 : Eqn
order-X-12 = derive (cx ∷ cx′ ∷ cx ∷ cx ∷ cx′ ∷ cx ∷ [])
  ([])
  (rw 2 rt2s-6 ∷ rw 1 rt2s-7 ∷ rw 0 rt2s-6 ∷ []) refl

order-K-12 : Eqn
order-K-12 = derive (cx ∷ ck′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ [])
  ([])
  (rw 2 rt2s-6 ∷ rw 3 rt2s-6 ∷ rw 4 rt2s-6 ∷ rw 1 rt2s-203 ∷ rw 3 rt2s-6 ∷ rw 4 rt2s-6 ∷
     rw 2 rt2s-85 ∷ rw 2 rt2s-6 ∷ rw 3 rt2s-6 ∷ rw 1 rt2s-85 ∷ rw 0 rt2s-6 ∷ []) refl

swap-iX-12 : Eqn
swap-iX-12 = derive (x₁ ∷ cs ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw⁻ 2 rt2s-70 ∷ rw⁻ 1 rt2s-72 ∷ rw⁻ 0 rt2s-70 ∷ []) refl

rel-13-12 : Eqn
rel-13-12 = derive (cx ∷ ck′ ∷ cx ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (cx ∷ cx′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ [])
  (rw 2 rt2s-32 ∷ rw 2 rt2s-383 ∷ rw 3 rt2s-32 ∷ rw 3 rt2s-383 ∷ rw 1 rt2s-40 ∷ rw⁻ 2 rt2s-6 ∷ []) refl

rel-14-12 : Eqn
rel-14-12 = derive (cx ∷ ck′ ∷ cx ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (x₁ ∷ cs ∷ x₁ ∷ cx ∷ ck′ ∷ cx ∷ x₁ ∷ cs ∷ x₁ ∷ cx ∷ ck′ ∷ cx ∷ [])
  (rw 2 rt2s-32 ∷ rw 2 rt2s-383 ∷ rw 3 rt2s-32 ∷ rw 3 rt2s-383 ∷ rw 1 rt2s-40 ∷ rw 3 rt2s-32 ∷
     rw 3 rt2s-383 ∷ rw⁻ 1 rt2s-84 ∷ rw⁻ 4 rt2s-6 ∷ rw⁻ 3 rt2s-383 ∷ rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-382 ∷ []) refl

rel-15-12 : Eqn
rel-15-12 = derive (cx ∷ ck′ ∷ cx ∷ x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₁ ∷ cx ∷ ck′ ∷ cx ∷ [])
  (rw 3 rt2s-1231 ∷ rw 2 rt2s-6 ∷ rw 1 rt2s-42 ∷ rw 4 rt2s-32 ∷ rw 3 rt2s-5 ∷ rw⁻ 2 rt2s-6 ∷
     rw⁻ 2 rt2s-5 ∷ rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-1231 ∷ []) refl

rel-16-12 : Eqn
rel-16-12 = derive (cx ∷ ck′ ∷ cx ∷ cx ∷ ck′ ∷ cx ∷ x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  ([])
  (rw 2 rt2s-6 ∷ rw 4 rt2s-1231 ∷ rw 3 rt2s-6 ∷ rw 2 rt2s-42 ∷ rw 1 rt2s-42 ∷ rw 1 rt2s-85 ∷
     rw 0 rt2s-32 ∷ rw 1 rt2s-6 ∷ rw 0 rt2s-5 ∷ []) refl

order-X-13 : Eqn
order-X-13 = derive (cx′ ∷ cx′ ∷ [])
  ([])
  (rw 0 rt2s-7 ∷ []) refl

order-K-13 : Eqn
order-K-13 = derive (ck′ ∷ ck′ ∷ ck′ ∷ ck′ ∷ ck′ ∷ ck′ ∷ ck′ ∷ ck′ ∷ [])
  ([])
  (rw 0 rt2s-203 ∷ rw 1 rt2s-85 ∷ rw 0 rt2s-85 ∷ []) refl

swap-iX-13 : Eqn
swap-iX-13 = derive (cs ∷ cx′ ∷ [])
  (cx′ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw⁻ 0 rt2s-390 ∷ rw⁻ 0 rt2s-34 ∷ []) refl

rel-13-13 : Eqn
rel-13-13 = derive (ck′ ∷ cs ∷ cs ∷ [])
  (cx′ ∷ ck′ ∷ [])
  (rw 0 rt2s-40 ∷ []) refl

rel-14-13 : Eqn
rel-14-13 = derive (ck′ ∷ cs ∷ cs ∷ cs ∷ [])
  (cs ∷ ck′ ∷ cs ∷ ck′ ∷ [])
  (rw 0 rt2s-40 ∷ rw⁻ 0 rt2s-84 ∷ []) refl

rel-15-13 : Eqn
rel-15-13 = derive (ck′ ∷ x₀ ∷ cs ∷ x₀ ∷ cs ∷ [])
  (x₀ ∷ cs ∷ x₀ ∷ cs ∷ ck′ ∷ [])
  (rw 1 rt2s-108 ∷ rw 0 rt2s-42 ∷ rw⁻ 0 rt2s-108 ∷ []) refl

rel-16-13 : Eqn
rel-16-13 = derive (ck′ ∷ ck′ ∷ x₀ ∷ cs ∷ x₀ ∷ cs ∷ [])
  ([])
  (rw 2 rt2s-108 ∷ rw 1 rt2s-42 ∷ rw 0 rt2s-42 ∷ rw 0 rt2s-85 ∷ []) refl

order-X-23 : Eqn
order-X-23 = derive (cx ∷ cx ∷ [])
  ([])
  (rw 0 rt2s-6 ∷ []) refl

order-K-23 : Eqn
order-K-23 = derive (ck ∷ ck ∷ ck ∷ ck ∷ ck ∷ ck ∷ ck ∷ ck ∷ [])
  ([])
  (rw 0 rt2s-197 ∷ rw 1 rt2s-83 ∷ rw 0 rt2s-83 ∷ []) refl

swap-iX-23 : Eqn
swap-iX-23 = derive (cs ∷ cx ∷ [])
  (cx ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw⁻ 0 rt2s-383 ∷ rw⁻ 0 rt2s-32 ∷ []) refl

rel-13-23 : Eqn
rel-13-23 = derive (ck ∷ cs ∷ cs ∷ [])
  (cx ∷ ck ∷ [])
  (rw 0 rt2s-36 ∷ []) refl

rel-14-23 : Eqn
rel-14-23 = derive (ck ∷ cs ∷ cs ∷ cs ∷ [])
  (cs ∷ ck ∷ cs ∷ ck ∷ [])
  (rw 0 rt2s-36 ∷ rw⁻ 0 rt2s-82 ∷ []) refl

rel-15-23 : Eqn
rel-15-23 = derive (ck ∷ x₁ ∷ cs ∷ x₁ ∷ cs ∷ [])
  (x₁ ∷ cs ∷ x₁ ∷ cs ∷ ck ∷ [])
  (rw 1 rt2s-106 ∷ rw 0 rt2s-38 ∷ rw⁻ 0 rt2s-106 ∷ []) refl

rel-16-23 : Eqn
rel-16-23 = derive (ck ∷ ck ∷ x₁ ∷ cs ∷ x₁ ∷ cs ∷ [])
  ([])
  (rw 2 rt2s-106 ∷ rw 1 rt2s-38 ∷ rw 0 rt2s-38 ∷ rw 0 rt2s-83 ∷ []) refl

comm-ii-01 : Eqn
comm-ii-01 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 4 rt2s-18 ∷ rw 3 rt2s-4 ∷ rw 2 rt2s-211 ∷ rw 1 rt2s-22 ∷ rw 2 rt2s-5 ∷ rw 0 rt2s-99 ∷
     rw⁻ 1 rt2s-5 ∷ rw⁻ 2 rt2s-194 ∷ rw⁻ 1 rt2s-194 ∷ rw⁻ 0 rt2s-99 ∷ rw⁻ 2 rt2s-18 ∷ rw⁻ 1 rt2s-211 ∷
     rw⁻ 2 rt2s-4 ∷ []) refl

comm-ii-02 : Eqn
comm-ii-02 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (x₁ ∷ cs ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 4 rt2s-5 ∷ rw 2 rt2s-218 ∷ rw 1 rt2s-115 ∷ rw 0 rt2s-4 ∷ rw 0 rt2s-101 ∷ rw⁻ 0 rt2s-101 ∷
     rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-115 ∷ rw⁻ 0 rt2s-115 ∷ rw⁻ 1 rt2s-218 ∷ rw⁻ 3 rt2s-5 ∷ rw⁻ 2 rt2s-18 ∷ []) refl

comm-ii-03 : Eqn
comm-ii-03 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ [])
  (cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 1 rt2s-1264 ∷ rw 0 rt2s-1677 ∷ rw⁻ 0 rt2s-470 ∷ rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-2754 ∷ []) refl

comm-ii-10 : Eqn
comm-ii-10 = derive (x₀ ∷ cs ∷ x₀ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw 2 rt2s-4 ∷ rw 1 rt2s-211 ∷ rw 2 rt2s-18 ∷ rw 0 rt2s-99 ∷ rw 1 rt2s-194 ∷ rw 2 rt2s-194 ∷
     rw 1 rt2s-5 ∷ rw⁻ 0 rt2s-99 ∷ rw⁻ 2 rt2s-5 ∷ rw⁻ 1 rt2s-22 ∷ rw⁻ 2 rt2s-211 ∷ rw⁻ 3 rt2s-4 ∷
     rw⁻ 4 rt2s-18 ∷ []) refl

comm-ii-12 : Eqn
comm-ii-12 = derive (x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (x₁ ∷ cs ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw 0 rt2s-1231 ∷ rw 3 rt2s-32 ∷ rw 2 rt2s-5 ∷ rw⁻ 3 rt2s-4 ∷ rw⁻ 0 rt2s-1264 ∷ rw⁻ 2 rt2s-18 ∷ []) refl

comm-ii-13 : Eqn
comm-ii-13 = derive (x₀ ∷ cs ∷ x₀ ∷ cs ∷ [])
  (cs ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw 1 rt2s-218 ∷ rw 0 rt2s-20 ∷ rw 1 rt2s-4 ∷ rw⁻ 1 rt2s-4 ∷ rw⁻ 0 rt2s-218 ∷ []) refl

comm-ii-20 : Eqn
comm-ii-20 = derive (x₁ ∷ cs ∷ x₁ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw 2 rt2s-18 ∷ rw 3 rt2s-5 ∷ rw 1 rt2s-218 ∷ rw 0 rt2s-115 ∷ rw 1 rt2s-115 ∷ rw 0 rt2s-4 ∷
     rw 0 rt2s-101 ∷ rw⁻ 0 rt2s-101 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-115 ∷ rw⁻ 2 rt2s-218 ∷ rw⁻ 4 rt2s-5 ∷ []) refl

comm-ii-21 : Eqn
comm-ii-21 = derive (x₁ ∷ cs ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw 2 rt2s-18 ∷ rw 0 rt2s-1264 ∷ rw 3 rt2s-4 ∷ rw⁻ 2 rt2s-5 ∷ rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-1231 ∷ []) refl

comm-ii-23 : Eqn
comm-ii-23 = derive (x₁ ∷ cs ∷ x₁ ∷ cs ∷ [])
  (cs ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw 1 rt2s-211 ∷ rw 0 rt2s-22 ∷ rw 1 rt2s-5 ∷ rw⁻ 1 rt2s-5 ∷ rw⁻ 0 rt2s-211 ∷ []) refl

comm-ii-30 : Eqn
comm-ii-30 = derive (cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ [])
  (rw 0 rt2s-2754 ∷ rw 3 rt2s-32 ∷ rw 0 rt2s-470 ∷ rw⁻ 0 rt2s-1677 ∷ rw⁻ 1 rt2s-1264 ∷ []) refl

comm-ii-31 : Eqn
comm-ii-31 = derive (cs ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (x₀ ∷ cs ∷ x₀ ∷ cs ∷ [])
  (rw 0 rt2s-218 ∷ rw 1 rt2s-4 ∷ rw⁻ 1 rt2s-4 ∷ rw⁻ 0 rt2s-20 ∷ rw⁻ 1 rt2s-218 ∷ []) refl

comm-ii-32 : Eqn
comm-ii-32 = derive (cs ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (x₁ ∷ cs ∷ x₁ ∷ cs ∷ [])
  (rw 0 rt2s-211 ∷ rw 1 rt2s-5 ∷ rw⁻ 1 rt2s-5 ∷ rw⁻ 0 rt2s-22 ∷ rw⁻ 1 rt2s-211 ∷ []) refl

comm-iX-012 : Eqn
comm-iX-012 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw⁻ 3 rt2s-18 ∷ rw⁻ 4 rt2s-95 ∷ rw⁻ 6 rt2s-32 ∷ rw⁻ 3 rt2s-70 ∷ rw⁻ 2 rt2s-72 ∷ rw⁻ 0 rt2s-18 ∷
     rw⁻ 1 rt2s-95 ∷ rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-70 ∷ []) refl

comm-iK-012 : Eqn
comm-iK-012 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cx ∷ ck′ ∷ cx ∷ [])
  (cx ∷ ck′ ∷ cx ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 3 rt2f-138 ∷ rw⁻ 0 rt2f-3721 ∷ rw⁻ 3 rt2f-245 ∷ rw⁻ 2 rt2f-139 ∷ []) refl

comm-iX-013 : Eqn
comm-iX-013 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cx′ ∷ [])
  (cx′ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 3 rt2s-134 ∷ rw⁻ 0 rt2s-392 ∷ rw⁻ 0 rt2s-135 ∷ rw⁻ 0 rt2s-34 ∷ []) refl

comm-iK-013 : Eqn
comm-iK-013 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ ck′ ∷ [])
  (ck′ ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw⁻ 0 rt2s-76 ∷ []) refl

comm-iX-023 : Eqn
comm-iX-023 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ cx ∷ [])
  (cx ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 3 rt2s-130 ∷ rw⁻ 1 rt2s-384 ∷ rw⁻ 0 rt2s-132 ∷ []) refl

comm-iK-023 : Eqn
comm-iK-023 = derive (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ ck ∷ [])
  (ck ∷ x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ [])
  (rw 0 rt2s-97458 ∷ rw⁻ 0 rt2s-15215 ∷ []) refl

comm-iX-102 : Eqn
comm-iX-102 = derive (x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (x₁ ∷ cx′ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw 2 rt2s-134 ∷ rw 3 rt2s-5 ∷ rw⁻ 0 rt2s-764 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-34 ∷ rw⁻ 0 rt2s-137 ∷ []) refl

comm-iK-102 : Eqn
comm-iK-102 = derive (x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (x₁ ∷ ck′ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw 3 rt2s-698 ∷ rw 2 rt2s-20 ∷ rw 1 rt2s-13 ∷ rw 0 rt2s-20 ∷ rw 1 rt2s-1235 ∷ rw⁻ 2 rt2s-14534 ∷
     rw⁻ 1 rt2s-42 ∷ rw⁻ 2 rt2s-3952 ∷ rw⁻ 0 rt2s-698 ∷ []) refl

comm-iX-103 : Eqn
comm-iX-103 = derive (x₀ ∷ cs ∷ x₀ ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw 3 rt2s-70 ∷ rw 6 rt2s-32 ∷ rw 4 rt2s-95 ∷ rw 3 rt2s-18 ∷ rw 2 rt2s-4 ∷ rw⁻ 2 rt2s-70 ∷
     rw⁻ 1 rt2s-72 ∷ rw⁻ 1 rt2s-5 ∷ rw⁻ 2 rt2s-70 ∷ rw⁻ 0 rt2s-18 ∷ rw⁻ 1 rt2s-95 ∷ rw⁻ 3 rt2s-32 ∷
     rw⁻ 0 rt2s-70 ∷ []) refl

comm-iK-103 : Eqn
comm-iK-103 = derive (x₀ ∷ cs ∷ x₀ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw 0 rt2s-389 ∷ rw 0 rt2s-764 ∷ rw⁻ 0 rt2s-12181 ∷ rw⁻ 3 rt2s-764 ∷ rw⁻ 3 rt2s-4 ∷ rw⁻ 4 rt2s-34 ∷
     rw⁻ 0 rt2s-34 ∷ []) refl

comm-iX-123 : Eqn
comm-iX-123 = derive (x₀ ∷ cs ∷ x₀ ∷ cx ∷ [])
  (cx ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw⁻ 0 rt2s-3407 ∷ []) refl

comm-iK-123 : Eqn
comm-iK-123 = derive (x₀ ∷ cs ∷ x₀ ∷ ck ∷ [])
  (ck ∷ x₀ ∷ cs ∷ x₀ ∷ [])
  (rw 0 rt2s-1233 ∷ rw⁻ 0 rt2s-1335 ∷ []) refl

comm-iX-201 : Eqn
comm-iX-201 = derive (x₁ ∷ cs ∷ x₁ ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw 2 rt2s-18 ∷ rw 2 rt2s-130 ∷ rw 3 rt2s-4 ∷ rw⁻ 0 rt2s-737 ∷ rw⁻ 0 rt2s-5 ∷ rw⁻ 1 rt2s-32 ∷
     rw⁻ 0 rt2s-245 ∷ []) refl

comm-iK-201 : Eqn
comm-iK-201 = derive (x₁ ∷ cs ∷ x₁ ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (x₀ ∷ ck ∷ x₀ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw 2 rt2s-18 ∷ rw 2 rt2s-948 ∷ rw 1 rt2s-12 ∷ rw 0 rt2s-22 ∷ rw 1 rt2s-1265 ∷ rw⁻ 2 rt2s-8160 ∷
     rw⁻ 1 rt2s-38 ∷ rw⁻ 2 rt2s-2881 ∷ rw⁻ 0 rt2s-687 ∷ []) refl

comm-iX-203 : Eqn
comm-iX-203 = derive (x₁ ∷ cs ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw 3 rt2s-70 ∷ rw 2 rt2s-5 ∷ rw 4 rt2s-32 ∷ rw 2 rt2s-95 ∷ rw⁻ 2 rt2s-95 ∷ rw⁻ 4 rt2s-32 ∷
     rw⁻ 1 rt2s-72 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-18 ∷ rw⁻ 2 rt2s-95 ∷ rw⁻ 4 rt2s-32 ∷ rw⁻ 0 rt2s-18 ∷
     rw⁻ 1 rt2s-95 ∷ rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-70 ∷ []) refl

comm-iK-203 : Eqn
comm-iK-203 = derive (x₁ ∷ cs ∷ x₁ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw 3 rt2s-34 ∷ rw 2 rt2s-18 ∷ rw 2 rt2s-134 ∷ rw 2 rt2s-27140 ∷ rw⁻ 4 rt2s-32 ∷ rw⁻ 1 rt2s-74 ∷
     rw⁻ 0 rt2s-245 ∷ rw⁻ 1 rt2s-6331 ∷ rw⁻ 3 rt2s-135 ∷ rw⁻ 0 rt2s-34 ∷ []) refl

comm-iX-213 : Eqn
comm-iX-213 = derive (x₁ ∷ cs ∷ x₁ ∷ cx′ ∷ [])
  (cx′ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw⁻ 0 rt2s-2825 ∷ []) refl

comm-iK-213 : Eqn
comm-iK-213 = derive (x₁ ∷ cs ∷ x₁ ∷ ck′ ∷ [])
  (ck′ ∷ x₁ ∷ cs ∷ x₁ ∷ [])
  (rw 0 rt2s-1266 ∷ rw⁻ 0 rt2s-1351 ∷ []) refl

comm-iX-301 : Eqn
comm-iX-301 = derive (cs ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ cs ∷ [])
  (rw 1 rt2s-245 ∷ rw⁻ 0 rt2s-736 ∷ rw⁻ 0 rt2s-245 ∷ []) refl

comm-iK-301 : Eqn
comm-iK-301 = derive (cs ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (x₀ ∷ ck ∷ x₀ ∷ cs ∷ [])
  (rw 1 rt2s-687 ∷ rw 0 rt2s-12 ∷ rw⁻ 0 rt2s-8558 ∷ rw⁻ 0 rt2s-687 ∷ []) refl

comm-iX-302 : Eqn
comm-iX-302 = derive (cs ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (x₁ ∷ cx′ ∷ x₁ ∷ cs ∷ [])
  (rw 1 rt2s-137 ∷ rw⁻ 0 rt2s-760 ∷ rw⁻ 0 rt2s-137 ∷ []) refl

comm-iK-302 : Eqn
comm-iK-302 = derive (cs ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (x₁ ∷ ck′ ∷ x₁ ∷ cs ∷ [])
  (rw 1 rt2s-698 ∷ rw 0 rt2s-13 ∷ rw⁻ 0 rt2s-8630 ∷ rw⁻ 0 rt2s-698 ∷ []) refl

comm-iX-312 : Eqn
comm-iX-312 = derive (cs ∷ cx ∷ cx′ ∷ cx ∷ [])
  (cx ∷ cx′ ∷ cx ∷ cs ∷ [])
  (rw⁻ 0 rt2s-72 ∷ []) refl

comm-iK-312 : Eqn
comm-iK-312 = derive (cs ∷ cx ∷ ck′ ∷ cx ∷ [])
  (cx ∷ ck′ ∷ cx ∷ cs ∷ [])
  (rw⁻ 0 rt2s-74 ∷ []) refl

comm-XX-0123 : Eqn
comm-XX-0123 = derive (x₀ ∷ cx ∷ x₀ ∷ cx ∷ [])
  (cx ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (rw 1 rt2s-31 ∷ rw 0 rt2s-4 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-18 ∷ rw⁻ 0 rt2s-31 ∷ []) refl

comm-XK-0123 : Eqn
comm-XK-0123 = derive (x₀ ∷ cx ∷ x₀ ∷ ck ∷ [])
  (ck ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (rw 0 rt2s-245 ∷ rw⁻ 0 rt2s-789 ∷ rw⁻ 1 rt2s-245 ∷ []) refl

comm-KK-0123 : Eqn
comm-KK-0123 = derive (x₀ ∷ ck ∷ x₀ ∷ ck ∷ [])
  (ck ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (rw 0 rt2s-57 ∷ rw⁻ 0 rt2s-57 ∷ rw⁻ 0 rt2s-51 ∷ []) refl

comm-XX-0213 : Eqn
comm-XX-0213 = derive (x₁ ∷ cx′ ∷ x₁ ∷ cx′ ∷ [])
  (cx′ ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (rw 1 rt2s-33 ∷ rw 0 rt2s-18 ∷ rw 1 rt2s-5 ∷ rw⁻ 1 rt2s-5 ∷ rw⁻ 0 rt2s-33 ∷ []) refl

comm-XK-0213 : Eqn
comm-XK-0213 = derive (x₁ ∷ cx′ ∷ x₁ ∷ ck′ ∷ [])
  (ck′ ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (rw 0 rt2s-137 ∷ rw⁻ 0 rt2s-794 ∷ rw⁻ 1 rt2s-137 ∷ []) refl

comm-KK-0213 : Eqn
comm-KK-0213 = derive (x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ [])
  (ck′ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (rw 0 rt2s-58 ∷ rw⁻ 0 rt2s-58 ∷ rw⁻ 0 rt2s-52 ∷ []) refl

comm-XX-0312 : Eqn
comm-XX-0312 = derive (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ [])
  (cx ∷ cx′ ∷ cx ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  (rw 0 rt2s-70 ∷ rw 3 rt2s-32 ∷ rw 1 rt2s-95 ∷ rw 0 rt2s-18 ∷ rw 4 rt2s-6 ∷ rw 3 rt2s-7 ∷
     rw 2 rt2s-6 ∷ rw⁻ 0 rt2s-6 ∷ rw⁻ 1 rt2s-7 ∷ rw⁻ 2 rt2s-6 ∷ []) refl

comm-XK-0312 : Eqn
comm-XK-0312 = derive (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ cx ∷ ck′ ∷ cx ∷ [])
  (cx ∷ ck′ ∷ cx ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  (rw 1 rt2s-247 ∷ rw 0 rt2s-32 ∷ rw 3 rt2s-32 ∷ rw 1 rt2s-254 ∷ rw 0 rt2s-18 ∷ rw 0 rt2s-130 ∷
     rw 3 rt2s-6 ∷ rw⁻ 1 rt2s-794 ∷ rw⁻ 2 rt2s-137 ∷ rw⁻ 4 rt2s-32 ∷ rw⁻ 2 rt2s-247 ∷ rw⁻ 2 rt2s-6 ∷ []) refl

comm-KK-0312 : Eqn
comm-KK-0312 = derive (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx ∷ ck′ ∷ cx ∷ [])
  (cx ∷ ck′ ∷ cx ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (rw 0 rt2s-34 ∷ rw 1 rt2s-6317 ∷ rw 0 rt2s-245 ∷ rw 2 rt2s-146 ∷ rw 1 rt2s-32 ∷ rw 0 rt2s-5 ∷
     rw⁻ 1 rt2s-85 ∷ rw⁻ 3 rt2s-40309 ∷ rw⁻ 1 rt2s-42 ∷ rw⁻ 2 rt2s-11178 ∷ rw⁻ 3 rt2s-34 ∷ []) refl

comm-XX-1203 : Eqn
comm-XX-1203 = derive (cx ∷ cx′ ∷ cx ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ [])
  (rw 2 rt2s-6 ∷ rw 1 rt2s-7 ∷ rw 0 rt2s-6 ∷ rw⁻ 2 rt2s-6 ∷ rw⁻ 3 rt2s-7 ∷ rw⁻ 4 rt2s-6 ∷
     rw⁻ 0 rt2s-18 ∷ rw⁻ 1 rt2s-95 ∷ rw⁻ 3 rt2s-32 ∷ rw⁻ 0 rt2s-70 ∷ []) refl

comm-XK-1203 : Eqn
comm-XK-1203 = derive (cx ∷ cx′ ∷ cx ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx ∷ cx′ ∷ cx ∷ [])
  (rw 1 rt2s-35 ∷ rw 0 rt2s-6 ∷ rw 0 rt2s-247 ∷ rw 0 rt2s-3848 ∷ rw⁻ 6 rt2s-6 ∷ rw⁻ 4 rt2s-35 ∷
     rw⁻ 0 rt2s-34 ∷ []) refl

comm-KK-1203 : Eqn
comm-KK-1203 = derive (cx ∷ ck′ ∷ cx ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx ∷ ck′ ∷ cx ∷ [])
  (rw 3 rt2s-34 ∷ rw 2 rt2s-11178 ∷ rw 1 rt2s-42 ∷ rw 3 rt2s-40309 ∷ rw 1 rt2s-85 ∷ rw⁻ 0 rt2s-5 ∷
     rw⁻ 1 rt2s-32 ∷ rw⁻ 2 rt2s-146 ∷ rw⁻ 0 rt2s-245 ∷ rw⁻ 1 rt2s-6317 ∷ rw⁻ 0 rt2s-34 ∷ []) refl

comm-XX-1302 : Eqn
comm-XX-1302 = derive (cx′ ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (x₁ ∷ cx′ ∷ x₁ ∷ cx′ ∷ [])
  (rw 0 rt2s-33 ∷ rw 1 rt2s-5 ∷ rw⁻ 1 rt2s-5 ∷ rw⁻ 0 rt2s-18 ∷ rw⁻ 1 rt2s-33 ∷ []) refl

comm-XK-1302 : Eqn
comm-XK-1302 = derive (cx′ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (x₁ ∷ ck′ ∷ x₁ ∷ cx′ ∷ [])
  (rw 1 rt2s-698 ∷ rw 0 rt2s-28 ∷ rw⁻ 1 rt2s-3974 ∷ rw⁻ 0 rt2s-698 ∷ []) refl

comm-KK-1302 : Eqn
comm-KK-1302 = derive (ck′ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ [])
  (rw 0 rt2s-52 ∷ rw 0 rt2s-58 ∷ rw⁻ 0 rt2s-58 ∷ []) refl

comm-XX-2301 : Eqn
comm-XX-2301 = derive (cx ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ cx ∷ [])
  (rw 0 rt2s-31 ∷ rw 1 rt2s-18 ∷ rw 0 rt2s-4 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-31 ∷ []) refl

comm-XK-2301 : Eqn
comm-XK-2301 = derive (cx ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (x₀ ∷ ck ∷ x₀ ∷ cx ∷ [])
  (rw 1 rt2s-687 ∷ rw 0 rt2s-25 ∷ rw⁻ 1 rt2s-2918 ∷ rw⁻ 0 rt2s-687 ∷ []) refl

comm-KK-2301 : Eqn
comm-KK-2301 = derive (ck ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (x₀ ∷ ck ∷ x₀ ∷ ck ∷ [])
  (rw 0 rt2s-51 ∷ rw 0 rt2s-57 ∷ rw⁻ 0 rt2s-57 ∷ []) refl

swap-XX-012 : Eqn
swap-XX-012 = derive (cx ∷ cx′ ∷ cx ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (rw 1 rt2s-247 ∷ rw 0 rt2s-32 ∷ rw 3 rt2s-6 ∷ rw 2 rt2s-34 ∷ rw 0 rt2s-131 ∷ rw⁻ 0 rt2s-254 ∷
     rw⁻ 0 rt2s-5 ∷ rw⁻ 1 rt2s-32 ∷ rw⁻ 0 rt2s-245 ∷ []) refl

swap-XX′-012 : Eqn
swap-XX′-012 = derive (x₁ ∷ cx′ ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (rw 0 rt2s-137 ∷ rw 1 rt2s-35 ∷ rw 3 rt2s-6 ∷ rw⁻ 0 rt2s-131 ∷ rw⁻ 2 rt2s-34 ∷ rw⁻ 3 rt2s-6 ∷
     rw⁻ 0 rt2s-70 ∷ []) refl

swap-KX-012 : Eqn
swap-KX-012 = derive (cx ∷ ck′ ∷ cx ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (rw 2 rt2s-31 ∷ rw 3 rt2s-18 ∷ rw 2 rt2s-4 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-132 ∷ []) refl

swap-KX′-012 : Eqn
swap-KX′-012 = derive (x₁ ∷ ck′ ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ [])
  (cx ∷ cx′ ∷ cx ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (rw 0 rt2s-698 ∷ rw 2 rt2s-37830 ∷ rw 1 rt2s-38594 ∷ rw⁻ 0 rt2s-11161 ∷ rw⁻ 0 rt2s-32 ∷ rw⁻ 1 rt2s-247 ∷ []) refl

swap-XX-013 : Eqn
swap-XX-013 = derive (cx′ ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  (rw 0 rt2s-34 ∷ rw 1 rt2s-247 ∷ rw 0 rt2s-134 ∷ rw⁻ 1 rt2s-32 ∷ rw⁻ 0 rt2s-5 ∷ rw⁻ 1 rt2s-247 ∷
     rw⁻ 1 rt2s-6 ∷ rw⁻ 0 rt2s-245 ∷ []) refl

swap-XX′-013 : Eqn
swap-XX′-013 = derive (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ cx′ ∷ [])
  (cx′ ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (rw 1 rt2s-247 ∷ rw 0 rt2s-32 ∷ rw 3 rt2s-32 ∷ rw 1 rt2s-95 ∷ rw 0 rt2s-18 ∷ rw 0 rt2s-130 ∷
     rw 2 rt2s-35 ∷ rw 0 rt2s-31 ∷ rw 0 rt2s-134 ∷ rw⁻ 0 rt2s-134 ∷ rw⁻ 1 rt2s-247 ∷ rw⁻ 0 rt2s-34 ∷ []) refl

swap-KX-013 : Eqn
swap-KX-013 = derive (ck′ ∷ x₀ ∷ cx ∷ x₀ ∷ [])
  (x₀ ∷ cx ∷ x₀ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (rw 1 rt2s-245 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-27025 ∷ rw⁻ 0 rt2s-131 ∷ rw⁻ 2 rt2s-34 ∷ rw⁻ 0 rt2s-245 ∷ []) refl

swap-KX′-013 : Eqn
swap-KX′-013 = derive (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx′ ∷ [])
  (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ [])
  (rw 0 rt2s-34 ∷ rw 4 rt2s-7 ∷ rw⁻ 0 rt2s-34 ∷ []) refl

swap-XX-023 : Eqn
swap-XX-023 = derive (cx ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (x₁ ∷ cx′ ∷ x₁ ∷ cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ [])
  (rw 0 rt2s-32 ∷ rw⁻ 3 rt2s-6 ∷ rw⁻ 1 rt2s-35 ∷ rw⁻ 2 rt2s-5 ∷ rw⁻ 3 rt2s-70 ∷ []) refl

swap-XX′-023 : Eqn
swap-XX′-023 = derive (cx ∷ cx′ ∷ cx ∷ x₀ ∷ x₁ ∷ cx ∷ [])
  (cx ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (rw 1 rt2s-247 ∷ rw 0 rt2s-32 ∷ rw 3 rt2s-32 ∷ rw 1 rt2s-254 ∷ rw 0 rt2s-18 ∷ rw 0 rt2s-130 ∷
     rw 3 rt2s-6 ∷ rw⁻ 0 rt2s-130 ∷ rw⁻ 0 rt2s-18 ∷ rw⁻ 1 rt2s-254 ∷ rw⁻ 0 rt2s-32 ∷ []) refl

swap-KX-023 : Eqn
swap-KX-023 = derive (ck ∷ x₁ ∷ cx′ ∷ x₁ ∷ [])
  (x₁ ∷ cx′ ∷ x₁ ∷ cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ [])
  (rw 1 rt2s-137 ∷ rw⁻ 0 rt2s-4 ∷ rw⁻ 1 rt2s-7 ∷ rw⁻ 0 rt2s-137 ∷ []) refl

swap-KX′-023 : Eqn
swap-KX′-023 = derive (cx′ ∷ x₀ ∷ ck ∷ x₀ ∷ cx′ ∷ cx ∷ [])
  (cx ∷ x₁ ∷ ck′ ∷ x₁ ∷ [])
  (rw 0 rt2s-34 ∷ rw 1 rt2s-6317 ∷ rw 0 rt2s-245 ∷ rw⁻ 0 rt2s-32 ∷ []) refl

swap-XX-123 : Eqn
swap-XX-123 = derive (cx ∷ cx ∷ cx′ ∷ cx ∷ [])
  (cx ∷ cx′ ∷ cx ∷ cx′ ∷ [])
  (rw 0 rt2s-6 ∷ rw⁻ 0 rt2s-6 ∷ rw⁻ 1 rt2s-35 ∷ []) refl

swap-XX′-123 : Eqn
swap-XX′-123 = derive (cx′ ∷ cx ∷ [])
  (cx ∷ cx ∷ cx′ ∷ cx ∷ [])
  (rw⁻ 0 rt2s-6 ∷ []) refl

swap-KX-123 : Eqn
swap-KX-123 = derive (ck ∷ cx ∷ cx′ ∷ cx ∷ [])
  (cx ∷ cx′ ∷ cx ∷ ck′ ∷ [])
  (rw 0 rt2s-56 ∷ []) refl

swap-KX′-123 : Eqn
swap-KX′-123 = derive (ck′ ∷ cx ∷ [])
  (cx ∷ cx ∷ ck′ ∷ cx ∷ [])
  (rw⁻ 0 rt2s-6 ∷ []) refl

rel-17-0123 : Eqn
rel-17-0123 = derive (x₀ ∷ ck ∷ x₀ ∷ ck ∷ x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ [])
  (x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ x₀ ∷ ck ∷ x₀ ∷ ck ∷ [])
  (rw 0 rt2s-57 ∷ rw 1 rt2s-58 ∷ rw 0 rt2s-59 ∷ rw⁻ 1 rt2s-57 ∷ rw⁻ 0 rt2s-58 ∷ []) refl

rel-17-0213 : Eqn
rel-17-0213 = derive (x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ x₀ ∷ ck ∷ x₀ ∷ ck ∷ [])
  (x₀ ∷ ck ∷ x₀ ∷ ck ∷ x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ [])
  (rw 0 rt2s-58 ∷ rw 1 rt2s-57 ∷ rw⁻ 0 rt2s-59 ∷ rw⁻ 1 rt2s-58 ∷ rw⁻ 0 rt2s-57 ∷ []) refl

d∘e-I : Eqn
d∘e-I = derive (ι ∷ [])
  (x₀ ∷ x₁ ∷ cs ∷ x₀ ∷ x₁ ∷ x₀ ∷ cs ∷ x₀ ∷ x₁ ∷ cs ∷ x₁ ∷ cs ∷ [])
  (rw⁻ 1 rt2s-83 ∷ rw⁻ 1 rt2s-38 ∷ rw⁻ 2 rt2s-38 ∷ rw⁻ 3 rt2s-106 ∷ rw⁻ 0 rt2s-99 ∷ rw⁻ 1 rt2s-106 ∷
     rw⁻ 3 rt2s-4 ∷ rw⁻ 4 rt2s-18 ∷ []) refl

d∘e-S : Eqn
d∘e-S = derive (s₀ ∷ [])
  (x₁ ∷ cs ∷ x₁ ∷ cs ∷ [])
  (rw⁻ 0 rt2s-106 ∷ []) refl

d∘e-S↑ : Eqn
d∘e-S↑ = derive (s₁ ∷ [])
  (x₀ ∷ cs ∷ x₀ ∷ cs ∷ [])
  (rw⁻ 0 rt2s-108 ∷ []) refl

d∘e-K : Eqn
d∘e-K = derive (k₀ ∷ [])
  (x₁ ∷ ck′ ∷ x₁ ∷ ck′ ∷ [])
  (rw⁻ 0 rt2s-58 ∷ []) refl

d∘e-K↑ : Eqn
d∘e-K↑ = derive (k₁ ∷ [])
  (x₀ ∷ ck ∷ x₀ ∷ ck ∷ [])
  (rw⁻ 0 rt2s-57 ∷ []) refl

------------------------------------------------------------------------
-- Presentations of groups
--
-- The ctrl lemma for the structural commutation rules, given
-- completeness on at most eight wires.
--
-- In `[ g ↥ᵃ ] • [ h ] = [ h ] • [ g ↥ᵃ ]` the gate g can sit anywhere
-- above h, and the controlled versions share the control wire and,
-- under ctrl₁, the spare.  If g is at the bottom of what is above h,
-- the controlled equation is a closed equation on at most eight wires
-- with idle wires on top, which completeness proves (the two sides
-- have the same matrix, CtrlSame).  Otherwise CtrlMove.move writes the
-- gadget of g as a cycle of the wires above h's gadget around the
-- gadget of g one wire lower with an idle wire on top; the cycle passes
-- h's gadget (Placement.apart), and what is left is the same equation
-- one wire narrower, under an idle wire on top.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.CtrlComm
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k P.⊢ u ≈ v)
  where

open import Data.Bool.Base using (T)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Syntactics
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (CTRL ; CTRL₁ ; ctrl ; XC)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl₁ ; ctrl₁-pad ; ctrl-pad)
open import Examples.Groups.CCX+HH.NaturalP.CtrlSame using (soundᴾ ; ctrl₁-same ; ctrl-same)
open import Examples.Groups.CCX+HH.NaturalP.CtrlMove using (Z ; Z⁻ ; move)
open import Examples.Groups.CCX+HH.NaturalP.Pad using (widen)
import Examples.Groups.Symmetric-Prop.Placement as Placement
import Examples.Groups.Symmetric-Prop.Cycle as Cycle

private
  variable
    n m b : ℕ

  le : ∀ a → T (a ≤ᵇ 8) → a ≤ 8
  le a p = ≤ᵇ⇒≤ a 8 p

  no-scalar : ∀ {n} (h h′ : Gate 0) →
    n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ
  no-scalar ()

  module PL = Placement Gate SW-gate _NP,_===_
  module CY = Cycle Gate SW-gate _NP,_===_

------------------------------------------------------------------------
-- Tools

private
  -- A closed core under ctrl₁, widened.
  core₁ : ∀ {u₀ v₀ : Circuit b} → b ⊢ u₀ ≈ v₀ → ₂₊ b ≤ 8 → ∀ j →
    (₂₊ b + j) ⊢ ctrl₁ (u₀ ↓ᵏ j) ≈ ctrl₁ (v₀ ↓ᵏ j)
  core₁ {u₀ = u₀} {v₀} e b≤ j =
    Eq.subst₂ (λ x y → _ ⊢ x ≈ y) (Eq.sym (ctrl₁-pad u₀ j)) (Eq.sym (ctrl₁-pad v₀ j))
      (widen j (complete≤ b≤ (ctrl₁-same u₀ v₀ (soundᴾ e))))

  -- An idle wire on top preserves derivations.
  top-cong : ∀ {u v : Circuit n} → n ⊢ u ≈ v → (₁₊ n) ⊢ u ⇓ ≈ v ⇓
  top-cong {u = u} {v} e =
    PB.trans (CY.top-is-bottom no-scalar u)
    (PB.trans (PB.cong PB.refl (PB.cong (lemma-cong↑ u v e) PB.refl))
      (PB.sym (CY.top-is-bottom no-scalar v)))

  -- A word passing B passes its conjugate by words passing B.
  conj-pass : ∀ {Y C Y⁻ B : Circuit n} →
    n ⊢ Y • B ≈ B • Y → n ⊢ C • B ≈ B • C → n ⊢ Y⁻ • B ≈ B • Y⁻ →
    n ⊢ (Y • (C • Y⁻)) • B ≈ B • (Y • (C • Y⁻))
  conj-pass YB CB Y⁻B =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.trans PB.assoc
      (PB.trans (PB.cong PB.refl Y⁻B)
      (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong CB PB.refl) PB.assoc)))))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong YB PB.refl) PB.assoc)))

  ↑ᵏ3 : (X : Circuit n) → X ↑ᵏ 3 ≡ X ↑ ↑ ↑
  ↑ᵏ3 X = Eq.trans (PL.↑ᵏ-suc X 2) (Eq.cong _↑ (PL.↑ᵏ-suc X 1))

  ↑ᵏ4 : (X : Circuit n) → X ↑ᵏ 4 ≡ X ↑ ↑ ↑ ↑
  ↑ᵏ4 X = Eq.trans (PL.↑ᵏ-suc X 3) (Eq.cong _↑ (↑ᵏ3 X))

  ↑ᵏ5 : (X : Circuit n) → X ↑ᵏ 5 ≡ X ↑ ↑ ↑ ↑ ↑
  ↑ᵏ5 X = Eq.trans (PL.↑ᵏ-suc X 4) (Eq.cong _↑ (↑ᵏ4 X))

  -- A closed word on the bottom k wires passes a word k wires up.
  apart₃ : (B₀ : Circuit 3) (X : Circuit n) →
    (₃₊ n) ⊢ X ↑ ↑ ↑ • (B₀ ↓ᵏ n) ≈ (B₀ ↓ᵏ n) • X ↑ ↑ ↑
  apart₃ B₀ X = Eq.subst (λ x → _ ⊢ x • (B₀ ↓ᵏ _) ≈ (B₀ ↓ᵏ _) • x) (↑ᵏ3 X)
    (PB.sym (PL.apart no-scalar B₀ X))

------------------------------------------------------------------------
-- Under ctrl₁: X at the bottom

-- CTRL₁ (g ↥) passes CTRL₁ X.
pass₁-X : (g : Gen n) → (₃₊ n) ⊢ CTRL₁ (g ↥) • CTRL₁ (gate₁ {n} X-gate) ≈
                                  CTRL₁ (gate₁ {n} X-gate) • CTRL₁ (g ↥)
pass₁-X (gate₀ ())
pass₁-X (gate₁ {k} X-gate) =
  core₁ {b = 2} (PB.axiom (comm₁ X-gate (gate₁ {0} X-gate))) (le 4 tt) k
pass₁-X (gate₂ {k} CX-gate) =
  core₁ {b = 3} (PB.axiom (comm₁ X-gate (gate₂ {0} CX-gate))) (le 5 tt) k
pass₁-X (gate₂ {k} HH-gate) =
  core₁ {b = 3} (PB.axiom (comm₁ X-gate (gate₂ {0} HH-gate))) (le 5 tt) k
pass₁-X (gate₂ {k} SW-gate) =
  core₁ {b = 3} (PB.axiom (comm₁ X-gate (gate₂ {0} SW-gate))) (le 5 tt) k
pass₁-X (gate₃ {k} CCX-gate) =
  core₁ {b = 4} (PB.axiom (comm₁ X-gate (gate₃ {0} CCX-gate))) (le 6 tt) k
pass₁-X {suc n} (g ↥) =
  PB.trans (PB.cong (move (g ↥)) PB.refl)
  (PB.trans (conj-pass (apart₃ B₀ (Z g)) (top-cong (pass₁-X g)) (apart₃ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥)))))
  where
  B₀ = CTRL₁ (gate₁ {0} X-gate)

private
  apart₄ : (B₀ : Circuit 4) (X : Circuit n) →
    (₄₊ n) ⊢ X ↑ ↑ ↑ ↑ • (B₀ ↓ᵏ n) ≈ (B₀ ↓ᵏ n) • X ↑ ↑ ↑ ↑
  apart₄ B₀ X = Eq.subst (λ x → _ ⊢ x • (B₀ ↓ᵏ _) ≈ (B₀ ↓ᵏ _) • x) (↑ᵏ4 X)
    (PB.sym (PL.apart no-scalar B₀ X))

  apart₅ : (B₀ : Circuit 5) (X : Circuit n) →
    (suc (₄₊ n)) ⊢ X ↑ ↑ ↑ ↑ ↑ • (B₀ ↓ᵏ n) ≈ (B₀ ↓ᵏ n) • X ↑ ↑ ↑ ↑ ↑
  apart₅ B₀ X = Eq.subst (λ x → _ ⊢ x • (B₀ ↓ᵏ _) ≈ (B₀ ↓ᵏ _) • x) (↑ᵏ5 X)
    (PB.sym (PL.apart no-scalar B₀ X))


------------------------------------------------------------------------
-- Under ctrl₁: CX at the bottom

pass₁-CX : (g : Gen n) → (₄₊ n) ⊢ CTRL₁ (g ↥ ↥) • CTRL₁ (gate₂ {n} CX-gate) ≈
                                  CTRL₁ (gate₂ {n} CX-gate) • CTRL₁ (g ↥ ↥)
pass₁-CX (gate₀ ())
pass₁-CX (gate₁ {k} X-gate) =
  core₁ {b = 3} (PB.axiom (comm₂ CX-gate (gate₁ {0} X-gate))) (le 5 tt) k
pass₁-CX (gate₂ {k} CX-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ CX-gate (gate₂ {0} CX-gate))) (le 6 tt) k
pass₁-CX (gate₂ {k} HH-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ CX-gate (gate₂ {0} HH-gate))) (le 6 tt) k
pass₁-CX (gate₂ {k} SW-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ CX-gate (gate₂ {0} SW-gate))) (le 6 tt) k
pass₁-CX (gate₃ {k} CCX-gate) =
  core₁ {b = 5} (PB.axiom (comm₂ CX-gate (gate₃ {0} CCX-gate))) (le 7 tt) k
pass₁-CX {suc n} (g ↥) =
  PB.trans (PB.cong (move (g ↥ ↥)) PB.refl)
  (PB.trans (conj-pass (apart₄ B₀ (Z g)) (top-cong (pass₁-CX g)) (apart₄ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥ ↥)))))
  where
  B₀ = CTRL₁ (gate₂ {0} CX-gate)

------------------------------------------------------------------------
-- Under ctrl₁: HH at the bottom

pass₁-HH : (g : Gen n) → (₄₊ n) ⊢ CTRL₁ (g ↥ ↥) • CTRL₁ (gate₂ {n} HH-gate) ≈
                                  CTRL₁ (gate₂ {n} HH-gate) • CTRL₁ (g ↥ ↥)
pass₁-HH (gate₀ ())
pass₁-HH (gate₁ {k} X-gate) =
  core₁ {b = 3} (PB.axiom (comm₂ HH-gate (gate₁ {0} X-gate))) (le 5 tt) k
pass₁-HH (gate₂ {k} CX-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ HH-gate (gate₂ {0} CX-gate))) (le 6 tt) k
pass₁-HH (gate₂ {k} HH-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ HH-gate (gate₂ {0} HH-gate))) (le 6 tt) k
pass₁-HH (gate₂ {k} SW-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ HH-gate (gate₂ {0} SW-gate))) (le 6 tt) k
pass₁-HH (gate₃ {k} CCX-gate) =
  core₁ {b = 5} (PB.axiom (comm₂ HH-gate (gate₃ {0} CCX-gate))) (le 7 tt) k
pass₁-HH {suc n} (g ↥) =
  PB.trans (PB.cong (move (g ↥ ↥)) PB.refl)
  (PB.trans (conj-pass (apart₄ B₀ (Z g)) (top-cong (pass₁-HH g)) (apart₄ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥ ↥)))))
  where
  B₀ = CTRL₁ (gate₂ {0} HH-gate)

------------------------------------------------------------------------
-- Under ctrl₁: SW at the bottom

pass₁-SW : (g : Gen n) → (₄₊ n) ⊢ CTRL₁ (g ↥ ↥) • CTRL₁ (gate₂ {n} SW-gate) ≈
                                  CTRL₁ (gate₂ {n} SW-gate) • CTRL₁ (g ↥ ↥)
pass₁-SW (gate₀ ())
pass₁-SW (gate₁ {k} X-gate) =
  core₁ {b = 3} (PB.axiom (comm₂ SW-gate (gate₁ {0} X-gate))) (le 5 tt) k
pass₁-SW (gate₂ {k} CX-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ SW-gate (gate₂ {0} CX-gate))) (le 6 tt) k
pass₁-SW (gate₂ {k} HH-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ SW-gate (gate₂ {0} HH-gate))) (le 6 tt) k
pass₁-SW (gate₂ {k} SW-gate) =
  core₁ {b = 4} (PB.axiom (comm₂ SW-gate (gate₂ {0} SW-gate))) (le 6 tt) k
pass₁-SW (gate₃ {k} CCX-gate) =
  core₁ {b = 5} (PB.axiom (comm₂ SW-gate (gate₃ {0} CCX-gate))) (le 7 tt) k
pass₁-SW {suc n} (g ↥) =
  PB.trans (PB.cong (move (g ↥ ↥)) PB.refl)
  (PB.trans (conj-pass (apart₄ B₀ (Z g)) (top-cong (pass₁-SW g)) (apart₄ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥ ↥)))))
  where
  B₀ = CTRL₁ (gate₂ {0} SW-gate)

------------------------------------------------------------------------
-- Under ctrl₁: CCX at the bottom

pass₁-CCX : (g : Gen n) → (suc (₄₊ n)) ⊢ CTRL₁ (g ↥ ↥ ↥) • CTRL₁ (gate₃ {n} CCX-gate) ≈
                                  CTRL₁ (gate₃ {n} CCX-gate) • CTRL₁ (g ↥ ↥ ↥)
pass₁-CCX (gate₀ ())
pass₁-CCX (gate₁ {k} X-gate) =
  core₁ {b = 4} (PB.axiom (comm₃ CCX-gate (gate₁ {0} X-gate))) (le 6 tt) k
pass₁-CCX (gate₂ {k} CX-gate) =
  core₁ {b = 5} (PB.axiom (comm₃ CCX-gate (gate₂ {0} CX-gate))) (le 7 tt) k
pass₁-CCX (gate₂ {k} HH-gate) =
  core₁ {b = 5} (PB.axiom (comm₃ CCX-gate (gate₂ {0} HH-gate))) (le 7 tt) k
pass₁-CCX (gate₂ {k} SW-gate) =
  core₁ {b = 5} (PB.axiom (comm₃ CCX-gate (gate₂ {0} SW-gate))) (le 7 tt) k
pass₁-CCX (gate₃ {k} CCX-gate) =
  core₁ {b = 6} (PB.axiom (comm₃ CCX-gate (gate₃ {0} CCX-gate))) (le 8 tt) k
pass₁-CCX {suc n} (g ↥) =
  PB.trans (PB.cong (move (g ↥ ↥ ↥)) PB.refl)
  (PB.trans (conj-pass (apart₅ B₀ (Z g)) (top-cong (pass₁-CCX g)) (apart₅ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥ ↥ ↥)))))
  where
  B₀ = CTRL₁ (gate₃ {0} CCX-gate)

------------------------------------------------------------------------
-- Under ctrl
--
-- The same with h's gadget at the bottom under ctrl, which holds wires
-- 0 … a, and wire a + 1 too where it borrows one (HH and CCX).  On at
-- most eight wires the whole instance is decided by completeness
-- (`direct`); with g at the bottom of what is above h, or for HH and
-- CCX just above, it is a closed core widened (`coreC`); otherwise the
-- cycle that `move` conjugates by lies above h's gadget.

private
  -- An equation on at most eight wires under ctrl, by completeness.
  direct : ∀ {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ u ≈ v → T (suc (₄₊ m) ≤ᵇ 8) →
    suc (₄₊ m) ⊢ ctrl u ≈ ctrl v
  direct {m = m} {u = u} {v} e le8 =
    complete≤ (le (suc (₄₊ m)) le8) (ctrl-same u v (soundᴾ e))

  -- A closed core under ctrl, widened.
  coreC : ∀ c {u₀ v₀ : Circuit (₄₊ c)} → (₄₊ c) ⊢ u₀ ≈ v₀ → T (suc (₄₊ c) ≤ᵇ 8) →
    ∀ j → (suc (₄₊ c) + j) ⊢ ctrl (u₀ ↓ᵏ j) ≈ ctrl (v₀ ↓ᵏ j)
  coreC c {u₀} {v₀} e le8 j =
    Eq.subst₂ (λ x y → _ ⊢ x ≈ y) (Eq.sym (ctrl-pad u₀ j)) (Eq.sym (ctrl-pad v₀ j))
      (widen j (direct e le8))

  apart₂ : (B₀ : Circuit 2) (X : Circuit n) →
    (₂₊ n) ⊢ X ↑ ↑ • (B₀ ↓ᵏ n) ≈ (B₀ ↓ᵏ n) • X ↑ ↑
  apart₂ B₀ X = Eq.subst (λ x → _ ⊢ x • (B₀ ↓ᵏ _) ≈ (B₀ ↓ᵏ _) • x) (PL.↑ᵏ-suc X 1)
    (PB.sym (PL.apart no-scalar B₀ X))

pass-X : (g : Gen (₃₊ m)) → suc (₄₊ m) ⊢
  CTRL₁ g • CTRL (gate₁ {₃₊ m} X-gate) ≈ CTRL (gate₁ {₃₊ m} X-gate) • CTRL₁ g
pass-X (gate₀ ())
pass-X (gate₁ {₂₊ j} h) = coreC 0 (PB.axiom (comm₁ X-gate (gate₁ {2} h))) tt j
pass-X (gate₂ {₁₊ j} h) = coreC 0 (PB.axiom (comm₁ X-gate (gate₂ {1} h))) tt j
pass-X (gate₃ {j} h)    = coreC 0 (PB.axiom (comm₁ X-gate (gate₃ {0} h))) tt j
pass-X {zero} (g ↥) = direct (PB.axiom (comm₁ X-gate (g ↥))) tt
pass-X {suc m} (g ↥) =
  PB.trans (PB.cong (move g) PB.refl)
  (PB.trans (conj-pass (apart₂ B₀ (Z g)) (top-cong (pass-X g)) (apart₂ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move g))))
  where
  B₀ = CTRL (gate₁ {0} X-gate)

pass-CX : (g : Gen (₂₊ m)) → suc (₄₊ m) ⊢
  CTRL₁ (g ↥) • CTRL (gate₂ {₂₊ m} CX-gate) ≈ CTRL (gate₂ {₂₊ m} CX-gate) • CTRL₁ (g ↥)
pass-CX (gate₀ ())
pass-CX (gate₁ {₁₊ j} h) = coreC 0 (PB.axiom (comm₂ CX-gate (gate₁ {1} h))) tt j
pass-CX (gate₂ {j} h)    = coreC 0 (PB.axiom (comm₂ CX-gate (gate₂ {0} h))) tt j
pass-CX (gate₃ {j} h)    = coreC 1 (PB.axiom (comm₂ CX-gate (gate₃ {0} h))) tt j
pass-CX {zero} (g ↥) = direct (PB.axiom (comm₂ CX-gate (g ↥))) tt
pass-CX {suc m} (g ↥) =
  PB.trans (PB.cong (move (g ↥)) PB.refl)
  (PB.trans (conj-pass (apart₃ B₀ (Z g)) (top-cong (pass-CX g)) (apart₃ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥)))))
  where
  B₀ = CTRL (gate₂ {0} CX-gate)

pass-SW : (g : Gen (₂₊ m)) → suc (₄₊ m) ⊢
  CTRL₁ (g ↥) • CTRL (gate₂ {₂₊ m} SW-gate) ≈ CTRL (gate₂ {₂₊ m} SW-gate) • CTRL₁ (g ↥)
pass-SW (gate₀ ())
pass-SW (gate₁ {₁₊ j} h) = coreC 0 (PB.axiom (comm₂ SW-gate (gate₁ {1} h))) tt j
pass-SW (gate₂ {j} h)    = coreC 0 (PB.axiom (comm₂ SW-gate (gate₂ {0} h))) tt j
pass-SW (gate₃ {j} h)    = coreC 1 (PB.axiom (comm₂ SW-gate (gate₃ {0} h))) tt j
pass-SW {zero} (g ↥) = direct (PB.axiom (comm₂ SW-gate (g ↥))) tt
pass-SW {suc m} (g ↥) =
  PB.trans (PB.cong (move (g ↥)) PB.refl)
  (PB.trans (conj-pass (apart₃ B₀ (Z g)) (top-cong (pass-SW g)) (apart₃ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥)))))
  where
  B₀ = CTRL (gate₂ {0} SW-gate)

pass-HH : (g : Gen (₂₊ m)) → suc (₄₊ m) ⊢
  CTRL₁ (g ↥) • CTRL (gate₂ {₂₊ m} HH-gate) ≈ CTRL (gate₂ {₂₊ m} HH-gate) • CTRL₁ (g ↥)
pass-HH (gate₀ ())
pass-HH (gate₁ {₁₊ j} h) = coreC 0 (PB.axiom (comm₂ HH-gate (gate₁ {1} h))) tt j
pass-HH (gate₂ {j} h)    = coreC 0 (PB.axiom (comm₂ HH-gate (gate₂ {0} h))) tt j
pass-HH (gate₃ {j} h)    = coreC 1 (PB.axiom (comm₂ HH-gate (gate₃ {0} h))) tt j
pass-HH (gate₀ () ↥)
pass-HH (gate₁ {j} h ↥) = coreC 0 (PB.axiom (comm₂ HH-gate (gate₁ {0} h ↥))) tt j
pass-HH (gate₂ {j} h ↥) = coreC 1 (PB.axiom (comm₂ HH-gate (gate₂ {0} h ↥))) tt j
pass-HH (gate₃ {j} h ↥) = coreC 2 (PB.axiom (comm₂ HH-gate (gate₃ {0} h ↥))) tt j
pass-HH {zero} (g ↥ ↥) = direct (PB.axiom (comm₂ HH-gate (g ↥ ↥))) tt
pass-HH {suc m} (g ↥ ↥) =
  PB.trans (PB.cong (move (g ↥ ↥)) PB.refl)
  (PB.trans (conj-pass (apart₄ B₀ (Z g)) (top-cong (pass-HH (g ↥))) (apart₄ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥ ↥)))))
  where
  B₀ = CTRL (gate₂ {1} HH-gate)

pass-CCX : (g : Gen (₁₊ m)) → suc (₄₊ m) ⊢
  CTRL₁ (g ↥ ↥) • CTRL (gate₃ {₁₊ m} CCX-gate) ≈
  CTRL (gate₃ {₁₊ m} CCX-gate) • CTRL₁ (g ↥ ↥)
pass-CCX (gate₀ ())
pass-CCX (gate₁ {j} h) = coreC 0 (PB.axiom (comm₃ CCX-gate (gate₁ {0} h))) tt j
pass-CCX (gate₂ {j} h) = coreC 1 (PB.axiom (comm₃ CCX-gate (gate₂ {0} h))) tt j
pass-CCX (gate₃ {j} h) = coreC 2 (PB.axiom (comm₃ CCX-gate (gate₃ {0} h))) tt j
pass-CCX (gate₀ () ↥)
pass-CCX (gate₁ {j} h ↥) = coreC 1 (PB.axiom (comm₃ CCX-gate (gate₁ {0} h ↥))) tt j
pass-CCX (gate₂ {j} h ↥) = coreC 2 (PB.axiom (comm₃ CCX-gate (gate₂ {0} h ↥))) tt j
pass-CCX (gate₃ {j} h ↥) = coreC 3 (PB.axiom (comm₃ CCX-gate (gate₃ {0} h ↥))) tt j
pass-CCX (g ↥ ↥) =
  PB.trans (PB.cong (move (g ↥ ↥ ↥)) PB.refl)
  (PB.trans (conj-pass (apart₅ B₀ (Z g)) (top-cong (pass-CCX (g ↥))) (apart₅ B₀ (Z⁻ g)))
    (PB.cong PB.refl (PB.sym (move (g ↥ ↥ ↥)))))
  where
  B₀ = CTRL (gate₃ {1} CCX-gate)

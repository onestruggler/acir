------------------------------------------------------------------------
-- Presentations of groups
--
-- A controlled gate one wire higher is the controlled gate with an
-- idle wire on top, conjugated by the cycle of all the wires above the
-- spare.
--
-- CTRL₁ (g ↥) conjugates CTRL₁ g ↑ by the swaps L of wires 0 1 2, and
-- CTRL₁ g ↑ is CTRL₁ g ⇓ conjugated by the cycle of all the wires
-- (Cycle.nat).  That cycle is L⁻¹ followed by the cycle K of the wires
-- from 2 up, so the swaps cancel and CTRL₁ (g ↥) is CTRL₁ g ⇓
-- conjugated by K (`fullmove`), for every g and with no closed base.
-- The same holds for a bare gate two wires up (`barefull`).  Unlike
-- CtrlMove.move, K moves every wire above the spare, which is what two
-- controlled gates high up need: both move by the same K.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.FullMove where

open import Data.Nat.Base using (ℕ)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Syntactics
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (CTRL₁)
import Examples.Groups.Symmetric-Prop.Cycle as Cycle

private
  variable
    n : ℕ

  no-scalar : ∀ {n} (h h′ : Gate 0) →
    n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ
  no-scalar ()

  module CY = Cycle Gate SW-gate _NP,_===_

-- The cycle of all the wires, and its inverse (Cycle's, named here so
-- that clients instantiating Cycle with other rules use the same words).
cy cy⁻ : (n : ℕ) → Circuit (₁₊ n)
cy  = CY.cyc
cy⁻ = CY.cyc⁻

-- The cycle of the wires from 2 up, and its inverse.
K K⁻ : (n : ℕ) → Circuit (₃₊ n)
K  n = cy n ↑ ↑
K⁻ n = cy⁻ n ↑ ↑

K⁻K : (n : ℕ) → (₃₊ n) ⊢ K⁻ n • K n ≈ ε
K⁻K n = lemma-cong↑ (CY.cyc⁻ n ↑ • CY.cyc n ↑) ε
  (lemma-cong↑ (CY.cyc⁻ n • CY.cyc n) ε (CY.cyc⁻-cyc n))

KK⁻ : (n : ℕ) → (₃₊ n) ⊢ K n • K⁻ n ≈ ε
KK⁻ n = lemma-cong↑ (CY.cyc n ↑ • CY.cyc⁻ n ↑) ε
  (lemma-cong↑ (CY.cyc n • CY.cyc⁻ n) ε (CY.cyc-cyc⁻ n))

-- A circuit one wire up is the circuit with an idle wire on top,
-- placed by the cycle of all the wires.
up-place : (w : Circuit n) → (₁₊ n) ⊢ w ↑ ≈ CY.cyc n • (w ⇓ • CY.cyc⁻ n)
up-place {n} w =
  PB.trans (PB.sym PB.right-unit)
  (PB.trans (PB.cong PB.refl (PB.sym (CY.cyc-cyc⁻ n)))
  (PB.trans (PB.sym PB.assoc)
  (PB.trans (PB.cong (CY.nat no-scalar w) PB.refl)
    PB.assoc)))

private
  σσ : (₂₊ n) ⊢ σ • σ ≈ ε
  σσ = PB.axiom (srel (σrel σ-inv))

  -- The swaps of wires 0 1 2 and their inverse cancel.
  LL⁻ : (₃₊ n) ⊢ (σ ↑ • σ) • (σ • σ ↑) ≈ ε
  LL⁻ = PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
    (PB.trans (PB.cong PB.refl (PB.cong σσ PB.refl))
    (PB.trans (PB.cong PB.refl PB.left-unit)
      (lemma-cong↑ (σ • σ) ε σσ))))

  sandwich : ∀ {L L⁻ Kc A Kc⁻ : Circuit n} → n ⊢ L • L⁻ ≈ ε →
    n ⊢ L • (((L⁻ • Kc) • (A • (Kc⁻ • L))) • L⁻) ≈ Kc • (A • Kc⁻)
  sandwich e =
    PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong e PB.refl)
    (PB.trans PB.left-unit
    (PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.assoc))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong PB.refl e)))
      (PB.cong PB.refl (PB.cong PB.refl PB.right-unit)))))))))

-- A controlled gate one wire higher.
fullmove : (g : Gen n) → (₃₊ n) ⊢ CTRL₁ (g ↥) ≈ K n • (CTRL₁ g ⇓ • K⁻ n)
fullmove {n} g =
  PB.trans (PB.cong PB.refl (PB.cong (up-place (CTRL₁ g)) PB.refl))
  (PB.trans (PB.cong PB.refl (PB.cong
     (PB.cong (PB.sym PB.assoc) (PB.cong PB.refl PB.assoc)) PB.refl))
    (sandwich LL⁻))

-- A bare gate two wires up, one wire higher.
barefull : (g : Gen n) → (₃₊ n) ⊢ [ g ↥ ↥ ↥ ]ʷ ≈ K n • ([ g ↥ ↥ ]ʷ ⇓ • K⁻ n)
barefull g = lemma-cong↑ ([ g ]ʷ ↑ ↑) _ (lemma-cong↑ ([ g ]ʷ ↑) _ (up-place [ g ]ʷ))

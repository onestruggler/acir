------------------------------------------------------------------------
-- Presentations of groups
--
-- At p = 5 with g = 2, M-power is independent of the other Paper-V1
-- rules
--
-- The witness weighs letters in the additive group ℤ/5ℤ: H weighs 3
-- and S weighs 1.  It is commutative, so comm-HHSHHS holds, and the
-- other one-wire rules balance:
--
--   order-S   S ^ 5 weighs 5 ≡ 0;
--   order-H   H ^ 2 weighs 6 and XM₋₁ (23 H, 37 S) weighs 106, both
--             ≡ 1;
--   semi-MR   its sides differ by (g − 1)·(2g, g + 1) in their H and S
--             counts, mod 5, so by (g − 1)(7g + 1) in weight, which
--             vanishes at g = 2.
--
-- M-power fails at k = 0: XMg ^ 0 is ε, while XM 1 is (S • H) ^ 3,
-- which weighs 12 ≡ 2.  This is the rule that makes (S • H) ^ 3 = ε a
-- theorem of Paper-V1, which the other one-wire rules do not prove.
--
-- The weights cannot be kept from width 2 on (order-Ex and blake-c12
-- fail in them), so the model is ℤ/5ℤ at width 1 and the trivial
-- monoid from width 2.  That suffices for an instance at width 1: a
-- derivation there involves only one-wire instances, every
-- multi-wire rule starting at width 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qupit.Independence.MPower where

open import Algebra.Bundles using (Monoid ; Ring)
import Algebra.Construct.Terminal as Terminal
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; suc)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Notations
open import Word.Base using (Word)
open import ForStdlib.Data.Fin.Mod using (ℤ ; +-*-ring)

open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Parameters
  using (prime-5 ; root-5 ; root-5-gen)
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  2 prime-5 root-5 root-5-gen as Pap
open Pap using (H-gate ; S-gate ; Gen ; gate₀ ; gate₁ ; gate₂ ; _↥)
open Pap.Clifford-Relations using (module Base ; srel)
open Base using (_SRel,_===_)
open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Selection
  2 prime-5 root-5 root-5-gen
  using (M-power ; Without ; _IndependentOf_ ; module Soundness)

private
  variable
    n : ℕ
    w v : Word (Gen n)

------------------------------------------------------------------------
-- ℤ/5ℤ at width ≤ 1, the trivial monoid from width 2

private
  module ℤ₅ = Ring (+-*-ring 3)

mon : ℕ → Monoid 0ℓ 0ℓ
mon 0          = ℤ₅.+-monoid
mon 1          = ℤ₅.+-monoid
mon (suc (suc _)) = Terminal.monoid

private
  C : ℕ → Set
  C n = Monoid.Carrier (mon n)

  infix 4 _⊢_≈_
  _⊢_≈_ : ∀ n → C n → C n → Set
  n ⊢ x ≈ y = Monoid._≈_ (mon n) x y

  _⊢_∙_ : ∀ n → C n → C n → C n
  n ⊢ x ∙ y = Monoid._∙_ (mon n) x y

-- The weight of a generator, read at width n.
weight : Gen n → ℤ 5
weight (gate₀ ())
weight (gate₁ H-gate) = ₃
weight (gate₁ S-gate) = ₁
weight (gate₂ _)      = ₀
weight (g ↥)          = weight g

emb : ∀ n → ℤ 5 → C n
emb 0             x = x
emb 1             x = x
emb (suc (suc _)) _ = _

⟦_⟧₀ : Gen n → C n
⟦_⟧₀ {n} g = emb n (weight g)

σ : C n → C (suc n)
σ {0}     x = x
σ {suc _} _ = _

σ-hom : MonoidMorphisms.IsMonoidHomomorphism
          (Monoid.rawMonoid (mon n)) (Monoid.rawMonoid (mon (suc n))) (σ {n})
σ-hom {0} = record
  { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → e }
      ; homo = λ _ _ → refl }
  ; ε-homo = refl }
σ-hom {suc _} = record
  { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ _ → _ }
      ; homo = λ _ _ → _ }
  ; ε-homo = _ }

⟦↥⟧ : (g : Gen n) → suc n ⊢ ⟦ g ↥ ⟧₀ ≈ σ {n} ⟦ g ⟧₀
⟦↥⟧ {0}     _ = refl
⟦↥⟧ {suc _} _ = _

comm : ∀ n (x y : C n) → n ⊢ (n ⊢ x ∙ y) ≈ (n ⊢ y ∙ x)
comm 0             = ℤ₅.+-comm
comm 1             = ℤ₅.+-comm
comm (suc (suc _)) _ _ = _

------------------------------------------------------------------------
-- Soundness for every rule but M-power, and the theorem

open Soundness M-power mon ⟦_⟧₀

sound-srel : (s : n SRel, w === v) → Without M-power (srel s) →
             n ⊢ ⟦ w ⟧ ≈ ⟦ v ⟧
sound-srel {0} () _
sound-srel {1} Base.order-S       _  = refl
sound-srel {1} Base.order-H       _  = refl
sound-srel {1} (Base.M-power _)   ¬u = ⊥-elim (¬u refl)
sound-srel {1} Base.semi-MR       _  = refl
sound-srel {1} Base.comm-HHSHHS   _  = refl
sound-srel {suc (suc _)} _        _  = _

open Shift (λ {n} → σ {n}) (λ {n} → σ-hom {n}) (λ {n} → ⟦↥⟧ {n})
open Rules sound-srel sound-cong↑
  (λ {n} h g _ → comm (suc n) ⟦ g ↥ ⟧₀ ⟦ gate₁ {n = n} h ⟧₀)
  (λ {n} h g _ → comm (suc (suc n)) ⟦ g ↥ ↥ ⟧₀ ⟦ gate₂ {n = n} h ⟧₀)
  (λ ())
  public

-- At width 1, M-power at k = 0 says ε = (S • H) ^ 3, of weights 0
-- and 2.
M-power-independent : srel (Base.M-power {0} ₀) IndependentOf M-power
M-power-independent = independent (srel (Base.M-power ₀)) λ ()

------------------------------------------------------------------------
-- Presentations of groups
--
-- The four-wire rule is independent of the three-qubit rules: the CS
-- parity
--
-- The number of CS gates mod 2 is invariant under every rule of
-- Syntactics but cx-ccz — each has an even difference of CS gates
-- between its sides — and under the structural rules; on three qubits
-- it is the determinant, which is why it survives completeness there.
-- On four qubits every generator has determinant 1 and the parity is
-- no longer semantic: cx-ccz, a CNOT carrying a CCZ on its target to
-- the product of two CCZs (the phase polynomial (−1)^{x₀x₁(x₂⊕x₃)}),
-- has 25 CS gates on one side and 54 on the other.  So the three-qubit
-- rules are not complete on four qubits, cx-ccz is not derivable from
-- them, and any complete rule set has a rule with an odd difference of
-- CS gates — of which cx-ccz is the shortest (scratchpad/parity.py).
--
-- The model is Circuit.Independence's soundness engine at the
-- selection of the instances not using cx-ccz, with ℤ/2 as Bool under
-- xor.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Parity where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-assoc ; xor-identityˡ ; xor-identityʳ ; xor-comm)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Unit using (⊤ ; tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Presentation.Independence using (Independent)
import Circuit.Independence

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.SemanticSteps using (same-sem)

------------------------------------------------------------------------
-- The model: ℤ/2, counting CS gates

xor-monoid : Monoid 0ℓ 0ℓ
xor-monoid = record
  { Carrier = Bool
  ; _≈_     = _≡_
  ; _∙_     = _xor_
  ; ε       = false
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record { isEquivalence = Eq.isEquivalence ; ∙-cong = Eq.cong₂ _xor_ }
      ; assoc   = xor-assoc }
    ; identity = xor-identityˡ , xor-identityʳ } }

-- Whether a generator is CS.
cs : ∀ {n} → Gen n → Bool
cs (gate₀ _)       = false
cs (gate₁ _)       = false
cs (gate₂ CS-gate) = true
cs (g ↥)           = cs g

-- The axiom instances not using the four-wire rule.
noΔ : ∀ {n} {w v : Circuit n} → n VRel, w === v → Set
noΔ (srel cx-ccz) = ⊥
noΔ (srel _)      = ⊤
noΔ (cong↑ a)     = noΔ a
noΔ (comm₁ _ _)   = ⊤
noΔ (comm₂ _ _)   = ⊤
noΔ (ω↑=ω _)      = ⊤

private
  module CI = Circuit.Independence Gate
  open CI.Structural _SRel,_===_ using (module Soundness)
  open Soundness (λ {n} → noΔ {n}) (λ p → p) (λ _ → xor-monoid) cs
    renaming (⟦_⟧ to par)

  -- Shifting a circuit up does not change its count.
  id-hom : MonoidMorphisms.IsMonoidHomomorphism
             (Monoid.rawMonoid xor-monoid) (Monoid.rawMonoid xor-monoid) (λ b → b)
  id-hom = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → e }
      ; homo = λ _ _ → Eq.refl }
    ; ε-homo = Eq.refl }

  open Shift (λ b → b) id-hom (λ g → Eq.refl) using (sound-cong↑)

  -- Every three-qubit rule has an even difference of CS gates; the
  -- four-wire rule is not selected.
  sound-srel : ∀ {n} {w v : Circuit n} (s : n SRel, w === v) → noΔ (srel s) → par w ≡ par v
  sound-srel order-I     _ = Eq.refl
  sound-srel order-S     _ = Eq.refl
  sound-srel order-K     _ = Eq.refl
  sound-srel order-SK    _ = Eq.refl
  sound-srel order-CS    _ = Eq.refl
  sound-srel comm-CS-S₀  _ = Eq.refl
  sound-srel comm-CS-S₁  _ = Eq.refl
  sound-srel X-CS₀       _ = Eq.refl
  sound-srel X-CS₁       _ = Eq.refl
  sound-srel CS-K₀       _ = Eq.refl
  sound-srel CS-K₁       _ = Eq.refl
  sound-srel comm-CS↑-CS _ = Eq.refl
  sound-srel rel-266     _ = Eq.refl
  sound-srel rel-267     _ = Eq.refl
  sound-srel rel-268     _ = Eq.refl
  sound-srel rel-269     _ = Eq.refl
  sound-srel rel-272     _ = Eq.refl
  sound-srel cx-ccz      p = ⊥-elim p

  open Rules sound-srel sound-cong↑
    (λ h g _ → xor-identityʳ (cs g))
    (λ h g _ → xor-comm (cs g) (cs (gate₂ h)))
    (λ ω _ → Eq.refl)
    using (independent)

------------------------------------------------------------------------
-- The four-wire rule is independent, and the three-qubit rules
-- incomplete on four qubits

-- The two sides of cx-ccz: CX₃₂ • CCZ₀₁₂ • CX₃₂ and CCZ₀₁₂ • CCZ₀₁₃.
Δˡ Δʳ : Circuit 4
Δˡ = CX₁₀ ↑ ↑ • CCZ • CX₁₀ ↑ ↑
Δʳ = CCZ • Swap ↑ ↑ • CCZ • Swap ↑ ↑

-- They denote the same matrix (also Soundness, through the rule).
Δ-sound : ⟦ Δˡ ⟧ ~ ⟦ Δʳ ⟧
Δ-sound = same-sem Δˡ Δʳ Eq.refl

-- Their CS parities differ, so the other rules do not relate them: the
-- rule is independent of them.
cx-ccz-independent : Independent (4 VRel,_===_) noΔ (srel cx-ccz)
cx-ccz-independent = independent (srel cx-ccz) true≢false
  where
  true≢false : true ≢ false
  true≢false ()

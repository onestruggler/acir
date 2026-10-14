------------------------------------------------------------------------
-- Presentations of groups
--
-- The three-qubit rules are incomplete at four qubits: the CS parity
--
-- The number of CS gates mod 2 is invariant under every rule of
-- Syntactics — each has an even difference of CS gates between its
-- sides — and under the structural rules; on three qubits it is the
-- determinant, which is why it survives completeness there.  On four
-- qubits every generator has determinant 1 and the parity is no longer
-- semantic: a CNOT carries a CCZ on its target to the product of two
-- CCZs,
--
--     CX₃₂ • CCZ₀₁₂ • CX₃₂  =  CCZ₀₁₂ • CCZ₀₁₃
--
-- (the phase polynomial (−1)^{x₀x₁(x₂⊕x₃)}), with 25 CS gates on one
-- side and 54 on the other.  So that true equation is underivable, the
-- rules of Syntactics are not complete on four qubits, and any complete
-- rule set has a rule with an odd difference of CS gates — of which
-- this equation is the shortest (scratchpad/parity.py).
--
-- The model is Circuit.Independence's soundness engine at the
-- selection of every axiom, with the monoid ℤ/2 as Bool under xor.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Parity where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-assoc ; xor-identityˡ ; xor-identityʳ ; xor-comm)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax ; _×_ ; _,_)
open import Data.Unit using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Negation using (¬_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Presentation.Independence using (all ; ≈-all)
import Circuit.Independence

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.MultiControlled using (CCZ)
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

private
  module CI = Circuit.Independence Gate
  open CI.Structural _SRel,_===_ using (module Soundness)
  open Soundness (λ {n} → all (n VRel,_===_)) (λ _ → tt) (λ _ → xor-monoid) cs
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

  -- Every rule has an even difference of CS gates.
  sound-srel : ∀ {n} {w v : Circuit n} (s : n SRel, w === v) →
               all (n VRel,_===_) (srel s) → par w ≡ par v
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

  open Rules sound-srel sound-cong↑
    (λ h g _ → xor-identityʳ (cs g))
    (λ h g _ → xor-comm (cs g) (cs (gate₂ h)))
    (λ ω _ → Eq.refl)
    using (sound)

-- The parity of CS gates is invariant under the congruence.
parity : ∀ {n} {w v : Circuit n} → n ⊢ w ≈ v → par w ≡ par v
parity {n} e = sound (≈-all (n VRel,_===_) e)

------------------------------------------------------------------------
-- A true equation with an odd difference

-- CX₃₂ • CCZ₀₁₂ • CX₃₂ and CCZ₀₁₂ • CCZ₀₁₃, on four wires.
Δˡ Δʳ : Circuit 4
Δˡ = CX₁₀ ↑ ↑ • CCZ • CX₁₀ ↑ ↑
Δʳ = CCZ • Swap ↑ ↑ • CCZ • Swap ↑ ↑

-- They denote the same matrix.
Δ-sound : ⟦ Δˡ ⟧ ~ ⟦ Δʳ ⟧
Δ-sound = same-sem Δˡ Δʳ Eq.refl

-- But their CS parities differ, so no derivation relates them.
Δ-underivable : ¬ (4 ⊢ Δˡ ≈ Δʳ)
Δ-underivable e = true≢false (parity e)
  where
  true≢false : true ≢ false
  true≢false ()

-- The rules of Syntactics are not complete on four qubits.
incomplete₄ : Σ[ w ∈ Circuit 4 ] Σ[ v ∈ Circuit 4 ] (⟦ w ⟧ ~ ⟦ v ⟧) × ¬ (4 ⊢ w ≈ v)
incomplete₄ = Δˡ , Δʳ , Δ-sound , Δ-underivable

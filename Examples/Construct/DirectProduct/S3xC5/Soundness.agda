------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the direct-product presentation S₃ × C₅: the raw
-- relation _===_ preserves the denotation ⟦_⟧ : Word Y → S₃ × C₅ into
-- the product group.  A left-embedded word acts as the tight
-- permutation of its S₃ part and fixes the C₅ coordinate at ₀; a
-- right-embedded word acts as the identity permutation and contributes
-- its C₅ residue; the mixed axiom is the commutation of the two.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)

open import Algebra.Bundles using (Group)
open import Function.Definitions using (Congruent)

open import Notations using (₀ ; ₃)
open import Word.Base using (Word ; _•_ ; [_]ʷ ; ε)
open import Presentation.Construct.Base
  using ([_]ₗ ; [_]ᵣ ; left ; right ; mid ; comm)
import Presentation.Base as PB

module Examples.Construct.DirectProduct.S3xC5.Soundness where

open import Examples.Construct.DirectProduct.S3xC5.Syntactics using (_===_)
open import Examples.Construct.DirectProduct.S3xC5.Semantic

open import Examples.Groups.Symmetric.Syntactics using (Gen)
import Examples.Groups.Symmetric.Tight.Semantics as TS
import Examples.Groups.Symmetric.Tight.Soundness as TSnd
open import Examples.Groups.Cyclic.Normalization using (X)
import Examples.Groups.Cyclic.Semantics as CS
import Examples.Groups.Cyclic.Soundness as CSnd
open import Zp.ModularArithmetic using (_+_ ; +-identityˡ ; +-identityʳ)

------------------------------------------------------------------------
-- Componentwise denotation of embedded words

-- A left-embedded word denotes the tight permutation of the underlying
-- S₃ word in its first coordinate…
π₁ₗ : ∀ (u : Word (Gen ₃)) k → proj₁ ⟦ [ u ]ₗ ⟧ ⟨$⟩ʳ k ≡ TS.⟦ u ⟧ ⟨$⟩ʳ k
π₁ₗ [ x ]ʷ  k = refl
π₁ₗ ε       k = refl
π₁ₗ (u • v) k =
  trans (cong (proj₁ ⟦ [ v ]ₗ ⟧ ⟨$⟩ʳ_) (π₁ₗ u k)) (π₁ₗ v (TS.⟦ u ⟧ ⟨$⟩ʳ k))

-- …and fixes the C₅ coordinate at ₀.
π₂ₗ : ∀ (u : Word (Gen ₃)) → proj₂ ⟦ [ u ]ₗ ⟧ ≡ ₀
π₂ₗ [ x ]ʷ  = refl
π₂ₗ ε       = refl
π₂ₗ (u • v) = trans (cong₂ _+_ (π₂ₗ u) (π₂ₗ v)) (+-identityˡ ₀)

-- A right-embedded word denotes the identity permutation in its first
-- coordinate…
π₁ᵣ : ∀ (u : Word X) k → proj₁ ⟦ [ u ]ᵣ ⟧ ⟨$⟩ʳ k ≡ k
π₁ᵣ [ x ]ʷ  k = refl
π₁ᵣ ε       k = refl
π₁ᵣ (u • v) k = trans (cong (proj₁ ⟦ [ v ]ᵣ ⟧ ⟨$⟩ʳ_) (π₁ᵣ u k)) (π₁ᵣ v k)

-- …and denotes the cyclic residue of the word in its C₅ coordinate.
π₂ᵣ : ∀ (u : Word X) → proj₂ ⟦ [ u ]ᵣ ⟧ ≡ CS.⟦_⟧ {5} u
π₂ᵣ [ x ]ʷ  = refl
π₂ᵣ ε       = refl
π₂ᵣ (u • v) = cong₂ _+_ (π₂ᵣ u) (π₂ᵣ v)

------------------------------------------------------------------------
-- Soundness of the raw relation _===_

soundness-ax : Congruent _===_ (Setoid._≈_ (Group.setoid S₃×C₅-group)) ⟦_⟧
soundness-ax (left {u} {v} p) =
    (λ k → trans (π₁ₗ u k) (trans (TSnd.sound-ax p k) (sym (π₁ₗ v k))))
  , trans (π₂ₗ u) (sym (π₂ₗ v))
soundness-ax (right {u} {v} p) =
    (λ k → trans (π₁ᵣ u k) (sym (π₁ᵣ v k)))
  , trans (π₂ᵣ u) (trans (CSnd.sound {5} (PB.axiom p)) (sym (π₂ᵣ v)))
soundness-ax (mid (comm a b)) =
    (λ k → refl)
  , trans (+-identityˡ (CS.⟦_⟧₀ {5} b)) (sym (+-identityʳ (CS.⟦_⟧₀ {5} b)))

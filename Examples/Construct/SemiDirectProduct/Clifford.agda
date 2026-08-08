------------------------------------------------------------------------
-- Presentations of groups
--
-- The (affine) Clifford group as a semidirect product
--
--   Pauli n ⋊ Sp(2n, ℤ/pℤ).
--
-- The Pauli group Pauli n (Examples.Groups.Pauli.Semantics) carries the
-- linear action of the symplectic group Sp(2n, ℤ/pℤ)
-- (Examples.Groups.Symplectic.Semantics): a symplectic transformation S
-- acts on a Pauli by its underlying linear map `ap S`.  For a Clifford
-- circuit word w this action is exactly `act w` (Action.agda).  The
-- resulting semidirect product Pauli n ⋊ Sp(2n, ℤ/pℤ) is the (affine)
-- Clifford group.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Construct.SemiDirectProduct.Clifford (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Algebra.Bundles using (Group)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; module ≡-Reasoning)

open import ForStdlib.Algebra.Construct.SemiDirectProduct as SDP using (Action)

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using (Pauli ; _+ₚ_ ; pIₙ ; -ₚ_ ; +ₚ-group ; +ₚ-assoc ; +ₚ-identityˡ ; +ₚ-inverseˡ)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; _≈ˢ_ ; εˢ ; _∘ˢ_ ; Sp-group)
open Symplectic

------------------------------------------------------------------------
-- The action preserves the identity
--
-- A linear map sends 0 to 0: ap S pIₙ ≡ pIₙ.  (From ap S x ≡ ap S x +ₚ
-- ap S x at x = pIₙ, cancelled in the Pauli additive group.)

ap-ε : ∀ {n} (S : Symplectic n) → ap S pIₙ ≡ pIₙ
ap-ε {n} S = begin
  x                ≡⟨ Eq.sym (+ₚ-identityˡ x) ⟩
  pIₙ +ₚ x         ≡⟨ Eq.cong (_+ₚ x) (Eq.sym (+ₚ-inverseˡ x)) ⟩
  (-ₚ x +ₚ x) +ₚ x ≡⟨ +ₚ-assoc (-ₚ x) x x ⟩
  -ₚ x +ₚ (x +ₚ x) ≡⟨ Eq.cong (-ₚ x +ₚ_) (Eq.sym hxx) ⟩
  -ₚ x +ₚ x        ≡⟨ +ₚ-inverseˡ x ⟩
  pIₙ              ∎
  where
  open ≡-Reasoning
  x = ap S pIₙ
  hxx : x ≡ x +ₚ x
  hxx = Eq.trans (Eq.cong (ap S) (Eq.sym (+ₚ-identityˡ pIₙ))) (linear-+ S pIₙ pIₙ)

-- Two agreeing transformations act equally.
act-cong-ap : ∀ {n} {S T : Symplectic n} {p q : Pauli n} → S ≈ˢ T → p ≡ q → ap S p ≡ ap T q
act-cong-ap {p = p} S≈T Eq.refl = S≈T p

------------------------------------------------------------------------
-- The semidirect product Pauli n ⋊ Sp(2n, ℤ/pℤ)

module _ (n : ℕ) where

  -- The symplectic group acts on the Pauli group by its linear action.
  φ : Action (Group.rawMonoid (+ₚ-group n)) (Group.rawMonoid (Sp-group n))
  φ = record
    { act          = ap
    ; act-cong     = λ {S} {T} {p} {q} → act-cong-ap {n} {S} {T} {p} {q}
    ; act-ε-homo   = ap-ε
    ; act-∙-homo   = linear-+
    ; act-identity = λ _ → Eq.refl
    ; act-compose  = λ _ _ _ → Eq.refl
    }

  Pauli⋊Sp-group : Group 0ℓ 0ℓ
  Pauli⋊Sp-group = SDP.group (+ₚ-group n) (Sp-group n) φ

------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled functor λ¹₄ and transport on five wires
--
-- λ¹₄ (the joint paper's controlled functor with control wire 4 and
-- domain wires 0 1 2 3) is letterwise: the scalar to S on wire 4, S and K
-- on a wire v to CS(v, 4) and the K on v controlled by 4, and CS on the
-- wires v, v + 1 to the doubly controlled S Σ(v; 4, v + 1 | u, A), its
-- borrowed wires u < A the other two domain wires (an S-box of
-- Five.Letters).  A four-wire circuit goes to a line of macro letters.
--
-- Transport: if every axiom instance of the four-wire theory is carried
-- to an equation of the five-wire theory (`AxOk`), so is every
-- derivation.  The instances are finitely many; Five.TransportAx gives
-- each its equation, from the joint paper's items F1, F2, F0 and windows.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Transport where

open import Data.List using (List ; [] ; _∷_ ; _++_)
open import Data.List.Properties using (++-assoc ; ++-identityʳ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Syntactics as Syn using (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁)

------------------------------------------------------------------------
-- The functor

λᵍ : Gen 4 → List Mac
λᵍ g = λ₁ g ∷ []

λʷ : Circuit 4 → List Mac
λʷ [ g ]ʷ   = λᵍ g
λʷ ε        = []
λʷ (u • v)  = λʷ u ++ λʷ v

------------------------------------------------------------------------
-- Transport

AxOk : Set
AxOk = ∀ {w v} → 4 VRel, w === v → ⟪ λʷ w ⟫ʷ ≈ ⟪ λʷ v ⟫ʷ

private
  refl≡ : ∀ {xs ys : List Mac} → xs ≡ ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
  refl≡ Eq.refl = refl

transport : AxOk → ∀ {u v} → 4 ⊢ u ≈ v → ⟪ λʷ u ⟫ʷ ≈ ⟪ λʷ v ⟫ʷ
transport ok PB.refl         = refl
transport ok (PB.sym e)      = sym (transport ok e)
transport ok (PB.trans e f)  = trans (transport ok e) (transport ok f)
transport ok (PB.cong {w} {w′} {v} {v′} e f) =
  trans (⟪⟫-++ (λʷ w) (λʷ v))
    (trans (cong (transport ok e) (transport ok f)) (sym (⟪⟫-++ (λʷ w′) (λʷ v′))))
transport ok (PB.assoc {w} {v} {u}) = refl≡ (++-assoc (λʷ w) (λʷ v) (λʷ u))
transport ok PB.left-unit    = refl
transport ok (PB.right-unit {w}) = refl≡ (++-identityʳ (λʷ w))
transport ok (PB.axiom a)    = ok a

------------------------------------------------------------------------
-- Presentations of groups
--
-- The five base commutations, and the relation calculus of the
-- controlled matchings
--
-- CRel's Calculus needs Ḡ to commute with the frame of G by each base
-- word of CLabels: Fr G (baseW k) is Q G Q⁻¹ for the three-wire circuit
-- Q = baseQ k (a three-wire identity for each side), and the
-- commutation is a three-wire identity for the first two base types
-- (on wires 0, 3 and on wires 0, 1, 3) and BaseComm's derivations for
-- the other three.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.CBC where

open import Data.Bool.Base using (true)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; reverse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (_•_)
import Presentation.Base as PB
import Presentation.Properties as PP

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (eqF ; eqF-sound)
open import Examples.Groups.XCXCCX-4bit.Placed
  using (PG ; Xᵖ ; CXᵖ ; CCXᵖ ; Wire ; ι ; ι* ; every ; avoids ; ⟦_⟧ᵖ*)
open import Examples.Groups.XCXCCX-4bit.ToPlaced using (pg ; pg-ok ; ι*-++)
open import Examples.Groups.XCXCCX-4bit.Narrow3 using (narrowᵖ)
open import Examples.Groups.XCXCCX-4bit.PlacedEngine using (Eqnᵖ ; lhs⁼ ; rhs⁼ ; prf)
open import Examples.Groups.XCXCCX-4bit.PFrames using (Pc ; Fr ; inv)
open import Examples.Groups.XCXCCX-4bit.CBase using (Comm ; G ; Ḡ)
open import Examples.Groups.XCXCCX-4bit.CLabels using (baseQ ; baseW)
open import Examples.Groups.XCXCCX-4bit.BaseComm using (BC211⁼ ; BC31⁼ ; BC4⁼)
import Examples.Groups.XCXCCX-4bit.CRel as CRel

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong)
open PP (4 VRel,_===_) using (by-assoc)

private
  -- An identity of placed words on three wires.
  nar : (m : Wire) (u v : List PG) → every (avoids m) u ≡ true → every (avoids m) v ≡ true →
        eqF 4 ⟦ u ⟧ᵖ* ⟦ v ⟧ᵖ* ≡ true → 4 ⊢ ι* u ≈ ι* v
  nar m u v hu hv hs = narrowᵖ m u v hu hv (eqF-sound 4 _ _ hs)

  -- Ḡ as placed letters.
  Ḡl : List PG
  Ḡl = Xᵖ ₃ ∷ CXᵖ ₃ ₀ ∷ Xᵖ ₃ ∷ []

  -- The frame of G by a base word, as placed letters.
  Frl : Fin 5 → List PG
  Frl k = baseQ k ++ CXᵖ ₃ ₀ ∷ reverse (baseQ k)

  -- The circuit of a base word is its base circuit, and the circuit of
  -- the inverse word the base circuit reversed (three-wire identities).
  pcQ : (k : Fin 5) → 4 ⊢ Pc 0 (baseW k) ≈ ι* (baseQ k)
  pcQ k = trans (pg-ok (Pc 0 (baseW k))) (nar ₃ (pg (Pc 0 (baseW k))) (baseQ k) (h₁ k) (h₂ k) (h₃ k))
    where
    h₁ : (k : Fin 5) → every (avoids ₃) (pg (Pc 0 (baseW k))) ≡ true
    h₁ ₀ = Eq.refl
    h₁ ₁ = Eq.refl
    h₁ ₂ = Eq.refl
    h₁ ₃ = Eq.refl
    h₁ ₄ = Eq.refl
    h₂ : (k : Fin 5) → every (avoids ₃) (baseQ k) ≡ true
    h₂ ₀ = Eq.refl
    h₂ ₁ = Eq.refl
    h₂ ₂ = Eq.refl
    h₂ ₃ = Eq.refl
    h₂ ₄ = Eq.refl
    h₃ : (k : Fin 5) → eqF 4 ⟦ pg (Pc 0 (baseW k)) ⟧ᵖ* ⟦ baseQ k ⟧ᵖ* ≡ true
    h₃ ₀ = Eq.refl
    h₃ ₁ = Eq.refl
    h₃ ₂ = Eq.refl
    h₃ ₃ = Eq.refl
    h₃ ₄ = Eq.refl

  pcQ⁻ : (k : Fin 5) → 4 ⊢ Pc 0 (inv (baseW k)) ≈ ι* (reverse (baseQ k))
  pcQ⁻ k = trans (pg-ok (Pc 0 (inv (baseW k))))
                 (nar ₃ (pg (Pc 0 (inv (baseW k)))) (reverse (baseQ k)) (h₁ k) (h₂ k) (h₃ k))
    where
    h₁ : (k : Fin 5) → every (avoids ₃) (pg (Pc 0 (inv (baseW k)))) ≡ true
    h₁ ₀ = Eq.refl
    h₁ ₁ = Eq.refl
    h₁ ₂ = Eq.refl
    h₁ ₃ = Eq.refl
    h₁ ₄ = Eq.refl
    h₂ : (k : Fin 5) → every (avoids ₃) (reverse (baseQ k)) ≡ true
    h₂ ₀ = Eq.refl
    h₂ ₁ = Eq.refl
    h₂ ₂ = Eq.refl
    h₂ ₃ = Eq.refl
    h₂ ₄ = Eq.refl
    h₃ : (k : Fin 5) → eqF 4 ⟦ pg (Pc 0 (inv (baseW k))) ⟧ᵖ* ⟦ reverse (baseQ k) ⟧ᵖ* ≡ true
    h₃ ₀ = Eq.refl
    h₃ ₁ = Eq.refl
    h₃ ₂ = Eq.refl
    h₃ ₃ = Eq.refl
    h₃ ₄ = Eq.refl

  fr-list : (k : Fin 5) → 4 ⊢ Fr G (baseW k) ≈ ι* (Frl k)
  fr-list k =
    trans (cong (pcQ k) (cong refl (pcQ⁻ k)))
          (sym (ι*-++ (baseQ k) (CXᵖ ₃ ₀ ∷ reverse (baseQ k))))

  Ḡ-list : 4 ⊢ Ḡ ≈ ι* Ḡl
  Ḡ-list = by-assoc Eq.refl

  -- The commutation, as an identity of placed words.
  comm-list : (k : Fin 5) → 4 ⊢ ι* (Ḡl ++ Frl k) ≈ ι* (Frl k ++ Ḡl)
  comm-list ₀ = nar ₁ (Ḡl ++ Frl ₀) (Frl ₀ ++ Ḡl) Eq.refl Eq.refl Eq.refl
  comm-list ₁ = nar ₂ (Ḡl ++ Frl ₁) (Frl ₁ ++ Ḡl) Eq.refl Eq.refl Eq.refl
  comm-list ₂ = prf BC211⁼
  comm-list ₃ = prf BC31⁼
  comm-list ₄ = prf BC4⁼

-- Ḡ commutes with the frame of G by each base word.
base : (k : Fin 5) → Comm Ḡ (Fr G (baseW k))
base k =
  trans (cong Ḡ-list (fr-list k))
    (trans (sym (ι*-++ Ḡl (Frl k)))
      (trans (comm-list k)
        (trans (ι*-++ (Frl k) Ḡl)
          (sym (cong (fr-list k) Ḡ-list)))))

open CRel.Calculus base public

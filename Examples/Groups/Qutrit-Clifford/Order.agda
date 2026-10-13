------------------------------------------------------------------------
-- Presentations of groups
--
-- The order of the qutrit Clifford group
--
-- The Clifford operators on n qutrits are the values that circuits
-- denote, compared exactly: the setoid Clifford-setoid.  By soundness
-- and completeness they correspond to the circuits modulo C₁–C₁₈
-- (clifford≃circuits), hence to the normal forms (circuits≃nf), of which
-- there are 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ − 1) 9ᵏ (Count): there are exactly that
-- many n-qutrit Clifford operators, the count of the paper's Section 3.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Order where

open import Algebra.Bundles using (Monoid)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (Inverse)
import Function.Construct.Composition as Compose
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Reasoning using (module Width)
open import Examples.Groups.Qutrit-Clifford.Semantics using (⟦_⟧ ; monoid)
open import Examples.Groups.Qutrit-Clifford.NormalForm using (NF ; ⟦_⟧ⁿ)
open import Examples.Groups.Qutrit-Clifford.Normalise using (normalise ; normalise-ok)
open import Examples.Groups.Qutrit-Clifford.Rels using (rels)
open import Examples.Groups.Qutrit-Clifford.Box1 using (br₁)
open import Examples.Groups.Qutrit-Clifford.Box2 using (br₂)
open import Examples.Groups.Qutrit-Clifford.Box3 using (br₃)
open import Examples.Groups.Qutrit-Clifford.Soundness using (sound)
open import Examples.Groups.Qutrit-Clifford.Completeness using (nf-injective)
open import Examples.Groups.Qutrit-Clifford.CompletenessN using (complete)
open import Examples.Groups.Qutrit-Clifford.Count using (order ; NF≅order)

private
  variable
    n : ℕ

  module V {n : ℕ} = Monoid (monoid n)

  -- Equality of values, with every implicit given.
  _≋_ : Circuit n → Circuit n → Set
  _≋_ {n} w v = V._≈_ {n} ⟦ w ⟧ ⟦ v ⟧

  ≋-refl : (w : Circuit n) → w ≋ w
  ≋-refl {n} w = V.refl {n} {⟦ w ⟧}

  ≋-sym : (w v : Circuit n) → w ≋ v → v ≋ w
  ≋-sym {n} w v = V.sym {n} {⟦ w ⟧} {⟦ v ⟧}

  ≋-trans : (u w v : Circuit n) → u ≋ w → w ≋ v → u ≋ v
  ≋-trans {n} u w v = V.trans {n} {⟦ u ⟧} {⟦ w ⟧} {⟦ v ⟧}

  nf : (n : ℕ) → Circuit n → NF n
  nf n = normalise n (rels br₁ br₂ br₃ n)

  nf-ok : (n : ℕ) (w : Circuit n) → n ⊢ w ≈ ⟦ nf n w ⟧ⁿ
  nf-ok n = normalise-ok n (rels br₁ br₂ br₃ n)

-- The Clifford operators on n qutrits, compared exactly.
Clifford-setoid : ℕ → Setoid 0ℓ 0ℓ
Clifford-setoid n = record
  { Carrier       = Circuit n
  ; _≈_           = _≋_
  ; isEquivalence = record
    { refl  = λ {w} → ≋-refl w
    ; sym   = λ {w} {v} → ≋-sym w v
    ; trans = λ {u} {w} {v} → ≋-trans u w v
    }
  }

-- They are the circuits modulo C₁–C₁₈ ...
clifford≃circuits : Inverse (Clifford-setoid n) (Width.word-setoid n)
clifford≃circuits {n} = record
  { to        = λ w → w
  ; from      = λ w → w
  ; to-cong   = complete n
  ; from-cong = sound
  ; inverse   = complete n , sound
  }

-- ... whose elements are the normal forms ...
circuits≃nf : Inverse (Width.word-setoid n) (Eq.setoid (NF n))
circuits≃nf {n} = record
  { to        = nf n
  ; from      = ⟦_⟧ⁿ
  ; to-cong   = λ {w} {v} e → nf-injective (nf n w) (nf n v)
                  (≋-trans ⟦ nf n w ⟧ⁿ w ⟦ nf n v ⟧ⁿ (≋-sym w ⟦ nf n w ⟧ⁿ (sound (nf-ok n w)))
                    (≋-trans w v ⟦ nf n v ⟧ⁿ (sound e) (sound (nf-ok n v))))
  ; from-cong = λ e → Width.refl' n (Eq.cong ⟦_⟧ⁿ e)
  ; inverse   = (λ {N} {w} e → nf-injective (nf n w) N
                   (≋-trans ⟦ nf n w ⟧ⁿ w ⟦ N ⟧ⁿ (≋-sym w ⟦ nf n w ⟧ⁿ (sound (nf-ok n w))) (sound e)))
              , (λ {w} {N} e → Width.trans (Width.refl' n (Eq.cong ⟦_⟧ⁿ e)) (Width.sym (nf-ok n w)))
  }

-- ... of which there are 6 · ∏ₖ₌₁ⁿ 3 (9ᵏ − 1) 9ᵏ.
clifford-order : Inverse (Clifford-setoid n) (Eq.setoid (Fin (order n)))
clifford-order {n} = Compose.inverse clifford≃circuits (Compose.inverse circuits≃nf (NF≅order n))

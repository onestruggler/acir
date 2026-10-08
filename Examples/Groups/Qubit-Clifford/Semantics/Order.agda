------------------------------------------------------------------------
-- Presentations of groups
--
-- The order of the Clifford group (Corollary 5.6)
--
-- The Clifford operators on n qubits are the operators that circuits
-- denote (the paper's Section 1), compared as matrices: the setoid
-- Clifford-setoid.  By soundness and completeness they correspond to
-- the circuits modulo C1–C15 (clifford≃circuits), hence to the normal
-- forms (circuits≃nf), of which there are 8 · ∏ᵢ₌₁ⁿ 2 (4ⁱ − 1) 4ⁱ
-- (Count): over any nontrivial commutative ring with s s + s s = 1 and
-- i i = −1, there are exactly that many n-qubit Clifford operators.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Instances using (Ring ; _+_ ; _*_ ; -_ ; 0# ; 1#)

module Examples.Groups.Qubit-Clifford.Semantics.Order
  {A : Set} {{RA : Ring A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (s : A) (s-half : s * s + s * s ≡ 1#)
  (i : A) (i² : i * i ≡ - 1#)
  (nontrivial : 1# ≢ 0#)
  where

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Function.Bundles using (Inverse)
import Function.Construct.Composition as Compose
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Reasoning using (module Width)
open import Examples.Groups.Qubit-Clifford.NormalForm using (NF ; ⟦_⟧ⁿ)
open import Examples.Groups.Qubit-Clifford.Normalise using (normalise ; normalise-ok)
open import Examples.Groups.Qubit-Clifford.Count using (order ; NF≅order)
open import Examples.Groups.Qubit-Clifford.Semantics.Interpretation isCR s s-half i i²
  using (⟦_⟧ᴬ ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans)
open import Examples.Groups.Qubit-Clifford.Semantics.Soundness isCR s s-half i i² using (sound)
open import Examples.Groups.Qubit-Clifford.Semantics.Completeness isCR s s-half i i² nontrivial
  using (nf-injective ; completeness)

private
  variable
    n : ℕ

-- The Clifford operators on n qubits, compared as matrices.
Clifford-setoid : ℕ → Setoid 0ℓ 0ℓ
Clifford-setoid n = record
  { Carrier       = Circuit n
  ; _≈_           = λ w v → ⟦ w ⟧ᴬ ≐ ⟦ v ⟧ᴬ
  ; isEquivalence = record { refl = ≐-refl _ ; sym = ≐-sym ; trans = ≐-trans }
  }

-- They are the circuits modulo C1–C15 ...
clifford≃circuits : Inverse (Clifford-setoid n) (Width.word-setoid n)
clifford≃circuits = record
  { to        = λ w → w
  ; from      = λ w → w
  ; to-cong   = completeness
  ; from-cong = sound
  ; inverse   = completeness , sound
  }

-- ... whose elements are the normal forms ...
circuits≃nf : Inverse (Width.word-setoid n) (Eq.setoid (NF n))
circuits≃nf {n} = record
  { to        = normalise n
  ; from      = ⟦_⟧ⁿ
  ; to-cong   = λ {w} {v} e → nf-injective (normalise n w) (normalise n v)
                  (≐-trans (≐-sym (sound (normalise-ok n w))) (≐-trans (sound e) (sound (normalise-ok n v))))
  ; from-cong = λ e → Width.refl' n (Eq.cong ⟦_⟧ⁿ e)
  ; inverse   = (λ {N} {w} e → nf-injective (normalise n w) N
                   (≐-trans (≐-sym (sound (normalise-ok n w))) (sound e)))
              , (λ {w} {N} e → Width.trans (Width.refl' n (Eq.cong ⟦_⟧ⁿ e)) (Width.sym (normalise-ok n w)))
  }

-- ... of which there are 8 · ∏ᵢ₌₁ⁿ 2 (4ⁱ − 1) 4ⁱ.
corollary-5-6 : Inverse (Clifford-setoid n) (Eq.setoid (Fin (order n)))
corollary-5-6 {n} = Compose.inverse clifford≃circuits (Compose.inverse circuits≃nf (NF≅order n))

------------------------------------------------------------------------
-- Presentations of groups
--
-- A table cell from stored representative matrices.  The cell
--
--   ⟦ rep c • e g ⟧ = ⟦ B • rep c′ ⟧
--
-- costs two long evaluations when both sides are computed from scratch,
-- and each representative occurs in some sixteen cells.  Given its
-- matrix P = ⟦ rep c ⟧ once and for all, the left side is P ⟦ e g ⟧,
-- and every encoded generator is symmetric, so that is the transpose of
-- e g acting on the transpose of P; the right side is B acting on the
-- stored ⟦ rep c′ ⟧.  What is left to evaluate is a few letters.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.ThreeQubit.Checks.Assemble where

open import Data.Product.Base using (proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; sym ; cong ; module ≡-Reasoning)
open import Word.Base using (_•_ ; _ʷ)

open import Quantum.Synthesis.Matrix using (Matrix ; adjoint ; _·*·_)

open import Examples.Groups.CCX+HH.Syntactics
open import Examples.Groups.CCX+HH.ThreeQubit.Cosets
open import Examples.Groups.CCX+HH.ThreeQubit.Table
open import Examples.Groups.CCX+HH.ThreeQubit.StabilizerGenerators using (b)
open import Examples.Groups.CCX+HH.ThreeQubit.Checks.Base
open import Examples.Groups.CCX+HH.Decide using (by-eq)
import Examples.Groups.CCX+HH.StructuralEncoding as E
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_ ; adjᴰ)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂)

Mat : Set
Mat = Matrix 8 8 D

------------------------------------------------------------------------
-- Every encoded generator is symmetric

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_ adjᴰ

  symmetric : (g : Gen 3) → adjoint S.⟦ E.e g ⟧ᵐ ≡ S.⟦ E.e g ⟧ᵐ
  symmetric X-gen = by-eq tt
  symmetric (X-gen ↥) = by-eq tt
  symmetric (X-gen ↥ ↥) = by-eq tt
  symmetric CX-gen = by-eq tt
  symmetric (CX-gen ↥) = by-eq tt
  symmetric CCX-gen = by-eq tt
  symmetric HH-gen = by-eq tt
  symmetric (HH-gen ↥) = by-eq tt
  symmetric (gate₀ ())
  symmetric ((gate₀ ()) ↥)
  symmetric ((gate₀ ()) ↥ ↥)
  symmetric ((gate₀ ()) ↥ ↥ ↥)

------------------------------------------------------------------------
-- A cell from the stored matrices of its two representatives

assemble : (c : Coset) (g : Gen 3) (P Q : Mat) →
  S.⟦ E.encode (rep c) ⟧ᵐ ≡ P →
  S.⟦ E.encode (rep (proj₂ (h c g))) ⟧ᵐ ≡ Q →
  adjoint (S.actMʷ (E.e g) (adjoint P)) ≡ S.actMʷ ((b ʷ) (proj₁ (h c g))) Q →
  Checked c g
assemble c g P Q p q e = begin
  S.⟦ E.encode (rep c) • E.e g ⟧ᵐ               ≡⟨ S.⟦•⟧ᵐ (E.encode (rep c)) (E.e g) ⟩
  S.⟦ E.encode (rep c) ⟧ᵐ ·*· G                 ≡⟨ cong (_·*· G) p ⟩
  P ·*· G                                       ≡⟨ sym (S.adjoint-involutive (P ·*· G)) ⟩
  adjoint (adjoint (P ·*· G))                   ≡⟨ cong adjoint (S.adjoint-·*· P G) ⟩
  adjoint (adjoint G ·*· adjoint P)             ≡⟨ cong (λ X → adjoint (X ·*· adjoint P)) (symmetric g) ⟩
  adjoint (G ·*· adjoint P)                     ≡⟨ cong adjoint (sym (S.actMʷ≡ (E.e g) (adjoint P))) ⟩
  adjoint (S.actMʷ (E.e g) (adjoint P))         ≡⟨ e ⟩
  S.actMʷ B Q                                   ≡⟨ cong (S.actMʷ B) (sym q) ⟩
  S.actMʷ B S.⟦ E.encode (rep (proj₂ (h c g))) ⟧ᵐ ∎
  where
  open ≡-Reasoning
  G = S.⟦ E.e g ⟧ᵐ
  B = (b ʷ) (proj₁ (h c g))

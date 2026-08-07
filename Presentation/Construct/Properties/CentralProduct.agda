------------------------------------------------------------------------
-- Presentations of groups
--
-- Presentations of central products.
--
-- Given ⟨A | Γ⟩ presenting G₁, ⟨B | Δ⟩ presenting G₂, and a third
-- presentation ⟨M | Θ⟩ of an abelian group C sitting centrally in both
-- factors — its generators realised by words f₁ m ∈ Word A and
-- f₂ m ∈ Word B — the central product G₁ ∘_C G₂ of
-- ForStdlib.Algebra.Construct.CentralProduct is presented on A ⊎ B by
--
--     Γ ⋄ Δ ⋄ (CommRel ∪ AmalgRel f₁ f₂),
--
-- the direct-product presentation together with the amalgamation
-- relations
--
--     [ f₁ m ]ₗ === [ f₂ m ]ᵣ        (m ∈ M),
--
-- which identify the two copies of C.  Dropping AmalgRel gives the
-- direct product (Presentation.Construct.Properties.DirectProduct);
-- dropping CommRel gives the amalgamated free product
-- (Presentation.Construct.Properties.Amalgamation).  The central
-- product sits between them: the factors commute AND share a central
-- subgroup.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel ; Word)

module Presentation.Construct.Properties.CentralProduct
  {A B : Set}
  (Γ : WRel A)
  (Δ : WRel B)
  where

open import Data.Sum using (_⊎_)

open import Presentation.Construct.Base
import Presentation.Base as PB

------------------------------------------------------------------------
-- The central-product relation
--
-- f₁ and f₂ say how each generator of the shared central group is
-- spelled in the two factors.

central-product-relation : ∀ {M : Set} (f₁ : M → Word A) (f₂ : M → Word B) →
                           WRel (A ⊎ B)
central-product-relation f₁ f₂ = Γ ⋄ Δ ⋄ (CommRel ∪ AmalgRel f₁ f₂)

------------------------------------------------------------------------
-- Weakening along the amalgamation relations
--
-- Every derivation from the direct-product relation is one from the
-- central-product relation: the two differ only in the mixed part, of
-- which CommRel is one half.  This is what lets the completeness proof
-- below hand its final step to the direct product.

module _ {M : Set} (f₁ : M → Word A) (f₂ : M → Word B) where

  open PB (Γ ⋄ Δ ⋄ CommRel) renaming (_≈_ to _≈ᵈ_) using ()
  open PB (central-product-relation f₁ f₂) renaming (_≈_ to _≈ᶜ_) using ()

  weaken : ∀ {w v} → w ≈ᵈ v → w ≈ᶜ v
  weaken PB.refl              = PB.refl
  weaken (PB.sym eq)          = PB.sym (weaken eq)
  weaken (PB.trans eq eq₁)    = PB.trans (weaken eq) (weaken eq₁)
  weaken (PB.cong eq eq₁)     = PB.cong (weaken eq) (weaken eq₁)
  weaken PB.assoc             = PB.assoc
  weaken PB.left-unit         = PB.left-unit
  weaken PB.right-unit        = PB.right-unit
  weaken (PB.axiom (left x))  = PB.axiom (left x)
  weaken (PB.axiom (right x)) = PB.axiom (right x)
  weaken (PB.axiom (mid x))   = PB.axiom (mid (left x))

------------------------------------------------------------------------
-- The presentation theorem
--
-- REMAINING GOAL.  With G₁, G₂, C, a CentralPair χ : CentralPair C G₁ G₂,
-- presentations p₁ : Γ IsPresentationOf G₁, p₂ : Δ IsPresentationOf G₂,
-- pC : Θ IsPresentationOf (AbelianGroup.group C), and the compatibility
--
--     ∀ m → P₁.⟦ f₁ m ⟧ ≈ ιˡ PC.⟦ [ m ]ʷ ⟧,
--     ∀ m → P₂.⟦ f₂ m ⟧ ≈ ιʳ PC.⟦ [ m ]ʷ ⟧,
--
-- saying that the two spellings really are the images of the central
-- generators, one has
--
--     cpres : central-product-relation f₁ f₂
--               IsPresentationOf (CentralProduct.group C G₁ G₂ χ).
--
-- The proof reuses DirectProduct.Presentation wholesale, because the
-- central product has the SAME CARRIER as the direct product and only a
-- coarser equality (`from≈` is the quotient map):
--
--   * The interpretation is the direct product's, ⟦_⟧₀ = DPP.⟦_⟧₀,
--     extended by Normalization.StarInterp; its congruence comes from
--     E.Cong applied to soundness of the axioms.
--
--   * Soundness: `left`, `right` and `mid (left _)` are the direct
--     product's soundness composed with from≈; `mid (right amal)` is
--     exactly CentralProduct.glue.
--
--   * Group-likeness: the factor inverse words again, transported by
--     the lefts/rights of LeftRightCongruence Γ Δ (CommRel ∪ AmalgRel _ _).
--
--   * Surjectivity: the direct product's, composed with from≈.
--
--   * Completeness is the one real step.  If ⟦w⟧ ≈ ⟦v⟧ in the central
--     product then, in the direct product, the two differ by an element
--     (ιˡ x , ιʳ (x ⁻¹)) of the antidiagonal.  Since Θ presents C, write
--     x = PC.⟦ m ⟧ for a word m over M; then the difference is realised
--     by U = [ (f₁ ʷ) m ]ₗ and V = [ (f₂ ʷ) m ]ᵣ, and
--
--         w ≈ᶜ w • U • V ⁻¹        (U ≈ᶜ V, by induction on m from the
--                                   AmalgRel axioms)
--         ⟦ w • U • V ⁻¹ ⟧ ≈ ⟦ v ⟧ in the DIRECT product
--                                  (by the compatibility above,
--                                   extended from generators to words)
--
--     so injectivity of the direct-product presentation gives
--     w • U • V ⁻¹ ≈ᵈ v, and `weaken` above turns that into w ≈ᶜ v.
--
-- Every ingredient is in place; what is missing is the assembly.

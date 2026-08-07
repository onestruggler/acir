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

open import Word.Base using (WRel ; Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

module Presentation.Construct.Properties.CentralProduct
  {A B : Set}
  (Γ : WRel A)
  (Δ : WRel B)
  where

open import Algebra.Bundles using (AbelianGroup ; Group)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function.Definitions using (Surjective)
open import Level using (0ℓ)

open import ForStdlib.Algebra.Construct.CentralProduct
  using (CentralPair ; from≈ ; glue) renaming (group to central-product-group)
open import Presentation.Construct.Base
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (Grouplike)
import Presentation.Base as PB
import Presentation.Construct.Properties.DirectProduct Γ Δ as DP

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

  ----------------------------------------------------------------------
  -- The two spellings agree on whole words
  --
  -- The amalgamation axioms identify the two spellings of a central
  -- GENERATOR; the identification of the two spellings of a central
  -- WORD is this induction.  It is the form completeness needs, since
  -- the antidiagonal element to be cancelled there is given by a word
  -- over the centre's generators, not by a single one.

  glue-word : ∀ (m : Word M) → [ (f₁ ʷ) m ]ₗ ≈ᶜ [ (f₂ ʷ) m ]ᵣ
  glue-word [ x ]ʷ  = PB.axiom (mid (right amal))
  glue-word ε       = PB.refl
  glue-word (u • v) = PB.cong (glue-word u) (glue-word v)

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

module Presentation
  {M : Set}
  (G₁ G₂ : Group 0ℓ 0ℓ)
  (C : AbelianGroup 0ℓ 0ℓ)
  (χ : CentralPair C G₁ G₂)
  (p₁ : Γ IsPresentationOf G₁)
  (p₂ : Δ IsPresentationOf G₂)
  (f₁ : M → Word A) (f₂ : M → Word B)
  where

  open CentralPair χ using (ιˡ ; ιʳ)

  private
    module P₁  = _IsPresentationOf_ p₁
    module P₂  = _IsPresentationOf_ p₂
    module DPP = DP.Presentation G₁ G₂ p₁ p₂

  -- The relation and the group it is to present.
  cprel : WRel (A ⊎ B)
  cprel = central-product-relation f₁ f₂

  cp : Group 0ℓ 0ℓ
  cp = central-product-group C G₁ G₂ χ

  private
    module CPG = Group cp
    module D   = Group DPP.dp
    module LRC = LeftRightCongruence Γ Δ (CommRel ∪ AmalgRel f₁ f₂)

  -- The interpretation is the direct product's: the two groups have the
  -- same carrier.
  ⟦_⟧₀ : (A ⊎ B) → Group.Carrier cp
  ⟦_⟧₀ = DPP.⟦_⟧₀

  open import Normalization.StarInterp cprel
  private module E = Extend (Group.monoid cp) ⟦_⟧₀
  open E using (⟦_⟧) public

  ----------------------------------------------------------------------
  -- The two folds agree
  --
  -- ⟦_⟧ and DPP.⟦_⟧ are the same fold of the same generator map, but
  -- over the two groups' monoids — which multiply pairs componentwise
  -- in both cases, though not by the same term.  This induction is what
  -- lets the direct product's soundness be reused verbatim.

  bridge : ∀ w → D._≈_ DPP.⟦ w ⟧ ⟦ w ⟧
  bridge [ x ]ʷ  = D.refl
  bridge ε       = D.refl
  bridge (u • v) = D.∙-cong (bridge u) (bridge v)

  ----------------------------------------------------------------------
  -- The quotient map, on the nose
  --
  -- Spelling out the four components keeps this usable at arbitrary
  -- terms: ⟦ w ⟧ is a fold, not syntactically a pair.

  fromD : ∀ {u v : Group.Carrier DPP.dp} → D._≈_ u v → CPG._≈_ u v
  fromD {u} {v} p =
    from≈ C G₁ G₂ χ {proj₁ u} {proj₁ v} {proj₂ u} {proj₂ v}
          (proj₁ p) (proj₂ p)

  ----------------------------------------------------------------------
  -- Soundness of the direct-product axioms
  --
  -- The amalgamation axioms are the remaining case; they are
  -- CentralProduct.glue, and need the realisation data saying that f₁
  -- and f₂ really do spell the central generators.

  sound-dp : ∀ {u v} → (Γ ⋄ Δ ⋄ CommRel) u v → CPG._≈_ ⟦ u ⟧ ⟦ v ⟧
  sound-dp {u} {v} x =
    fromD (D.trans (D.sym (bridge u)) (D.trans (DPP.sound-ax x) (bridge v)))

  ----------------------------------------------------------------------
  -- Group-likeness
  --
  -- The inverse words are the factors', as for the direct product; only
  -- the ambient relation is bigger.

  grouplike : Grouplike cprel
  grouplike (inj₁ a) = [ proj₁ (P₁.gl a) ]ₗ , LRC.lefts (proj₂ (P₁.gl a))
  grouplike (inj₂ b) = [ proj₁ (P₂.gl b) ]ᵣ , LRC.rights (proj₂ (P₂.gl b))

  ----------------------------------------------------------------------
  -- Soundness in full
  --
  -- The amalgamation axioms are sound as soon as f₁ and f₂ really do
  -- spell the images of a central element: then the two sides are inl
  -- and inr of that element, which CentralProduct.glue identifies.

  module Sound
    (cgen : M → AbelianGroup.Carrier C)
    (r₁ : ∀ m → Group._≈_ G₁ P₁.⟦ f₁ m ⟧ (ιˡ (cgen m)))
    (r₂ : ∀ m → Group._≈_ G₂ P₂.⟦ f₂ m ⟧ (ιʳ (cgen m)))
    where

    private
      module H₁ = Group G₁
      module H₂ = Group G₂

    sound-amal : ∀ {u v} → AmalgRel f₁ f₂ u v → CPG._≈_ ⟦ u ⟧ ⟦ v ⟧
    sound-amal (amal {m}) =
      CPG.trans (fromD (D.trans into-l (r₁ m , H₂.refl)))
        (CPG.trans (glue C G₁ G₂ χ (cgen m))
                   (fromD (D.trans (H₁.refl , H₂.sym (r₂ m)) out-r)))
      where
      into-l : D._≈_ ⟦ [ f₁ m ]ₗ ⟧ (P₁.⟦ f₁ m ⟧ , H₂.ε)
      into-l = D.trans (D.sym (bridge [ f₁ m ]ₗ)) (DPP.emb-l (f₁ m))
      out-r : D._≈_ (H₁.ε , P₂.⟦ f₂ m ⟧) ⟦ [ f₂ m ]ᵣ ⟧
      out-r = D.trans (D.sym (DPP.emb-r (f₂ m))) (bridge [ f₂ m ]ᵣ)

    sound-ax : ∀ {u v} → cprel u v → CPG._≈_ ⟦ u ⟧ ⟦ v ⟧
    sound-ax (left x)         = sound-dp (left x)
    sound-ax (right x)        = sound-dp (right x)
    sound-ax (mid (left x))   = sound-dp (mid x)
    sound-ax (mid (right x))  = sound-amal x

    private module EC = E.Cong sound-ax

    -- The interpretation is a congruence for the central-product
    -- relation, i.e. the presentation is sound.
    ⟦⟧-cong : ∀ {w v} → PB._≈_ cprel w v → CPG._≈_ ⟦ w ⟧ ⟦ v ⟧
    ⟦⟧-cong = EC.fʷ-cong

    ------------------------------------------------------------------
    -- Surjectivity
    --
    -- The direct product is already onto the shared carrier; the
    -- quotient map only coarsens the equality.

    surj : Surjective (PB._≈_ cprel) CPG._≈_ ⟦_⟧
    surj y with DPP.surj y
    ... | w , pf = w , λ {z} eq →
      CPG.trans (⟦⟧-cong eq)
                (fromD (D.trans (D.sym (bridge w)) (pf PB.refl)))

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
import Algebra.Morphism.Structures as GM
open import Data.Product using (_,_ ; _×_ ; ∃ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function.Definitions using (Injective ; Surjective)
open import Level using (0ℓ)

open import ForStdlib.Algebra.Construct.CentralProduct
  using (CentralPair ; from≈ ; glue) renaming (group to central-product-group)
open import Presentation.Construct.Base
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)
open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)
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
-- With G₁, G₂, C, a CentralPair χ : CentralPair C G₁ G₂,
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
-- The theorem is Presentation.Complete.WithRealises.cpres below.  One
-- step of the reuse needs care and is `bridge`: the two interpretations
-- are the same fold of the same generator map, but over the two groups'
-- monoids, which multiply pairs componentwise in both cases though not
-- by the same term.

module Presentation
  {M : Set}
  (G₁ G₂ : Group 0ℓ 0ℓ)
  (C : AbelianGroup 0ℓ 0ℓ)
  (χ : CentralPair C G₁ G₂)
  (p₁ : Γ IsPresentationOf G₁)
  (p₂ : Δ IsPresentationOf G₂)
  (f₁ : M → Word A) (f₂ : M → Word B)
  where

  open CentralPair χ

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

    open E.Cong sound-ax public using (isMonoidHomomorphism)
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

  ----------------------------------------------------------------------
  -- Completeness
  --
  -- Here the centre must itself be presented: the antidiagonal element
  -- separating two words has to be named by a word over its generators
  -- before the amalgamation relations can cancel it.

  module Complete
    (Θ : WRel M)
    (pC : Θ IsPresentationOf AbelianGroup.group C)
    where

    private
      module PC = _IsPresentationOf_ pC

    -- The spellings, extended from generators to words: if f₁ m and
    -- f₂ m name the images of each central generator, then their word
    -- extensions name the images of each central word.
    Realises : Set
    Realises =
      (∀ m → Group._≈_ G₁ P₁.⟦ f₁ m ⟧ (ιˡ PC.⟦ [ m ]ʷ ⟧)) ×
      (∀ m → Group._≈_ G₂ P₂.⟦ f₂ m ⟧ (ιʳ PC.⟦ [ m ]ʷ ⟧))

    module WithRealises (r : Realises) where

      private
        module H₁ = Group G₁
        module H₂ = Group G₂
        module AC = AbelianGroup C

        open GM.GroupMorphisms (Group.rawGroup P₁.GL.•-ε-group)
                               (Group.rawGroup G₁)
          using () renaming (module IsGroupIsomorphism to IGI₁)
        open GM.GroupMorphisms (Group.rawGroup P₂.GL.•-ε-group)
                               (Group.rawGroup G₂)
          using () renaming (module IsGroupIsomorphism to IGI₂)
        open GM.GroupMorphisms (Group.rawGroup PC.GL.•-ε-group)
                               (Group.rawGroup (AbelianGroup.group C))
          using () renaming (module IsGroupIsomorphism to IGIC)
        module Iso₁ = IGI₁ P₁.iso
        module Iso₂ = IGI₂ P₂.iso
        module IsoC = IGIC PC.iso

        r₁ = proj₁ r
        r₂ = proj₂ r

      ------------------------------------------------------------------
      -- The spellings name central WORDS, not just central generators

      word-r₁ : ∀ mw → Group._≈_ G₁ P₁.⟦ (f₁ ʷ) mw ⟧ (ιˡ PC.⟦ mw ⟧)
      word-r₁ [ m ]ʷ  = r₁ m
      word-r₁ ε       =
        H₁.trans Iso₁.ε-homo
          (H₁.sym (H₁.trans (ιˡ-cong IsoC.ε-homo) ιˡ-ε))
      word-r₁ (u • v) =
        H₁.trans (Iso₁.∙-homo _ _)
          (H₁.trans (H₁.∙-cong (word-r₁ u) (word-r₁ v))
            (H₁.sym (H₁.trans (ιˡ-cong (IsoC.∙-homo _ _)) (ιˡ-∙ _ _))))

      word-r₂ : ∀ mw → Group._≈_ G₂ P₂.⟦ (f₂ ʷ) mw ⟧ (ιʳ PC.⟦ mw ⟧)
      word-r₂ [ m ]ʷ  = r₂ m
      word-r₂ ε       =
        H₂.trans Iso₂.ε-homo
          (H₂.sym (H₂.trans (ιʳ-cong IsoC.ε-homo) ιʳ-ε))
      word-r₂ (u • v) =
        H₂.trans (Iso₂.∙-homo _ _)
          (H₂.trans (H₂.∙-cong (word-r₂ u) (word-r₂ v))
            (H₂.sym (H₂.trans (ιʳ-cong (IsoC.∙-homo _ _)) (ιʳ-∙ _ _))))

      private
        module S  = Sound (λ m → PC.⟦ [ m ]ʷ ⟧) r₁ r₂
        module GL = Group-Lemmas cprel grouplike
        module Pdp = _IsPresentationOf_ DPP.dpres
        open GM.GroupMorphisms (Group.rawGroup Pdp.GL.•-ε-group)
                               (Group.rawGroup DPP.dp)
          using () renaming (module IsGroupIsomorphism to IGIdp)
        module Isodp = IGIdp Pdp.iso

      open GL using (•-cancelʳ)

      ------------------------------------------------------------------
      -- Injectivity
      --
      -- Two words equal in the central product differ, in the direct
      -- product, by an antidiagonal element (ιˡ x , ιʳ (x ⁻¹)).  Name x
      -- by a word mw over the central generators — possible because Θ
      -- presents C — and let U, V be its two spellings.  Then w • U and
      -- v • V have the SAME direct-product value, so the direct
      -- product's injectivity identifies them; glue-word identifies U
      -- with V; and cancelling V on the right leaves w ≈ v.

      inj : Injective (PB._≈_ cprel) CPG._≈_ ⟦_⟧
      inj {w} {v} (x , e₁ , e₂) =
        •-cancelʳ (PB.trans (PB.cong PB.refl (PB.sym (glue-word f₁ f₂ mw)))
                            wU≈vV)
        where
        mw : Word M
        mw = proj₁ (IsoC.surjective x)

        pmw : AbelianGroup._≈_ C PC.⟦ mw ⟧ x
        pmw = proj₂ (IsoC.surjective x) PB.refl

        U V : Word (A ⊎ B)
        U = [ (f₁ ʷ) mw ]ₗ
        V = [ (f₂ ʷ) mw ]ᵣ

        semU : D._≈_ ⟦ U ⟧ (ιˡ x , H₂.ε)
        semU = D.trans (D.sym (bridge U))
                 (D.trans (DPP.emb-l ((f₁ ʷ) mw))
                          (H₁.trans (word-r₁ mw) (ιˡ-cong pmw) , H₂.refl))

        semV : D._≈_ ⟦ V ⟧ (H₁.ε , ιʳ x)
        semV = D.trans (D.sym (bridge V))
                 (D.trans (DPP.emb-r ((f₂ ʷ) mw))
                          (H₁.refl , H₂.trans (word-r₂ mw) (ιʳ-cong pmw)))

        -- The right-hand components meet because ιʳ (x ⁻¹) ∙ ιʳ x is ε.
        second : H₂._≈_ (proj₂ ⟦ w ⟧ H₂.∙ proj₂ ⟦ U ⟧)
                        (proj₂ ⟦ v ⟧ H₂.∙ proj₂ ⟦ V ⟧)
        second =
          H₂.trans (H₂.∙-congˡ (proj₂ semU))
            (H₂.trans (H₂.identityʳ _)
              (H₂.sym
                (H₂.trans (H₂.∙-cong e₂ (proj₂ semV))
                  (H₂.trans (H₂.assoc _ _ _)
                    (H₂.trans (H₂.∙-congˡ (H₂.trans (H₂.sym (ιʳ-∙ _ _))
                                            (H₂.trans (ιʳ-cong (AbelianGroup.inverseˡ C x))
                                                      ιʳ-ε)))
                              (H₂.identityʳ _))))))

        first : H₁._≈_ (proj₁ ⟦ w ⟧ H₁.∙ proj₁ ⟦ U ⟧)
                       (proj₁ ⟦ v ⟧ H₁.∙ proj₁ ⟦ V ⟧)
        first =
          H₁.trans (H₁.∙-congˡ (proj₁ semU))
            (H₁.trans (H₁.sym e₁)
              (H₁.sym (H₁.trans (H₁.∙-congˡ (proj₁ semV))
                                (H₁.identityʳ _))))

        key : D._≈_ ⟦ w • U ⟧ ⟦ v • V ⟧
        key = first , second

        wU≈vV : PB._≈_ cprel (w • U) (v • V)
        wU≈vV = weaken f₁ f₂
          (Isodp.injective
            (D.trans (bridge (w • U)) (D.trans key (D.sym (bridge (v • V))))))

      ------------------------------------------------------------------
      -- The presentation theorem

      cpres : cprel IsPresentationOf cp
      cpres = record
        { gl  = grouplike
        ; ⟦_⟧ = ⟦_⟧
        ; iso = record
          { isGroupMonomorphism = record
            { isGroupHomomorphism =
                isMonoidHomomorphism⇒isGroupHomomorphism
                  GL.•-ε-group cp S.isMonoidHomomorphism
            ; injective = inj
            }
          ; surjective = S.surj
          }
        }

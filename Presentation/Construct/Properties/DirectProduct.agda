------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal-form properties for direct products of group presentations.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base using (WRel)

module Presentation.Construct.Properties.DirectProduct
  {A B : Set}
  (Γ : WRel A)
  (Δ : WRel B)
  where

open import Algebra.Bundles using (Group)
import Algebra.Construct.DirectProduct as ADP
import Algebra.Morphism.Structures as GM
open import Level
open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂ ; ∃)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_)
import Function.Construct.Composition as FCC
open import Function.Definitions using (Injective ; Surjective)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; inspect) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Base as PB
open import Presentation.Definitions
open import Presentation.GroupLike using (Grouplike)
open import Presentation.Construct.Base
open import Presentation.Properties as PP
open import Normalization.NormalForm.Propositional using (NormalForm ; NormalFormInjective)
import Normalization.NormalForm.Setoid as SNF
open import Normalization.Reidemeister-Schreier
import Normalization.StarPresentation as SP
open import Word.Base
open import Word.Properties

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()
open PB (Γ ⋄ Δ ⋄ CommRel) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_) using ()
open PP (Γ ⋄ Δ ⋄ CommRel) renaming (•-ε-monoid to m₃ ; word-setoid to word-setoid₃) using ()

open _≈₃_

------------------------------------------------------------------------
-- Reidemeister-Schreier setup
--
-- The right factor enumerates the cosets of the left factor: the
-- coset space is Word B up to Δ-equivalence (the setoid Cₛ), the
-- section [_] is the right embedding [_]ᵣ, and the coset table h
-- pushes a product generator past a coset representative.

-- The coset setoid.
Cₛ = word-setoid₂

-- Generators of the direct product.
Y = A ⊎ B

-- The initial coset: the coset of the unit.
I : Word B
I = ε

open Star-Injective-Full-Setoid Γ (Γ ⋄ Δ ⋄ CommRel) Cₛ I

-- The section: embed a coset representative on the right.
[_] : C → Word Y
[_] = [_]ᵣ

-- Left embedding of the generators of Γ.
f : A → Word Y
f x = [ [ x ]ʷ ]ₗ

-- The coset table: a left generator passes through and is emitted; a
-- right generator is absorbed into the coset.
h : C → Y → Word A × C
h c (inj₁ x) = [ x ]ʷ , c
h c (inj₂ y) = ε , (c • [ y ]ʷ)

-- The fold (h ᵗ) leaves a left-embedded word untouched.
lemma-hᵗ-left' : ∀ c {w} → (h ᵗ) c [ w ]ₗ ≡ (w , c)
lemma-hᵗ-left' c {[ x ]ʷ} = Eq.refl
lemma-hᵗ-left' c {ε} = Eq.refl
lemma-hᵗ-left' c {w • w₁}
  rewrite lemma-hᵗ-left' c {w} | lemma-hᵗ-left' c {w₁} = Eq.refl

-- Setoid version of lemma-hᵗ-left'.
lemma-hᵗ-left : ∀ c {w} → (h ᵗ) c [ w ]ₗ ~ (w , c)
lemma-hᵗ-left c {[ x ]ʷ} = _≈₁_.refl , _≈₂_.refl
lemma-hᵗ-left c {ε} = _≈₁_.refl , _≈₂_.refl
lemma-hᵗ-left c {w • w₁}
  with (h ᵗ) c [ w ]ₗ | inspect ((h ᵗ) c) [ w ]ₗ
... | (w' , c') | [ eq1 ]'
  with (h ᵗ) c' [ w₁ ]ₗ | inspect ((h ᵗ) c') [ w₁ ]ₗ
... | (w₁' , c'') | [ eq2 ]'
  with lemma-hᵗ-left c {w} | lemma-hᵗ-left c' {w₁}
... | ih1 | ih2 rewrite eq1 | eq2 =
  (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) ,
  _≈₂_.trans (ih2 .proj₂) (ih1 .proj₂)

-- The fold (h ᵗ) absorbs a right-embedded word into the coset.
lemma-hᵗ-right : ∀ c {w} → (h ᵗ) c [ w ]ᵣ ~ (ε , c • w)
lemma-hᵗ-right c {[ x ]ʷ} = _≈₁_.refl , _≈₂_.refl
lemma-hᵗ-right c {ε} = _≈₁_.refl , _≈₂_.sym _≈₂_.right-unit
lemma-hᵗ-right c {w • w₁}
  with (h ᵗ) c [ w ]ᵣ | inspect ((h ᵗ) c) [ w ]ᵣ
... | (w' , c') | [ eq1 ]'
  with (h ᵗ) c' [ w₁ ]ᵣ | inspect ((h ᵗ) c') [ w₁ ]ᵣ
... | (w₁' , c'') | [ eq2 ]'
  with lemma-hᵗ-right c {w} | lemma-hᵗ-right c' {w₁}
... | ih1 | ih2 rewrite eq1 | eq2 =
  (_≈₁_.trans (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) _≈₁_.right-unit) ,
  _≈₂_.trans (ih2 .proj₂)
    (_≈₂_.trans (_≈₂_.cong (ih1 .proj₂) _≈₂_.refl) _≈₂_.assoc)

-- The coset table respects the coset setoid.
h-congₛ-gen : ∀ {c d} y → c ≈ₛ d → h c y ~ h d y
h-congₛ-gen {c} {d} (inj₁ x) eq = _≈₁_.refl , eq
h-congₛ-gen {c} {d} (inj₂ y) eq =
  trans~ (lemma-hᵗ-right c {[ y ]ʷ})
    (trans~ (_≈₁_.refl , _≈₂_.cong eq (_≈₂_.refl))
      (sym~ (lemma-hᵗ-right d {[ y ]ʷ})))

-- On generators, (h ᵗ) started at the initial coset inverts f.
h=⁻¹f-gen : ∀ (x : A) → ([ x ]ʷ , I) ~ ((h ᵗ) I (f x))
h=⁻¹f-gen x = refl~

-- (h ᵗ) is well defined on the axioms of the product; the mid case
-- is the commutation of left and right generators.
h-wd : ∀ (c : C){u t : Word Y} → u ===₃ t → ((h ᵗ) c u) ~ ((h ᵗ) c t)
h-wd c {u} {t} (left x) =
  trans~ (lemma-hᵗ-left c)
    (trans~ ((_≈₁_.axiom x) , reflₛ) (sym~ (lemma-hᵗ-left c)))
h-wd c {u} {t} (right x) =
  trans~ (lemma-hᵗ-right c)
    (trans~ (_≈₁_.refl , _≈₂_.cong _≈₂_.refl (_≈₂_.axiom x))
      (sym~ (lemma-hᵗ-right c)))
h-wd c {u} {t} (mid (comm a b)) =
  _≈₁_.trans _≈₁_.right-unit (_≈₁_.sym _≈₁_.left-unit) , reflₛ

-- Instantiate the Reidemeister-Schreier machinery.
open Reidemeister-Schreier-Full f h h-congₛ-gen h=⁻¹f-gen h-wd

------------------------------------------------------------------------
-- Commutation and coset lemmas

-- The extension of f is the left embedding.
aux-fʷ : ∀ {w} → (f ʷ) w ≡ [ ([_]ʷ ʷ) w ]ₗ
aux-fʷ {[ x ]ʷ} = Eq.refl
aux-fʷ {ε} = Eq.refl
aux-fʷ {w • w₁} rewrite aux-fʷ {w} | aux-fʷ {w₁} = Eq.refl

-- f maps the axioms of Γ to equalities of the product.
f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₃ (f ʷ) v
f-well-defined {w} {v} ax
  rewrite aux-fʷ {w} | aux-fʷ {v} | wconcatmap-[-]ʷ w | wconcatmap-[-]ʷ v
  = axiom (left ax)

-- The initial coset is represented by the unit.
[I]≈ε : [ I ] ≈₃ ε
[I]≈ε = _≈₃_.refl

-- The coset table, viewed as a right action.
ract = h

-- Embedding of the emitted word into the product.
[_]ₓ = f ʷ

-- A single right generator commutes with a left-embedded word.
lemma-comm1 : ∀ x w → [ [ x ]ʷ ]ᵣ • [ w ]ₗ ≈₃ [ w ]ₗ • [ [ x ]ʷ ]ᵣ
lemma-comm1 x [ x₁ ]ʷ = _≈₃_.sym (_≈₃_.axiom (mid (comm x₁ x)))
lemma-comm1 x ε = _≈₃_.trans _≈₃_.right-unit (_≈₃_.sym _≈₃_.left-unit)
lemma-comm1 x (w • w₁) with lemma-comm1 x w | lemma-comm1 x w₁
... | ih1 | ih2 =
  _≈₃_.trans (_≈₃_.sym _≈₃_.assoc)
    (_≈₃_.trans (_≈₃_.cong ih1 _≈₃_.refl)
      (_≈₃_.trans _≈₃_.assoc
        (_≈₃_.trans (_≈₃_.cong refl ih2) (_≈₃_.sym _≈₃_.assoc))))

-- Left-embedded words commute with right-embedded words.
lemma-comm : ∀ w v → [ v ]ᵣ • [ w ]ₗ ≈₃ [ w ]ₗ • [ v ]ᵣ
lemma-comm w [ x ]ʷ = lemma-comm1 x w
lemma-comm w ε = _≈₃_.trans _≈₃_.left-unit (_≈₃_.sym _≈₃_.right-unit)
lemma-comm w (v • v₁) with lemma-comm w v | lemma-comm w v₁
... | ih1 | ih2 =
  _≈₃_.sym
    (_≈₃_.trans (_≈₃_.sym _≈₃_.assoc)
      (_≈₃_.trans (_≈₃_.cong (_≈₃_.sym ih1) _≈₃_.refl)
        (_≈₃_.trans _≈₃_.assoc
          (_≈₃_.trans (_≈₃_.cong refl (_≈₃_.sym ih2))
            (_≈₃_.sym _≈₃_.assoc)))))

-- The coset table is sound: acting by a generator agrees with
-- multiplication in the product.
lemma-ract : ∀ c y → let (y' , c') = ract c y in [ c ] • [ y ]ʷ ≈₃ [ y' ]ₓ • [ c' ]
lemma-ract c (inj₁ x₁) = lemma-comm [ x₁ ]ʷ c
lemma-ract c (inj₂ y) = _≈₃_.sym _≈₃_.left-unit

open LeftRightCongruence Γ Δ CommRel

-- The section respects the coset setoid.
[]-cong : ∀ {c d} → c ≈ₛ d → [ c ] ≈₃ [ d ]
[]-cong = rights

open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε
  lemma-ract renaming (nf to coset-nf) hiding ([_]ₓ)

-- The coset-pair normal form: split a word over A ⊎ B into a word
-- over A and a coset representative in Word B.
nf0 = coset-nf

nf0-cong : ∀ {w v} → w ≈₃ v → nf0 w ~ nf0 v
nf0-cong {w} {v} = lemma-hypB I w v

------------------------------------------------------------------------
-- Lifting normal forms without inverse
--
-- Given normal forms without inverse for the two factors, the pair of
-- normal forms is a normal form for the direct product.

module NFP
  {NF₁ NF₂ : Set}
  (nfp-Γ : NormalFormInjective Γ NF₁)
  (nfp-Δ : NormalFormInjective Δ NF₂)
  where

  open SNF.NormalFormInjective nfp-Γ
    renaming (nf to nf₁ ;
              nf-injective to nf₁-inj ; nf-cong to nf₁-cong)
    using ()
  open SNF.NormalFormInjective nfp-Δ
    renaming (nf to nf₂ ;
              nf-injective to nf₂-inj ; nf-cong to nf₂-cong)
    using ()

  nf : Word Y → NF₁ × NF₂
  nf = map nf₁ nf₂ ∘ nf0

  nf-inj× : Injective _≈₃_ (PW.Pointwise _≡_ _≡_) nf
  nf-inj× {w} {v} =
    FCC.injective _≈₃_ _~_ (PW.Pointwise _≡_ _≡_)
      nf-isInjective' (map nf₁-inj nf₂-inj)

  nf-inj : Injective _≈₃_ _≡_ nf
  nf-inj {w} {v} =
    FCC.injective _≈₃_ (PW.Pointwise _≡_ _≡_) _≡_ nf-inj× PW.≡⇒≡×≡

  nf-cong : ∀ {w v} → w ≈₃ v → nf w ≡ nf v
  nf-cong {w} {v} eq =
    PW.≡×≡⇒≡
      (FCC.congruent _≈₃_ _~_ (PW.Pointwise _≡_ _≡_)
        nf0-cong (map nf₁-cong nf₂-cong) eq)

  nfp : NormalFormInjective (Γ ⋄ Δ ⋄ CommRel) (NF₁ × NF₂)
  nfp = record
    { injection = record
        { to        = nf
        ; cong      = nf-cong
        ; injective = nf-inj
        }
    }

------------------------------------------------------------------------
-- Lifting normal forms
--
-- Given normal forms with inverse for the two factors, the pair
-- normal form again has an inverse, obtained by embedding and
-- multiplying the two inverses.

module NFP'
  {NF₁ NF₂ : Set}
  (nfp-Γ : NormalForm Γ NF₁)
  (nfp-Δ : NormalForm Δ NF₂)
  where

  open SNF.NormalForm nfp-Γ
    renaming (normalFormInjective to nfp-Γ' ;
              nf to nf₁ ; nf-injective to nf₁-inj ; nf-cong to nf₁-cong ;
              inv-nf to inv-nf₁ ; inv-nf∘nf=id to inv-nf₁∘nf₁=id)
    using ()
  open SNF.NormalForm nfp-Δ
    renaming (normalFormInjective to nfp-Δ' ;
              nf to nf₂ ; nf-injective to nf₂-inj ; nf-cong to nf₂-cong ;
              inv-nf to inv-nf₂ ; inv-nf∘nf=id to inv-nf₂∘nf₂=id)
    using ()

  open NFP nfp-Γ' nfp-Δ' using (nfp)
  open SNF.NormalFormInjective nfp

  -- The inverse of the pair normal form: embed both components and
  -- multiply.
  gg : NF₁ × NF₂ → Word Y
  gg (a , b) = ([_]ₓ ∘ inv-nf₁) a • ([_] ∘ inv-nf₂) b

  -- Soundness of the iterated coset action.
  hᵗ-hyp : ∀ c b → let (b' , c') = (ract ᵗ) c b in
      [ c ] • b ≈₃ [ b' ]ₓ • [ c' ]
  hᵗ-hyp c b =
    Star-Injective-Full.RightAction.lemma-⊛
      Γ (Γ ⋄ Δ ⋄ CommRel) C I f h f-well-defined [_] [I]≈ε lemma-ract c b

  -- The extension of f respects Γ-equivalence.
  fʷ-cong : ∀ {w v} → w ≈₁ v → (f ʷ) w ≈₃ (f ʷ) v
  fʷ-cong {w} {v} eq =
    PP.StarCongruence.fʷ-cong Γ (Γ ⋄ Δ ⋄ CommRel) f f-well-defined eq

  -- gg is a left inverse of the pair normal form.
  ggnf=id : {w : Word Y} → gg (nf w) ≈₃ w
  ggnf=id {w} =
    let (a , b) = nf0 w in begin
    gg (nf w) ≈⟨ refl ⟩
    gg ((map nf₁ nf₂) (a , b)) ≈⟨ refl ⟩
    gg (nf₁ a , nf₂ b) ≈⟨ refl ⟩
    ([_]ₓ ∘ inv-nf₁ ∘ nf₁) a • ([_] ∘ inv-nf₂ ∘ nf₂) b ≈⟨ refl ⟩
    [ inv-nf₁ (nf₁ a)]ₓ • [ inv-nf₂ (nf₂ b) ] ≈⟨ cong (fʷ-cong inv-nf₁∘nf₁=id) refl ⟩
    [ a ]ₓ • [ inv-nf₂ (nf₂ b) ] ≈⟨ cong refl ([]-cong inv-nf₂∘nf₂=id) ⟩
    [ a ]ₓ • [ b ] ≈⟨ sym (hᵗ-hyp ε w) ⟩
    [ I ] • w ≈⟨ refl ⟩
    ε • w ≈⟨ left-unit ⟩
    w ∎
    where
      open SR word-setoid₃

  nfp' : NormalForm (Γ ⋄ Δ ⋄ CommRel) (NF₁ × NF₂)
  nfp' = record
    { rightInverse = record
        { to        = nf
        ; from      = gg
        ; to-cong   = nf-cong
        ; from-cong = λ { Eq.refl → refl }
        ; inverseʳ  = λ { Eq.refl → ggnf=id }
        }
    }

module Presentation
  (G1 : Group 0ℓ 0ℓ)
  (G2 : Group 0ℓ 0ℓ)
  (p1 : Γ IsPresentationOf G1)
  (p2 : Δ IsPresentationOf G2)
  where

  private
    module P1 = _IsPresentationOf_ p1
    module P2 = _IsPresentationOf_ p2
    module H1 = Group G1
    module H2 = Group G2

    open GM.GroupMorphisms (Group.rawGroup P1.GL.•-ε-group) (Group.rawGroup G1)
      using () renaming (module IsGroupIsomorphism to IGI₁)
    open GM.GroupMorphisms (Group.rawGroup P2.GL.•-ε-group) (Group.rawGroup G2)
      using () renaming (module IsGroupIsomorphism to IGI₂)
    module Iso1 = IGI₁ P1.iso
    module Iso2 = IGI₂ P2.iso

  -- The direct product of the groups G1 and G2.
  dp : Group 0ℓ 0ℓ
  dp = ADP.group G1 G2

  private
    module D = Group dp

    nf-setoid : Setoid 0ℓ 0ℓ
    nf-setoid = PW.×-setoid word-setoid₁ Cₛ

  -- Interpretation of generators: left generators land in the first
  -- factor, right generators in the second.
  ⟦_⟧₀ : Y → Group.Carrier dp
  ⟦ inj₁ x ⟧₀ = P1.⟦ [ x ]ʷ ⟧ , H2.ε
  ⟦ inj₂ y ⟧₀ = H1.ε , P2.⟦ [ y ]ʷ ⟧

  private
    module GS = SP.GroupSem (Γ ⋄ Δ ⋄ CommRel) nf-setoid dp ⟦_⟧₀
  open GS using (⟦_⟧)

  -- The interpretation of a left- (resp. right-) embedded word is the
  -- factor interpretation in the first (resp. second) component.
  emb-l : ∀ w → D._≈_ ⟦ [ w ]ₗ ⟧ (P1.⟦ w ⟧ , H2.ε)
  emb-l [ x ]ʷ = D.refl
  emb-l ε       = H1.sym Iso1.ε-homo , H2.refl
  emb-l (w • v) =
    D.trans (D.∙-cong (emb-l w) (emb-l v))
      (H1.sym (Iso1.∙-homo w v) , H2.identityˡ H2.ε)

  emb-r : ∀ c → D._≈_ ⟦ [ c ]ᵣ ⟧ (H1.ε , P2.⟦ c ⟧)
  emb-r [ x ]ʷ = D.refl
  emb-r ε       = H1.refl , H2.sym Iso2.ε-homo
  emb-r (c • d) =
    D.trans (D.∙-cong (emb-r c) (emb-r d))
      (H1.identityˡ H1.ε , H2.sym (Iso2.∙-homo c d))

  emb-x : ∀ w → D._≈_ ⟦ [ w ]ₓ ⟧ (P1.⟦ w ⟧ , H2.ε)
  emb-x w rewrite aux-fʷ {w} | wconcatmap-[-]ʷ w = emb-l w

  -- ⟦_⟧ maps the axioms of the product presentation to equalities of dp.
  sound-ax : ∀ {u t} → (Γ ⋄ Δ ⋄ CommRel) u t → D._≈_ ⟦ u ⟧ ⟦ t ⟧
  sound-ax (left {u} {v} x) =
    D.trans (emb-l u)
      (D.trans (Iso1.⟦⟧-cong (_≈₁_.axiom x) , H2.refl) (D.sym (emb-l v)))
  sound-ax (right {u} {v} x) =
    D.trans (emb-r u)
      (D.trans (H1.refl , Iso2.⟦⟧-cong (_≈₂_.axiom x)) (D.sym (emb-r v)))
  sound-ax (mid (comm a b)) =
    D.trans (D.trans (D.∙-cong (emb-l [ a ]ʷ) (emb-r [ b ]ʷ))
                     (H1.identityʳ _ , H2.identityˡ _))
      (D.sym (D.trans (D.∙-cong (emb-r [ b ]ʷ) (emb-l [ a ]ʷ))
                      (H1.identityˡ _ , H2.identityʳ _)))

  -- Every generator of the product has a left inverse.
  grouplike : Grouplike (Γ ⋄ Δ ⋄ CommRel)
  grouplike (inj₁ a) = [ proj₁ (P1.gl a) ]ₗ , lefts (proj₂ (P1.gl a))
  grouplike (inj₂ b) = [ proj₁ (P2.gl b) ]ᵣ , rights (proj₂ (P2.gl b))

  -- The coset normal form, viewed as a setoid normal form.
  nfp : SNF.NormalForm (Γ ⋄ Δ ⋄ CommRel) nf-setoid
  nfp = record
    { rightInverse = record
        { to        = nf0
        ; from      = ⁻¹nf
        ; to-cong   = nf0-cong
        ; from-cong = ⁻¹nf-wd
        ; inverseʳ  = λ eq → _≈₃_.trans (⁻¹nf-wd eq) ⁻¹nf-nf=id
        }
    }

  -- The interpretation of an inverse normal form is the pair of factor
  -- interpretations.
  sem-⁻¹nf : ∀ a c → D._≈_ ⟦ ⁻¹nf (a , c) ⟧ (P1.⟦ a ⟧ , P2.⟦ c ⟧)
  sem-⁻¹nf a c =
    D.trans (D.∙-cong (emb-x a) (emb-r c)) (H1.identityʳ _ , H2.identityˡ _)

  -- Normal forms with equal denotations are equal, reducing factor by
  -- factor to injectivity of the two factor interpretations.
  unfp : SNF.UniqueNormalForm (Γ ⋄ Δ ⋄ CommRel) nf-setoid (Group.setoid dp) ⟦_⟧ nfp
  unfp = record
    { unique = λ { {a , c} {a' , c'} eq →
        let p = D.trans (D.sym (sem-⁻¹nf a c)) (D.trans eq (sem-⁻¹nf a' c'))
        in Iso1.injective (proj₁ p) , Iso2.injective (proj₂ p) } }

  -- The product presentation is a sub-presentation of dp.
  subPres : (Γ ⋄ Δ ⋄ CommRel) IsSubPresentationOf dp
  subPres = GS.GetSubPresentation.groupSubPres sound-ax grouplike nfp unfp

  private
    open import Normalization.StarInterp (Γ ⋄ Δ ⋄ CommRel)
    module E  = Extend (Group.monoid dp) ⟦_⟧₀
    module EC = E.Cong sound-ax

  -- ⟦_⟧ is onto: every pair is realised by a left word times a right
  -- word, using surjectivity of the two factors.
  surj : Surjective _≈₃_ D._≈_ ⟦_⟧
  surj (g1 , g2) =
    [ proj₁ s1 ]ₗ • [ proj₁ s2 ]ᵣ ,
    λ z≈w →
      D.trans (EC.fʷ-cong z≈w)
        (D.trans (D.∙-cong (emb-l (proj₁ s1)) (emb-r (proj₁ s2)))
          (D.trans (H1.identityʳ _ , H2.identityˡ _)
            (proj₂ s1 _≈₁_.refl , proj₂ s2 _≈₂_.refl)))
    where
    s1 = Iso1.surjective g1
    s2 = Iso2.surjective g2

  -- A surjective sub-presentation is a presentation.
  dpres : (Γ ⋄ Δ ⋄ CommRel) IsPresentationOf dp
  dpres = isPresentationOf subPres surj

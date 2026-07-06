------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal-form properties for direct products of group presentations.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Word.Base using (WRel)

module Presentation.Construct.Properties.DirectProduct
  {A B : Set}
  (Γ : WRel A)
  (Δ : WRel B)
  where

open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_)
import Function.Construct.Composition as FCC
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; inspect) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Base as PB
open import Presentation.Construct.Base
open import Presentation.Properties as PP
open import Normalization.Base using (NormalForm ; NormalFormWithoutInverse)
open import Presentation.Reidemeister-Schreier
open import Word.Base
open import Word.Properties

open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()
open PB (Γ ⸲ Δ ⸲ Γₓ) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_) using ()
open PP (Γ ⸲ Δ ⸲ Γₓ) renaming (•-ε-monoid to m₃ ; word-setoid to word-setoid₃) using ()

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

open Star-Injective-Full-Setoid Γ (Γ ⸲ Δ ⸲ Γₓ) Cₛ I renaming (nf to coset-nf)

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

-- The fold (h **) leaves a left-embedded word untouched.
lemma-h**-left' : ∀ c {w} → (h **) c [ w ]ₗ ≡ (w , c)
lemma-h**-left' c {[ x ]ʷ} = Eq.refl
lemma-h**-left' c {ε} = Eq.refl
lemma-h**-left' c {w • w₁}
  rewrite lemma-h**-left' c {w} | lemma-h**-left' c {w₁} = Eq.refl

-- Setoid version of lemma-h**-left'.
lemma-h**-left : ∀ c {w} → (h **) c [ w ]ₗ ~ (w , c)
lemma-h**-left c {[ x ]ʷ} = _≈₁_.refl , _≈₂_.refl
lemma-h**-left c {ε} = _≈₁_.refl , _≈₂_.refl
lemma-h**-left c {w • w₁}
  with (h **) c [ w ]ₗ | inspect ((h **) c) [ w ]ₗ
... | (w' , c') | [ eq1 ]'
  with (h **) c' [ w₁ ]ₗ | inspect ((h **) c') [ w₁ ]ₗ
... | (w₁' , c'') | [ eq2 ]'
  with lemma-h**-left c {w} | lemma-h**-left c' {w₁}
... | ih1 | ih2 rewrite eq1 | eq2 =
  (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) ,
  _≈₂_.trans (ih2 .proj₂) (ih1 .proj₂)

-- The fold (h **) absorbs a right-embedded word into the coset.
lemma-h**-right : ∀ c {w} → (h **) c [ w ]ᵣ ~ (ε , c • w)
lemma-h**-right c {[ x ]ʷ} = _≈₁_.refl , _≈₂_.refl
lemma-h**-right c {ε} = _≈₁_.refl , _≈₂_.sym _≈₂_.right-unit
lemma-h**-right c {w • w₁}
  with (h **) c [ w ]ᵣ | inspect ((h **) c) [ w ]ᵣ
... | (w' , c') | [ eq1 ]'
  with (h **) c' [ w₁ ]ᵣ | inspect ((h **) c') [ w₁ ]ᵣ
... | (w₁' , c'') | [ eq2 ]'
  with lemma-h**-right c {w} | lemma-h**-right c' {w₁}
... | ih1 | ih2 rewrite eq1 | eq2 =
  (_≈₁_.trans (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) _≈₁_.right-unit) ,
  _≈₂_.trans (ih2 .proj₂)
    (_≈₂_.trans (_≈₂_.cong (ih1 .proj₂) _≈₂_.refl) _≈₂_.assoc)

-- The coset table respects the coset setoid.
h-congₛ-gen : ∀ {c d} y → c ≈ₛ d → h c y ~ h d y
h-congₛ-gen {c} {d} (inj₁ x) eq
  rewrite lemma-h**-left' c {[ x ]ʷ} | lemma-h**-left' d {[ x ]ʷ}
  = _≈₁_.refl , eq
h-congₛ-gen {c} {d} (inj₂ y) eq =
  trans~ (lemma-h**-right c {[ y ]ʷ})
    (trans~ (_≈₁_.refl , _≈₂_.cong eq (_≈₂_.refl))
      (sym~ (lemma-h**-right d {[ y ]ʷ})))

-- On generators, (h **) started at the initial coset inverts f.
h=⁻¹f-gen : ∀ (x : A) → ([ x ]ʷ , I) ~ ((h **) I (f x))
h=⁻¹f-gen x = refl~

-- (h **) is well defined on the axioms of the product; the mid case
-- is the commutation of left and right generators.
h-wd : ∀ (c : C){u t : Word Y} → u ===₃ t → ((h **) c u) ~ ((h **) c t)
h-wd c {u} {t} (left x) =
  trans~ (lemma-h**-left c)
    (trans~ ((_≈₁_.axiom x) , reflₛ) (sym~ (lemma-h**-left c)))
h-wd c {u} {t} (right x) =
  trans~ (lemma-h**-right c)
    (trans~ (_≈₁_.refl , _≈₂_.cong _≈₂_.refl (_≈₂_.axiom x))
      (sym~ (lemma-h**-right c)))
h-wd c {u} {t} (mid (comm a b)) =
  _≈₁_.trans _≈₁_.right-unit (_≈₁_.sym _≈₁_.left-unit) , reflₛ

-- Instantiate the Reidemeister-Schreier machinery.
open Reidemeister-Schreier-Full f h h-congₛ-gen h=⁻¹f-gen h-wd

------------------------------------------------------------------------
-- Commutation and coset lemmas

-- The extension of f is the left embedding.
aux-f* : ∀ {w} → (f *) w ≡ [ ([_]ʷ *) w ]ₗ
aux-f* {[ x ]ʷ} = Eq.refl
aux-f* {ε} = Eq.refl
aux-f* {w • w₁} rewrite aux-f* {w} | aux-f* {w₁} = Eq.refl

-- f maps the axioms of Γ to equalities of the product.
f-well-defined : ∀ {w v} → w ===₁ v → (f *) w ≈₃ (f *) v
f-well-defined {w} {v} ax
  rewrite aux-f* {w} | aux-f* {v} | wconcatmap-[-]ʷ w | wconcatmap-[-]ʷ v
  = axiom (left ax)

-- The initial coset is represented by the unit.
[I]≈ε : [ I ] ≈₃ ε
[I]≈ε = _≈₃_.refl

-- The coset table, viewed as a right action.
ract = h

-- Embedding of the emitted word into the product.
[_]ₓ = f *

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
lemma-ract c (inj₁ x₁)
  rewrite lemma-h**-left' c {[ x₁ ]ʷ} = lemma-comm [ x₁ ]ʷ c
lemma-ract c (inj₂ y) = _≈₃_.sym _≈₃_.left-unit

open LeftRightCongruence Γ Δ Γₓ

-- The section respects the coset setoid.
[]-cong : ∀ {c d} → c ≈ₛ d → [ c ] ≈₃ [ d ]
[]-cong = rights

open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε
  lemma-ract hiding ([_]ₓ)

-- The coset-pair normal form: split a word over A ⊎ B into a word
-- over A and a coset representative in Word B.
nf0 = (coset-nf f h h-congₛ-gen)

nf0-cong : ∀ {w v} → w ≈₃ v → nf0 w ~ nf0 v
nf0-cong {w} {v} = lemma-hypB I w v

------------------------------------------------------------------------
-- Lifting normal forms without inverse
--
-- Given normal forms without inverse for the two factors, the pair of
-- normal forms is a normal form for the direct product.

module NFP
  (nfp-Γ : NormalFormWithoutInverse Γ)
  (nfp-Δ : NormalFormWithoutInverse Δ)
  where

  open NormalFormWithoutInverse nfp-Γ
    renaming (NF to NF₁ ; nf to nf₁ ;
              nf-injective to nf₁-inj ; nf-cong to nf₁-cong)
    using ()
  open NormalFormWithoutInverse nfp-Δ
    renaming (NF to NF₂ ; nf to nf₂ ;
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

  nfp : NormalFormWithoutInverse (Γ ⸲ Δ ⸲ Γₓ)
  nfp = record
    { NF           = NF₁ × NF₂
    ; nf           = nf
    ; nf-cong      = nf-cong
    ; nf-injective = nf-inj
    }

------------------------------------------------------------------------
-- Lifting normal forms
--
-- Given normal forms with inverse for the two factors, the pair
-- normal form again has an inverse, obtained by embedding and
-- multiplying the two inverses.

module NFP'
  (nfp-Γ : NormalForm Γ)
  (nfp-Δ : NormalForm Δ)
  where

  open NormalForm nfp-Γ
    renaming (hasNormalFormWithoutInverse to nfp-Γ' ; NF to NF₁ ;
              nf to nf₁ ; nf-injective to nf₁-inj ; nf-cong to nf₁-cong ;
              inv-nf to inv-nf₁ ; inv-nf∘nf=id to inv-nf₁∘nf₁=id)
    using ()
  open NormalForm nfp-Δ
    renaming (hasNormalFormWithoutInverse to nfp-Δ' ; NF to NF₂ ;
              nf to nf₂ ; nf-injective to nf₂-inj ; nf-cong to nf₂-cong ;
              inv-nf to inv-nf₂ ; inv-nf∘nf=id to inv-nf₂∘nf₂=id)
    using ()

  open NFP nfp-Γ' nfp-Δ' using (nfp)
  open NormalFormWithoutInverse nfp

  -- The inverse of the pair normal form: embed both components and
  -- multiply.
  gg : NF₁ × NF₂ → Word Y
  gg (a , b) = ([_]ₓ ∘ inv-nf₁) a • ([_] ∘ inv-nf₂) b

  -- Soundness of the iterated coset action.
  h**-hyp : ∀ c b → let (b' , c') = (ract **) c b in
      [ c ] • b ≈₃ [ b' ]ₓ • [ c' ]
  h**-hyp c b =
    Star-Injective-Full.RightAction.lemma-⊛
      Γ (Γ ⸲ Δ ⸲ Γₓ) C I f h f-well-defined [_] [I]≈ε lemma-ract c b

  -- The extension of f respects Γ-equivalence.
  f*-cong : ∀ {w v} → w ≈₁ v → (f *) w ≈₃ (f *) v
  f*-cong {w} {v} eq =
    Star-Congruence.lemma-f*-cong Γ (Γ ⸲ Δ ⸲ Γₓ) f f-well-defined eq

  -- gg is a left inverse of the pair normal form.
  ggnf=id : {w : Word Y} → gg (nf w) ≈₃ w
  ggnf=id {w} =
    let (a , b) = nf0 w in
    begin
    gg (nf w) ≈⟨ refl ⟩
    gg ((map nf₁ nf₂) (a , b)) ≈⟨ refl ⟩
    gg (nf₁ a , nf₂ b) ≈⟨ refl ⟩
    ([_]ₓ ∘ inv-nf₁ ∘ nf₁) a • ([_] ∘ inv-nf₂ ∘ nf₂) b ≈⟨ refl ⟩
    [ inv-nf₁ (nf₁ a)]ₓ • [ inv-nf₂ (nf₂ b) ] ≈⟨ cong (f*-cong inv-nf₁∘nf₁=id) refl ⟩
    [ a ]ₓ • [ inv-nf₂ (nf₂ b) ] ≈⟨ cong refl ([]-cong inv-nf₂∘nf₂=id) ⟩
    [ a ]ₓ • [ b ] ≈⟨ sym (h**-hyp ε w) ⟩
    [ I ] • w ≈⟨ refl ⟩
    ε • w ≈⟨ left-unit ⟩
    w ∎
    where
      open SR word-setoid₃

  nfp' : NormalForm (Γ ⸲ Δ ⸲ Γₓ)
  nfp' = record
           { NF = NF ; nf = nf ; nf-cong = nf-cong ; inv-nf = gg ; inv-nf∘nf=id = ggnf=id }


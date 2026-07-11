------------------------------------------------------------------------
-- Presentations of groups
--
-- Normal-form properties for semi-direct products, via the setoid
-- variant of Reidemeister-Schreier: cosets are words over H up to
-- ≈, and the H-action on N is word-valued (the relation ConjRelʷ conj).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Word.Base

-- The parameter `conj h n` gives the word over N to which the
-- H-generator h conjugates the N-generator n.

module Presentation.Construct.Properties.SemiDirectProduct2
  {N H : Set}
  (Γ : WRel N)
  (Δ : WRel H)
  (conj : H → N → Word N)
  where

open import Data.Product using (_,_ ; _×_ ; map ; proj₁ ; proj₂)
import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_)
import Function.Construct.Composition as FCC
open import Function.Definitions using (Injective ; Surjective)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; inspect) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR

import Presentation.Base as PB
open import Presentation.Construct.Base
open import Presentation.Properties as PP
open import Normalization.NormalForm.Propositional using (NormalForm ; NormalFormInjective)
import Normalization.NormalForm.Setoid as SNF
open import Normalization.Reidemeister-Schreier
open import Word.Properties

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Level using (0ℓ)
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)
open import Presentation.GroupLike using (Grouplike)
import ForStdlib.Algebra.Construct.SemiDirectProduct as SDP
import Normalization.StarPresentation

open PB Γ renaming
  (_===_ to _===₁_ ; _≈_ to _≈₁_ ; refl to refl₁ ; sym to sym₁ ;
   trans to trans₁ ; cong to cong₁ ; left-unit to left-unit₁ ;
   right-unit to right-unit₁ ; refl' to refl'₁)
  using ()
open PP Γ renaming (word-setoid to word-setoid₁) using ()
open PB Δ renaming
  (_===_ to _===₂_ ; _≈_ to _≈₂_ ; axiom to axiom₂ ; refl to refl₂ ;
   sym to sym₂ ; cong to cong₂ ; right-unit to right-unit₂ ;
   left-unit to left-unit₂ ; assoc to assoc₂)
  using ()
open PP Δ renaming (word-setoid to word-setoid₂) using ()

open PB (Γ ⋄ Δ ⋄ ConjRelʷ conj) renaming
  (_===_ to _===₃_ ; _≈_ to _≈₃_ ; refl' to refl'₃)
  using ()
open PP (Γ ⋄ Δ ⋄ ConjRelʷ conj) renaming (word-setoid to word-setoid₃) using ()

open _≈₃_

------------------------------------------------------------------------
-- Setup

-- Cosets are words over H, compared up to ≈₂ (a setoid of cosets).
Cₛ = word-setoid₂

-- The initial coset: the empty word.
I : Word H
I = ε

-- The generators of the semi-direct product.
Y = N ⊎ H

open Star-Injective-Full-Setoid Γ (Γ ⋄ Δ ⋄ ConjRelʷ conj) Cₛ I

-- The section embedding a coset back into the product.
[_] : C → Word Y
[_] = [_]ᵣ

-- The embedding of the N-generators into the product.
f : N → Word Y
f x = [ [ x ]ʷ ]ₗ

-- The conjugation action of an H-generator, extended to words over N.
conjs : H → Word N → Word N
conjs = conj ⁿ'

-- The conjugation action, extended to words in both arguments.
conjss : Word H → Word N → Word N
conjss = conj ʰ'

-- The two hypotheses assert that the conjugation action respects the
-- Δ-axioms in its left argument (conj-hyph) and the Γ-axioms in its
-- right argument (conj-hypn).
module _
  (conj-hyph : ∀ {c d} n → c ===₂ d → (conj ʰ') c n ≈₁ (conj ʰ') d n)
  (conj-hypn : ∀ c {w v} → w ===₁ v → (conj ⁿ') c w ≈₁ (conj ⁿ') c v)
  where

------------------------------------------------------------------------
-- The conjugation action

  conj-congN : ∀ h {ns ns'} → ns ≈₁ ns' → conjs h ns ≈₁ conjs h ns'
  conj-congN h {ns} {ns'} refl = _≈₁_.refl
  conj-congN h {ns} {ns'} (sym eq) = _≈₁_.sym (conj-congN h eq)
  conj-congN h {ns} {ns'} (trans eq eqₕ) = _≈₁_.trans (conj-congN h eq) (conj-congN h eqₕ)
  conj-congN h {ns} {ns'} (cong eq eqₕ) = (_≈₁_.cong (conj-congN h eq) (conj-congN h eqₕ))
  conj-congN h {ns} {ns'} assoc = _≈₁_.assoc
  conj-congN h {ns} {ns'} left-unit =  _≈₁_.left-unit
  conj-congN h {ns} {ns'} right-unit =  _≈₁_.right-unit
  conj-congN h {ns} {ns'} (axiom x) = conj-hypn h x

  conj-congNH : ∀ h {ns ns'} → ns ≈₁ ns' → conjss h ns ≈₁ conjss h ns'
  conj-congNH [ x ]ʷ {ns} {ns'} eq = conj-congN x eq
  conj-congNH ε {ns} {ns'} eq = eq
  conj-congNH (h • h₁) {ns} {ns'} eq = conj-congNH h ih1
    where
    ih1 : conjss h₁ ns ≈₁ conjss h₁ ns'
    ih1 = conj-congNH h₁ {ns} {ns'} eq

  lemma-conjss-ε : ∀ n → conjss ε n ≡ n
  lemma-conjss-ε [ x ]ʷ = Eq.refl
  lemma-conjss-ε ε = Eq.refl
  lemma-conjss-ε (n • n₁) = Eq.refl

  conjss-homo : ∀ c w v → conjss c (w • v) ≡ conjss c w • conjss c v
  conjss-homo [ x ]ʷ w v = Eq.refl
  conjss-homo ε w v = Eq.refl
  conjss-homo (c • c₁) w v with conjss-homo c₁ w v
  ... | ih with conjss-homo c (conjss c₁ w) (conjss c₁ v)
  ... | ih2 rewrite ih = ih2

  conjss-c-ε=ε : ∀ c → conjss c ε ≡ ε
  conjss-c-ε=ε [ x ]ʷ = Eq.refl
  conjss-c-ε=ε ε = Eq.refl
  conjss-c-ε=ε (c • c₁) with conjss-c-ε=ε c₁
  ... | ih1 rewrite ih1 with conjss-c-ε=ε c
  ... | ih2 = ih2

  mutual
    conj-congH : ∀ {h1 h2} ns → h1 ≈₂ h2 → conjss h1 ns ≈₁ conjss h2 ns
    conj-congH {h1} {h2} ns PB.refl = refl₁
    conj-congH {h1} {h2} ns (PB.sym eq) = sym₁ (conj-congH ns eq)
    conj-congH {h1} {h2} ns (PB.trans eq eq₁) = trans₁ (conj-congH ns eq) (conj-congH ns eq₁)
    conj-congH {h1} {h2} ns (PB.cong eq eq₁) = conjss-cong eq (conj-congH ns eq₁)
    conj-congH {h1} {h2} ns PB.assoc = refl₁
    conj-congH {h1} {h2} ns PB.left-unit = refl₁
    conj-congH {h1} {h2} ns PB.right-unit = refl₁
    conj-congH {h1} {h2} ns (PB.axiom x) = conj-hyph ns x

    conjss-cong : ∀ {hs hs' ns ns'} → hs ≈₂ hs' → ns ≈₁ ns' → conjss hs ns ≈₁ conjss hs' ns'
    conjss-cong {hs} {hs'} {ns} {ns'} eqh eqn = begin
      conjss hs ns ≈⟨ conj-congH ns eqh ⟩
      conjss hs' ns ≈⟨ conj-congNH hs' eqn ⟩
      conjss hs' ns' ∎
      where
        open SR word-setoid₁

------------------------------------------------------------------------
-- The coset action

  -- The coset table: an N-generator emits its conjugated word and
  -- keeps the coset; an H-generator emits ε and extends the coset.
  h : C → Y → Word N × C
  h c (inj₁ x) = conjss c [ x ]ʷ , c
  h c (inj₂ y) = ε , (c • [ y ]ʷ)

  h-congₛ-gen-gen : ∀ {c d} y → c ===₂ d → h c y ~ h d y
  h-congₛ-gen-gen {c} {d} (inj₁ x) eq = conjss-cong (axiom₂ eq) refl₁ , (axiom₂ eq)
  h-congₛ-gen-gen {c} {d} (inj₂ y) eq = refl₁ , (cong₂ (axiom₂ eq) refl₂)

  h-congₛ-gen : ∀ {c d} y → c ≈ₛ d → h c y ~ h d y
  h-congₛ-gen {c} {d} y refl = refl~
  h-congₛ-gen {c} {d} y (sym eq) = sym~ (h-congₛ-gen y eq)
  h-congₛ-gen {c} {d} y (trans eq eq₁) = trans~ (h-congₛ-gen y eq) (h-congₛ-gen y eq₁)
  h-congₛ-gen {c} {d} y (axiom x) = h-congₛ-gen-gen y x
  h-congₛ-gen (inj₁ x₂) (PB.cong x x₁) = conjss-cong x (conjss-cong x₁ refl₁) , (cong₂ x x₁)
  h-congₛ-gen (inj₂ y) (PB.cong x x₁) = refl₁ , cong₂ (cong₂ x x₁) refl₂
  h-congₛ-gen (inj₁ x) PB.assoc = refl₁ , assoc₂
  h-congₛ-gen (inj₂ y) PB.assoc = refl₁ , cong₂ assoc₂ refl₂
  h-congₛ-gen (inj₁ x) PB.left-unit = refl₁ , left-unit₂
  h-congₛ-gen (inj₂ y) PB.left-unit = refl₁ , cong₂ left-unit₂ refl₂
  h-congₛ-gen (inj₁ x) PB.right-unit = refl₁ , right-unit₂
  h-congₛ-gen (inj₂ y) PB.right-unit = refl₁ , cong₂ right-unit₂ refl₂

  lemma-hᵗ-left' : ∀ c {w} → (h ᵗ) c [ w ]ₗ ≡ (conjss c w , c)
  lemma-hᵗ-left' c {[ x ]ʷ} = Eq.refl
  lemma-hᵗ-left' c {ε} = PW.≡×≡⇒≡ ((Eq.sym (conjss-c-ε=ε c)) , Eq.refl)
  lemma-hᵗ-left' c {w • w₁} rewrite lemma-hᵗ-left' c {w} | lemma-hᵗ-left' c {w₁} = PW.≡×≡⇒≡ ((Eq.sym (conjss-homo c w w₁)) , Eq.refl)

  lemma-hᵗ-left : ∀ c {w} → (h ᵗ) c [ w ]ₗ ~ (conjss c w , c)
  lemma-hᵗ-left c {w} with lemma-hᵗ-left' c {w}
  ... | ih rewrite ih = _≈₁_.refl , _≈₂_.refl

  lemma-hᵗ-right : ∀ c {w} → (h ᵗ) c [ w ]ᵣ ~ (ε , c • w)
  lemma-hᵗ-right c {[ x ]ʷ} = _≈₁_.refl , _≈₂_.refl
  lemma-hᵗ-right c {ε} = _≈₁_.refl , _≈₂_.sym _≈₂_.right-unit
  lemma-hᵗ-right c {w • w₁} with (h ᵗ) c [ w ]ᵣ | inspect ((h ᵗ) c) [ w ]ᵣ
  ... | (w' , c') | [ eq1 ]' with (h ᵗ) c' [ w₁ ]ᵣ | inspect ((h ᵗ) c') [ w₁ ]ᵣ
  ... | (w₁' , c'') | [ eq2 ]' with lemma-hᵗ-right c {w} | lemma-hᵗ-right c' {w₁}
  ... | ih1 | ih2 rewrite eq1 | eq2 =
    (_≈₁_.trans (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) _≈₁_.right-unit) ,
    _≈₂_.trans (ih2 .proj₂)
      (_≈₂_.trans (_≈₂_.cong (ih1 .proj₂) _≈₂_.refl) _≈₂_.assoc)

  h=⁻¹f-gen : ∀ (x : N) → ([ x ]ʷ , I) ~ ((h ᵗ) I (f x))
  h=⁻¹f-gen x = refl~

  h-wd : ∀ (c : C){u t : Word Y} → u ===₃ t → ((h ᵗ) c u) ~ ((h ᵗ) c t)
  h-wd c {u} {t} (left {u₁} {v} x) rewrite lemma-hᵗ-left' c {u₁} | lemma-hᵗ-left' c {v} = conj-congNH c (_≈₁_.axiom x) , _≈₂_.refl
  h-wd c {u} {t} (right {w} {v} x) = trans~ (lemma-hᵗ-right c {w}) (trans~ (_≈₁_.refl , _≈₂_.cong _≈₂_.refl (_≈₂_.axiom x)) (sym~ (lemma-hᵗ-right c {v})))
  h-wd c {u} {t} (mid (comm a b)) =
    let (w1 , c1) = (h ᵗ) c ([ conj b a ]ₗ) in
    let (w2 , c2) = (h ᵗ) c1 [ inj₂ b ]ʷ in
    let (w3 , c3) = (h ᵗ) c [ inj₂ b ]ʷ in
    let (eq1 , eq2) = lemma-hᵗ-left c {(conj b a)} in begin
    (h ᵗ) c ([ inj₂ b ]ʷ • [ inj₁ a ]ʷ) ≈⟨ left-unit₁ , refl₂ ⟩
    (h ᵗ) (c • [ b ]ʷ) ([ inj₁ a ]ʷ) ≈⟨ lemma-hᵗ-left (c • [ b ]ʷ) ⟩
    (conjss (c • [ b ]ʷ) [ a ]ʷ , c • [ b ]ʷ) ≈⟨ sym₁ right-unit₁ , refl₂ ⟩
    (conjss c (conj b a) • (ε) , c • [ b ]ʷ) ≈⟨ cong₁ (sym₁ eq1) refl₁ , cong₂ (sym₂ eq2) refl₂ ⟩
    (h ᵗ) c ([ conj b a ]ₗ • [ inj₂ b ]ʷ) ∎
      where
        open SR setoid-WX-Cₛ

  open Reidemeister-Schreier-Full f h h-congₛ-gen h=⁻¹f-gen h-wd

  aux-fʷ : ∀ {w} → (f ʷ) w ≡ [ ([_]ʷ ʷ) w ]ₗ
  aux-fʷ {[ x ]ʷ} = Eq.refl
  aux-fʷ {ε} = Eq.refl
  aux-fʷ {w • w₁} rewrite aux-fʷ {w} | aux-fʷ {w₁} = Eq.refl

  f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₃ (f ʷ) v
  f-well-defined {w} {v} ax rewrite aux-fʷ {w} | aux-fʷ {v} | wconcatmap-[-]ʷ w | wconcatmap-[-]ʷ v = _≈₃_.axiom (left ax)

  [I]≈ε : [ I ] ≈₃ ε
  [I]≈ε = _≈₃_.refl

  ract = h

  [_]ₓ = f ʷ

  aux-fʷ' : ∀ {w} → [ w ]ₓ ≡ [ w ]ₗ
  aux-fʷ' {[ x ]ʷ} = Eq.refl
  aux-fʷ' {ε} = Eq.refl
  aux-fʷ' {w • w₁} rewrite aux-fʷ' {w} | aux-fʷ' {w₁} = Eq.refl

------------------------------------------------------------------------
-- Commutation lemmas

  -- The semi-direct commutation relation [v]ᵣ • [w]ₗ ≈ [conj v w]ₗ •
  -- [v]ᵣ, lifted from generators to words: first in the N-argument
  -- (lemma-comm1), then in both arguments (lemma-comm).
  lemma-comm1 : ∀ x w → [ [ x ]ʷ ]ᵣ • [ w ]ₗ ≈₃ [ conjs x w ]ₗ • [ [ x ]ʷ ]ᵣ
  lemma-comm1 x [ x₁ ]ʷ = (_≈₃_.axiom (mid (comm x₁ x)))
  lemma-comm1 x ε = _≈₃_.trans _≈₃_.right-unit (_≈₃_.sym _≈₃_.left-unit)
  lemma-comm1 x (w • w₁) with lemma-comm1 x w | lemma-comm1 x w₁
  ... | ih1 | ih2 =
    _≈₃_.trans (_≈₃_.sym _≈₃_.assoc )
      (_≈₃_.trans (_≈₃_.cong ih1 _≈₃_.refl)
        (_≈₃_.trans _≈₃_.assoc
          (_≈₃_.trans (_≈₃_.cong _≈₃_.refl ih2) (_≈₃_.sym _≈₃_.assoc)) ) )

  lemma-comm : ∀ w v → [ v ]ᵣ • [ w ]ₗ ≈₃ [ conjss v w ]ₗ • [ v ]ᵣ
  lemma-comm w [ x ]ʷ = lemma-comm1 x w
  lemma-comm w ε = _≈₃_.trans _≈₃_.left-unit (_≈₃_.sym _≈₃_.right-unit)
  lemma-comm w (v • v₁) with lemma-comm w v₁
  ... | ih2 with lemma-comm (conjss v₁ w) v
  ... | ih1 =
    _≈₃_.sym
      (_≈₃_.trans (_≈₃_.sym _≈₃_.assoc )
        (_≈₃_.trans (_≈₃_.cong (_≈₃_.sym ih1) _≈₃_.refl)
          (_≈₃_.trans _≈₃_.assoc
            (_≈₃_.trans (_≈₃_.cong _≈₃_.refl (_≈₃_.sym ih2))
              (_≈₃_.sym _≈₃_.assoc)) ) ))

  lemma-ract : ∀ c y → let (y' , c') = ract c y in [ c ] • [ y ]ʷ ≈₃ [ y' ]ₓ • [ c' ]
  lemma-ract c y@(inj₁ x₁) = begin
    [ c ]ᵣ • [ y ]ʷ ≈⟨ lemma-comm [ x₁ ]ʷ c ⟩
    [ conjss c [ x₁ ]ʷ ]ₗ • [ c ]ᵣ ≈⟨ cong (refl'₃ (Eq.sym (aux-fʷ' {conjss c [ x₁ ]ʷ}))) refl ⟩
    [ conjss c [ x₁ ]ʷ ]ₓ • [ c ] ∎
    where open SR word-setoid₃
  lemma-ract c (inj₂ y) = _≈₃_.sym _≈₃_.left-unit

  []-cong : ∀ {c d} → c ≈ₛ d → [ c ] ≈₃ [ d ]
  []-cong {c} {d} refl = _≈₃_.refl
  []-cong {c} {d} (sym eqv) = _≈₃_.sym ([]-cong eqv)
  []-cong {c} {d} (trans eqv eqv₁) = _≈₃_.trans ([]-cong eqv) ([]-cong eqv₁)
  []-cong {c} {d} (cong eqv eqv₁) = _≈₃_.cong ([]-cong eqv) ([]-cong eqv₁)
  []-cong {c} {d} assoc = _≈₃_.assoc
  []-cong {c} {d} left-unit = _≈₃_.left-unit
  []-cong {c} {d} right-unit = _≈₃_.right-unit
  []-cong {c} {d} (axiom x) = _≈₃_.axiom (right x)

  open RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε
    lemma-ract
    renaming (nf to anf ; nf-isInjective' to nf0-inj) hiding ([_]ₓ)

------------------------------------------------------------------------
-- Normal forms

  -- The first stage of the normal form: a pair of a word over N and a
  -- coset, obtained from the Reidemeister-Schreier construction.
  nf0 = anf

  -- Builds a NormalFormInjective for the semi-direct product from
  -- NormalFormInjective witnesses for the two factors.
  module NFP
    {NF₁ NF₂ : Set}
    (nfp-Γ : NormalFormInjective Γ NF₁)
    (nfp-Δ : NormalFormInjective Δ NF₂)
    where

    open SNF.NormalFormInjective nfp-Γ renaming
      (nf to nf₁ ; nf-injective to nf₁-inj ;
       nf-cong to nf₁-cong)
      using ()
    open SNF.NormalFormInjective nfp-Δ renaming
      (nf to nf₂ ; nf-injective to nf₂-inj ;
       nf-cong to nf₂-cong)
      using ()

    -- The second stage: normalise each component of nf0.
    nf : Word Y → NF₁ × NF₂
    nf = map nf₁ nf₂ ∘ nf0

    nf-inj× : Injective _≈₃_ (PW.Pointwise _≡_ _≡_) nf
    nf-inj× {w} {v} =
      FCC.injective _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-inj
        (map nf₁-inj nf₂-inj)

    nf-inj : Injective _≈₃_ _≡_ nf
    nf-inj {w} {v} = FCC.injective _≈₃_ (PW.Pointwise _≡_ _≡_) _≡_ nf-inj× PW.≡⇒≡×≡

    nf0-cong : ∀ {w v} → w ≈₃ v → nf0 w ~ nf0 v
    nf0-cong {w} {v} = lemma-hypB I w v

    nf-cong : ∀ {w v} → w ≈₃ v → nf w ≡ nf v
    nf-cong {w} {v} eq =
      PW.≡×≡⇒≡
        (FCC.congruent _≈₃_ _~_ (PW.Pointwise _≡_ _≡_) nf0-cong
          (map nf₁-cong nf₂-cong) eq)

    -- The headline export: a normal form (without inverse) for the
    -- semi-direct product.
    nfp : NormalFormInjective (Γ ⋄ Δ ⋄ ConjRelʷ conj) (NF₁ × NF₂)
    nfp = record { injection = record { to = nf ; cong = nf-cong ; injective = nf-inj } }

  -- Builds a NormalForm (with inverse) for the semi-direct product
  -- from NormalForm witnesses for the two factors.
  module NFP'
    {NF₁ NF₂ : Set}
    (nfp-Γ : NormalForm Γ NF₁)
    (nfp-Δ : NormalForm Δ NF₂)
    where

    open SNF.NormalForm nfp-Γ renaming
      (normalFormInjective to nfp-Γ' ; nf to nf₁ ;
       nf-injective to nf₁-inj ; nf-cong to nf₁-cong ;
       inv-nf to inv-nf₁ ; inv-nf∘nf=id to inv-nf₁∘nf₁=id)
      using ()
    open SNF.NormalForm nfp-Δ renaming
      (normalFormInjective to nfp-Δ' ; nf to nf₂ ;
       nf-injective to nf₂-inj ; nf-cong to nf₂-cong ;
       inv-nf to inv-nf₂ ; inv-nf∘nf=id to inv-nf₂∘nf₂=id)
      using ()

    open NFP nfp-Γ' nfp-Δ' using (nfp)
    open SNF.NormalFormInjective nfp

    -- The inverse normal form, assembled from the factors' inv-nf
    -- functions.
    gg : NF₁ × NF₂ → Word Y
    gg (a , b) = ([_]ₓ ∘ inv-nf₁) a • ([_] ∘ inv-nf₂) b

    hᵗ-hyp : ∀ c b → let (b' , c') = (ract ᵗ) c b in
        [ c ] • b ≈₃ [ b' ]ₓ • [ c' ]
    hᵗ-hyp c b =
      Star-Injective-Full.RightAction.lemma-⊛ Γ (Γ ⋄ Δ ⋄ ConjRelʷ conj) C I
        f h f-well-defined [_] [I]≈ε lemma-ract c b

    fʷ-cong : ∀ {w v} → w ≈₁ v → (f ʷ) w ≈₃ (f ʷ) v
    fʷ-cong {w} {v} eq =
      PP.StarCongruence.fʷ-cong Γ (Γ ⋄ Δ ⋄ ConjRelʷ conj) f
        f-well-defined eq

    -- gg is a left inverse of nf, up to ≈₃.
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

    -- The headline export: a normal form (with inverse) for the
    -- semi-direct product.
    nfp' : NormalForm (Γ ⋄ Δ ⋄ ConjRelʷ conj) (NF₁ × NF₂)
    nfp' = record
      { rightInverse = record
          { to        = nf
          ; from      = gg
          ; to-cong   = nf-cong
          ; from-cong = λ { Eq.refl → refl }
          ; inverseʳ  = λ { Eq.refl → ggnf=id }
          }
      }



------------------------------------------------------------------------
-- Presentation of the semi-direct product group
--
-- If Γ presents G1 and Δ presents G2, then Γ ⋄ Δ ⋄ ConjRelʷ conj
-- presents the semi-direct product G1 ⋊ G2, where G2 acts on G1 by
-- transporting the word-level conjugation action conjss through the two
-- presentation isomorphisms.  (Lives inside the conj-hyph/conj-hypn
-- block so the action-congruence lemmas are in scope.)

  module Presentation
    (G1 : Group 0ℓ 0ℓ)
    (G2 : Group 0ℓ 0ℓ)
    (p1 : Γ IsPresentationOf G1)
    (p2 : Δ IsPresentationOf G2)
    where

    open Group G1 using ()
      renaming (Carrier to |G1| ; _≈_ to _≈G1_ ; _∙_ to _∙G1_ ; ε to εG1 ;
                trans to transG1 ; sym to symG1 ; ∙-cong to ∙-congG1)
    open Group G2 using ()
      renaming (Carrier to |G2| ; _≈_ to _≈G2_ ; _∙_ to _∙G2_ ; ε to εG2 ;
                trans to transG2 ; sym to symG2 ; ∙-cong to ∙-congG2)

    private
      module P1 = _IsPresentationOf_ p1
      module P2 = _IsPresentationOf_ p2
      module I1 = GroupMorphisms.IsGroupIsomorphism P1.iso
      module I2 = GroupMorphisms.IsGroupIsomorphism P2.iso

    -- The presentation isomorphisms and their (up-to-≈) section inverses.
    ⟦_⟧₁ : Word N → |G1|
    ⟦_⟧₁ = P1.⟦_⟧
    ⟦_⟧₂ : Word H → |G2|
    ⟦_⟧₂ = P2.⟦_⟧

    inv₁ : |G1| → Word N
    inv₁ g = proj₁ (I1.surjective g)
    inv₂ : |G2| → Word H
    inv₂ g = proj₁ (I2.surjective g)

    inv₁-corr : ∀ g → ⟦ inv₁ g ⟧₁ ≈G1 g
    inv₁-corr g = proj₂ (I1.surjective g) refl₁
    inv₂-corr : ∀ g → ⟦ inv₂ g ⟧₂ ≈G2 g
    inv₂-corr g = proj₂ (I2.surjective g) refl₂

    inv₁-⟦⟧ : ∀ w → inv₁ ⟦ w ⟧₁ ≈₁ w
    inv₁-⟦⟧ w = I1.injective (inv₁-corr ⟦ w ⟧₁)

    inv₁-cong : ∀ {g g'} → g ≈G1 g' → inv₁ g ≈₁ inv₁ g'
    inv₁-cong {g} {g'} eq =
      I1.injective (transG1 (inv₁-corr g) (transG1 eq (symG1 (inv₁-corr g'))))
    inv₂-cong : ∀ {g g'} → g ≈G2 g' → inv₂ g ≈₂ inv₂ g'
    inv₂-cong {g} {g'} eq =
      I2.injective (transG2 (inv₂-corr g) (transG2 eq (symG2 (inv₂-corr g'))))

    inv₁-hom : ∀ x y → inv₁ (x ∙G1 y) ≈₁ inv₁ x • inv₁ y
    inv₁-hom x y = I1.injective
      (transG1 (inv₁-corr (x ∙G1 y))
      (transG1 (∙-congG1 (symG1 (inv₁-corr x)) (symG1 (inv₁-corr y)))
               (symG1 (I1.∙-homo (inv₁ x) (inv₁ y)))))
    inv₂-hom : ∀ x y → inv₂ (x ∙G2 y) ≈₂ inv₂ x • inv₂ y
    inv₂-hom x y = I2.injective
      (transG2 (inv₂-corr (x ∙G2 y))
      (transG2 (∙-congG2 (symG2 (inv₂-corr x)) (symG2 (inv₂-corr y)))
               (symG2 (I2.∙-homo (inv₂ x) (inv₂ y)))))

------------------------------------------------------------------------
-- The induced action of G2 on G1 and its laws

    act : |G2| → |G1| → |G1|
    act g x = ⟦ conjss (inv₂ g) (inv₁ x) ⟧₁

    act-cong : ∀ {h h' x x'} → h ≈G2 h' → x ≈G1 x' → act h x ≈G1 act h' x'
    act-cong eqh eqx = I1.⟦⟧-cong (conjss-cong (inv₂-cong eqh) (inv₁-cong eqx))

    act-ε-homo : ∀ h → act h εG1 ≈G1 εG1
    act-ε-homo h = transG1 (I1.⟦⟧-cong step) I1.ε-homo
      where
      inv₁ε : inv₁ εG1 ≈₁ ε
      inv₁ε = I1.injective (transG1 (inv₁-corr εG1) (symG1 I1.ε-homo))
      step : conjss (inv₂ h) (inv₁ εG1) ≈₁ ε
      step = trans₁ (conj-congNH (inv₂ h) inv₁ε) (refl'₁ (conjss-c-ε=ε (inv₂ h)))

    act-∙-homo : ∀ h x y → act h (x ∙G1 y) ≈G1 (act h x ∙G1 act h y)
    act-∙-homo h x y = transG1 (I1.⟦⟧-cong step) (I1.∙-homo _ _)
      where
      step : conjss (inv₂ h) (inv₁ (x ∙G1 y))
           ≈₁ conjss (inv₂ h) (inv₁ x) • conjss (inv₂ h) (inv₁ y)
      step = trans₁ (conj-congNH (inv₂ h) (inv₁-hom x y))
                    (refl'₁ (conjss-homo (inv₂ h) (inv₁ x) (inv₁ y)))

    act-identity : ∀ x → act εG2 x ≈G1 x
    act-identity x = transG1 (I1.⟦⟧-cong step) (inv₁-corr x)
      where
      inv₂ε : inv₂ εG2 ≈₂ ε
      inv₂ε = I2.injective (transG2 (inv₂-corr εG2) (symG2 I2.ε-homo))
      step : conjss (inv₂ εG2) (inv₁ x) ≈₁ inv₁ x
      step = trans₁ (conj-congH (inv₁ x) inv₂ε) (refl'₁ (lemma-conjss-ε (inv₁ x)))

    act-compose : ∀ h h' x → act (h ∙G2 h') x ≈G1 act h (act h' x)
    act-compose h h' x = I1.⟦⟧-cong step
      where
      step : conjss (inv₂ (h ∙G2 h')) (inv₁ x)
           ≈₁ conjss (inv₂ h) (inv₁ (act h' x))
      step = trans₁ (conj-congH (inv₁ x) (inv₂-hom h h'))
                    (conj-congNH (inv₂ h)
                      (sym₁ (inv₁-⟦⟧ (conjss (inv₂ h') (inv₁ x)))))

    φ : SDP.Action (Group.rawMonoid G1) (Group.rawMonoid G2)
    φ = record
      { act          = act
      ; act-cong     = act-cong
      ; act-ε-homo   = act-ε-homo
      ; act-∙-homo   = act-∙-homo
      ; act-identity = act-identity
      ; act-compose  = act-compose
      }

------------------------------------------------------------------------
-- The semi-direct product group  G1 ⋊ G2  and the presentation

    -- First hole: the semi-direct product of the groups G1 and G2.
    G1⋊G2 : Group 0ℓ 0ℓ
    G1⋊G2 = SDP.group G1 G2 φ

    -- The generator semantics: an N-generator lands in the G1 factor,
    -- an H-generator in the G2 factor.  Its monoid-homomorphic extension
    -- GS.⟦_⟧ (via StarPresentation) is the candidate isomorphism.
    ⟦_⟧₀ : Y → Group.Carrier G1⋊G2
    ⟦ inj₁ n  ⟧₀ = ⟦ [ n ]ʷ ⟧₁ , εG2
    ⟦ inj₂ hh ⟧₀ = εG1 , ⟦ [ hh ]ʷ ⟧₂

    private
      -- The coset normal form is valued in the product of the N-word
      -- setoid and the coset setoid (as in the direct-product case).
      nf-setoid = PW.×-setoid word-setoid₁ Cₛ
      module SP = Normalization.StarPresentation
        (Γ ⋄ Δ ⋄ ConjRelʷ conj) nf-setoid
      module GS = SP.GroupSem G1⋊G2 ⟦_⟧₀
      module NF₃ = SNF (Γ ⋄ Δ ⋄ ConjRelʷ conj) nf-setoid
      module D = Group G1⋊G2

    open LeftRightCongruence Γ Δ (ConjRelʷ conj) using (lefts)

    -- Section property for the second factor (analogue of inv₁-⟦⟧).
    inv₂-⟦⟧ : ∀ w → inv₂ ⟦ w ⟧₂ ≈₂ w
    inv₂-⟦⟧ w = I2.injective (inv₂-corr ⟦ w ⟧₂)

    -- The coset map nf0 respects ≈₃.
    nf0-cong : ∀ {w v} → w ≈₃ v → nf0 w ~ nf0 v
    nf0-cong {w} {v} = lemma-hypB I w v

    -- ⟦_⟧ of a left- (resp. right-) embedded word is the factor
    -- interpretation in the matching component.  The action twist
    -- collapses: εG2 acts as the identity and every action fixes εG1.
    emb-l : ∀ w → D._≈_ (GS.⟦ [ w ]ₗ ⟧) (⟦ w ⟧₁ , εG2)
    emb-l [ x ]ʷ = D.refl
    emb-l ε       = symG1 I1.ε-homo , Group.refl G2
    emb-l (w • v) =
      D.trans (D.∙-cong (emb-l w) (emb-l v))
        ( transG1 (∙-congG1 (Group.refl G1) (act-identity ⟦ v ⟧₁))
                  (symG1 (I1.∙-homo w v))
        , Group.identityˡ G2 εG2 )

    emb-r : ∀ c → D._≈_ (GS.⟦ [ c ]ᵣ ⟧) (εG1 , ⟦ c ⟧₂)
    emb-r [ x ]ʷ = D.refl
    emb-r ε       = Group.refl G1 , symG2 I2.ε-homo
    emb-r (c • d) =
      D.trans (D.∙-cong (emb-r c) (emb-r d))
        ( transG1 (∙-congG1 (Group.refl G1) (act-ε-homo ⟦ c ⟧₂))
                  (Group.identityˡ G1 εG1)
        , symG2 (I2.∙-homo c d) )

    emb-x : ∀ w → D._≈_ (GS.⟦ [ w ]ₓ ⟧) (⟦ w ⟧₁ , εG2)
    emb-x w rewrite aux-fʷ' {w} = emb-l w

    -- ⟦_⟧ of an inverse normal form is the pair of factor
    -- interpretations.
    sem-⁻¹nf : ∀ a c → D._≈_ (GS.⟦ ⁻¹nf (a , c) ⟧) (⟦ a ⟧₁ , ⟦ c ⟧₂)
    sem-⁻¹nf a c =
      D.trans (D.∙-cong (emb-x a) (emb-r c))
        ( transG1 (∙-congG1 (Group.refl G1) (act-identity εG1))
                  (Group.identityʳ G1 ⟦ a ⟧₁)
        , Group.identityˡ G2 ⟦ c ⟧₂ )

    -- (1) ⟦_⟧ preserves the defining axioms: left = Γ, right = Δ, and
    -- mid = the conjugation relation (act ⟦[h]⟧₂ ⟦[n]⟧₁ ≈ ⟦conj h n⟧₁).
    sound-ax : ∀ {w v} → w ===₃ v → Group._≈_ G1⋊G2 (GS.⟦ w ⟧) (GS.⟦ v ⟧)
    sound-ax (left {u} {v} x) =
      D.trans (emb-l u)
        (D.trans (I1.⟦⟧-cong (_≈₁_.axiom x) , Group.refl G2) (D.sym (emb-l v)))
    sound-ax (right {u} {v} x) =
      D.trans (emb-r u)
        (D.trans (Group.refl G1 , I2.⟦⟧-cong (axiom₂ x)) (D.sym (emb-r v)))
    sound-ax (mid (comm n h)) =
      D.trans (D.∙-cong (emb-r [ h ]ʷ) (emb-l [ n ]ʷ))
        (D.trans
          ( transG1 (Group.identityˡ G1 (act ⟦ [ h ]ʷ ⟧₂ ⟦ [ n ]ʷ ⟧₁))
              (transG1 act-key
                (transG1 (symG1 (Group.identityʳ G1 ⟦ conj h n ⟧₁))
                  (∙-congG1 (Group.refl G1) (symG1 (act-identity εG1)))))
          , transG2 (Group.identityʳ G2 ⟦ [ h ]ʷ ⟧₂)
              (symG2 (Group.identityˡ G2 ⟦ [ h ]ʷ ⟧₂)) )
          (D.sym (D.∙-cong (emb-l (conj h n)) (emb-r [ h ]ʷ))))
      where
      act-key : act ⟦ [ h ]ʷ ⟧₂ ⟦ [ n ]ʷ ⟧₁ ≈G1 ⟦ conj h n ⟧₁
      act-key = I1.⟦⟧-cong (conjss-cong (inv₂-⟦⟧ [ h ]ʷ) (inv₁-⟦⟧ [ n ]ʷ))

    -- (2) Every generator has a left inverse, lifted from the factors.
    grouplike₃ : Grouplike (Γ ⋄ Δ ⋄ ConjRelʷ conj)
    grouplike₃ (inj₁ n) = [ proj₁ (P1.gl n) ]ₗ , lefts (proj₂ (P1.gl n))
    grouplike₃ (inj₂ h) = [ proj₁ (P2.gl h) ]ᵣ , []-cong (proj₂ (P2.gl h))

    -- (3) The coset normal form as a setoid normal form.
    nfp₃ : NF₃.NormalForm
    nfp₃ = record
      { rightInverse = record
          { to        = nf0
          ; from      = ⁻¹nf
          ; to-cong   = nf0-cong
          ; from-cong = ⁻¹nf-wd
          ; inverseʳ  = λ eq → _≈₃_.trans (⁻¹nf-wd eq) ⁻¹nf-nf=id
          }
      }

    -- (4) Normal forms with equal denotations are equal, reducing factor
    -- by factor to injectivity of the two factor interpretations.
    unfp₃ : NF₃.UniqueNormalForm (Group.setoid G1⋊G2) GS.⟦_⟧ nfp₃
    unfp₃ = record
      { unique = λ { {a , c} {a' , c'} eq →
          let p = D.trans (D.sym (sem-⁻¹nf a c)) (D.trans eq (sem-⁻¹nf a' c'))
          in I1.injective (proj₁ p) , I2.injective (proj₂ p) } }

    subpres : (Γ ⋄ Δ ⋄ ConjRelʷ conj) IsSubPresentationOf G1⋊G2
    subpres = GS.GetSubPresentation.groupSubPres sound-ax grouplike₃ nfp₃ unfp₃

    private
      open import Normalization.StarInterp (Γ ⋄ Δ ⋄ ConjRelʷ conj)
      module E  = Extend (Group.monoid G1⋊G2) ⟦_⟧₀
      module EC = E.Cong sound-ax

    -- (5) ⟦_⟧ is onto: each (g₁ , g₂) is realised by inv₁ g₁ on the left
    -- and inv₂ g₂ on the right, using surjectivity of the two factors.
    claim : Surjective _≈₃_ (Group._≈_ G1⋊G2) GS.⟦_⟧
    claim (g1 , g2) =
      [ inv₁ g1 ]ₗ • [ inv₂ g2 ]ᵣ ,
      λ z≈w →
        D.trans (EC.fʷ-cong z≈w)
          (D.trans (D.∙-cong (emb-l (inv₁ g1)) (emb-r (inv₂ g2)))
            ( transG1 (∙-congG1 (Group.refl G1) (act-identity εG1))
                (transG1 (Group.identityʳ G1 ⟦ inv₁ g1 ⟧₁) (inv₁-corr g1))
            , transG2 (Group.identityˡ G2 ⟦ inv₂ g2 ⟧₂) (inv₂-corr g2) ))

    dpres : (Γ ⋄ Δ ⋄ ConjRelʷ conj) IsPresentationOf G1⋊G2
    dpres = isPresentationOf subpres claim

    ------------------------------------------------------------------------
    -- Uniqueness lifts through the semi-direct product
    --
    -- If the two factor normal forms are unique for the factor
    -- semantics, the pair normal form of NFP' is unique for the
    -- semi-direct product semantics: the interpretation of a pair
    -- section computes componentwise (the action twist collapses on
    -- units), so distinct pairs are separated factor by factor.

    module LiftUNF
      {NF₁ NF₂ : Set}
      (nfp-Γ : NormalForm Γ NF₁)
      (nfp-Δ : NormalForm Δ NF₂)
      (unfp-Γ : SNF.UniqueNormalForm Γ (Eq.setoid NF₁)
                  (Group.setoid G1) ⟦_⟧₁ nfp-Γ)
      (unfp-Δ : SNF.UniqueNormalForm Δ (Eq.setoid NF₂)
                  (Group.setoid G2) ⟦_⟧₂ nfp-Δ)
      where

      open NFP' nfp-Γ nfp-Δ using (nfp' ; gg)

      open SNF.UniqueNormalForm unfp-Γ
        renaming (unique to unique₁ ; inv-nf to inv-nf₁) using ()
      open SNF.UniqueNormalForm unfp-Δ
        renaming (unique to unique₂ ; inv-nf to inv-nf₂) using ()

      -- The interpretation of a pair section is the pair of factor
      -- interpretations of the factor sections.
      sem-gg : ∀ u₁ u₂ →
        D._≈_ (GS.⟦ gg (u₁ , u₂) ⟧) (⟦ inv-nf₁ u₁ ⟧₁ , ⟦ inv-nf₂ u₂ ⟧₂)
      sem-gg u₁ u₂ =
        D.trans (D.∙-cong (emb-x (inv-nf₁ u₁)) (emb-r (inv-nf₂ u₂)))
          ( transG1 (∙-congG1 (Group.refl G1) (act-identity εG1))
                    (Group.identityʳ G1 ⟦ inv-nf₁ u₁ ⟧₁)
          , Group.identityˡ G2 ⟦ inv-nf₂ u₂ ⟧₂ )

      unfp' : SNF.UniqueNormalForm (Γ ⋄ Δ ⋄ ConjRelʷ conj)
                (Eq.setoid (NF₁ × NF₂)) (Group.setoid G1⋊G2) GS.⟦_⟧ nfp'
      unfp' = record
        { unique = λ { {u₁ , u₂} {v₁ , v₂} eq →
            let p = D.trans (D.sym (sem-gg u₁ u₂)) (D.trans eq (sem-gg v₁ v₂))
            in Eq.cong₂ _,_ (unique₁ (proj₁ p)) (unique₂ (proj₂ p)) } }


------------------------------------------------------------------------
-- Presentations of groups
--
-- The Reidemeister–Schreier method.
--
-- Setup: Γ presents a subgroup H, Δ presents the ambient group G, and
-- f : X → Word Y embeds the generators of H as words of G. If certain
-- condition holds, the method shows the induced monoid map (f ʷ) :
-- Word X → Word Y is injective modulo the presentations — i.e. H
-- really is the subgroup it looks like — and, given a Schreier
-- section, packages a normal form.
--
-- The engine is a coset action h : C → Y → Word X × C (a "Schreier
-- table"): h c y slides the letter y past coset c, recording the piece
-- of H peeled off and the coset landed in; (h ᵗ) extends it to words.
--
-- The congruence lemma "(f ʷ) preserves ≈" lives in
-- Presentation.Properties (module StarCongruence).
--
-- Modules, in increasing generality:
--
--   Star-Injective-Simplified  injectivity of (f ʷ) when a section
--                              g : Y → Word X is already available.
--   Star-Injective-Full        the coset-enumeration version, with a
--                              propositional (≡) coset index; provides
--                              the Schreier map, injectivity, and
--                              right/left normal forms.
--   Star-Injective-Full-Setoid the same for a coset index that is a
--                              setoid (≈ₛ); Star-Injective-Full is the
--                              special case Cₛ = (C, ≡).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (0ℓ)

open import Relation.Binary.PropositionalEquality as Eq
  renaming ([_] to [_]') using ( _≡_ ; inspect)
open import Relation.Binary using (IsEquivalence ; Setoid)
open import Function.Definitions using (Injective ; Surjective)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂)

import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP

module Normalization.Reidemeister-Schreier where

------------------------------------------------------------------------
-- Injectivity from an explicit section
--
-- When a candidate inverse g : Y → Word X is already available — well
-- defined on Δ's relations, and a left inverse of f on generators
-- ([ x ]ʷ ≈₁ (g ʷ)(f x)) — injectivity of (f ʷ) is immediate: (g ʷ) is
-- a retraction of (f ʷ).  This also yields surjectivity of (g ʷ), and
-- avoids the coset bookkeeping of the Full versions below.

module Star-Injective-Simplified {X Y : Set} (Γ : WRel X) (Δ : WRel Y) where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂)

  -- f, g the two maps; well-defined makes (g ʷ) a congruence; and
  -- left-inv-gen says g inverts f on generators.  Yields left-inv (g ʷ
  -- is a left inverse of f ʷ on all words), surjectivity of (g ʷ), and
  -- the injectivity theorem reidemeister-schreier-simplified.
  module Reidemeister-Schreier-Simplified
    (f : X → Word Y)
    (g : Y → Word X)
    (well-defined : ∀ {u t : Word Y} → u ===₂ t → (g ʷ) u ≈₁ (g ʷ) t)
    (left-inv-gen : ∀ (x : X) → [ x ]ʷ ≈₁ (g ʷ) (f x))
    where

    left-inv : ∀ (w : Word X) → w ≈₁ (g ʷ) ((f ʷ) w)
    left-inv ([ x ]ʷ) = left-inv-gen x
    left-inv ε = _≈₁_.refl
    left-inv (w • v) = _≈₁_.cong (left-inv w) (left-inv v)

    lemma-b : ∀ {u t : Word Y} → u ≈₂ t → (g ʷ) u ≈₁ (g ʷ) t
    lemma-b = fʷ-cong g well-defined
      where open PP.StarCongruence Δ Γ

    gʷ-surj : Surjective _≈₂_ _≈₁_ (g ʷ)
    gʷ-surj y = (f ʷ) y , λ x → _≈₁_.trans (lemma-b x) (_≈₁_.sym (left-inv y))

    reidemeister-schreier-simplified : (w v : Word X) → (f ʷ) w ≈₂ (f ʷ) v → w ≈₁ v
    reidemeister-schreier-simplified w v hyp = begin
      w               ≈⟨ left-inv w ⟩
      (g ʷ) ((f ʷ) w) ≈⟨ lemma-b hyp ⟩
      (g ʷ) ((f ʷ) v) ≈⟨ _≈₁_.sym (left-inv v) ⟩
      v         ∎
      where open SR word-setoid₁

    fʷ-inj : Injective _≈₁_ _≈₂_ (f ʷ)
    fʷ-inj = λ x₁ → reidemeister-schreier-simplified _ _ x₁


------------------------------------------------------------------------
-- Injectivity by coset enumeration (setoid cosets)
--
-- The coset index is a setoid (Cₛ, ≈ₛ): two cosets need only be
-- identified up to ≈ₛ.  The special case ≈ₛ = ≡ is Star-Injective-Full,
-- derived from this module below.
-- The setoid version additionally requires the coset action to respect
-- ≈ₛ (h-congₛ-gen) and the section to respect ≈ₛ ([]-cong), and exposes
-- the ≈ₛ-aware injectivity variants nf-isInjective' / nfl-isInjective'.

module Star-Injective-Full-Setoid
  {X Y : Set}
  (Γ  : WRel X)                -- subgroup presentation
  (Δ  : WRel Y)                -- group presentation
  (Cₛ : Setoid 0ℓ 0ℓ)          -- cosets, up to a setoid equivalence ≈ₛ
  (I  : Setoid.Carrier Cₛ)     -- identity coset
  where


  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂)

  open Setoid Cₛ renaming (Carrier to C ; isEquivalence to isEquivalenceₛ ; _≈_ to _≈ₛ_) using () public
  open IsEquivalence isEquivalenceₛ renaming (refl to reflₛ ; sym to symₛ ; trans to transₛ) using () public
  
  open _≈₂_

  setoid-WX-Cₛ : Setoid 0ℓ 0ℓ
  setoid-WX-Cₛ = PW.×-setoid word-setoid₁ Cₛ

  open Setoid setoid-WX-Cₛ renaming (refl to refl~ ; sym to sym~ ; trans to trans~ ; _≈_ to _~_) using () public

  -- Fix the embedding f and the coset action h (now required to respect
  -- ≈ₛ, via h-congₛ-gen); h-congₛ lifts that congruence to whole words.
  module _
    (f : X → Word Y)
    (h : C → Y → Word X × C)
    (h-congₛ-gen : ∀ {c d} y → c ≈ₛ d → h c y ~ h d y)
    where

    private
      hᵗ = (h ᵗ)
      fʷ = f ʷ

    -- h ᵗ is congruent over C w.r.t a word in Y.
    h-congₛ : ∀ {c d w} → c ≈ₛ d → hᵗ c w ~ hᵗ d w
    h-congₛ {c} {d} {[ x ]ʷ} eq = h-congₛ-gen x eq
    h-congₛ {c} {d} {ε} eq = _≈₁_.refl , eq
    h-congₛ {c} {d} {(w • v)} eq with hᵗ c w | inspect (hᵗ c) w | hᵗ d w | inspect (hᵗ d) w
    ... | (wc , c') | [ Eq.refl ]' | (wd , d') | [ Eq.refl ]' with h-congₛ {c} {d} {w} eq | hᵗ c' v | inspect (hᵗ c') v | hᵗ d' v | inspect (hᵗ d') v
    ... | ih1 | (vc , c'') | [ Eq.refl ]' | (vd , d'') | [ Eq.refl ]' with h-congₛ {c'} {d'} {v} (ih1 .proj₂)
    ... | ih2 = (_≈₁_.cong (ih1 .proj₁) (ih2 .proj₁)) , ih2 .proj₂


    module Reidemeister-Schreier-Full
      (h=⁻¹f-gen : ∀ (x : X) → ([ x ]ʷ , I) ~ (hᵗ I (f x)))
      (h-wd : ∀ (c : C){u t : Word Y} → u ===₂ t → (hᵗ c u) ~ (hᵗ c t))
      where

      -- Setoid analogue of Star-Injective-Full.Reidemeister-Schreier-Full:
      -- reconstruct a Schreier section and prove fʷ injective, now
      -- tracking cosets only up to ≈ₛ.

      -- Definition: A word is special if it doesn't leave the "I"-coset.
      special : Word Y → Set
      special w = proj₂ (hᵗ I w) ≈ₛ I

      -- Lemma: ε is special.
      lemma-special-ε : special ε
      lemma-special-ε = reflₛ

      -- Lemma: The image of f is special.
      lemma-special-f : ∀ (x : X) → special (f x)
      lemma-special-f x with h=⁻¹f-gen x
      ... | hyp = symₛ (proj₂ hyp)

      -- Lemma: Special words are closed under multiplication.
      lemma-special-• : ∀ (w v : Word Y) → special w → special v → special (w • v)
      lemma-special-• w v sw sv with hᵗ I w | inspect (hᵗ I ) w
      ... | (w' , c') | [ Eq.refl ]' with hᵗ c' v | inspect (hᵗ c' ) v
      ... | (v' , c'') | [ Eq.refl ]' = lem3
        where

          lem1 : c' ≈ₛ I
          lem1 = sw

          lem2 : (v' , c'') ~ hᵗ I v
          lem2 = begin
            (v' , c'') ≡⟨ Eq.refl ⟩
            hᵗ c' v ≈⟨ h-congₛ {w = v} sw ⟩
            hᵗ I v ∎
            where open SR setoid-WX-Cₛ

          lem3 : c'' ≈ₛ I
          lem3 = begin
            c'' ≈⟨ proj₂ lem2 ⟩
            proj₂ (hᵗ I v) ≈⟨ sv ⟩
            I ∎
            where open SR Cₛ          

      -- Lemma: The image of fʷ is special.
      lemma-special-fʷ : ∀ (w : Word X) → special (fʷ w)
      lemma-special-fʷ [ x ]ʷ = lemma-special-f x
      lemma-special-fʷ ε = lemma-special-ε
      lemma-special-fʷ (w • v) = lemma-special-• (fʷ w) (fʷ v) (lemma-special-fʷ w) (lemma-special-fʷ v)

      -- Definition: For special words, there is a translation back.
      g : Word Y → Word X
      g w = proj₁ (hᵗ I w)

      -- Lemma: g preserves ε.
      lemma-g-ε : g ε ≡ ε
      lemma-g-ε = Eq.refl

      -- Lemma: g is a homomorphism on special words.
      lemma-g-• : ∀ (w v : Word Y) → special w → g (w • v) ≈₁ g w • g v
      lemma-g-• w v hyp with hᵗ I w | inspect (hᵗ I) w
      lemma-g-• w v hyp | (w' , c') | [ eq1 ]' with hᵗ c' v | inspect (hᵗ c') v
      lemma-g-• w v hyp | (w' , c') | [ eq1 ]' | (v' , c'') | [ eq2 ]' = lem6
        where

          lem1 : c' ≈ₛ I
          lem1 = hyp

          lem2 : (v' , c'') ~ hᵗ I v
          lem2 = begin
            (v' , c'') ≡⟨ Eq.sym eq2 ⟩
            hᵗ c' v ≈⟨ h-congₛ {w = v} lem1 ⟩
            hᵗ I v ∎
            where open SR setoid-WX-Cₛ

          lem4 : v' ≈₁ g v
          lem4 = proj₁ lem2 

          lem6 : w' • v' ≈₁ w' • g v
          lem6 = _≈₁_.cong _≈₁_.refl lem4


      -- Lemma: g is a left inverse of f ʷ.
      lemma-a : ∀ (w : Word X) → w ≈₁ g (fʷ w)
      lemma-a [ x ]ʷ = proj₁ (h=⁻¹f-gen x)
      lemma-a ε = _≈₁_.refl
      lemma-a (w • u) = claim
        where
          open SR word-setoid₁
          claim :  w • u ≈₁ g (fʷ (w • u))
          claim = begin
            w • u ≈⟨ _≈₁_.cong (lemma-a w) _≈₁_.refl  ⟩
            g (fʷ w) • u ≈⟨ _≈₁_.cong _≈₁_.refl (lemma-a u) ⟩
            g (fʷ w) • g (fʷ u) ≈⟨ _≈₁_.sym ((lemma-g-• (fʷ w) (fʷ u) (lemma-special-fʷ w))) ⟩
            g (fʷ w • fʷ u) ∎


      -- Lemma: Hypothesis B can be extended from the elements of Δ to
      -- all consequences of Δ.
      lemma-hypB : ∀ (c : C) (u t : Word Y) → u ≈₂ t → hᵗ c u ~ hᵗ c t
      lemma-hypB c u t (axiom x) = h-wd c x
      lemma-hypB c u .u refl = _≈₁_.refl , reflₛ
      lemma-hypB c ((u • v) • w) (.u • (.v • .w)) assoc with hᵗ c u
      ... | (u' , c') with hᵗ c' v
      ... | (v' , c'') with hᵗ c'' w
      ... | (w' , c''') = (_≈₁_.assoc , reflₛ)
      lemma-hypB c (ε • u) .u left-unit with hᵗ c u
      ... | (u' , c') = (_≈₁_.left-unit , reflₛ)
      lemma-hypB c (u • ε) .u right-unit with hᵗ c u
      ... | (u' , c') = (_≈₁_.right-unit , reflₛ)

      lemma-hypB c u t (sym hyp) = (_≈₁_.sym (lemma-hypB c t u hyp .proj₁)) , symₛ (lemma-hypB c t u hyp .proj₂)
      lemma-hypB c u t (trans {v = v} hyp1 hyp2) = _≈₁_.trans (lemma-hypB c u v hyp1 .proj₁) (lemma-hypB c v t hyp2 .proj₁) , transₛ (lemma-hypB c u v hyp1 .proj₂) (lemma-hypB c v t hyp2 .proj₂)
      lemma-hypB c (u • u') (t • t') (cong hyp1 hyp2)
        with hᵗ c u | hᵗ c t | inspect (hᵗ c) u | inspect (hᵗ c) t | lemma-hypB c u t hyp1
      ... | (u'' , c') | (t'' , c'') | [ Eq.refl ]' | [ Eq.refl ]' | (ih1 , ih1')
        with hᵗ c'' u' | hᵗ c'' t' | inspect (hᵗ c'') u' | inspect (hᵗ c'') t' | lemma-hypB c'' u' t' hyp2
      ... | (u''' , c''') | (t''' , c'''') | [ Eq.refl ]' | [ Eq.refl ]' | (ih2 , ih2') = (_≈₁_.cong ih1 (proj₁ claim)) , proj₂ claim
        where
        open SR setoid-WX-Cₛ
        claim : hᵗ (hᵗ c u .proj₂) u' ~ hᵗ (hᵗ c t .proj₂) t'
        claim = begin
          hᵗ (hᵗ c u .proj₂) u' ≈⟨ lemma-hypB ((hᵗ c u .proj₂)) u' t' hyp2 ⟩
          hᵗ (hᵗ c u .proj₂) t' ≈⟨ h-congₛ {w = t'} ih1' ⟩
          hᵗ (hᵗ c t .proj₂) t' ∎

      -- Lemma: g preserves relations.
      lemma-b : ∀ (u t : Word Y) → u ≈₂ t → g u ≈₁ g t
      lemma-b u t hyp with hᵗ I u | hᵗ I t | lemma-hypB I u t hyp
      ... | (u' , c') | (t' , c'') | (ih , ih') = ih

      -- Reidemeister-Schreier Theorem.
      reidemeister-schreier : (w v : Word X) → fʷ w ≈₂ fʷ v → w ≈₁ v
      reidemeister-schreier w v hyp = begin
          w ≈⟨ lemma-a w ⟩
          g (fʷ w) ≈⟨ lemma-b (fʷ w) (fʷ v) hyp ⟩
          g (fʷ v) ≈⟨ _≈₁_.sym (lemma-a v) ⟩
          v ∎
          where
            open SR word-setoid₁

      fʷ-inj : Injective _≈₁_ _≈₂_ fʷ
      fʷ-inj = λ x₁ → reidemeister-schreier _ _ x₁

    -- Setoid analogue of RightAction.  The section must respect ≈ₛ
    -- ([]-cong); besides nf-isInjective (over ≡ on the coset) it also
    -- provides nf-isInjective' (over ≈ₛ on the coset).
    module RightAction
      (f-well-defined : ∀ {w v} → w ===₁ v → fʷ w ≈₂ fʷ v)
      ([_] : C → Word Y)
      ([]-cong : ∀ {c d} → c ≈ₛ d → [ c ] ≈₂ [ d ])
      ([I]≈ε : [ I ] ≈₂ ε)
      (lemma-ract : ∀ c b → let (b' , c') = h c b in let [_]ₓ = f ʷ in
        [ c ] • [ b ]ʷ ≈₂ [ b' ]ₓ • [ c' ])
      where

      [_]ₓ : Word X → Word Y
      [_]ₓ = f ʷ

      infixl 4 _⊛_
      _⊛_ : C → Word Y → Word X × C
      _⊛_ = h ᵗ

      nf : Word Y → Word X × C
      nf = I ⊛_

      lemma-⊛ : ∀ c w → let (w' , c') = c ⊛ w in [ c ] • w ≈₂ [ w' ]ₓ • [ c' ]
      lemma-⊛ c [ x ]ʷ = lemma-ract c x
      lemma-⊛ c ε = _≈₂_.trans _≈₂_.right-unit (_≈₂_.sym _≈₂_.left-unit)
      lemma-⊛ c (w • v) with c ⊛ w | inspect (c ⊛_) w
      ... | (w' , c') | [ Eq.refl ]' with c' ⊛ v | inspect (c' ⊛_) v
      ... | (v' , c'') | [ Eq.refl ]' = claim
        where
        claim : [ c ] • (w • v) ≈₂ [ w' • v' ]ₓ • [ c'' ]
        claim = begin
          [ c ] • (w • v) ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          ([ c ] • w) • v ≈⟨ _≈₂_.cong (lemma-⊛ _ _) _≈₂_.refl ⟩
          ([ w' ]ₓ • [ c' ]) • v ≈⟨ _≈₂_.assoc ⟩
          [ w' ]ₓ • [ c' ] • v ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-⊛ _ _) ⟩
          [ w' ]ₓ • [ v' ]ₓ • [ c'' ] ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          [ w' • v' ]ₓ • [ c'' ] ∎
          where
            open SR word-setoid₂

      ⁻¹nf : Word X × C → Word Y
      ⁻¹nf (a , c) = [ a ]ₓ • [ c ]

      ⁻¹nf-nf=id : ∀ {w} → ⁻¹nf (nf w) ≈₂ w
      ⁻¹nf-nf=id {w} = _≈₂_.trans (_≈₂_.sym (lemma-⊛ _ _)) (_≈₂_.trans (_≈₂_.cong [I]≈ε _≈₂_.refl) _≈₂_.left-unit)

      nf-isInjective : Injective _≈₂_ (PW.Pointwise _≈₁_ _≡_) nf
      nf-isInjective {x} {y} (eqa , eqc) with nf x | inspect nf x | nf y | inspect nf y
      ... | (a , c) | [ Eq.refl ]' | (a' , c') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nf-nf=id ⟩
        ⁻¹nf (nf x) ≈⟨ _≈₂_.refl ⟩
        [ a ]ₓ • [ c ] ≡⟨ Eq.cong (\ □ → [ a ]ₓ • [ □ ]) eqc ⟩
        [ a ]ₓ • [ c' ] ≈⟨ _≈₂_.cong (fʷ-cong f f-well-defined eqa) _≈₂_.refl ⟩
        [ a' ]ₓ • [ c' ] ≡⟨ Eq.refl ⟩
        ⁻¹nf (nf y) ≈⟨ ⁻¹nf-nf=id ⟩
        y ∎
          where
            open SR word-setoid₂
            open PP.StarCongruence Γ Δ


      nf-isInjective' : Injective _≈₂_ (PW.Pointwise _≈₁_ _≈ₛ_) nf
      nf-isInjective' {x} {y} (eqa , eqc) with nf x | inspect nf x | nf y | inspect nf y
      ... | (a , c) | [ Eq.refl ]' | (a' , c') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nf-nf=id ⟩
        ⁻¹nf (nf x) ≈⟨ _≈₂_.refl ⟩
        [ a ]ₓ • [ c ] ≈⟨ _≈₂_.cong _≈₂_.refl ([]-cong eqc) ⟩
        [ a ]ₓ • [ c' ] ≈⟨ _≈₂_.cong (fʷ-cong f f-well-defined eqa) _≈₂_.refl ⟩
        [ a' ]ₓ • [ c' ] ≡⟨ Eq.refl ⟩
        ⁻¹nf (nf y) ≈⟨ ⁻¹nf-nf=id ⟩
        y ∎
          where
            open SR word-setoid₂
            open PP.StarCongruence Γ Δ

      ⁻¹nf-wd : ∀ {u t : Word X × C} → u ~ t → ⁻¹nf u ≈₂ ⁻¹nf t
      ⁻¹nf-wd (eqa , eqc) = _≈₂_.cong (fʷ-cong f f-well-defined eqa) ([]-cong eqc)
        where open PP.StarCongruence Γ Δ

      ⁻¹nf-isSurjective : Surjective _~_ _≈₂_ ⁻¹nf
      ⁻¹nf-isSurjective y = nf y , claim
        where
          claim : {z : Word X × C} → z ~ nf y → ⁻¹nf z ≈₂ y
          claim eqv = _≈₂_.trans (⁻¹nf-wd eqv) ⁻¹nf-nf=id


    -- Setoid analogue of LeftAction (left coset action), likewise adding
    -- []-cong and the ≈ₛ-aware variant nfl-isInjective'.
    module LeftAction
      (f-well-defined : ∀ {w v} → w ===₁ v → fʷ w ≈₂ fʷ v)
      ([_] : C → Word Y)
      ([]-cong : ∀ {c d} → c ≈ₛ d → [ c ] ≈₂ [ d ])
      ([I]≈ε : [ I ] ≈₂ ε)
      (lact : Y → C → C × Word X)
      (lemma-lact : ∀ b c → let (c' , b') = lact b c in let [_]ₓ = f ʷ in
          [ b ]ʷ • [ c ] ≈₂ [ c' ] • [ b' ]ₓ)
      where

      [_]ₓ = f ʷ


      infixl 4 _⊛_
      _⊛_ : Word Y → C → C × Word X
      _⊛_ = lact ᵗ'

      lemma-⊛ : ∀ w c → let (c' , w') = w ⊛ c in w • [ c ] ≈₂ [ c' ] • [ w' ]ₓ
      lemma-⊛ [ x ]ʷ c = lemma-lact x c
      lemma-⊛ ε c = _≈₂_.trans _≈₂_.left-unit (_≈₂_.sym _≈₂_.right-unit)
      lemma-⊛ (w • v) c with v ⊛ c | inspect (v ⊛_) c
      ... | (c' , v') | [ Eq.refl ]' with w ⊛ c' | inspect (w ⊛_) c'
      ... | (c'' , w') | [ Eq.refl ]' = claim
        where
        claim : (w • v) • [ c ] ≈₂ [ c'' ] • [ w' • v' ]ₓ
        claim = begin
          (w • v) • [ c ] ≈⟨ _≈₂_.assoc ⟩
          w • v • [ c ] ≈⟨ _≈₂_.cong _≈₂_.refl (lemma-⊛ v c) ⟩
          w • [ c' ] • [ v' ]ₓ ≈⟨ _≈₂_.sym _≈₂_.assoc ⟩
          (w • [ c' ]) • [ v' ]ₓ ≈⟨ _≈₂_.cong (lemma-⊛ w c') _≈₂_.refl ⟩
          ([ c'' ] • [ w' ]ₓ) • [ v' ]ₓ ≈⟨ _≈₂_.assoc ⟩
          [ c'' ] • [ w' • v' ]ₓ ∎
          where
            open SR word-setoid₂

      nf : Word Y → C × Word X
      nf = _⊛ I

      ⁻¹nf : C × Word X → Word Y
      ⁻¹nf (c , a) = [ c ] • [ a ]ₓ

      ⁻¹nf-nf=id : ∀ {w} → ⁻¹nf (nf w) ≈₂ w
      ⁻¹nf-nf=id {w} = _≈₂_.trans (_≈₂_.sym (lemma-⊛ _ _) ) (_≈₂_.trans (_≈₂_.cong _≈₂_.refl [I]≈ε) _≈₂_.right-unit)

      nf-isInjective : Injective _≈₂_ (PW.Pointwise _≡_ _≈₁_) nf
      nf-isInjective {x} {y} (eqc , eqa) with nf x | inspect nf x | nf y | inspect nf y
      ... | (c , a) | [ Eq.refl ]' | (c' , a') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nf-nf=id ⟩
        ⁻¹nf (nf x) ≈⟨ _≈₂_.refl ⟩
        [ c ] • [ a ]ₓ ≡⟨ Eq.cong (\ □ → [ □ ] • [ a ]ₓ) eqc ⟩
        [ c' ] • [ a ]ₓ ≈⟨ _≈₂_.cong _≈₂_.refl (fʷ-cong f f-well-defined eqa) ⟩
        [ c' ] • [ a' ]ₓ ≡⟨ Eq.refl ⟩
        ⁻¹nf (nf y) ≈⟨ ⁻¹nf-nf=id ⟩
        y ∎
          where
            open SR word-setoid₂
            open PP.StarCongruence Γ Δ

      nf-isInjective' : Injective _≈₂_ (PW.Pointwise _≈ₛ_ _≈₁_) nf
      nf-isInjective' {x} {y} (eqc , eqa) with nf x | inspect nf x | nf y | inspect nf y
      ... | (c , a) | [ Eq.refl ]' | (c' , a') | [ Eq.refl ]' = begin
        x ≈⟨ _≈₂_.sym ⁻¹nf-nf=id ⟩
        ⁻¹nf (nf x) ≈⟨ _≈₂_.refl ⟩
        [ c ] • [ a ]ₓ ≈⟨ _≈₂_.cong ([]-cong eqc) _≈₂_.refl ⟩
        [ c' ] • [ a ]ₓ ≈⟨ _≈₂_.cong _≈₂_.refl (fʷ-cong f f-well-defined eqa) ⟩
        [ c' ] • [ a' ]ₓ ≡⟨ Eq.refl ⟩
        ⁻¹nf (nf y) ≈⟨ ⁻¹nf-nf=id ⟩
        y ∎
          where
            open SR word-setoid₂
            open PP.StarCongruence Γ Δ
------------------------------------------------------------------------
-- Injectivity by coset enumeration (propositional cosets)
--
-- The special case of Star-Injective-Full-Setoid where the coset index
-- is a plain set C with propositional equality.  Over ≡ the coset
-- action and the section are automatically congruent, so the
-- hypotheses h-congₛ-gen and []-cong are discharged here and everything
-- else is inherited.  The interface is that of Star-Injective-Full-Setoid
-- with those two hypotheses dropped:
--
--   Reidemeister-Schreier-Full  reconstructs a Schreier section g via
--        "special" words and proves (f ʷ) injective;
--   RightAction  the normal form nf = (h ᵗ) I and its section-based
--        inverse ⁻¹nf, with injectivity and surjectivity;
--   LeftAction   the mirror image, for a left coset action.

module Star-Injective-Full
  {X Y : Set}
  (Γ : WRel X)                 -- subgroup presentation
  (Δ : WRel Y)                 -- group presentation
  (C : Set)                    -- set of right cosets
  (I : C)                      -- identity coset (that of the subgroup)
  where

  private
    module S = Star-Injective-Full-Setoid Γ Δ (Eq.setoid C) I
    open PB Γ renaming (_===_ to _===₁_) using ()
    open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
    open S using (refl~)
  open S public using (_~_)

  module _
    (f : X → Word Y)
    (h : C → Y → Word X × C)
    where

    private
      -- Over ≡, the coset action is automatically congruent.
      h-congₛ-gen : ∀ {c d} y → c ≡ d → h c y ~ h d y
      h-congₛ-gen y Eq.refl = refl~

    module Reidemeister-Schreier-Full
      (h=⁻¹f-gen : ∀ (x : X) → ([ x ]ʷ , I) ~ ((h ᵗ) I (f x)))
      (h-wd : ∀ (c : C) {u t : Word Y} → u ===₂ t → ((h ᵗ) c u) ~ ((h ᵗ) c t))
      where
      open S.Reidemeister-Schreier-Full f h h-congₛ-gen h=⁻¹f-gen h-wd public

    module RightAction
      (f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
      ([_] : C → Word Y)
      ([I]≈ε : [ I ] ≈₂ ε)
      (lemma-ract : ∀ c b → let (b' , c') = h c b in let [_]ₓ = f ʷ in
        [ c ] • [ b ]ʷ ≈₂ [ b' ]ₓ • [ c' ])
      where
      private
        []-cong : ∀ {c d} → c ≡ d → [ c ] ≈₂ [ d ]
        []-cong Eq.refl = _≈₂_.refl
      open S.RightAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε lemma-ract public

    module LeftAction
      (f-well-defined : ∀ {w v} → w ===₁ v → (f ʷ) w ≈₂ (f ʷ) v)
      ([_] : C → Word Y)
      ([I]≈ε : [ I ] ≈₂ ε)
      (lact : Y → C → C × Word X)
      (lemma-lact : ∀ b c → let (c' , b') = lact b c in let [_]ₓ = f ʷ in
          [ b ]ʷ • [ c ] ≈₂ [ c' ] • [ b' ]ₓ)
      where
      private
        []-cong : ∀ {c d} → c ≡ d → [ c ] ≈₂ [ d ]
        []-cong Eq.refl = _≈₂_.refl
      open S.LeftAction f h h-congₛ-gen f-well-defined [_] []-cong [I]≈ε lact lemma-lact public


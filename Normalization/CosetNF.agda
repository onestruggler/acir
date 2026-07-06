------------------------------------------------------------------------
-- Presentations of groups
--
-- Coset normal forms via Reidemeister–Schreier.
--
-- Given a subgroup presentation Γ, a group presentation Δ, and coset
-- data (an embedding f, a coset action h, and a section [_]), the
-- normal-form map nf = (h **) I : Word Y → Word X × C is injective and
-- well-defined, and transports a normal form for Γ to one for Δ.
--
-- This file provides three layers:
--   * Data       — one level of the construction, for an explicit
--                  coset index set C;
--   * Data-CT    — the same for a "coset table" carrying a
--                  distinguished identity coset, indexing by C ⊎ ⊤,
--                  together with the packed record
--                  PackedCosetTable;
--   * CosetTower — iterating Data up an ℕ-indexed family of
--                  presentations to build a normal form at every level.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Relation.Binary.PropositionalEquality as Eq renaming ([_] to [_]') using ( _≡_ ; inspect)
open import Relation.Binary using (IsEquivalence ; Setoid)

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Unit using (⊤ ; tt)
open import Data.Sum using ([_,_] ; _⊎_ ; inj₁ ; inj₂)
open import Data.Sum.Properties using (inj₁-injective)
open import Data.Product using (_,_ ; _×_ ; proj₁ ; proj₂ ; map ; ∃)
open import Data.Product.Relation.Binary.Pointwise.NonDependent as PW
open import Data.List hiding ([_] ; map)

open import Function.Definitions using (Injective ; Surjective)
open import Function using (_∘_ ; id)
import Relation.Binary.Reasoning.Setoid as SR
import Function.Construct.Composition as FCC


open import Word.Base
open import Word.Properties
open import Presentation.Reidemeister-Schreier

import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Base as NFBase
open NFBase using (NormalFormWithoutInverse ; NormalForm)

module Normalization.CosetNF where

------------------------------------------------------------------------
-- Extension of an action law from letters to words
--
-- If sliding one letter x past a coset c satisfies the section/action
-- compatibility law  [ c ] • f x ≈ (f *) w' • [ c' ]  (where (w' , c')
-- = c ⊕ x), then sliding a whole word (f *) w does too, with (_⊕_ **)
-- threading the coset.

lemma-**-act :
  {Y X D : Set}
  (py : WRel Y) (_⊕_ : D → X → Word X × D) ([_] : D → Word Y) (f : X → Word Y) →
  let open PB py using (_≈_) in
  (hyp : (c : D) (x : X) → ([ c ] • f x) ≈ (f *) ((c ⊕ x) .proj₁) • [ (c ⊕ x) .proj₂ ]) →
  ∀ (c : D) (w : Word X) → let _⊕'_ = _⊕_ ** in
  [ c ] • (f *) w ≈ (f *) ((c ⊕' w) .proj₁) • [ (c ⊕' w) .proj₂ ]
lemma-**-act py _⊕_ [_] f hyp c [ x ]ʷ = hyp c x
lemma-**-act py _⊕_ [_] f hyp c ε = _≈_.trans _≈_.right-unit (_≈_.sym _≈_.left-unit)
  where
  open PB py
lemma-**-act py _⊕_ [_] f hyp c (w • v) with (_⊕_ **) c w | inspect (((_⊕_) **) c) w
... | (w' , c') | [ Eq.refl ]' with (_⊕_ **) c' v | inspect ((_⊕_ **) c') v
... | (v' , c'') | [ Eq.refl ]' = claim
  where
  open PB py
  open PP py renaming (word-setoid to ws) using ()

  [_]ₓ' = f *

  open SR ws

  claim : [ c ] • [ w • v ]ₓ' ≈ [ w' • v' ]ₓ' • [ c'' ]
  claim = begin
    [ c ] • [ w • v ]ₓ' ≈⟨ _≈_.sym _≈_.assoc ⟩
    ([ c ] • [ w ]ₓ') • [ v ]ₓ' ≈⟨ _≈_.cong (lemma-**-act py _⊕_ [_] f hyp c w) _≈_.refl ⟩
    ([ w' ]ₓ' • [ c' ]) • [ v ]ₓ' ≈⟨ _≈_.assoc ⟩
    [ w' ]ₓ' • [ c' ] • [ v ]ₓ' ≈⟨ _≈_.cong _≈_.refl (lemma-**-act py _⊕_ [_] f hyp c' v) ⟩
    [ w' ]ₓ' • [ v' ]ₓ' • [ c'' ] ≈⟨ _≈_.sym _≈_.assoc ⟩
    [ w' • v' ]ₓ' • [ c'' ] ∎

------------------------------------------------------------------------
-- Single-level coset extension (Reidemeister–Schreier transfer)
--
-- Think of Γ as a presentation of a subgroup H and Δ as a presentation
-- of the whole group G that H sits inside.  The parameters describe the
-- right cosets of H in G:
--
--   Γ, Δ  the subgroup / group presentations (letters X resp. Y);
--   C, I  the set of right cosets and the identity coset (that of H);
--   f     embeds a generator of H as a word of G; (f *) is its
--         extension to words (the "Schreier generators");
--   h     the coset action / Schreier table: h c y pushes the letter y
--         past coset c, returning (a word of H, the new coset); (h **)
--         is its extension to words;
--   [_]   a Schreier section choosing a representing word for a coset.
--
-- From this, nf = (h **) I is an injective, well-defined map
-- Word Y → Word X × C whose right inverse is inv-nf (w , c) = (f *) w •
-- [ c ].  Consequently a normal form for Γ transports to one for Δ
-- (nfp, nfp').

module Data
  {X Y : Set}
  (Γ   : WRel X)               -- subgroup presentation  (letters X)
  (Δ   : WRel Y)               -- group presentation     (letters Y)
  (C   : Set)                  -- set of right cosets
  (I   : C)                    -- identity coset (that of the subgroup)
  (f   : X → Word Y)           -- generator embedding  H ↪ G
  (h   : C → Y → Word X × C)   -- coset action (Schreier table)
  ([_] : C → Word Y)           -- Schreier section
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP Γ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
  open PP Δ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()

  -- Coset descriptors are related when their Word X components are
  -- ≈-equal in Γ and their coset components are propositionally equal.
  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C})

  -- The five hypotheses that make the data a genuine coset presentation.
  module Assumptions-And-Theorems
    -- (1) h inverts f on the identity coset: pushing f x through I
    --     recovers the letter x and returns to coset I.
    (h=⁻¹f-gen : ∀ (x : X) → ([ x ]ʷ , I) ~ ((h **) I (f x)))
    -- (2) the coset action respects the relations of Δ.
    (h-wd-ax : ∀ (c : C){u t : Word Y} → u ===₂ t → ((h **) c u) ~ ((h **) c t))
    -- (3) the embedding f respects the relations of Γ.
    (f-wd-ax : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
    -- (4) the identity coset is represented by the empty word.
    ([I]≈ε : [ I ] ≈₂ ε)
    -- (5) section/action compatibility: sliding a letter b past coset c
    --     matches the table entry h c b.
    (h=ract :  ∀ c b → let (b' , c') = h c b in let [_]ₓ = f * in
      [ c ] • [ b ]ʷ ≈₂ [ b' ]ₓ • [ c' ])
    where

    [_]ₓ = f *

    -- The Reidemeister–Schreier engine, instantiated once with all of
    -- the data above; every theorem below is a projection out of it.
    module RA  = Star-Injective-Full.RightAction
                   Γ Δ C I f h f-wd-ax [_] [I]≈ε h=ract
    module RSF = Star-Injective-Full.Reidemeister-Schreier-Full
                   Γ Δ C I f h h=⁻¹f-gen h-wd-ax

    -- f * is a congruence for the full congruence ≈ of Γ.
    f*-cong : ∀ {w v} → w ≈₁ v → (f *) w ≈₂ (f *) v
    f*-cong = Star-Congruence.lemma-f*-cong Γ Δ f f-wd-ax

    -- The normal-form map: run the coset action from the identity coset.
    nf : Word Y → Word X × C
    nf = (h **) I

    -- Sliding a whole word past a coset factors through the section.
    h**-hyp : ∀ c b → let (b' , c') = (h **) c b in
        [ c ] • b ≈₂ [ b' ]ₓ • [ c' ]
    h**-hyp c b = RA.lemma-⊛ c b

    -- nf, and the coset action generally, are well-defined for ≈ of Δ.
    nf-wd : ∀ {u t : Word Y} → u ≈₂ t → nf u ~ nf t
    nf-wd {u} {t} = RSF.lemma-hypB I u t

    h-wd : ∀ c {u t : Word Y} → u ≈₂ t → (h **) c u ~ (h **) c t
    h-wd c {u} {t} = RSF.lemma-hypB c u t

    -- f * is well-defined for ≈ of Γ.
    f-wd : ∀ {w v} → w ≈₁ v → (f *) w ≈₂ (f *) v
    f-wd {w} {v} eqv = RA.[]ₓ-wd eqv


    -- nf is injective: it faithfully records a word up to ≈.
    nf-injective : Injective _≈₂_ _~_ nf
    nf-injective = RA.nf-isInjective

    -- Section-based right inverse of nf.
    inv-nf : Word X × C → Word Y
    inv-nf (w , c) = (f *) w • [ c ]

    inv-nf-wd : ∀ {u t : Word X × C} → u ~ t → inv-nf u ≈₂ inv-nf t
    inv-nf-wd = RA.⁻¹nf-wd

    inv-nf-surjective : Surjective _~_ _≈₂_ inv-nf
    inv-nf-surjective = RA.⁻¹nf-isSurjective


    -- inv-nf is a right inverse of nf (up to ≈ of Δ).
    inv-nf∘nf=id : ∀ {w} → inv-nf (nf w) ≈₂ w
    inv-nf∘nf=id {w} = RA.⁻¹nf-nf=id

    -- f * is injective, because h ∘ f is the identity on Word X
    -- (a consequence of hypothesis (1)).
    f*-injective : (w v : Word X) → (f *) w ≈₂ (f *) v → w ≈₁ v
    f*-injective = RSF.reidemeister-schreier

    -- Rewrites a word of G back to a word of H (the Schreier map).
    nfx : Word Y → Word X
    nfx = RSF.g


    -- Transport a normal form for Γ to one for Δ, extending the
    -- normal-form carrier by the coset index:  NF_Δ = NF_Γ × C.
    -- (nf' = normalise the Word X component, keep the coset.)
    nfp : NormalFormWithoutInverse Γ → NormalFormWithoutInverse Δ
    nfp nfp1 = record { NF = NF₁ × C ; nf = nf' ; nf-cong = nf'-cong ; nf-injective = nf'-inj }
      where
        open NormalFormWithoutInverse nfp1 renaming (NF to NF₁ ; nf to f₁ ; nf-cong to f₁-cong ; nf-injective to f₁-inj) using ()

        nf' : Word Y → NF₁ × C
        nf' = map f₁ id ∘ nf

        nf'-inj× : Injective _≈₂_ (PW.Pointwise _≡_ _≡_) nf'
        nf'-inj× {w} {v} = FCC.injective _≈₂_ _~_ (PW.Pointwise _≡_ _≡_) nf-injective (map f₁-inj λ {x} z → z)

        nf'-inj : Injective _≈₂_ _≡_ nf'
        nf'-inj {w} {v} = FCC.injective _≈₂_ (PW.Pointwise _≡_ _≡_) _≡_ nf'-inj× PW.≡⇒≡×≡

        nf-cong : ∀ {w v} → w ≈₂ v → nf w ~ nf v
        nf-cong = nf-wd

        nf'-cong : ∀ {w v} → w ≈₂ v → nf' w ≡ nf' v
        nf'-cong {w} {v} eq = PW.≡×≡⇒≡ (FCC.congruent _≈₂_ _~_ (PW.Pointwise _≡_ _≡_) nf-cong (map f₁-cong λ {x} z → z) eq)


    -- Same transport for the inverse-carrying NormalForm.  The inverse
    -- gg (n , c) = (f *)(g₁ n) • [ c ] embeds the normalised Word X part
    -- and appends the coset's section; ggnf'=id checks it inverts nf'.
    nfp' : NormalForm Γ → NormalForm Δ
    nfp' nfp1 = record { NF = NF₁ × C ; nf = nf' ; nf-cong = nf-cong ; inv-nf = gg ; inv-nf∘nf=id = ggnf'=id }
      where
        open NormalForm nfp1 renaming (hasNormalFormWithoutInverse to nfp-Γ' ; NF to NF₁ ; nf to f₁ ; nf-cong to f₁-cong ; nf-injective to f₁-inj ; inv-nf to g₁ ; inv-nf∘nf=id to gf=id) using ()

        open NormalFormWithoutInverse (nfp nfp-Γ') renaming (nf to nf')

        gg : NF₁ × C → Word Y
        gg (n , c) = [ g₁ n ]ₓ • [ c ]

        ggnf'=id : {w : Word Y} → gg (nf' w) ≈₂ w
        ggnf'=id  {w} =
          let (w' , c) = nf w in
          begin
          gg (nf' w) ≈⟨ _≈₂_.refl ⟩
          gg ((map f₁ id)(nf w)) ≈⟨ _≈₂_.refl ⟩
          gg ((map f₁ id)(w' , c)) ≈⟨ _≈₂_.refl ⟩
          gg (f₁ w' , c) ≈⟨ _≈₂_.refl ⟩
          [ g₁ (f₁ w') ]ₓ • [ c ] ≈⟨ _≈₂_.cong (f*-cong (gf=id)) _≈₂_.refl ⟩
          [ w' ]ₓ • [ c ] ≈⟨ _≈₂_.sym (h**-hyp I w) ⟩
          [ I ] • w ≈⟨ _≈₂_.cong [I]≈ε _≈₂_.refl ⟩
          ε • w ≈⟨ _≈₂_.left-unit ⟩
          w ∎
          where
            open SR word-setoid₂


------------------------------------------------------------------------
-- Coset table with a distinguished identity coset
--
-- A variant of Data for the common case where the coset index comes
-- with a separate identity coset.  Here the cosets are C ⊎ ⊤, with the
-- identity coset I = inj₂ tt represented by the empty word, and the
-- user supplies the action h and section [_]ₒ on the "proper" cosets C
-- only.  The theorems are obtained by specialising Data at C ⊎ ⊤.

module Data-CT
  {M A : Set}
  (P₁   : WRel M)                        -- subgroup presentation
  (P₂   : WRel A)                        -- group presentation
  (C    : Set)                           -- proper cosets (identity added below)
  (f    : M → Word A)                    -- generator embedding
  (h    : C ⊎ ⊤ → A → Word M × (C ⊎ ⊤))  -- action on C ⊎ {identity}
  ([_]ₒ : C → Word A)                    -- section on the proper cosets
  where

  open PB P₁ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP P₁ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
  open PB P₂ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP P₂ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()

  open _≈₂_

  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C ⊎ ⊤})

  s1ct : Setoid _ _
  s1ct = PW.×-setoid word-setoid₁ (Eq.setoid (C ⊎ ⊤))

  [_]ₓ = f *

  I : C ⊎ ⊤
  I = inj₂ tt

  [_] : C ⊎ ⊤ → Word A
  [_] = [_,_] [_]ₒ (λ v → ε)

  module Assumptions-And-Theorems
    -- Action on an embedded generator f m: from a proper coset it stays
    -- proper (hcme); from the identity coset it returns the single
    -- letter m and stays in the identity coset (htme).
    (hcme : ∀ c m → ∃ \ w → ∃ \ c' → ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c'))
    (htme : ∀ m → ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt))
    -- ≈-level counterparts of htme / hcme.
    (htme~ : ∀ (m : M) → ([ m ]ʷ , I) ~ ((h **) I (f m)))
    (hcme~ : ∀ (c : C) (m : M) → let (w' , c' , p) = hcme c m in [ c ]ₒ • f m ≈₂ [ w' ]ₓ • [ c' ]ₒ)
    -- The same well-definedness and compatibility axioms as in Data.
    (h-wd-ax : ∀ (c : C ⊎ ⊤){u t : Word A} → u ===₂ t → ((h **) c u) ~ ((h **) c t))
    (f-wd-ax : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v)
    (h=ract :  ∀ c y → let (m' , c') = h c y in
      [ c ] • [ y ]ʷ ≈₂ [ m' ]ₓ • [ c' ])
    where

    hcm : C → M → Word M × C
    hcm c m with hcme c m
    ... | w , c' , hyp = w , c'

    hca : C → A → Word M × (C ⊎ ⊤)
    hca c a = h (inj₁ c) a

    hcm' : C ⊎ ⊤ → M → Word M × (C ⊎ ⊤)
    hcm' (inj₁ d) m with hcm d m
    ... | (wm , d') = wm , inj₁ d'
    hcm' (inj₂ tt) m = [ m ]ʷ , (inj₂ tt)

    htm : ⊤ → M → Word M × ⊤
    htm tt m = [ m ]ʷ , tt

    htm-hyp : ∀ m → htm tt m ≡ ([ m ]ʷ , tt)
    htm-hyp m = Eq.refl

    hcmw = hcm **
    hcmw' = hcm' **

    h**-hyp : ∀ c w → let (m' , c') = (h **) c w in
       [ c ] • w ≈₂ [ m' ]ₓ • [ c' ]
    h**-hyp c [ x ]ʷ = h=ract c x
    h**-hyp c ε = _≈₂_.trans _≈₂_.right-unit (_≈₂_.sym _≈₂_.left-unit)
    h**-hyp c (w • v) =
      let (wv' , c2) = (h **) c (w • v) in
      let (w' , c') = (h **) c w in
      let (v' , c'') = (h **) c' v in
      begin
      [ c ] • (w • v) ≈⟨ sym assoc ⟩
      ([ c ] • w) • v ≈⟨ cong (h**-hyp c w) refl ⟩
      ([ w' ]ₓ • [ c' ]) • v ≈⟨ assoc ⟩
      [ w' ]ₓ • [ c' ] • v ≈⟨ cong refl (h**-hyp c' v) ⟩
      [ w' ]ₓ • [ v' ]ₓ • [ c2 ] ≈⟨ sym assoc ⟩
      [ wv' ]ₓ • [ c2 ] ∎
      where
      open SR word-setoid₂

    hcm-hyp :  ∀ c m → let (m' , c') = hcm c m in
     [ c ]ₒ • f m ≈₂ [ m' ]ₓ • [ c' ]ₒ
    hcm-hyp c m with hcme c m | hcme~ c m | (h**-hyp) (inj₁ c) (f m)
    ... | w , c' , hyp | h2 | h3 rewrite hyp = h3

    hcm'-hyp :  ∀ c m → let (m' , c') = hcm' c m in
     [ c ] • f m ≈₂ [ m' ]ₓ • [ c' ]
    hcm'-hyp (inj₂ tt) m with htme m | htme~ m | (h**-hyp) (inj₂ tt) (f m)
    ... |  hyp | h2 | h3 rewrite hyp = h3
    hcm'-hyp (inj₁ c) m with hcme c m | hcme~ c m | (h**-hyp) (inj₁ c) (f m)
    ... | w , c' , hyp | h2 | h3 rewrite hyp = h3


    hca-hyp :  ∀ c a → let (w , c') = hca c a in
     [ c ]ₒ • [ a ]ʷ ≈₂ [ w ]ₓ • [ c' ]
    hca-hyp c a = h=ract (inj₁ c) a



    hcmw-hyp :  ∀ c m → let (m' , c') = hcmw c m in
       [ c ]ₒ • [ m ]ₓ ≈₂ [ m' ]ₓ • [ c' ]ₒ
    hcmw-hyp c m = lemma-**-act P₂ hcm [_]ₒ f hcm-hyp c m

    hcmw'-hyp :  ∀ c m → let (m' , c') = hcmw' c m in
       [ c ] • [ m ]ₓ ≈₂ [ m' ]ₓ • [ c' ]
    hcmw'-hyp c m = lemma-**-act P₂ hcm' [_] f hcm'-hyp c m


    [I]≡ε : [ inj₂ tt ] ≡ ε
    [I]≡ε = Eq.refl

    [I]≈ε : [ I ] ≈₂ ε
    [I]≈ε rewrite [I]≡ε = _≈₂_.refl

    module asData = Data P₁ P₂ (C ⊎ ⊤) (inj₂ tt) f h [_]

    open asData.Assumptions-And-Theorems htme~ h-wd-ax f-wd-ax [I]≈ε h=ract using (f*-injective ; nfx ; h-wd ; f-wd ; nfp') public 


    lemma-h**=hcmw : ∀ c w → let (w' , c') = hcmw c w in
      (h **) (inj₁ c) [ w ]ₓ ≡ (w' , inj₁ c')
    lemma-h**=hcmw c [ x ]ʷ with hcme c x
    ... | (w , c' , p) = p
    lemma-h**=hcmw c ε = Eq.refl
    lemma-h**=hcmw c (w • w₁) rewrite lemma-h**=hcmw c w | lemma-h**=hcmw (hcmw c w .proj₂) w₁ = Eq.refl

    hcmw-cong : ∀ c w v → w ≈₁ v → hcmw c w .proj₁ ≈₁ hcmw c v .proj₁
    hcmw-cong c w v eq =
      begin
      hcmw c w .proj₁ ≡⟨ Eq.sym ( Eq.cong proj₁ (lemma-h**=hcmw c w)) ⟩
      (h **) (inj₁ c) [ w ]ₓ .proj₁ ≈⟨ proj₁ (h-wd (inj₁ c) (f-wd eq)) ⟩
      (h **) (inj₁ c) [ v ]ₓ .proj₁ ≡⟨ Eq.cong proj₁ (lemma-h**=hcmw c v) ⟩
      hcmw c v .proj₁ ∎
      where
      open SR word-setoid₁

    hcmw-cong2 : ∀ c w v → w ≈₁ v → hcmw c w .proj₂ ≡ hcmw c v .proj₂
    hcmw-cong2 c w v eq = inj₁-injective ( 
      begin
      inj₁ (hcmw c w .proj₂) ≡⟨ Eq.sym ( Eq.cong proj₂ (lemma-h**=hcmw c w)) ⟩
      (h **) (inj₁ c) [ w ]ₓ .proj₂ ≡⟨ proj₂ (h-wd (inj₁ c) (f-wd eq)) ⟩
      (h **) (inj₁ c) [ v ]ₓ .proj₂ ≡⟨ Eq.cong proj₂ (lemma-h**=hcmw c v) ⟩
      inj₁ (hcmw c v .proj₂) ∎)
      where
      open Eq.≡-Reasoning


    lemma-h**=hcmw' : ∀ c w → let (w' , c') = hcmw' c w in
      (h **) c [ w ]ₓ ≡ (w' , c')
    lemma-h**=hcmw' (inj₁ c) [ x ]ʷ with hcme c x
    ... | (w , c' , p) = p
    lemma-h**=hcmw' (inj₂ tt) [ x ]ʷ with htme x
    ... | (p) = p
    lemma-h**=hcmw' c ε = Eq.refl
    lemma-h**=hcmw' c (w • w₁) rewrite lemma-h**=hcmw' c w | lemma-h**=hcmw' (hcmw' c w .proj₂) w₁ = Eq.refl


    hcmw-cong' : ∀ c w v → w ≈₁ v → hcmw' c w .proj₁ ≈₁ hcmw' c v .proj₁
    hcmw-cong' c w v eq =
      begin
      hcmw' c w .proj₁ ≡⟨ Eq.sym ( Eq.cong proj₁ (lemma-h**=hcmw' c w)) ⟩
      (h **) ( c) [ w ]ₓ .proj₁ ≈⟨ proj₁ (h-wd ( c) (f-wd eq)) ⟩
      (h **) ( c) [ v ]ₓ .proj₁ ≡⟨ Eq.cong proj₁ (lemma-h**=hcmw' c v) ⟩
      hcmw' c v .proj₁ ∎
      where
      open SR word-setoid₁


    hcmw-cong'2 : ∀ c w v → w ≈₁ v → hcmw' c w .proj₂ ≡ hcmw' c v .proj₂
    hcmw-cong'2 c w v eq = 
      begin
      hcmw' c w .proj₂ ≡⟨ Eq.sym ( Eq.cong proj₂ (lemma-h**=hcmw' c w)) ⟩
      (h **) ( c) [ w ]ₓ .proj₂ ≡⟨ proj₂ (h-wd ( c) (f-wd eq)) ⟩
      (h **) ( c) [ v ]ₓ .proj₂ ≡⟨ Eq.cong proj₂ (lemma-h**=hcmw' c v) ⟩
      hcmw' c v .proj₂ ∎
      where
      open Eq.≡-Reasoning


    h-wd-m : ∀ (c : C){u t : Word M} → u ≈₁ t →
      let (w' , c') = hcmw c u in
      let (w'' , c'') = hcmw c t in
      (w' , inj₁ c') ~ (w'' , inj₁ c'')
    h-wd-m c {u} {t} eqax =
      let (w' , c') = hcmw c u in
      let (w'' , c'') = hcmw c t in
      begin
      (w' , inj₁ c') ≡⟨ Eq.sym (lemma-h**=hcmw c u) ⟩
      ((h **) (inj₁ c) [ u ]ₓ) ≈⟨ h-wd (inj₁ c) (f-wd ( eqax)) ⟩
      ((h **) (inj₁ c) [ t ]ₓ) ≡⟨ (lemma-h**=hcmw c t) ⟩ 
      (w'' , inj₁ c'') ∎
      where open SR s1ct




------------------------------------------------------------------------
-- Packaged coset-table assumptions
--
-- Bundles the data and hypotheses of Data-CT into a single record, so a
-- caller can hand over the whole transfer as one value.  Opening it
-- re-exports every theorem of Data-CT.Assumptions-And-Theorems.

record PackedCosetTable
  {M A : Set}
  (P₁ : WRel M)
  (P₂ : WRel A) : Set₁
  where

  open PB P₁ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
  open PP P₁ renaming (•-ε-monoid to m₁ ; word-setoid to word-setoid₁) using ()
  open PB P₂ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()
  open PP P₂ renaming (•-ε-monoid to m₂ ; word-setoid to word-setoid₂) using ()

  open _≈₂_

  field
    C : Set
    f : M → Word A
    h : C ⊎ ⊤ → A → Word M × (C ⊎ ⊤)
    [_]ₒ : C → Word A
  
  infix 4 _~_
  _~_ = PW.Pointwise _≈₁_ (_≡_ {A = C ⊎ ⊤})
  
  s1ct : Setoid _ _
  s1ct = PW.×-setoid word-setoid₁ (Eq.setoid (C ⊎ ⊤))

  [_]ₓ = f *
  
  I : C ⊎ ⊤
  I = inj₂ tt
  
  [_] : C ⊎ ⊤ → Word A
  [_] = [_,_] [_]ₒ (λ v → ε)

  field
    -- Action on embedded generators (see Data-CT for the meaning).
    hcme : ∀ c m → ∃ \ w → ∃ \ c' → ((h **) (inj₁ c) (f m)) ≡ (w , inj₁ c')
    htme : ∀ m → ((h **) (inj₂ tt) (f m)) ≡ ([ m ]ʷ , inj₂ tt)
    

  field
    htme~ : ∀ (m : M) → ([ m ]ʷ , I) ~ ((h **) I (f m))
    hcme~ : ∀ (c : C) (m : M) → let (w' , c' , p) = hcme c m in [ c ]ₒ • f m ≈₂ [ w' ]ₓ • [ c' ]ₒ 
    h-wd-ax : ∀ (c : C ⊎ ⊤){u t : Word A} → u ===₂ t → ((h **) c u) ~ ((h **) c t)
    f-wd-ax : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v
    h=ract :  ∀ c y → let (m' , c') = h c y in
     [ c ] • [ y ]ʷ ≈₂ [ m' ]ₓ • [ c' ]


  module asDataCT = Data-CT P₁ P₂ C f h [_]ₒ
  open asDataCT.Assumptions-And-Theorems hcme htme htme~ hcme~ h-wd-ax f-wd-ax h=ract public


------------------------------------------------------------------------
-- Coset tower
--
-- Iterating the single-level coset extension (module Data) up an
-- ℕ-indexed family of presentations.  Given
--   * a family of presentations  P : ∀ n → WRel (X n),
--   * a family of coset types     Cᶜ : ℕ → Set,
--   * for each n an Extension n bundling the single-level coset data
--     (embedding f, coset action h, section [_], and the five
--     Reidemeister–Schreier hypotheses) taking P n to P (suc n),
--   * a base normal form for P 0,
-- the tower produces a normal form (NormalFormWithoutInverse / NormalForm) for
-- every level P n by folding the single-level extension.

module CosetTower
  (X  : ℕ → Set)
  (P  : ∀ n → WRel (X n))
  (Cᶜ : ℕ → Set)
  where

  -- One level of coset extension, from P n to P (suc n).
  record Extension (n : ℕ) : Set₁ where
    open PB (P n)       renaming (_===_ to _===₁_ ; _≈_ to _≈₁_) using ()
    open PB (P (suc n)) renaming (_===_ to _===₂_ ; _≈_ to _≈₂_) using ()

    infix 4 _~_
    _~_ = PW.Pointwise _≈₁_ (_≡_ {A = Cᶜ n})

    field
      I    : Cᶜ n
      f    : X n → Word (X (suc n))
      h    : Cᶜ n → X (suc n) → Word (X n) × Cᶜ n
      [_]  : Cᶜ n → Word (X (suc n))

      h=⁻¹f-gen : ∀ (x : X n) → ([ x ]ʷ , I) ~ ((h **) I (f x))
      h-wd-ax   : ∀ (c : Cᶜ n) {u t : Word (X (suc n))} →
                  u ===₂ t → ((h **) c u) ~ ((h **) c t)
      f-wd-ax   : ∀ {w v} → w ===₁ v → (f *) w ≈₂ (f *) v
      [I]≈ε     : [ I ] ≈₂ ε
      h=ract    : ∀ c b → let (b' , c') = h c b in
                  [ c ] • [ b ]ʷ ≈₂ (f *) b' • [ c' ]

    module D = Data (P n) (P (suc n)) (Cᶜ n) I f h [_]
    open D.Assumptions-And-Theorems
      h=⁻¹f-gen h-wd-ax f-wd-ax [I]≈ε h=ract public
      using (nfp ; nfp')

  -- Fold the extensions over the tower, from a base normal form for P 0.
  module _ (ext : ∀ n → Extension n) where

    nfp-tower : NormalFormWithoutInverse (P 0) → ∀ n → NormalFormWithoutInverse (P n)
    nfp-tower base zero    = base
    nfp-tower base (suc n) = Extension.nfp (ext n) (nfp-tower base n)

    nfp'-tower : NormalForm (P 0) → ∀ n → NormalForm (P n)
    nfp'-tower base zero    = base
    nfp'-tower base (suc n) = Extension.nfp' (ext n) (nfp'-tower base n)

------------------------------------------------------------------------
-- Presentations of groups
--
-- Free, direct, semi-direct, and amalgamated products of presented
-- monoids, together with congruence lifting and the transport of
-- normal forms along monoid monomorphisms
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Presentation.Construct.Base where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ ; zero)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
import Presentation.Base as PB
import Normalization.Base as NFBase
import Presentation.Properties as PP
open import Word.Base

------------------------------------------------------------------------
-- Embeddings

-- Embed a word over A as a word over A ⊎ B.
[_]ₗ : ∀ {A B} → Word A → Word (A ⊎ B)
[_]ₗ {A} {B} = wmap inj₁

-- Embed a word over B as a word over A ⊎ B.
[_]ᵣ : ∀ {A B} → Word B → Word (A ⊎ B)
[_]ᵣ {A} {B} = wmap inj₂

------------------------------------------------------------------------
-- Relation combinators

infix 5 _⸲_⸲_
infixr 5 _∪_

-- Join a relation on Word A, a relation on Word B, and a mixed
-- relation on Word (A ⊎ B) into one relation on Word (A ⊎ B).  The
-- mixed component Γ₃ is what distinguishes the various products.
data _⸲_⸲_ {A B} (Γ₁ : WRel A) (Γ₂ : WRel B) (Γ₃ : WRel (A ⊎ B))
    : WRel (A ⊎ B) where
  left  : ∀ {u v} → Γ₁ u v → (Γ₁ ⸲ Γ₂ ⸲ Γ₃) [ u ]ₗ [ v ]ₗ
  right : ∀ {u v} → Γ₂ u v → (Γ₁ ⸲ Γ₂ ⸲ Γ₃) [ u ]ᵣ [ v ]ᵣ
  mid   : ∀ {u v} → Γ₃ u v → (Γ₁ ⸲ Γ₂ ⸲ Γ₃) u v

-- Union of two relations over the same generating set.
data _∪_ {A} (Γ₁ Γ₂ : WRel A) : WRel A where
  left  : ∀ {u v} → Γ₁ u v → (Γ₁ ∪ Γ₂) u v
  right : ∀ {u v} → Γ₂ u v → (Γ₁ ∪ Γ₂) u v

------------------------------------------------------------------------
-- Primitive relation families

-- The empty relation: no axioms.
data Γₑ {A} : WRel A where

-- The coarsest relation: every word is identified with ε.
data Γᵤ {A} : WRel A where
  alleq : ∀ {w} → Γᵤ {A} w ε

-- Commutation: left generators commute with right generators.
data Γₓ {A B} : WRel (A ⊎ B) where
  comm : (a : A) (b : B) →
         Γₓ ([ [ a ]ʷ ]ₗ • [ [ b ]ʷ ]ᵣ) ([ [ b ]ʷ ]ᵣ • [ [ a ]ʷ ]ₗ)

-- Conjugation: moving a right generator h past a left generator n
-- replaces n by its conjugate, a single generator.
data Γⱼ {N H} (conj : H → N → N) : WRel (N ⊎ H) where
  comm : (n : N) (h : H) →
         Γⱼ conj ([ [ h ]ʷ ]ᵣ • [ [ n ]ʷ ]ₗ)
                 ([ [ conj h n ]ʷ ]ₗ • [ [ h ]ʷ ]ᵣ)

-- Conjugation, word-valued: as Γⱼ, but the conjugate of a generator
-- may be an arbitrary word over N.
data Γⱼ' {N H} (conj : H → N → Word N) : WRel (N ⊎ H) where
  comm : (n : N) (h : H) →
         Γⱼ' conj ([ [ h ]ʷ ]ᵣ • [ [ n ]ʷ ]ₗ)
                  ([ conj h n ]ₗ • [ [ h ]ʷ ]ᵣ)

-- Amalgamation: identify the two embedded images of a common
-- generating set M.
data Γₐ {M A B : Set} (f₁ : M → Word A) (f₂ : M → Word B)
    : WRel (A ⊎ B) where
  amal : ∀ {m} → Γₐ f₁ f₂ [ (f₁ m) ]ₗ [ (f₂ m) ]ᵣ

-- Sugar relation.  Each newly added generator m desugars to a word
-- over A.
data Γₛ {M A} (f : M → Word A) : WRel (M ⊎ A) where
  desugar : ∀ {m} → Γₛ f [ inj₁ m ]ʷ [ f m ]ᵣ

------------------------------------------------------------------------
-- Product constructions

-- Free product.
infix 4 _*_
_*_ : {A B : Set} → WRel A → WRel B → WRel (A ⊎ B)
_*_  Γ Δ = Γ ⸲ Δ ⸲ Γₑ

-- Direct product.
infix 4 _⊕_
_⊕_ : {A B : Set} → WRel A → WRel B → WRel (A ⊎ B)
_⊕_  Γ Δ = Γ ⸲ Δ ⸲ Γₓ

-- n-fold sum of generating sets.
infix 4 _⊎^_
_⊎^_ : Set → ℕ → Set
_⊎^_ A zero = ⊥
_⊎^_ A (₁₊ zero) = A
_⊎^_ A (₂₊ n) = A ⊎ (A ⊎^ (₁₊ n))

-- n-fold direct product.
infix 4 _⊕^_
_⊕^_ : {A : Set} → WRel A → (n : ℕ) → WRel (A ⊎^ n)
_⊕^_ {A} Γ zero = Γₑ
_⊕^_ {A} Γ (₁₊ zero) = Γ
_⊕^_ {A} Γ (₂₊ n) = Γ ⸲ Γ ⊕^ (₁₊ n) ⸲ Γₓ

-- Semi-direct product.
infix 4 _⋊_⋆_
_⋊_⋆_ : {N H : Set} → WRel N → WRel H → (conj : H → N → N) →
        WRel (N ⊎ H)
_⋊_⋆_  Γ Δ conj = Γ ⸲ Δ ⸲ Γⱼ conj

-- Amalgamated product.
infix 4 _*_⋆_⋆_
_*_⋆_⋆_ : {M A B : Set} → WRel A → WRel B →
          (f₁ : M → Word A) → (f₂ : M → Word B) → WRel (A ⊎ B)
_*_⋆_⋆_  Γ Δ f₁ f₂ = Γ ⸲ Δ ⸲ Γₐ f₁ f₂

------------------------------------------------------------------------
-- Congruence lifting

-- Equalities in the component presentations lift to equalities in
-- the join Γ ⸲ Δ ⸲ Λ, along the embeddings [_]ₗ and [_]ᵣ.
module LeftRightCongruence
  {A B : Set}
  (Γ : WRel A)
  (Δ : WRel B)
  (Λ : WRel (A ⊎ B))
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PB {A ⊎ B} (Γ ⸲ Δ ⸲ Λ) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_)

  -- [_]ₗ maps the congruence of Γ into the congruence of the join.
  lefts :  ∀ {u v} → u ≈₁ v → [ u ]ₗ ≈₃ [ v ]ₗ
  lefts {u} {v} refl = _≈₃_.refl
  lefts {u} {v} (sym h) = _≈₃_.sym (lefts h)
  lefts {u} {v} (trans h h₁) = _≈₃_.trans (lefts h) (lefts h₁)
  lefts {u} {v} (cong h h₁) = _≈₃_.cong (lefts h) (lefts h₁)
  lefts {u} {v} assoc = _≈₃_.assoc
  lefts {u} {v} left-unit = _≈₃_.left-unit
  lefts {u} {v} right-unit = _≈₃_.right-unit
  lefts {u} {v} (axiom x) = _≈₃_.axiom (left x)

  -- [_]ᵣ maps the congruence of Δ into the congruence of the join.
  rights :  ∀ {u v} → u ≈₂ v → [ u ]ᵣ ≈₃ [ v ]ᵣ
  rights {u} {v} refl = _≈₃_.refl
  rights {u} {v} (sym h) = _≈₃_.sym (rights h)
  rights {u} {v} (trans h h₁) = _≈₃_.trans (rights h) (rights h₁)
  rights {u} {v} (cong h h₁) = _≈₃_.cong (rights h) (rights h₁)
  rights {u} {v} assoc = _≈₃_.assoc
  rights {u} {v} left-unit = _≈₃_.left-unit
  rights {u} {v} right-unit = _≈₃_.right-unit
  rights {u} {v} (axiom x) = _≈₃_.axiom (right x)

-- Equalities in either component presentation lift to equalities in
-- the union Γ ∪ Δ.
module LeftRightCongruence-∪
  {A : Set}
  (Γ : WRel A)
  (Δ : WRel A)
  where

  open PB Γ renaming (_===_ to _===₁_ ; _≈_ to _≈₁_)
  open PB Δ renaming (_===_ to _===₂_ ; _≈_ to _≈₂_)
  open PB (Γ ∪ Δ) renaming (_===_ to _===₃_ ; _≈_ to _≈₃_)

  -- The congruence of Γ is included in the congruence of Γ ∪ Δ.
  lefts :  ∀ {u v} → u ≈₁ v → u ≈₃ v
  lefts {u} {v} refl = _≈₃_.refl
  lefts {u} {v} (sym h) = _≈₃_.sym (lefts h)
  lefts {u} {v} (trans h h₁) = _≈₃_.trans (lefts h) (lefts h₁)
  lefts {u} {v} (cong h h₁) = _≈₃_.cong (lefts h) (lefts h₁)
  lefts {u} {v} assoc = _≈₃_.assoc
  lefts {u} {v} left-unit = _≈₃_.left-unit
  lefts {u} {v} right-unit = _≈₃_.right-unit
  lefts {u} {v} (axiom x) = _≈₃_.axiom (left x)

  -- The congruence of Δ is included in the congruence of Γ ∪ Δ.
  rights :  ∀ {u v} → u ≈₂ v → u ≈₃ v
  rights {u} {v} refl = _≈₃_.refl
  rights {u} {v} (sym h) = _≈₃_.sym (rights h)
  rights {u} {v} (trans h h₁) = _≈₃_.trans (rights h) (rights h₁)
  rights {u} {v} (cong h h₁) = _≈₃_.cong (rights h) (rights h₁)
  rights {u} {v} assoc = _≈₃_.assoc
  rights {u} {v} left-unit = _≈₃_.left-unit
  rights {u} {v} right-unit = _≈₃_.right-unit
  rights {u} {v} (axiom x) = _≈₃_.axiom (right x)

------------------------------------------------------------------------
-- Transporting normal forms

-- A normal form for Γ gives a weak normal form for the union Γ ∪ Δ.
anfpₗ : ∀ {A} {Γ Δ : WRel A} →
        NFBase.NormalFormWithoutInverse Γ → NFBase.WeakNormalForm (Γ ∪ Δ)
anfpₗ {A} {Γ} {Δ} nfp = record
  { ANF = NF
  ; anf = nf
  ; anf-injective = λ x → lefts (nf-injective x)
  }
  where
  open NFBase.NormalFormWithoutInverse nfp
  open LeftRightCongruence-∪ Γ Δ

-- A weak normal form for Γ gives one for the union Γ ∪ Δ.
anfpₗ' : ∀ {A} {Γ Δ : WRel A} →
         NFBase.WeakNormalForm Γ → NFBase.WeakNormalForm (Γ ∪ Δ)
anfpₗ' {A} {Γ} {Δ} anfp = record
  { ANF = ANF
  ; anf = anf
  ; anf-injective = λ x → lefts (anf-injective x)
  }
  where
  open NFBase.WeakNormalForm anfp
  open LeftRightCongruence-∪ Γ Δ

-- A normal form for Δ gives a weak normal form for the union Γ ∪ Δ.
anfpᵣ : ∀ {A} {Γ Δ : WRel A} →
        NFBase.NormalFormWithoutInverse Δ → NFBase.WeakNormalForm (Γ ∪ Δ)
anfpᵣ {A} {Γ} {Δ} nfp = record
  { ANF = NF
  ; anf = nf
  ; anf-injective = λ x → rights (nf-injective x)
  }
  where
  open NFBase.NormalFormWithoutInverse nfp
  open LeftRightCongruence-∪ Γ Δ

-- A weak normal form for Δ gives one for the union Γ ∪ Δ.
anfpᵣ' : ∀ {A} {Γ Δ : WRel A} →
         NFBase.WeakNormalForm Δ → NFBase.WeakNormalForm (Γ ∪ Δ)
anfpᵣ' {A} {Γ} {Δ} anfp = record
  { ANF = ANF
  ; anf = anf
  ; anf-injective = λ x → rights (anf-injective x)
  }
  where
  open NFBase.WeakNormalForm anfp
  open LeftRightCongruence-∪ Γ Δ

-- Pull a weak normal form back along a monoid monomorphism between
-- the presented monoids.
mono-anfp : ∀ {A B} {Γ : WRel A} {Δ : WRel B} →
  NFBase.WeakNormalForm Δ → (f : Word A → Word B) →
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidMonomorphism (Monoid.rawMonoid m₁)
    ((Monoid.rawMonoid m₂)) f → NFBase.WeakNormalForm (Γ)
mono-anfp {A} {B} {Γ} {Δ} anfp f mono = record
  { ANF = ANF ; anf = anf ∘ f ; anf-injective = inj }
  where
  open PB Γ renaming (_≈_ to _≈₁_)
  open PB Δ renaming (_≈_ to _≈₂_)
  open NFBase.WeakNormalForm anfp
  open MonoidMorphisms.IsMonoidMonomorphism mono
    renaming (injective to f-inj)
  inj : {w v : Word A} → anf (f w) ≡ anf (f v) → w ≈₁ v
  inj {w} {v} eq = f-inj (anf-injective eq)

-- Pull a normal form (without inverse) back along a monoid
-- monomorphism between the presented monoids.
mono-nfp : ∀ {A B} {Γ : WRel A} {Δ : WRel B} →
  NFBase.NormalFormWithoutInverse Δ → (f : Word A → Word B) →
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidMonomorphism (Monoid.rawMonoid m₁)
    ((Monoid.rawMonoid m₂)) f → NFBase.NormalFormWithoutInverse (Γ)
mono-nfp {A} {B} {Γ} {Δ} nfp f mono = record
  { NF = NF ; nf = nf ∘ f ; nf-cong = nf∘f-cong ; nf-injective = inj }
  where
  open PB Γ renaming (_≈_ to _≈₁_)
  open PB Δ renaming (_≈_ to _≈₂_)
  open NFBase.NormalFormWithoutInverse nfp
  open MonoidMorphisms.IsMonoidMonomorphism mono
    renaming (injective to f-inj)
  inj : {w v : Word A} → nf (f w) ≡ nf (f v) → w ≈₁ v
  inj {w} {v} eq = f-inj (nf-injective eq)

  nf∘f-cong : {w v : Word A} → w ≈₁ v → nf (f w) ≡ nf (f v)
  nf∘f-cong {w} {v} eq = nf-cong (⟦⟧-cong eq)

-- Pull a normal form back along a monoid isomorphism between the
-- presented monoids.
iso-nfp' : ∀ {A B} {Γ : WRel A} {Δ : WRel B} →
  NFBase.NormalForm Δ → (f : Word A → Word B) →
  let open PP Γ renaming (•-ε-monoid to m₁) in
  let open PP Δ renaming (•-ε-monoid to m₂) in
  MonoidMorphisms.IsMonoidIsomorphism (Monoid.rawMonoid m₁)
    ((Monoid.rawMonoid m₂)) f → NFBase.NormalForm (Γ)
iso-nfp' {A} {B} {Γ} {Δ} nfp f iso = record
  { NF = NF
  ; nf = nf ∘ f
  ; nf-cong = nf∘f-cong
  ; inv-nf = f⁻¹ ∘ inv-nf
  ; inv-nf∘nf=id = f⁻¹∘nf⁻¹∘nf∘f≈id
  }
  where
  open PB Γ renaming (_≈_ to _≈₁_ ; refl to refl₁)
  open PB Δ renaming (_≈_ to _≈₂_ ; trans to trans₂)
  open NFBase.NormalForm nfp
  open MonoidMorphisms.IsMonoidIsomorphism iso
    renaming (injective to f-inj ; surjective to f-surj)

  nf∘f-cong : {w v : Word A} → w ≈₁ v → nf (f w) ≡ nf (f v)
  nf∘f-cong {w} {v} eq = nf-cong (⟦⟧-cong eq)

  f⁻¹ : Word B → Word A
  f⁻¹ x with f-surj x
  ... | (y , _) = y

  f∘f⁻¹≈id : ∀ {x} → f (f⁻¹ x) ≈₂ x
  f∘f⁻¹≈id {x} with f-surj x
  ... | (y , p) = p refl₁

  f⁻¹∘nf⁻¹∘nf∘f≈id : {w : Word A} → f⁻¹ (inv-nf (nf (f w))) ≈₁ w
  f⁻¹∘nf⁻¹∘nf∘f≈id {w} with f-surj (f w)
  ... | (y , p) = f-inj (trans₂ f∘f⁻¹≈id inv-nf∘nf=id)

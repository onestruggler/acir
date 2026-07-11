------------------------------------------------------------------------
-- Presentations of groups
--
-- Properties of the free-monoid functor (wmap, wconcat, wconcatmap)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Word.Properties where

open import Data.Nat using (ℕ ; suc ; zero)
open import Function using (_∘_ ; id)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≗_)
open import Relation.Nullary using (yes ; no)

open import Notations
open import Word.Base

private
  variable
    A B C X Y Z : Set

------------------------------------------------------------------------
-- wmap / wconcat fusion laws

-- wmap distributes over composition.
wmap-∘ : {g : B → C} {f : A → B} → wmap (g ∘ f) ≗ wmap g ∘ wmap f
wmap-∘ [ x ]ʷ   = Eq.refl
wmap-∘ ε        = Eq.refl
wmap-∘ (w • w₁) = Eq.cong₂ _•_ (wmap-∘ w) (wmap-∘ w₁)

-- wconcat ∘ wmap [_]ʷ is the identity.
wconcatmap-[-]ʷ : (wconcat {A = A} ∘ wmap [_]ʷ) ≗ id
wconcatmap-[-]ʷ [ x ]ʷ = Eq.refl
wconcatmap-[-]ʷ ε      = Eq.refl
wconcatmap-[-]ʷ (w • w₁)
  rewrite wconcatmap-[-]ʷ w | wconcatmap-[-]ʷ w₁ = Eq.refl

-- wconcatmap with a singleton-wrapped function equals wmap.
wconcatmap-[f]ʷ : {f : A → B} → (wconcat ∘ wmap ([_]ʷ ∘ f)) ≗ wmap f
wconcatmap-[f]ʷ [ x ]ʷ     = Eq.refl
wconcatmap-[f]ʷ ε          = Eq.refl
wconcatmap-[f]ʷ (ws • ws₁) =
  Eq.cong₂ _•_ (wconcatmap-[f]ʷ ws) (wconcatmap-[f]ʷ ws₁)

-- wconcat commutes with wmap of wmap.
wconcat-wmap : {f : A → B} → wconcat ∘ (wmap (wmap f)) ≗ wmap f ∘ wconcat
wconcat-wmap [ ws ]ʷ    = Eq.refl
wconcat-wmap ε          = Eq.refl
wconcat-wmap (ws • ws₁) =
  Eq.cong₂ _•_ (wconcat-wmap ws) (wconcat-wmap ws₁)

-- (f ʷ) distributes over word powers.
lemma-fʷ-w^n : {f : A → Word B} {w : Word A} (n : ℕ) →
               wconcatmap f (w ^ n) ≡ wconcatmap f w ^ n
lemma-fʷ-w^n zero      = Eq.refl
lemma-fʷ-w^n (₁₊ zero) = Eq.refl
lemma-fʷ-w^n (₂₊ n)    = Eq.cong₂ _•_ Eq.refl (lemma-fʷ-w^n (₁₊ n))

-- Post-composing the target of a wconcatmap with a map fuses.
lemma-ʷ-∘ : (f : A → Word B) → (g : B → C) → (w : Word A) →
            wconcatmap (wmap g ∘ f) w ≡ (wmap g ∘ wconcatmap f) w
lemma-ʷ-∘ f g [ x ]ʷ   = Eq.refl
lemma-ʷ-∘ f g ε        = Eq.refl
lemma-ʷ-∘ f g (w • w₁) = Eq.cong₂ _•_ (lemma-ʷ-∘ f g w) (lemma-ʷ-∘ f g w₁)

------------------------------------------------------------------------
-- Congruence for wfoldr / wfoldl

-- If ⊕ respects R in its accumulator argument, then folding ⊕ over a
-- word does too.
wfoldr-cong :
  {_⊕_ : X → Y → Y} (R : Y → Y → Set) →
  (hyp : (a : X) → ∀ {b1 b2} → R b1 b2 → R (a ⊕ b1) (a ⊕ b2)) →
  ∀ (w : Word X) → ∀ {b1 b2} → R b1 b2 →
  let _⊕'_ = wfoldr _⊕_ in R (w ⊕' b1) (w ⊕' b2)
wfoldr-cong R hyp [ x ]ʷ  eq = hyp x eq
wfoldr-cong R hyp ε        eq = eq
wfoldr-cong {_⊕_ = _⊕_} R hyp (w • w₁) eq
  with wfoldr-cong R hyp w₁ eq
... | ih with (let _⊕'_ = wfoldr _⊕_ in wfoldr-cong R hyp w {w₁ ⊕' _} {w₁ ⊕' _})
... | ih2 = ih2 ih

-- If ⊕ respects R in its accumulator argument, then folding ⊕ over a
-- word does too (left fold).
wfoldl-cong :
  {_⊕_ : Y → X → Y} (R : Y → Y → Set) →
  (hyp : (a : X) → ∀ {b1 b2} → R b1 b2 → R (b1 ⊕ a) (b2 ⊕ a)) →
  ∀ (w : Word X) → ∀ {b1 b2} → R b1 b2 →
  let _⊕'_ = wfoldl _⊕_ in R (b1 ⊕' w) (b2 ⊕' w)
wfoldl-cong R hyp [ x ]ʷ  eq = hyp x eq
wfoldl-cong R hyp ε        eq = eq
wfoldl-cong {_⊕_ = _⊕_} R hyp (w • w₁) eq
  with wfoldl-cong R hyp w eq
... | ih with (let _⊕'_ = wfoldl _⊕_ in wfoldl-cong R hyp w₁ {_ ⊕' w} {_ ⊕' w})
... | ih2 = ih2 ih

------------------------------------------------------------------------
-- Decidable equality

-- If B has decidable equality, so does Word B.
≡-dec : DecidableEquality B → DecidableEquality (Word B)
≡-dec deceqB [ x ]ʷ [ x₁ ]ʷ with deceqB x x₁
... | yes p = yes (Eq.cong [_]ʷ p)
... | no np = no (λ { Eq.refl → np Eq.refl })
≡-dec deceqB [ x ]ʷ   ε         = no (λ { () })
≡-dec deceqB [ x ]ʷ   (y • y₁)  = no (λ { () })
≡-dec deceqB ε        [ x ]ʷ    = no (λ { () })
≡-dec deceqB ε        ε         = yes Eq.refl
≡-dec deceqB ε        (y • y₁)  = no (λ { () })
≡-dec deceqB (x • x₁) [ x₂ ]ʷ   = no (λ { () })
≡-dec deceqB (x • x₁) ε         = no (λ { () })
≡-dec deceqB (x • x₁) (y • y₁)
  with ≡-dec deceqB x y | ≡-dec deceqB x₁ y₁
... | yes p  | yes p' = yes (Eq.cong₂ _•_ p p')
... | yes p  | no np' = no (λ { Eq.refl → np' Eq.refl })
... | no np  | _      = no (λ { Eq.refl → np  Eq.refl })

------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of a product of letters over P: the scalar exponent
-- adds up and the operators multiply; products of diagonal operators;
-- and a product over an enumeration of contexts whose factors are
-- trivial but at one context
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.EncodingSemantics.Products where

open import Data.Bool using (Bool ; true ; false ; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; foldr)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Soundness.Operators using (diag ; diag-⊙ ; diag-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
import Examples.Groups.Real-Clifford+CH.Section8 as Section8

------------------------------------------------------------------------
-- The reading of a product

module _ {m : ℕ} where
  private
    n : ℕ
    n = ₃₊ m

  ⟦_⟧Y : Word (GenP n) → Scaled n
  ⟦ u ⟧Y = Section8.⟦_⟧Y m u

  -- The exponents add up.
  ∏-ℓ : ∀ {A : Set} (cs : List A) (f : A → Word (GenP n)) →
        proj₁ ⟦ ∏ cs f ⟧Y ≡ foldr (λ c k → proj₁ ⟦ f c ⟧Y +ℕ k) 0 cs
  ∏-ℓ []       f = Eq.refl
  ∏-ℓ (c ∷ cs) f = Eq.cong (proj₁ ⟦ f c ⟧Y +ℕ_) (∏-ℓ cs f)

  -- The operators multiply, the first letter first.
  ∏-M : ∀ {A : Set} (cs : List A) (f : A → Word (GenP n)) →
        proj₂ ⟦ ∏ cs f ⟧Y ≐ foldr (λ c M → proj₂ ⟦ f c ⟧Y ⊙ M) Idₒ cs
  ∏-M []       f = ≐-refl Idₒ
  ∏-M (c ∷ cs) f = ⊙-cong (≐-refl (proj₂ ⟦ f c ⟧Y)) (∏-M cs f)

------------------------------------------------------------------------
-- Products of operators, factor by factor

fold-cong : ∀ {A : Set} {n} (cs : List A) {F G : A → Op n} → (∀ c → F c ≐ G c) →
            foldr (λ c M → F c ⊙ M) Idₒ cs ≐ foldr (λ c M → G c ⊙ M) Idₒ cs
fold-cong []       e = ≐-refl Idₒ
fold-cong (c ∷ cs) e = ⊙-cong (e c) (fold-cong cs e)

------------------------------------------------------------------------
-- Products of diagonal operators

-- The pointwise product of the signs of a list of factors.
∏ᶠ : ∀ {A : Set} {n} → List A → (A → Bits n → 𝔽) → Bits n → 𝔽
∏ᶠ cs g x = foldr (λ c acc → g c x * acc) 1# cs

diag-1 : ∀ {n} → diag {n} (λ _ → 1#) ≐ Idₒ
diag-1 x y = *-identityˡ (δb x y)

diag-fold : ∀ {A : Set} {n} (cs : List A) (g : A → Bits n → 𝔽) →
            foldr (λ c M → diag (g c) ⊙ M) Idₒ cs ≐ diag (∏ᶠ cs g)
diag-fold []       g = ≐-sym diag-1
diag-fold (c ∷ cs) g =
  ≐-trans (⊙-cong (≐-refl (diag (g c))) (diag-fold cs g)) (diag-⊙ (g c) (∏ᶠ cs g))

------------------------------------------------------------------------
-- Evaluating a product over an enumeration

-- All the enumerated factors trivial.
∏ᶠ-one : ∀ {k n} (cs : List (Bits k)) (g : Bits k → Bits n → 𝔽) (x : Bits n) →
         (∀ c → c ∈ᵇ cs ≡ true → g c x ≡ 1#) → ∏ᶠ cs g x ≡ 1#
∏ᶠ-one []       g x h = Eq.refl
∏ᶠ-one (c ∷ cs) g x h =
  Eq.trans (Eq.cong₂ _*_ (h c (Eq.cong (_∨ (c ∈ᵇ cs)) (eqB-refl c)))
                         (∏ᶠ-one cs g x (λ c′ p → h c′ (Eq.trans (Eq.cong (eqB c′ c ∨_) p) (∨-true (eqB c′ c))))))
           (*-identityˡ 1#)
  where
  ∨-true : ∀ a → a ∨ true ≡ true
  ∨-true true  = Eq.refl
  ∨-true false = Eq.refl

-- All factors trivial but the one at c₀, which occurs exactly once.
∏ᶠ-unique : ∀ {k n} (cs : List (Bits k)) (g : Bits k → Bits n → 𝔽) (x : Bits n) (c₀ : Bits k) →
            Nodup cs → c₀ ∈ᵇ cs ≡ true →
            (∀ c → eqB c c₀ ≡ false → g c x ≡ 1#) → ∏ᶠ cs g x ≡ g c₀ x
∏ᶠ-unique (c ∷ cs) g x c₀ (nc , nd) mem h with eqB c₀ c in eq
... | true  = begin
  g c x * ∏ᶠ cs g x
    ≡⟨ Eq.cong (g c x *_) (∏ᶠ-one cs g x tail) ⟩
  g c x * 1#
    ≡⟨ *-identityʳ (g c x) ⟩
  g c x
    ≡⟨ Eq.cong (λ v → g v x) (Eq.sym (eqB-sound c₀ c eq)) ⟩
  g c₀ x ∎
  where
  open Eq.≡-Reasoning
  -- A member of the tail is not c₀ = c, the list having no duplicate.
  tail : ∀ c′ → c′ ∈ᵇ cs ≡ true → g c′ x ≡ 1#
  tail c′ mem′ with eqB c′ c₀ in eq′
  ... | false = h c′ eq′
  ... | true  = ⊥-elim (true≢false (Eq.trans (Eq.sym (Eq.subst (λ v → v ∈ᵇ cs ≡ true) c′≡c mem′)) nc))
    where
    c′≡c : c′ ≡ c
    c′≡c = Eq.trans (eqB-sound c′ c₀ eq′) (eqB-sound c₀ c eq)
    true≢false : true ≢ false
    true≢false ()
... | false = begin
  g c x * ∏ᶠ cs g x
    ≡⟨ Eq.cong₂ _*_ (h c (Eq.trans (eqB-sym c c₀) eq)) (∏ᶠ-unique cs g x c₀ nd mem′ h) ⟩
  1# * g c₀ x
    ≡⟨ *-identityˡ (g c₀ x) ⟩
  g c₀ x ∎
  where
  open Eq.≡-Reasoning
  -- The with-abstraction has already rewritten the head of mem.
  mem′ : c₀ ∈ᵇ cs ≡ true
  mem′ = mem

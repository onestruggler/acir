------------------------------------------------------------------------
-- Presentations of groups
--
-- Diagonal operators, their products, and the product of a list of
-- diagonal factors evaluated over an enumeration of contexts
--
-- After Real-Clifford+CH.EncodingSemantics.Products, over ℤ[i] and
-- with no width fixed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.EncodingSemantics.Diag where

open import Data.Bool using (Bool ; true ; false ; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List ; [] ; _∷_ ; foldr)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
  using (_∈ᵇ_ ; Nodup ; eqB-refl ; eqB-sound ; eqB-sym)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- δ on bit vectors, off the diagonal

δb-≢ : (x y : Bits k) → x ≢ y → δb x y ≡ 0#
δb-≢ []          []          ne = ⊥-elim (ne Eq.refl)
δb-≢ (true ∷ x)  (true ∷ y)  ne = δb-≢ x y (λ e → ne (Eq.cong (true ∷_) e))
δb-≢ (false ∷ x) (false ∷ y) ne = δb-≢ x y (λ e → ne (Eq.cong (false ∷_) e))
δb-≢ (true ∷ x)  (false ∷ y) ne = Eq.refl
δb-≢ (false ∷ x) (true ∷ y)  ne = Eq.refl

------------------------------------------------------------------------
-- Diagonal operators

diag : (Bits k → 𝔽) → Op k
diag f x y = f x * δb x y

diag-cong : {f g : Bits k → 𝔽} → (∀ x → f x ≡ g x) → diag f ≐ diag g
diag-cong e x y = Eq.cong (_* δb x y) (e x)

diag-⊙ : (f g : Bits k → 𝔽) → (diag f ⊙ diag g) ≐ diag (λ x → f x * g x)
diag-⊙ f g x y = begin
  Σb (λ z → (f x * δb x z) * (g z * δb z y))
    ≡⟨ Σ-cong (λ z → shuffle (f x) (δb x z) (g z * δb z y)) ⟩
  Σb (λ z → δb x z * (f x * (g z * δb z y)))
    ≡⟨ Σ-δˡ x (λ z → f x * (g z * δb z y)) ⟩
  f x * (g x * δb x y)
    ≡⟨ Eq.sym (*-assoc (f x) (g x) (δb x y)) ⟩
  (f x * g x) * δb x y ∎
  where
  open Eq.≡-Reasoning
  shuffle : ∀ a d b → (a * d) * b ≡ d * (a * b)
  shuffle a d b = Eq.trans (Eq.cong (_* b) (*-comm a d)) (*-assoc d a b)

diag-1 : diag {k} (λ _ → 1#) ≐ Idₒ
diag-1 x y = *-identityˡ (δb x y)

------------------------------------------------------------------------
-- Products of operators, factor by factor

fold-cong : ∀ {A : Set} (cs : List A) {F G : A → Op k} → (∀ c → F c ≐ G c) →
            foldr (λ c M → F c ⊙ M) Idₒ cs ≐ foldr (λ c M → G c ⊙ M) Idₒ cs
fold-cong []       e = ≐-refl Idₒ
fold-cong (c ∷ cs) e = ⊙-cong (e c) (fold-cong cs e)

------------------------------------------------------------------------
-- Products of diagonal operators

-- The pointwise product of the entries of a list of factors.
∏ᶠ : ∀ {A : Set} → List A → (A → Bits k → 𝔽) → Bits k → 𝔽
∏ᶠ cs g x = foldr (λ c acc → g c x * acc) 1# cs

diag-fold : ∀ {A : Set} (cs : List A) (g : A → Bits k → 𝔽) →
            foldr (λ c M → diag (g c) ⊙ M) Idₒ cs ≐ diag (∏ᶠ cs g)
diag-fold []       g = ≐-sym diag-1
diag-fold (c ∷ cs) g =
  ≐-trans (⊙-cong (≐-refl (diag (g c))) (diag-fold cs g)) (diag-⊙ (g c) (∏ᶠ cs g))

------------------------------------------------------------------------
-- Evaluating a product over an enumeration

private
  ∨-true : ∀ a → a ∨ true ≡ true
  ∨-true true  = Eq.refl
  ∨-true false = Eq.refl

  true≢false : true ≢ false
  true≢false ()

-- All the enumerated factors trivial.
∏ᶠ-one : ∀ {j} (cs : List (Bits j)) (g : Bits j → Bits k → 𝔽) (x : Bits k) →
         (∀ c → c ∈ᵇ cs ≡ true → g c x ≡ 1#) → ∏ᶠ cs g x ≡ 1#
∏ᶠ-one []       g x h = Eq.refl
∏ᶠ-one (c ∷ cs) g x h =
  Eq.trans (Eq.cong₂ _*_ (h c (Eq.cong (_∨ (c ∈ᵇ cs)) (eqB-refl c)))
                         (∏ᶠ-one cs g x (λ c′ p → h c′ (Eq.trans (Eq.cong (eqB c′ c ∨_) p) (∨-true (eqB c′ c))))))
           (*-identityˡ 1#)

-- All factors trivial but the one at c₀, which occurs exactly once.
∏ᶠ-unique : ∀ {j} (cs : List (Bits j)) (g : Bits j → Bits k → 𝔽) (x : Bits k) (c₀ : Bits j) →
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

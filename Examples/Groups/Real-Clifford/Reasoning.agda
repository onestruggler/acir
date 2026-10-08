------------------------------------------------------------------------
-- Presentations of groups
--
-- Reasoning about real Clifford circuits at a fixed width, and the
-- commutation of gates on the bottom wires with circuits shifted past
-- them
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Reasoning where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine using (⟪_⟫ ; ⟪++⟫ ; ⟪≈⟫ ; ⟪map↥⟫)

private
  variable
    n m : ℕ

------------------------------------------------------------------------
-- Reasoning at a fixed width

module Width (n : ℕ) where

  open PB (n VRel,_===_) public
    using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; refl')
  open PP (n VRel,_===_) public using (word-setoid ; by-assoc)
  open PP.Pattern-Assoc (n VRel,_===_) public using (by-passoc ; □)
  open SR word-setoid public

  front : ∀ {a b} (s : Circuit n) → a ≈ b → a • s ≈ b • s
  front s e = cong e refl

  back : ∀ (p : Circuit n) {a b} → a ≈ b → p • a ≈ p • b
  back p e = cong refl e

  -- Swapping two adjacent factors at the front of a product.
  swap : ∀ {a b} (s : Circuit n) → a • b ≈ b • a → a • b • s ≈ b • a • s
  swap s e = trans (sym assoc) (trans (front s e) assoc)

  -- Rewriting the first two factors of a product.
  pair : ∀ {a b c d} (s : Circuit n) → a • b ≈ c • d → a • b • s ≈ c • d • s
  pair s e = trans (sym assoc) (trans (front s e) assoc)

  -- Rewriting a product as a reassociated product.
  ⊙ : ∀ (a b c : Circuit n) → (a • b) • c ≈ a • b • c
  ⊙ a b c = assoc

lift : {w v : Circuit n} → n ⊢ w ≈ v → (₁₊ n) ⊢ w ↑ ≈ v ↑
lift {w = w} {v} = lemma-cong↑ w v

-- A scalar is the same at every width.
neg↑ : (₁₊ n) ⊢ neg ↑ ≈ neg
neg↑ = PB.axiom (ω↑=ω neg-gate)

------------------------------------------------------------------------
-- Gates on the bottom wires commute with circuits shifted past them

all : {A : Set} → (A → Bool) → List A → Bool
all p []       = true
all p (x ∷ xs) = p x ∧ all p xs

-- Letters on wire 0 (and scalars).
low1 : Gen (₁₊ m) → Bool
low1 (gate₀ _) = true
low1 (gate₁ _) = true
low1 (gate₂ _) = false
low1 (_ ↥)     = false

-- Letters on wires 0 and 1 (and scalars).
low2 : Gen (₂₊ m) → Bool
low2 (gate₀ _)         = true
low2 (gate₁ _)         = true
low2 (gate₂ _)         = true
low2 (gate₀ _ ↥)       = true
low2 (gate₁ _ ↥)       = true
low2 (gate₂ _ ↥)       = false
low2 ((_ ↥) ↥)         = false

private
  ∧-l : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧-l {true} _ = Eq.refl

  ∧-r : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧-r {true} e = e

  comm-word : ∀ {x w : Circuit n} {xs : Circuit n} →
              n ⊢ x • w ≈ w • x → n ⊢ xs • w ≈ w • xs → n ⊢ (x • xs) • w ≈ w • (x • xs)
  comm-word {n} {x} {w} {xs} e es = begin
    (x • xs) • w      ≈⟨ assoc ⟩
    x • xs • w        ≈⟨ back x es ⟩
    x • w • xs        ≈⟨ sym assoc ⟩
    (x • w) • xs      ≈⟨ front xs e ⟩
    (w • x) • xs      ≈⟨ assoc ⟩
    w • x • xs        ∎
    where open Width n

low1-comm : (x : Gen (₁₊ m)) → low1 x ≡ true → (w : Circuit m) →
            (₁₊ m) ⊢ [ x ]ʷ • w ↑ ≈ w ↑ • [ x ]ʷ
low1-comm (gate₀ h) _ w = PB.sym (comm-gate₀-w h (w ↑))
low1-comm (gate₁ h) _ w = PB.sym (comm-gate₁-w↑ h w)

low2-comm : (x : Gen (₂₊ m)) → low2 x ≡ true → (w : Circuit m) →
            (₂₊ m) ⊢ [ x ]ʷ • w ↑ ↑ ≈ w ↑ ↑ • [ x ]ʷ
low2-comm (gate₀ h)   _ w = PB.sym (comm-gate₀-w h (w ↑ ↑))
low2-comm (gate₁ h)   _ w = PB.sym (comm-gate₁-w↑ h (w ↑))
low2-comm (gate₂ h)   _ w = PB.sym (comm-gate₂-w↑↑ h w)
low2-comm (gate₀ h ↥) _ w = lift (low1-comm (gate₀ h) Eq.refl w)
low2-comm (gate₁ h ↥) _ w = lift (low1-comm (gate₁ h) Eq.refl w)

low1s-comm : (xs : List (Gen (₁₊ m))) → all low1 xs ≡ true → (w : Circuit m) →
             (₁₊ m) ⊢ ⟪ xs ⟫ • w ↑ ≈ w ↑ • ⟪ xs ⟫
low1s-comm []       _ w = PB.trans PB.left-unit (PB.sym PB.right-unit)
low1s-comm (x ∷ xs) e w = comm-word (low1-comm x (∧-l e) w) (low1s-comm xs (∧-r {low1 x} e) w)

low2s-comm : (xs : List (Gen (₂₊ m))) → all low2 xs ≡ true → (w : Circuit m) →
             (₂₊ m) ⊢ ⟪ xs ⟫ • w ↑ ↑ ≈ w ↑ ↑ • ⟪ xs ⟫
low2s-comm []       _ w = PB.trans PB.left-unit (PB.sym PB.right-unit)
low2s-comm (x ∷ xs) e w = comm-word (low2-comm x (∧-l e) w) (low2s-comm xs (∧-r {low2 x} e) w)

-- Scalars commute with everything.
neg-comm : (w : Circuit n) → n ⊢ neg • w ≈ w • neg
neg-comm w = PB.sym (comm-gate₀-w neg-gate w)

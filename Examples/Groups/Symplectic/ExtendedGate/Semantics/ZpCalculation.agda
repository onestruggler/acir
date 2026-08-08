------------------------------------------------------------------------
-- Presentations of groups
--
-- Pure ℤ/pℤ arithmetic identities used by the action lemmas.
--
-- These are equalities  x ≡ y  with  x , y : ℤ ₚ  (no circuits, Paulis or
-- relations); they are collected here so the action-lemma files can stay
-- focused on the action itself.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality as Eq

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.ExtendedGate.Semantics.ZpCalculation (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)


-- Recover the first coordinate a' from the nested-negation form.
recover-a' : ∀ a' a'' -> - (- (- a' + - a'') + - a') + - (- a' + - a'') ≡ a'
recover-a' a' a'' = begin
  - (- (- a' + - a'') + - a') + - (- a' + - a'') ≡⟨ cong (_+ - (- a' + - a'')) (sym (-‿+-comm (- (- a' + - a'')) (- a'))) ⟩
  (- - (- a' + - a'') + - - a') + - (- a' + - a'') ≡⟨ cong (_+ - (- a' + - a'')) (+-comm (- - (- a' + - a'')) (- - a')) ⟩
  (- - a' + - - (- a' + - a'')) + - (- a' + - a'') ≡⟨ +-assoc (- - a') (- - (- a' + - a'')) (- (- a' + - a'')) ⟩
  - - a' + (- - (- a' + - a'') + - (- a' + - a'')) ≡⟨ cong (- - a' +_) (+-inverseˡ (- (- a' + - a''))) ⟩
  - - a' + ₀ ≡⟨ +-identityʳ (- - a') ⟩
  - - a' ≡⟨ -‿involutive a' ⟩
  a' ∎
  where
  open ≡-Reasoning


-- Recover the first coordinate b' from the split-negation form.
recover-b' : ∀ b'' b' a ->  - (- (- b'' + (b' + a)) + (- b'' + a)) ≡ b'
recover-b' b'' b' a = begin
  - (- (- b'' + (b' + a)) + (- b'' + a)) ≡⟨ (sym (-‿+-comm (- (- b'' + (b' + a))) ((- b'' + a)))) ⟩
  - - (- b'' + (b' + a)) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (-‿involutive ((- b'' + (b' + a)))) ⟩
  (- b'' + (b' + a)) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (sym (+-assoc (- b'') b' a)) ⟩
  (- b'' + b' + a) + - (- b'' + a) ≡⟨ cong (_+ - (- b'' + a)) (trans (cong (_+ a)  (+-comm (- b'') b')) (+-assoc b' (- b'') a)) ⟩
  b' + (- b'' + a) + - (- b'' + a) ≡⟨ +-assoc b' ((- b'' + a)) (- (- b'' + a)) ⟩
  b' + ((- b'' + a) + - (- b'' + a)) ≡⟨ cong (b' +_) (+-inverseʳ ((- b'' + a))) ⟩
  b' + ₀ ≡⟨ +-identityʳ b' ⟩
  b' ∎
  where
  open ≡-Reasoning


-- Recover the second coordinate b'' from the split-negation form.
recover-b'' : ∀ b'' b' a -> - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡ b''
recover-b'' b'' b' a = begin
  - (- (- b'' + (b' + a)) + (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡⟨ cong (_+ (- (- b'' + (b' + a)) + a)) (sym (-‿+-comm (- (- b'' + (b' + a))) ((- b'' + a)))) ⟩
  (- - (- b'' + (b' + a)) + - (- b'' + a)) + (- (- b'' + (b' + a)) + a) ≡⟨ cong (_+ (- (- b'' + (b' + a)) + a)) (+-comm (- - (- b'' + (b' + a))) (- (- b'' + a))) ⟩
  (- (- b'' + a) + - - (- b'' + (b' + a))) + (- (- b'' + (b' + a)) + a) ≡⟨ trans (+-assoc (- (- b'' + a)) (- - (- b'' + (b' + a))) ((- (- b'' + (b' + a)) + a))) (cong (- (- b'' + a) +_) (sym (+-assoc (- - (- b'' + (b' + a))) (- (- b'' + (b' + a))) a))) ⟩
  - (- b'' + a) + ((- - (- b'' + (b' + a)) + - (- b'' + (b' + a))) + a) ≡⟨ cong (\ xx -> - (- b'' + a) + (xx + a)) (+-inverseˡ (- (- b'' + (b' + a)))) ⟩
  - (- b'' + a) + (₀ + a) ≡⟨ cong₂ _+_ (sym (-‿+-comm (- b'') a)) (+-identityˡ a) ⟩
  - - b'' + - a + a ≡⟨ +-assoc (- - b'') (- a) a ⟩
  - - b'' + (- a + a) ≡⟨ cong₂ _+_ (-‿involutive b'') (+-inverseˡ a) ⟩
  b'' + ₀ ≡⟨ +-identityʳ b'' ⟩
  b'' ∎
  where
  open ≡-Reasoning


-- Recover the second coordinate a'' from the nested-negation form.
recover-a'' : ∀ a' a'' -> - (- a' + - a'') + - a' ≡ a''
recover-a'' a' a'' = begin
  - (- a' + - a'') + - a' ≡⟨ cong (_+ - a') (sym (-‿+-comm (- a') (- a''))) ⟩
  (- - a' + - - a'') + - a' ≡⟨ cong (_+ - a') (+-comm (- - a') (- - a'')) ⟩
  (- - a'' + - - a') + - a' ≡⟨ +-assoc (- - a'') (- - a') (- a') ⟩
  - - a'' + (- - a' + - a') ≡⟨ cong (- - a'' +_) (+-inverseˡ (- a')) ⟩
  - - a'' + ₀ ≡⟨ +-identityʳ (- - a'') ⟩
  - - a'' ≡⟨ -‿involutive a'' ⟩
  a'' ∎
  where
  open ≡-Reasoning


-- Swap the roles of a and a' across a subtraction of  · - ₁  scalings.
mul-neg1-swap : ∀ b a b' a' -> (b + a * - ₁) + - (b' + a' * - ₁) ≡ (b + a') + - (b' + a) * ₁
mul-neg1-swap b a b' a' = begin
  (b + a * - ₁) + - (b' + a' * - ₁) ≡⟨ Eq.cong₂ _+_ (Eq.cong (b +_) (Eq.trans (*-comm a (- ₁)) (-1*x≈-x a))) (Eq.sym (-‿+-comm b' (a' * - ₁))) ⟩
  (b + - a) + (- b' + - (a' * - ₁)) ≡⟨ Eq.cong (\ xx -> (b + - a) + (- b' + xx)) (-‿distribʳ-* a' (- ₁)) ⟩
  (b + - a) + (- b' + (a' * - - ₁)) ≡⟨ Eq.cong (λ xx → b + - a + (- b' + a' * xx)) (-‿involutive ₁) ⟩
  (b + - a) + (- b' + (a' * ₁)) ≡⟨ Eq.cong (λ xx → b + - a + (- b' + xx)) (*-identityʳ a') ⟩
  (b + - a) + (- b' + (a')) ≡⟨ Eq.cong ((b + - a) +_) (+-comm (- b') a') ⟩
  b + - a + (a' + - b') ≡⟨ +-assoc b (- a) ((a' + - b')) ⟩
  b + (- a + (a' + - b')) ≡⟨ Eq.cong (b +_) (Eq.sym (+-assoc (- a) a' (- b'))) ⟩
  b + (- a + a' + - b') ≡⟨ Eq.cong (b +_) (Eq.cong (_+ - b') (+-comm (- a) a')) ⟩
  b + (a' + - a + - b') ≡⟨ Eq.cong (b +_) (+-assoc a' (- a) (- b')) ⟩
  b + (a' + (- a + - b')) ≡⟨ Eq.sym (+-assoc b a' (- a + - b')) ⟩
  (b + a') + (- a + - b') ≡⟨ Eq.cong ((b + a') +_) (+-comm (- a) (- b')) ⟩
  (b + a') + (- b' + - a) ≡⟨ Eq.cong (b + a' +_) (-‿+-comm b' a) ⟩
  (b + a') + - (b' + a) ≡⟨ Eq.cong (b + a' +_) (Eq.sym (*-identityʳ (- (b' + a)))) ⟩
  (b + a') + - (b' + a) * ₁ ∎
  where
  open ≡-Reasoning


-- Recover the coordinate a' + a · 1 from a doubly-scaled  · - ₁  form.
mul-neg1-recover : ∀ b' a' a ->  - (b' + a' * - ₁) + - ((a' + a) + - (b' + a' * - ₁) * - ₁) * - ₁ ≡ a' + a * ₁
mul-neg1-recover b' a' a = begin
  - (b' + a' * - ₁) + - ((a' + a) + - (b' + a' * - ₁) * - ₁) * - ₁ ≡⟨ cong (- (b' + a' * - ₁) +_) (Eq.trans (*-comm (- ((a' + a) + - (b' + a' * - ₁) * - ₁)) (- ₁)) (-1*x≈-x (- ((a' + a) + - (b' + a' * - ₁) * - ₁)))) ⟩
  - (b' + a' * - ₁) + - - ((a' + a) + - (b' + a' * - ₁) * - ₁) ≡⟨ cong (- (b' + a' * - ₁) +_) (-‿involutive (((a' + a) + - (b' + a' * - ₁) * - ₁))) ⟩
  - (b' + a' * - ₁) + ((a' + a) + - (b' + a' * - ₁) * - ₁) ≡⟨ cong (- (b' + a' * - ₁) +_) (cong ((a' + a) +_) (Eq.trans (*-comm (- (b' + a' * - ₁)) (- ₁)) (-1*x≈-x (- (b' + a' * - ₁))))) ⟩
  - (b' + a' * - ₁) + ((a' + a) + - - (b' + a' * - ₁)) ≡⟨ cong (- (b' + a' * - ₁) +_) (cong ((a' + a) +_) (-‿involutive ((b' + a' * - ₁)))) ⟩
  - (b' + a' * - ₁) + ((a' + a) + (b' + a' * - ₁)) ≡⟨ cong (- (b' + a' * - ₁) +_) (+-comm (a' + a) (b' + a' * - ₁)) ⟩
  - (b' + a' * - ₁) + ((b' + a' * - ₁) + (a' + a)) ≡⟨ sym (+-assoc (- (b' + a' * - ₁)) ((b' + a' * - ₁)) (a' + a)) ⟩
  - (b' + a' * - ₁) + (b' + a' * - ₁) + (a' + a) ≡⟨ cong (_+ (a' + a)) (+-inverseˡ ((b' + a' * - ₁))) ⟩
  ₀ + (a' + a) ≡⟨ +-identityˡ (a' + a) ⟩
  (a' + a) ≡⟨ Eq.cong (a' +_) (Eq.sym (*-identityʳ a)) ⟩
  a' + a * ₁ ∎
  where
  open ≡-Reasoning


-- -a + -(-a' + -a) collapses the double negation to a'.
neg-neg-cancelˡ : ∀ a a' -> - a + - (- a' + - a) ≡ a'
neg-neg-cancelˡ a a' = begin
  - a + - (- a' + - a) ≡⟨ Eq.cong (- a +_) (Eq.sym (-‿+-comm (- a') (- a))) ⟩
  - a + (- - a' + - - a) ≡⟨ Eq.cong (- a +_) (+-comm (- - a') (- - a)) ⟩
  - a + (- - a + - - a') ≡⟨ Eq.sym (+-assoc (- a) (- - a) (- - a')) ⟩
  - a + - - a + - - a' ≡⟨ Eq.cong (_+ - - a') (+-inverseʳ (- a)) ⟩
  ₀ + - - a' ≡⟨ +-identityˡ (- - a') ⟩
  - - a' ≡⟨ -‿involutive a' ⟩
  a' ∎
  where
  open ≡-Reasoning


-- -a + -(a' + -a) collapses the double negation to -a'.
neg-neg-cancelʳ : ∀ a a' -> - a + - (a' + - a) ≡ - a'
neg-neg-cancelʳ a a' = begin
  - a + - (a' + - a) ≡⟨ Eq.cong (- a +_) (Eq.sym (-‿+-comm (a') (- a))) ⟩
  - a + (- a' + - - a) ≡⟨ Eq.cong (- a +_) (+-comm (- a') (- - a)) ⟩
  - a + (- - a + - a') ≡⟨ Eq.sym (+-assoc (- a) (- - a) (- a')) ⟩
  - a + - - a + - a' ≡⟨ Eq.cong (_+ - a') (+-inverseʳ (- a)) ⟩
  ₀ + - a' ≡⟨ +-identityˡ (- a') ⟩
  - a' ∎
  where
  open ≡-Reasoning


-- Negation of a difference:  -(b + -b') ≡ -b + b'.
neg-sub : ∀ b b' -> - (b + - b') ≡ - b + b'
neg-sub b b' = Eq.trans (Eq.sym (-‿+-comm b (- b'))) (Eq.cong (- b +_) (-‿involutive b'))

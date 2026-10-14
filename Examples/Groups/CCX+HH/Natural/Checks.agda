------------------------------------------------------------------------
-- Presentations of groups
--
-- Finite checks by one boolean, for the generated coset tables of the
-- natural calculus: a property of every state or of a range of indices,
-- and distinctness of representatives from a table of their matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.Natural.Checks where

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; not ; T)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _≤_ ; _<_ ; z≤n)
open import Data.Nat.Properties
  using (<-cmp ; m+[n∸m]≡n ; +-suc ; +-identityʳ ; <-trans ; <-irrefl ; <-≤-trans ; _<?_ ; ≮⇒≥)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary using (yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix)
open import Examples.Groups.CCX+HH.Decide using (eqMat ; eqMat-refl)

private
  T-∧ : ∀ {x y} → T (x ∧ y) → T x × T y
  T-∧ {true} {true} _ = tt , tt

allF : ∀ {K} → (Fin K → Bool) → Bool
allF {zero} p = true
allF {suc K} p = p zero ∧ allF {K} (λ c → p (suc c))

allF-sound : ∀ {K} (p : Fin K → Bool) → T (allF p) → ∀ c → T (p c)
allF-sound {suc K} p h zero with p zero
allF-sound {suc K} p h zero | true = tt
allF-sound {suc K} p () zero | false
allF-sound {suc K} p h (suc c) with p zero
allF-sound {suc K} p h (suc c) | true = allF-sound (λ c → p (suc c)) h c
allF-sound {suc K} p () (suc c) | false

------------------------------------------------------------------------
-- Checks over a range of naturals

-- allR lo k p: p holds at lo, lo + 1, …, lo + k - 1.  A large table is
-- checked in chunks, one module each, since Agda frees the memory of an
-- evaluation only when its module is done.
allR : ℕ → ℕ → (ℕ → Bool) → Bool
allR lo zero p = true
allR lo (suc k) p = p lo ∧ allR (suc lo) k p

allR-sound : ∀ lo k (p : ℕ → Bool) → T (allR lo k p) → ∀ i → lo ≤ i → i < lo + k → T (p i)
allR-sound lo zero p h i lo≤i i<lo =
  ⊥-elim (<-irrefl Eq.refl (<-≤-trans (Eq.subst (i <_) (+-identityʳ lo) i<lo) lo≤i))
allR-sound lo (suc k) p h i lo≤i i<lo+k with <-cmp lo i
... | tri< lo<i _ _ = allR-sound (suc lo) k p (proj₂ (T-∧ {p lo} h)) i lo<i
        (Eq.subst (i <_) (+-suc lo k) i<lo+k)
... | tri≈ _ Eq.refl _ = proj₁ (T-∧ {p lo} h)
... | tri> _ _ i<lo = ⊥-elim (<-irrefl Eq.refl (<-≤-trans i<lo lo≤i))

-- Two adjacent ranges make one.
join : ∀ (P : ℕ → Set) lo a b → (∀ i → lo ≤ i → i < lo + a → P i) →
  (∀ i → lo + a ≤ i → i < lo + a + b → P i) → ∀ i → lo ≤ i → i < lo + a + b → P i
join P lo a b f g i lo≤i i<s with i <? lo + a
... | yes i<m = f i lo≤i i<m
... | no i≮m = g i (≮⇒≥ i≮m) i<s

-- The matrices of N representatives, given by a function on their
-- indices, checked against a stored table (chunk by chunk: `agree`) and
-- the stored table checked free of repeats (`apart`), over any type of
-- entries with a boolean equality that is reflexive.
apartR : ∀ {A : Set} {m} → (A → A → Bool) → ℕ → (ℕ → Matrix m m A) → Bool
apartR eq N t = allR 0 N (λ i → allR (suc i) (N ∸ suc i) (λ j → not (eqMat eq (t i) (t j))))

module DistinctR {A : Set} (eq : A → A → Bool) (eq-refl : ∀ x → T (eq x x))
  {N m : ℕ} (sem table : ℕ → Matrix m m A)
  (agree : ∀ i → i < N → sem i ≡ table i)
  (apart : T (apartR eq N table))
  where

  private
    refuted : ∀ b → T b → T (not b) → ⊥
    refuted true _ ()

    -- Below the upper index, two stored matrices differ.
    differ : ∀ i j → i < j → j < N → table i ≡ table j → ⊥
    differ i j i<j j<N e = refuted (eqMat eq (table i) (table i))
      (eqMat-refl eq eq-refl (table i))
      (Eq.subst (λ M → T (not (eqMat eq (table i) M))) (Eq.sym e)
        (allR-sound (suc i) (N ∸ suc i) _ (allR-sound 0 N _ apart i z≤n (<-trans i<j j<N))
          j i<j (Eq.subst (j <_) (Eq.sym (m+[n∸m]≡n (<-trans i<j j<N))) j<N)))

  distinct : ∀ (c d : Fin N) → sem (toℕ c) ≡ sem (toℕ d) → c ≡ d
  distinct c d e with <-cmp (toℕ c) (toℕ d)
  ... | tri< c<d _ _ = ⊥-elim (differ (toℕ c) (toℕ d) c<d (FP.toℕ<n d) e′)
    where
    e′ = Eq.trans (Eq.sym (agree _ (FP.toℕ<n c))) (Eq.trans e (agree _ (FP.toℕ<n d)))
  ... | tri≈ _ c≡d _ = FP.toℕ-injective c≡d
  ... | tri> _ _ d<c = ⊥-elim (differ (toℕ d) (toℕ c) d<c (FP.toℕ<n c) (Eq.sym e′))
    where
    e′ = Eq.trans (Eq.sym (agree _ (FP.toℕ<n c))) (Eq.trans e (agree _ (FP.toℕ<n d)))

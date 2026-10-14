------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrices of a prefix-closed family of words, from stored
-- matrices checked one gate at a time.
--
-- Evaluating the matrix of a long word from scratch makes Agda's
-- evaluator recompute shared subproducts, which exhausted a 4.5 GB heap
-- on two-wire words of twenty letters.  Here every word k > 0 is a
-- parent word followed by one letter, and its stored matrix is checked
-- against the parent's stored matrix times that letter's, also stored
-- (gate, checked once per letter: gate-ok): one product of two
-- literals per word, decided by one boolean.
-- The CCX+H copy of CCX+HH.Natural.Prefix, over 𝔻[√2].
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base using (Bool ; true ; false ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≤_ ; _<_ ; _<ᵇ_ ; z≤n ; s≤s)
  renaming (_^_ to _^ℕ_)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D)

open import Examples.Groups.CCX+H.Natural.Syntactics using (Gen)
import Examples.Groups.CCX+H.Presentation as Sem

module Examples.Groups.CCX+H.Natural.Prefix
  {W : ℕ} (K : ℕ)
  (word : ℕ → List (Gen W)) (parent : ℕ → ℕ) (last : ℕ → Gen W)
  (stored : ℕ → Matrix (2 ^ℕ W) (2 ^ℕ W) D)
  (gate : Gen W → Matrix (2 ^ℕ W) (2 ^ℕ W) D)
  where

open import Data.List.Properties using (length-++)
open import Data.Nat.Properties using (<ᵇ⇒< ; +-comm ; ≤-trans ; n≤1+n ; ≤-pred)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Examples.Groups.CCX+H.Natural.Engine using (⟪_⟫ ; ⟪++⟫ ; eqL ; eqL-sound)
open import Examples.Groups.CCX+H.Natural.Soundness using (sound)
open import Examples.Groups.CCX+HH.Decide using (eqMat ; eqD√ ; eqMat-sound ; eqD√-sound)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)

-- The matrix product of the semantics, with its ring given (two
-- instances for the dyadics are in scope).
infixl 7 _∙_
_∙_ : ∀ {a b c} → Matrix a b D → Matrix b c D → Matrix a c D
_∙_ = _·*·_ {{RingD}}

-- The check at word k: the root is the empty word with the identity's
-- matrix; any other word is its parent's followed by one letter, its
-- parent is in range, and its stored matrix is the parent's times the
-- letter's.
ok : ℕ → Bool
ok zero = eqL (word zero) [] ∧ eqMat eqD√ (stored zero) (Sem.interpret {W} ε)
ok (suc k) = eqL (word (suc k)) (word (parent (suc k)) ++ last (suc k) ∷ [])
  ∧ (parent (suc k) <ᵇ K)
  ∧ eqMat eqD√ (stored (suc k)) (stored (parent (suc k)) ∙ gate (last (suc k)))

private
  T-∧ : ∀ {x y} → T (x ∧ y) → T x × T y
  T-∧ {true} {true} _ = tt , tt

  true≡ : ∀ {b} → T b → b ≡ true
  true≡ {true} _ = Eq.refl

module Agree
  (gate-ok : ∀ y → Sem.interpret ⟪ y ∷ [] ⟫ ≡ gate y)
  (checked : ∀ k → k < K → T (ok k))
  where

  private
    shorter : ∀ k → T (ok (suc k)) → suc (length (word (parent (suc k)))) ≤ length (word (suc k))
    shorter k h = Eq.subst (λ xs → suc (length (word (parent (suc k)))) ≤ length xs)
      (Eq.sym (eqL-sound (word (suc k)) wp (true≡ (proj₁ (T-∧ {eqL (word (suc k)) wp} h)))))
      (Eq.subst (suc (length (word (parent (suc k)))) ≤_)
        (Eq.sym (Eq.trans (length-++ (word (parent (suc k))) {last (suc k) ∷ []})
          (+-comm (length (word (parent (suc k)))) 1)))
        (≤-refl′ _))
      where
      wp = word (parent (suc k)) ++ last (suc k) ∷ []
      ≤-refl′ : ∀ n → n ≤ n
      ≤-refl′ zero = z≤n
      ≤-refl′ (suc n) = s≤s (≤-refl′ n)

    -- By induction on a bound for the length of the word.
    go : ∀ f k → length (word k) ≤ f → k < K → Sem.interpret ⟪ word k ⟫ ≡ stored k
    go f zero _ k<K with T-∧ (checked zero k<K)
    ... | w₀ , m₀ = Eq.trans (Eq.cong (λ xs → Sem.interpret ⟪ xs ⟫) (eqL-sound _ _ (true≡ w₀)))
      (Eq.sym (eqMat-sound eqD√ eqD√-sound _ _ m₀))
    go f (suc k) len k<K with T-∧ (checked (suc k) k<K)
    ... | w , rest with T-∧ rest
    ... | p<K , m = begin
        Sem.interpret ⟪ word (suc k) ⟫
          ≡⟨ Eq.cong (λ xs → Sem.interpret ⟪ xs ⟫) (eqL-sound _ _ (true≡ w)) ⟩
        Sem.interpret ⟪ word p ++ y ∷ [] ⟫
          ≡⟨ sound (⟪++⟫ (word p) (y ∷ [])) ⟩
        Sem.interpret ⟪ word p ⟫ ∙ Sem.interpret ⟪ y ∷ [] ⟫
          ≡⟨ Eq.cong (_∙ Sem.interpret ⟪ y ∷ [] ⟫) (go′ f len) ⟩
        stored p ∙ Sem.interpret ⟪ y ∷ [] ⟫
          ≡⟨ Eq.cong (stored p ∙_) (gate-ok y) ⟩
        stored p ∙ gate y
          ≡⟨ Eq.sym (eqMat-sound eqD√ eqD√-sound _ _ m) ⟩
        stored (suc k) ∎
      where
      open Eq.≡-Reasoning
      p = parent (suc k)
      y = last (suc k)
      go′ : ∀ f → length (word (suc k)) ≤ f → Sem.interpret ⟪ word p ⟫ ≡ stored p
      go′ (suc f) l = go f p (≤-pred (≤-trans (shorter k (checked (suc k) k<K)) l)) (<ᵇ⇒< _ _ p<K)
      go′ zero l with ≤-trans (shorter k (checked (suc k) k<K)) l
      ... | ()

  agree : ∀ k → k < K → Sem.interpret ⟪ word k ⟫ ≡ stored k
  agree k = go (length (word k)) k (≤-refl′ (length (word k)))
    where
    ≤-refl′ : ∀ n → n ≤ n
    ≤-refl′ zero = z≤n
    ≤-refl′ (suc n) = s≤s (≤-refl′ n)

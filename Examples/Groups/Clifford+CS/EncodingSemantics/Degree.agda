------------------------------------------------------------------------
-- Presentations of groups
--
-- The two-level encoding of a gate has degree 0 mod 4
--
-- Each of its letters moves the coset action one degree up (a phase,
-- a K; the five-letter spelling of a reversed K pair too), and there
-- are 2ᵏ of them with k ≥ 2, so the action returns to the identity
-- coset — which is what lets the action translate the product into a
-- word over P′ (Encoding.e, ActionSound.spell).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.EncodingSemantics.Degree (m : ℕ) where

open import Data.Bool using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin) renaming (_<_ to _<ᶠ_)
open import Data.List using (List ; [] ; _∷_ ; length ; map ; _++_)
open import Data.Vec using () renaming (_∷_ to _∷ᵛ_)
open import Data.List.Properties using (length-++ ; length-map)
open import Data.Nat using (zero ; suc ; _+_ ; _*_ ; _^_ ; _<_ ; _≤_ ; s≤s)
open import Data.Nat.Properties using (+-identityʳ ; ^-distribˡ-+-* ; *-comm ; ≤-pred)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Data.Fin.Properties as FinP

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Clifford+CS.Semantics.Algebra using (Bits)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Encoding m
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets using (Coset ; ⟨0⟩ ; ⟨1⟩ ; ⟨2⟩ ; ⟨3⟩ ; inc)
open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big using (cos)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits ; lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas using (lookup-insert)
import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL

private
  true≢false : true ≢ false
  true≢false ()

------------------------------------------------------------------------
-- Iterating the degree

incⁱ : ℕ → Coset → Coset
incⁱ zero    c = c
incⁱ (suc k) c = incⁱ k (inc c)

incⁱ-+ : ∀ a b c → incⁱ (a + b) c ≡ incⁱ b (incⁱ a c)
incⁱ-+ zero    b c = Eq.refl
incⁱ-+ (suc a) b c = incⁱ-+ a b (inc c)

inc⁴ : ∀ c → incⁱ 4 c ≡ c
inc⁴ ⟨0⟩ = Eq.refl
inc⁴ ⟨1⟩ = Eq.refl
inc⁴ ⟨2⟩ = Eq.refl
inc⁴ ⟨3⟩ = Eq.refl

inc⁵ : ∀ c → inc (inc (inc (inc (inc c)))) ≡ inc c
inc⁵ ⟨0⟩ = Eq.refl
inc⁵ ⟨1⟩ = Eq.refl
inc⁵ ⟨2⟩ = Eq.refl
inc⁵ ⟨3⟩ = Eq.refl

-- A multiple of four degrees is none.
incⁱ-4j : ∀ j c → incⁱ (j * 4) c ≡ c
incⁱ-4j zero    c = Eq.refl
incⁱ-4j (suc j) c = Eq.trans (incⁱ-+ 4 (j * 4) c) (Eq.trans (Eq.cong (incⁱ (j * 4)) (inc⁴ c)) (incⁱ-4j j c))

-- 2ᵏ letters for k ≥ 2 are a multiple of four.
incⁱ-2^ : ∀ j c → incⁱ (2 ^ (2 + j)) c ≡ c
incⁱ-2^ j c =
  Eq.trans (Eq.cong (λ k → incⁱ k c) (Eq.trans (^-distribˡ-+-* 2 2 j) (*-comm 4 (2 ^ j))))
           (incⁱ-4j (2 ^ j) c)

------------------------------------------------------------------------
-- The letters and the products

-- A product of letters each of degree one.
cos-∏ : ∀ {A : Set} (c : Coset) (cs : List A) (f : A → Word (TL.Gen N)) →
        (∀ a c → cos c (f a) ≡ inc c) → cos c (∏ cs f) ≡ incⁱ (length cs) c
cos-∏ c []       f h = Eq.refl
cos-∏ c (a ∷ cs) f h = Eq.trans (Eq.cong (λ c′ → cos c′ (∏ cs f)) (h a c)) (cos-∏ (inc c) cs f h)

-- A K pair, in either spelling.
cos-Kp : ∀ (c : Coset) (a b : Fin N) → a ≢ b → cos c (Kp a b) ≡ inc c
cos-Kp c a b ne = go (FinP.<-cmp a b)
  where
  go : Tri (a <ᶠ b) (a ≡ b) (b <ᶠ a) → cos c (Kp a b) ≡ inc c
  go (tri< p _ _) = Eq.cong (cos c) (Kp-< a b p)
  go (tri≈ _ e _) = ⊥-elim (ne e)
  go (tri> _ _ q) = Eq.trans (Eq.cong (cos c) (Kp-> a b q)) (inc⁵ c)

-- The number of contexts.
length-allBits : ∀ k → length (allBits k) ≡ 2 ^ k
length-allBits zero    = Eq.refl
length-allBits (suc k) = begin
  length (map (false ∷ᵛ_) (allBits k) ++ map (true ∷ᵛ_) (allBits k))
    ≡⟨ length-++ (map (false ∷ᵛ_) (allBits k)) ⟩
  length (map (false ∷ᵛ_) (allBits k)) + length (map (true ∷ᵛ_) (allBits k))
    ≡⟨ Eq.cong₂ _+_ (length-map (false ∷ᵛ_) (allBits k)) (length-map (true ∷ᵛ_) (allBits k)) ⟩
  length (allBits k) + length (allBits k)
    ≡⟨ Eq.cong₂ _+_ (length-allBits k) (Eq.trans (length-allBits k) (Eq.sym (+-identityʳ (2 ^ k)))) ⟩
  2 ^ k + (2 ^ k + 0) ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Every encoding returns to the identity coset

private
  -- A product over all contexts of a width k + 2.
  deg-∏ : ∀ {j} {A : Set} (cs : List A) (f : A → Word (TL.Gen N)) →
          length cs ≡ 2 ^ (2 + j) → (∀ a c → cos c (f a) ≡ inc c) → cos ⟨0⟩ (∏ cs f) ≡ ⟨0⟩
  deg-∏ {j} cs f len h =
    Eq.trans (cos-∏ ⟨0⟩ cs f h) (Eq.trans (Eq.cong (λ k → incⁱ k ⟨0⟩) len) (incⁱ-2^ j ⟨0⟩))

  -- The two vectors of a K pair differ.
  pair-≢ : ∀ p (c : Bits (₃₊ m)) → p < n → idx (str₁ p c false) ≢ idx (str₁ p c true)
  pair-≢ p c (s≤s q) e = true≢false
    (Eq.trans (Eq.sym (lookup-insert p true c q))
      (Eq.trans (Eq.cong (lookupℕ p) (Eq.sym (idx-inj {str₁ p c false} {str₁ p c true} e))) (lookup-insert p false c q)))

deg-E′ : ∀ (g : Gen n) → cos ⟨0⟩ (eTL′ (view g)) ≡ ⟨0⟩
deg-E′ g = go (view g) Eq.refl
  where
  go : (v : View) → view g ≡ v → cos ⟨0⟩ (eTL′ v) ≡ ⟨0⟩
  go (scalar I-gate) eq = deg-∏ {2 + m} (allBits n) (λ x → TL.i (idx x)) (length-allBits n) (λ _ _ → Eq.refl)
  go (one p S-gate) eq  = deg-∏ {1 + m} (allBits (₃₊ m)) (λ c → TL.i (idx (str₁ p c true)))
                          (length-allBits (₃₊ m)) (λ _ _ → Eq.refl)
  go (one p K-gate) eq  = deg-∏ {1 + m} (allBits (₃₊ m)) (λ c → Kp (idx (str₁ p c false)) (idx (str₁ p c true)))
                          (length-allBits (₃₊ m)) (λ c c′ → cos-Kp c′ (idx (str₁ p c false)) (idx (str₁ p c true)) (pair-≢ p c (view-bound₁ g eq)))
  go (two p CS-gate) eq = deg-∏ {m} (allBits (₂₊ m)) (λ c → TL.i (idx (str₂ p c true true)))
                          (length-allBits (₂₊ m)) (λ _ _ → Eq.refl)

deg-E : ∀ (g : Gen n) → cos ⟨0⟩ (eTL g) ≡ ⟨0⟩
deg-E = deg-E′

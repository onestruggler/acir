------------------------------------------------------------------------
-- Presentations of groups
--
-- The phases of the derived diagonals (Lemma 8)
--
--     CZ  : x₀ x₁            (p odd)
--     CS  : x₁ (x₀ choose 2) (p > 3; dot on wire 1, square on wire 0)
--     CCZ : x₀ x₁ x₂         (p > 3)
--
-- each by evaluating its defining circuit and expanding the binomials
-- of sums (Lemmas 5, 6).  The placements used by the rules are their
-- conjugates by swaps, with the wires of the phase exchanged.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Soundness.Derived
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (_∷_ ; head ; tail)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)

import Data.Integer.Base as ℤ
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Undoing an addition

-- CX⁻¹ after CX: (a + b) - b.
undo : (a b : F) → a + b + - 1F * b ≡ a
undo a b = solve 2 (λ a b → a :+ b :+ (:- con (ℤ.+ 1)) :* b := a) refl a b

-- CX after CX⁻¹.
redo : (a b : F) → a + - 1F * b + b ≡ a
redo a b = solve 2 (λ a b → a :+ (:- con (ℤ.+ 1)) :* b :+ b := a) refl a b

-- -1 · b = - b.
neg1* : (b : F) → - 1F * b ≡ - b
neg1* b = solve 1 (λ b → (:- con (ℤ.+ 1)) :* b := :- b) refl b

------------------------------------------------------------------------
-- CZ

module Quadratic (odd : 1 ≤ p-2) where

  open Odd odd

  CZ-diag : .(h : 2 ≤ lv) → DiagC {₂₊ n} (CZ h) (λ x → head x * head (tail x))
  CZ-diag h (a ∷ b ∷ y) = at-≡ e refl phase
    where
    e = •-at (•-at (at-≡ (•-at (•-at (CX-at a b y) (S-at h (a + b) (b ∷ y)))
                               (CXᶠ-at (- 1F) (a + b) b y))
                         (cong (λ c → c ∷ b ∷ y) (undo a b)) refl)
                   (↑-at (DiagC-^ᶠ (S-diag h) (- 1F) (b ∷ y))))
             (DiagC-^ᶠ (S-diag h) (- 1F) (a ∷ b ∷ y))
    phase : 0F + binom2 (a + b) + 0F + - 1F * binom2 b + - 1F * binom2 a ≡ a * b
    phase = trans (cong (λ q → 0F + q + 0F + - 1F * binom2 b + - 1F * binom2 a) (binom2-add a b))
      (solve 4 (λ A B a b → con (ℤ.+ 0) :+ (A :+ B :+ a :* b) :+ con (ℤ.+ 0)
                           :+ (:- con (ℤ.+ 1)) :* B :+ (:- con (ℤ.+ 1)) :* A := a :* b)
             refl (binom2 a) (binom2 b) a b)

  -- CZ on wires 0 and 2.
  CZ₂₀-diag : .(h : 2 ≤ lv) → DiagC {₃₊ n} (CZ₂₀ h) (λ x → head x * head (tail (tail x)))
  CZ₂₀-diag h = DiagC-≡ (DiagC-conj SWAP↑-at sw₁₂-inv (CZ-diag h)) λ { (a ∷ b ∷ c ∷ x) → refl }

------------------------------------------------------------------------
-- CS and CCZ

module Cubic (big : 2 ≤ p-2) where

  open Big big
  open Quadratic (big⇒odd big)

  CS-diag : .(h : 3 ≤ lv) → DiagC {₂₊ n} (CS h) (λ x → head (tail x) * binom2 (head x))
  CS-diag h (a ∷ b ∷ y) = at-≡ e (cong (λ c → c ∷ b ∷ y) (redo a b)) phase
    where
    e = •-at (•-at (•-at (at-≡ (•-at (•-at (•-at (•-at (•-at (•-at (DiagC-^ᶠ (CZ-diag (quad₃ h)) half (a ∷ b ∷ y))
          (↑-at (DiagC-^ᶠ (Z-diag (lin₃ h)) (- half) (b ∷ y))))
          (↑-at (DiagC-^ᶠ (T-diag h) (- 1F) (b ∷ y))))
          (↑-at (DiagC-^ᶠ (S-diag (quad₃ h)) (- 1F) (b ∷ y))))
          (CX-at a b y))
          (DiagC-^ᶠ (T-diag h) half (a + b ∷ b ∷ y)))
          (CXᶠ-at (- 1F) (a + b) b y))
          (cong (λ c → c ∷ b ∷ y) (undo a b)) refl)
          (CXᶠ-at (- 1F) a b y))
          (DiagC-^ᶠ (T-diag h) (- half) (a + - 1F * b ∷ b ∷ y)))
          (CX-at (a + - 1F * b) b y)
    phase : half * (a * b) + - half * b + - 1F * binom3 b + - 1F * binom2 b + 0F
            + half * binom3 (a + b) + 0F + 0F + - half * binom3 (a + - 1F * b) + 0F
            ≡ b * binom2 a
    phase = begin
      half * (a * b) + - half * b + - 1F * binom3 b + - 1F * binom2 b + 0F
        + half * binom3 (a + b) + 0F + 0F + - half * binom3 (a + - 1F * b) + 0F
        ≡⟨ cong₂ (λ u v → half * (a * b) + - half * b + - 1F * binom3 b + - 1F * binom2 b + 0F
                           + half * u + 0F + 0F + - half * v + 0F)
                 (binom3-add a b)
                 (trans (cong (λ c → binom3 (a + c)) (neg1* b))
                   (trans (binom3-add a (- b))
                     (cong₂ (λ u v → binom3 a + u + binom2 a * (- b) + a * v) (binom3-neg b) (binom2-neg b)))) ⟩
      half * (a * b) + - half * b + - 1F * binom3 b + - 1F * binom2 b + 0F
        + half * (binom3 a + binom3 b + binom2 a * b + a * binom2 b) + 0F + 0F
        + - half * (binom3 a + (- binom3 b - 2F * binom2 b - b) + binom2 a * (- b) + a * (binom2 b + b)) + 0F
        ≡⟨ solve 7 (λ t a b A3 A2 B3 B2 →
             t :* (a :* b) :+ (:- t) :* b :+ (:- con (ℤ.+ 1)) :* B3 :+ (:- con (ℤ.+ 1)) :* B2 :+ con (ℤ.+ 0)
             :+ t :* (A3 :+ B3 :+ A2 :* b :+ a :* B2) :+ con (ℤ.+ 0) :+ con (ℤ.+ 0)
             :+ (:- t) :* (A3 :+ (:- B3 :- con (ℤ.+ 2) :* B2 :- b) :+ A2 :* (:- b) :+ a :* (B2 :+ b)) :+ con (ℤ.+ 0)
             := :- B3 :- B2 :+ (con (ℤ.+ 2) :* t) :* (B3 :+ B2 :+ A2 :* b))
             refl half a b (binom3 a) (binom2 a) (binom3 b) (binom2 b) ⟩
      - binom3 b - binom2 b + (2F * half) * (binom3 b + binom2 b + binom2 a * b)
        ≡⟨ cong (λ u → - binom3 b - binom2 b + u * (binom3 b + binom2 b + binom2 a * b)) 2*half ⟩
      - binom3 b - binom2 b + 1F * (binom3 b + binom2 b + binom2 a * b)
        ≡⟨ solve 4 (λ B3 B2 A2 b → :- B3 :- B2 :+ con (ℤ.+ 1) :* (B3 :+ B2 :+ A2 :* b) := b :* A2)
                 refl (binom3 b) (binom2 b) (binom2 a) b ⟩
      b * binom2 a
        ∎
      where open ≡-Reasoning

  CCZ-diag : .(h : 3 ≤ lv) →
             DiagC {₃₊ n} (CCZ h) (λ x → head x * head (tail x) * head (tail (tail x)))
  CCZ-diag h (a ∷ b ∷ c ∷ y) = at-≡ st₅ refl phase
    where
    st₁ : ⟦ CX ^ᶠ (- 1F) • T h • CX • CX ↑ ⟧ (a ∷ b ∷ c ∷ y) ≡ (a ∷ b + c ∷ c ∷ y , 0F + 0F + binom3 (a + (b + c)) + 0F)
    st₁ =
      at-≡ (•-at (•-at (•-at (↑-at (CX-at b c y))
      (CX-at a (b + c) (c ∷ y)))
      (T-at h (a + (b + c)) (b + c ∷ c ∷ y)))
      (CXᶠ-at (- 1F) (a + (b + c)) (b + c) (c ∷ y)))
      (cong (λ x → x ∷ b + c ∷ c ∷ y) (undo a (b + c))) refl

    st₂ : ⟦ (CX ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • CX ↑ • (CX ^ᶠ (- 1F)) ↑ • CX ^ᶠ (- 1F) • T h • CX • CX ↑ ⟧ (a ∷ b ∷ c ∷ y) ≡ (a ∷ b ∷ c ∷ y , 0F + 0F + binom3 (a + (b + c)) + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F)
    st₂ =
      at-≡ (•-at (•-at (•-at (at-≡ (•-at (st₁)
      (↑-at (CXᶠ-at (- 1F) (b + c) c y)))
      (cong (λ x → a ∷ x ∷ c ∷ y) (undo b c)) refl)
      (↑-at (CX-at b c y)))
      (↑-at (DiagC-^ᶠ (T-diag h) (- 1F) (b + c ∷ c ∷ y))))
      (↑-at (CXᶠ-at (- 1F) (b + c) c y)))
      (cong (λ x → a ∷ x ∷ c ∷ y) (undo b c)) refl

    st₃ : ⟦ CX ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX • (CX ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • CX ↑ • (CX ^ᶠ (- 1F)) ↑ • CX ^ᶠ (- 1F) • T h • CX • CX ↑ ⟧ (a ∷ b ∷ c ∷ y) ≡ (a ∷ b ∷ c ∷ y , 0F + 0F + binom3 (a + (b + c)) + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F + - 1F * binom3 (a + b) + 0F)
    st₃ =
      at-≡ (•-at (•-at (•-at (st₂)
      (CX-at a b (c ∷ y)))
      (DiagC-^ᶠ (T-diag h) (- 1F) (a + b ∷ b ∷ c ∷ y)))
      (CXᶠ-at (- 1F) (a + b) b (c ∷ y)))
      (cong (λ x → x ∷ b ∷ c ∷ y) (undo a b)) refl

    st₄ : ⟦ CX₂₀ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX₂₀ • CX ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • CX • (CX ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • CX ↑ • (CX ^ᶠ (- 1F)) ↑ • CX ^ᶠ (- 1F) • T h • CX • CX ↑ ⟧ (a ∷ b ∷ c ∷ y) ≡ (a ∷ b ∷ c ∷ y , 0F + 0F + binom3 (a + (b + c)) + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F + - 1F * binom3 (a + b) + 0F + 0F + - 1F * binom3 (a + c) + 0F)
    st₄ =
      at-≡ (•-at (•-at (•-at (st₃)
      (CX₂₀-at a b c y))
      (DiagC-^ᶠ (T-diag h) (- 1F) (a + c ∷ b ∷ c ∷ y)))
      (CX₂₀ᶠ-at (- 1F) (a + c) b c y))
      (cong (λ x → x ∷ b ∷ c ∷ y) (undo a c)) refl

    st₅ : ⟦ CCZ h ⟧ (a ∷ b ∷ c ∷ y) ≡ (a ∷ b ∷ c ∷ y , 0F + 0F + binom3 (a + (b + c)) + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F + - 1F * binom3 (a + b) + 0F + 0F + - 1F * binom3 (a + c) + 0F + binom3 c + binom3 b + binom3 a)
    st₅ =
      •-at (•-at (•-at (st₄)
      (↑-at (↑-at (T-at h c y))))
      (↑-at (T-at h b (c ∷ y))))
      (T-at h a (b ∷ c ∷ y))

    phase : 0F + 0F + binom3 (a + (b + c)) + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F
            + - 1F * binom3 (a + b) + 0F + 0F + - 1F * binom3 (a + c) + 0F
            + binom3 c + binom3 b + binom3 a
            ≡ a * b * c
    phase = begin
      0F + 0F + binom3 (a + (b + c)) + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F
        + - 1F * binom3 (a + b) + 0F + 0F + - 1F * binom3 (a + c) + 0F
        + binom3 c + binom3 b + binom3 a
        ≡⟨ cong₂ (λ u v → 0F + 0F + u + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F
                           + - 1F * v + 0F + 0F + - 1F * binom3 (a + c) + 0F
                           + binom3 c + binom3 b + binom3 a)
             (trans (binom3-add a (b + c)) (cong (λ q → binom3 a + binom3 (b + c) + binom2 a * (b + c) + a * q) (binom2-add b c)))
             (binom3-add a b) ⟩
      0F + 0F + (binom3 a + binom3 (b + c) + binom2 a * (b + c) + a * (binom2 b + binom2 c + b * c))
        + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F
        + - 1F * (binom3 a + binom3 b + binom2 a * b + a * binom2 b) + 0F + 0F
        + - 1F * binom3 (a + c) + 0F + binom3 c + binom3 b + binom3 a
        ≡⟨ cong (λ u → 0F + 0F + (binom3 a + binom3 (b + c) + binom2 a * (b + c) + a * (binom2 b + binom2 c + b * c))
                        + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F
                        + - 1F * (binom3 a + binom3 b + binom2 a * b + a * binom2 b) + 0F + 0F
                        + - 1F * u + 0F + binom3 c + binom3 b + binom3 a)
             (binom3-add a c) ⟩
      0F + 0F + (binom3 a + binom3 (b + c) + binom2 a * (b + c) + a * (binom2 b + binom2 c + b * c))
        + 0F + 0F + 0F + - 1F * binom3 (b + c) + 0F + 0F
        + - 1F * (binom3 a + binom3 b + binom2 a * b + a * binom2 b) + 0F + 0F
        + - 1F * (binom3 a + binom3 c + binom2 a * c + a * binom2 c) + 0F + binom3 c + binom3 b + binom3 a
        ≡⟨ solve 10 (λ a b c A3 Bc A2 B2 C2 B3 C3 →
             con (ℤ.+ 0) :+ con (ℤ.+ 0) :+ (A3 :+ Bc :+ A2 :* (b :+ c) :+ a :* (B2 :+ C2 :+ b :* c))
             :+ con (ℤ.+ 0) :+ con (ℤ.+ 0) :+ con (ℤ.+ 0) :+ (:- con (ℤ.+ 1)) :* Bc :+ con (ℤ.+ 0) :+ con (ℤ.+ 0)
             :+ (:- con (ℤ.+ 1)) :* (A3 :+ B3 :+ A2 :* b :+ a :* B2) :+ con (ℤ.+ 0) :+ con (ℤ.+ 0)
             :+ (:- con (ℤ.+ 1)) :* (A3 :+ C3 :+ A2 :* c :+ a :* C2) :+ con (ℤ.+ 0) :+ C3 :+ B3 :+ A3
             := a :* b :* c)
             refl a b c (binom3 a) (binom3 (b + c)) (binom2 a) (binom2 b) (binom2 c) (binom3 b) (binom3 c) ⟩
      a * b * c
        ∎
      where open ≡-Reasoning

  -- CS with dot on wire 2 and square on wire 0.
  CS₂₀-diag : .(h : 3 ≤ lv) →
              DiagC {₃₊ n} (CS₂₀ h) (λ x → head (tail (tail x)) * binom2 (head x))
  CS₂₀-diag h = DiagC-≡ (DiagC-conj SWAP↑-at sw₁₂-inv (CS-diag h)) λ { (a ∷ b ∷ c ∷ x) → refl }

  -- CCZ on wires 3, 1, 0.
  CCZ₃₁₀-diag : .(h : 3 ≤ lv) →
                DiagC {₁₊ (₃₊ n)} (CCZ₃₁₀ h) (λ x → head x * head (tail x) * head (tail (tail (tail x))))
  CCZ₃₁₀-diag h = DiagC-≡ (DiagC-conj SWAP↑↑-at sw₂₃-inv (CCZ-diag h)) λ { (a ∷ b ∷ c ∷ d ∷ x) → refl }

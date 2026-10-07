------------------------------------------------------------------------
-- Presentations of groups
--
-- Every rule holds under the interpretation (Lemmas 1 and 9)
--
-- Each rule is evaluated on symbolic labels at the width it is drawn
-- on, both sides to an explicit pair (labels , phase), and the two
-- pairs are compared (meet).  The affine rules are identities of
-- linear maps; the transport rules are the Pascal identities of
-- Section 3.2.  The quadratic rules need p odd and the cubic rules
-- p > 3, the conditions under which the binomials are the paper's.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Soundness.Rules
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Product.Base using (_,_ ; proj₁)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂)
open import Word.Base using (ε ; _•_ ; _^_)

import Data.Integer.Base as ℤ

open import Notations using (₁₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Eval p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Soundness.Derived p-2 p-prime lv

private
  variable
    n : ℕ

  -- Sums of zeros.
  0+0 : 0F + 0F ≡ 0F
  0+0 = FR.+-identityʳ 0F

  [0+0]+0 : 0F + 0F + 0F ≡ 0F
  [0+0]+0 = trans (FR.+-identityʳ (0F + 0F)) 0+0

  -- 0 + a ≡ a + 0.
  swap0 : (a : F) → 0F + a ≡ a + 0F
  swap0 a = trans (FR.+-identityˡ a) (sym (FR.+-identityʳ a))

------------------------------------------------------------------------
-- Aff_d (Figure 1)

r1 : _≐_ {₁₊ n} ⟦ M⟨ 1* ⟩ ⟧ ⟦ ε ⟧
r1 (a ∷ z) = meet (M-at 1F 1≢0 a z) (⟦⟧-ε (a ∷ z)) (cong (_∷ z) (FR.*-identityˡ a)) refl

r2 : (x y : F*) → _≐_ {₁₊ n} ⟦ M⟨ y ⟩ • M⟨ x ⟩ ⟧ ⟦ M⟨ x ⊛ y ⟩ ⟧
r2 (x , nx) (y , ny) (a ∷ z) =
  meet (•-at (M-at x nx a z) (M-at y ny (x * a) z)) (M-at (x * y) (*-nonzero nx ny) a z)
       (cong (_∷ z) (solve 3 (λ x y a → y :* (x :* a) := (x :* y) :* a) refl x y a))
       0+0

r3 : (x : F*) → _≐_ {₁₊ n} ⟦ X ^ᶠ proj₁ x • M⟨ x ⟩ • X ^ᶠ (- 1F) ⟧ ⟦ M⟨ x ⟩ ⟧
r3 (x , nx) (a ∷ z) =
  meet (•-at (•-at (Xᶠ-at (- 1F) a z) (M-at x nx (a + - 1F) z)) (Xᶠ-at x (x * (a + - 1F)) z))
       (M-at x nx a z)
       (cong (_∷ z) (solve 2 (λ x a → x :* (a :+ (:- con (ℤ.+ 1))) :+ x := x :* a) refl x a))
       [0+0]+0

r4 : (x : F*) → _≐_ {₂₊ n} ⟦ CX • M⟨ x ⟩ ↑ ⟧ ⟦ M⟨ x ⟩ ↑ • CX ^ᶠ proj₁ x ⟧
r4 (x , nx) (a ∷ b ∷ z) =
  meet (•-at (↑-at (M-at x nx b z)) (CX-at a (x * b) z))
       (•-at (CXᶠ-at x a b z) (↑-at (M-at x nx b z)))
       refl refl

r5 : (x : F*) → _≐_ {₂₊ n} ⟦ CX ^ᶠ (- proj₁ x) • M⟨ x ⟩ • CX ⟧ ⟦ M⟨ x ⟩ ⟧
r5 (x , nx) (a ∷ b ∷ z) =
  meet (•-at (•-at (CX-at a b z) (M-at x nx (a + b) (b ∷ z))) (CXᶠ-at (- x) (x * (a + b)) b z))
       (M-at x nx a (b ∷ z))
       (cong (_∷ b ∷ z) (solve 3 (λ x a b → x :* (a :+ b) :+ (:- x) :* b := x :* a) refl x a b))
       [0+0]+0

r6 : _≐_ {₂₊ n} ⟦ CX • X ↑ ⟧ ⟦ X • X ↑ • CX ⟧
r6 (a ∷ b ∷ z) =
  meet (•-at (↑-at (X-at b z)) (CX-at a (b + 1F) z))
       (•-at (•-at (CX-at a b z) (↑-at (X-at b z))) (X-at (a + b) (b + 1F ∷ z)))
       (cong (λ q → q ∷ b + 1F ∷ z) (sym (FR.+-assoc a b 1F)))
       (sym (FR.+-identityʳ (0F + 0F)))

private
  -- The reversed CX⁻¹, conjugated by swaps.
  B-at : (a b : F) (z : Labels n) →
         ⟦ SWAP • CX ^ᶠ (- 1F) • SWAP ⟧ (a ∷ b ∷ z) ≡ (a ∷ b + - 1F * a ∷ z , 0F)
  B-at a b z = at-≡ (•-at (•-at (SWAP-at a b z) (CXᶠ-at (- 1F) b a z)) (SWAP-at (b + - 1F * a) a z))
                    refl [0+0]+0

r7 : _≐_ {₂₊ n} ⟦ SWAP ⟧
       ⟦ M⟨ -1* ⟩ ↑ • (SWAP • CX ^ᶠ (- 1F) • SWAP) • CX • (SWAP • CX ^ᶠ (- 1F) • SWAP) ⟧
r7 (a ∷ b ∷ z) =
  meet (SWAP-at a b z)
       (•-at (•-at (•-at (B-at a b z) (CX-at a (b + - 1F * a) z))
                   (B-at (a + (b + - 1F * a)) (b + - 1F * a) z))
             (↑-at (M-at (- 1F) -1≢0 ((b + - 1F * a) + - 1F * (a + (b + - 1F * a))) z)))
       (cong₂ (λ s t → s ∷ t ∷ z)
         (solve 2 (λ a b → b := a :+ (b :+ (:- con (ℤ.+ 1)) :* a)) refl a b)
         (solve 2 (λ a b → a := (:- con (ℤ.+ 1)) :* ((b :+ (:- con (ℤ.+ 1)) :* a)
                                  :+ (:- con (ℤ.+ 1)) :* (a :+ (b :+ (:- con (ℤ.+ 1)) :* a)))) refl a b))
       (solve 0 (con (ℤ.+ 0) := con (ℤ.+ 0) :+ con (ℤ.+ 0) :+ con (ℤ.+ 0) :+ con (ℤ.+ 0)) refl)

r8 : _≐_ {₃₊ n} ⟦ CX ↑ • CX • CX₂₀ ⟧ ⟦ CX • CX ↑ ⟧
r8 (a ∷ b ∷ c ∷ z) =
  meet (•-at (•-at (CX₂₀-at a b c z) (CX-at (a + c) b (c ∷ z))) (↑-at (CX-at b c z)))
       (•-at (↑-at (CX-at b c z)) (CX-at a (b + c) (c ∷ z)))
       (cong (λ q → q ∷ b + c ∷ c ∷ z) (solve 3 (λ a b c → a :+ c :+ b := a :+ (b :+ c)) refl a b c))
       (FR.+-identityʳ (0F + 0F))

------------------------------------------------------------------------
-- The symmetry

s-order : _≐_ {₂₊ n} ⟦ SWAP • SWAP ⟧ ⟦ ε ⟧
s-order (a ∷ b ∷ z) = meet (•-at (SWAP-at a b z) (SWAP-at b a z)) (⟦⟧-ε (a ∷ b ∷ z)) refl 0+0

s-braid : _≐_ {₃₊ n} ⟦ SWAP • SWAP ↑ • SWAP ⟧ ⟦ SWAP ↑ • SWAP • SWAP ↑ ⟧
s-braid (a ∷ b ∷ c ∷ z) =
  meet (•-at (•-at (SWAP-at a b (c ∷ z)) (↑-at (SWAP-at a c z))) (SWAP-at b c (a ∷ z)))
       (•-at (•-at (↑-at (SWAP-at b c z)) (SWAP-at a c (b ∷ z))) (↑-at (SWAP-at a b z)))
       refl refl

s-X : _≐_ {₂₊ n} ⟦ X • SWAP ⟧ ⟦ SWAP • X ↑ ⟧
s-X (a ∷ b ∷ z) =
  meet (•-at (SWAP-at a b z) (X-at b (a ∷ z))) (•-at (↑-at (X-at b z)) (SWAP-at a (b + 1F) z)) refl refl

s-M : (c : F) .(nz : c ≢ 0F) → _≐_ {₂₊ n} ⟦ M c nz • SWAP ⟧ ⟦ SWAP • M c nz ↑ ⟧
s-M c nz (a ∷ b ∷ z) =
  meet (•-at (SWAP-at a b z) (M-at c nz b (a ∷ z))) (•-at (↑-at (M-at c nz b z)) (SWAP-at a (c * b) z))
       refl refl

s-Z : .(h : 1 ≤ lv) → _≐_ {₂₊ n} ⟦ Z h • SWAP ⟧ ⟦ SWAP • Z h ↑ ⟧
s-Z h (a ∷ b ∷ z) =
  meet (•-at (SWAP-at a b z) (Z-at h b (a ∷ z))) (•-at (↑-at (Z-at h b z)) (SWAP-at a b z)) refl (swap0 b)

s-S : .(h : 2 ≤ lv) → _≐_ {₂₊ n} ⟦ S h • SWAP ⟧ ⟦ SWAP • S h ↑ ⟧
s-S h (a ∷ b ∷ z) =
  meet (•-at (SWAP-at a b z) (S-at h b (a ∷ z))) (•-at (↑-at (S-at h b z)) (SWAP-at a b z))
       refl (swap0 (binom2 b))

s-T : .(h : 3 ≤ lv) → _≐_ {₂₊ n} ⟦ T h • SWAP ⟧ ⟦ SWAP • T h ↑ ⟧
s-T h (a ∷ b ∷ z) =
  meet (•-at (SWAP-at a b z) (T-at h b (a ∷ z))) (•-at (↑-at (T-at h b z)) (SWAP-at a b z))
       refl (swap0 (binom3 b))

s-CX : _≐_ {₃₊ n} ⟦ CX • SWAP ↑ • SWAP ⟧ ⟦ SWAP ↑ • SWAP • CX ↑ ⟧
s-CX (a ∷ b ∷ c ∷ z) =
  meet (•-at (•-at (SWAP-at a b (c ∷ z)) (↑-at (SWAP-at a c z))) (CX-at b c (a ∷ z)))
       (•-at (•-at (↑-at (CX-at b c z)) (SWAP-at a (b + c) (c ∷ z))) (↑-at (SWAP-at a c z)))
       refl refl

------------------------------------------------------------------------
-- LinPhase_d (Figure 3)

r19 : .(h : 1 ≤ lv) → _≐_ {n} ⟦ ω h ^ p ⟧ ⟦ ε ⟧
r19 h x = meet (DiagC-^ (ω-diag h) p x) (⟦⟧-ε x) refl (p-×ᶠ 1F)

r20 : .(h : 1 ≤ lv) → _≐_ {₁₊ n} ⟦ Z h ^ p ⟧ ⟦ ε ⟧
r20 h (a ∷ z) = meet (DiagC-^ (Z-diag h) p (a ∷ z)) (⟦⟧-ε (a ∷ z)) refl (p-×ᶠ a)

r21 : .(h : 1 ≤ lv) → _≐_ {₂₊ n} ⟦ CX • Z h • Z h ↑ ⟧ ⟦ Z h • CX ⟧
r21 h (a ∷ b ∷ z) =
  meet (•-at (•-at (↑-at (Z-at h b z)) (Z-at h a (b ∷ z))) (CX-at a b z))
       (•-at (CX-at a b z) (Z-at h (a + b) (b ∷ z)))
       refl
       (solve 2 (λ a b → b :+ a :+ con (ℤ.+ 0) := con (ℤ.+ 0) :+ (a :+ b)) refl a b)

r22 : .(h : 1 ≤ lv) (x : F*) → _≐_ {₁₊ n} ⟦ Z h • M⟨ x ⟩ ⟧ ⟦ M⟨ x ⟩ • Z h ^ᶠ proj₁ x ⟧
r22 h (x , nx) (a ∷ z) =
  meet (•-at (M-at x nx a z) (Z-at h (x * a) z))
       (•-at (DiagC-^ᶠ (Z-diag h) x (a ∷ z)) (M-at x nx a z))
       refl (swap0 (x * a))

r23 : .(h : 1 ≤ lv) → _≐_ {₁₊ n} ⟦ Z h • X ⟧ ⟦ ω h • X • Z h ⟧
r23 h (a ∷ z) =
  meet (•-at (X-at a z) (Z-at h (a + 1F) z))
       (•-at (•-at (Z-at h a z) (X-at a z)) (ω-at h (a + 1F ∷ z)))
       refl
       (solve 1 (λ a → con (ℤ.+ 0) :+ (a :+ con (ℤ.+ 1)) := a :+ con (ℤ.+ 0) :+ con (ℤ.+ 1)) refl a)

------------------------------------------------------------------------
-- QuadPhase_d (Figure 4), for p odd

module Quad (odd : 1 ≤ p-2) where

  open Odd odd
  open Quadratic odd

  r24 : .(h : 2 ≤ lv) → _≐_ {₁₊ n} ⟦ S h ^ p ⟧ ⟦ ε ⟧
  r24 h (a ∷ z) = meet (DiagC-^ (S-diag h) p (a ∷ z)) (⟦⟧-ε (a ∷ z)) refl (p-×ᶠ (binom2 a))

  r25 : .(h : 2 ≤ lv) → _≐_ {₁₊ n} ⟦ S h • X ⟧ ⟦ X • Z (lin₂ h) • S h ⟧
  r25 h (a ∷ z) =
    meet (•-at (X-at a z) (S-at h (a + 1F) z))
         (•-at (•-at (S-at h a z) (Z-at (lin₂ h) a z)) (X-at a z))
         refl
         (trans (FR.+-identityˡ _) (trans (binom2-shift a) (sym (FR.+-identityʳ _))))

  r26 : .(h : 2 ≤ lv) → _≐_ {₁₊ n} ⟦ S h • Z (lin₂ h) ⟧ ⟦ Z (lin₂ h) • S h ⟧
  r26 h (a ∷ z) =
    meet (•-at (Z-at (lin₂ h) a z) (S-at h a z)) (•-at (S-at h a z) (Z-at (lin₂ h) a z))
         refl (FR.+-comm a (binom2 a))

  r27 : .(h : 2 ≤ lv) (x : F*) → _≐_ {₁₊ n} ⟦ S h • M⟨ x ⟩ ⟧
          ⟦ M⟨ x ⟩ • Z (lin₂ h) ^ᶠ binom2 (proj₁ x) • S h ^ᶠ (proj₁ x * proj₁ x) ⟧
  r27 h (x , nx) (a ∷ z) =
    meet (•-at (M-at x nx a z) (S-at h (x * a) z))
         (•-at (•-at (DiagC-^ᶠ (S-diag h) (x * x) (a ∷ z)) (DiagC-^ᶠ (Z-diag (lin₂ h)) (binom2 x) (a ∷ z)))
               (M-at x nx a z))
         refl
         (trans (FR.+-identityˡ _) (trans (binom2-scale x a) (sym (FR.+-identityʳ _))))

  r28 : .(h : 2 ≤ lv) → _≐_ {₂₊ n} ⟦ M⟨ -1* ⟩ ↑ • CZ h ^ᶠ (- 1F) • M⟨ -1* ⟩ ↑ ⟧ ⟦ CZ h ⟧
  r28 h (a ∷ b ∷ z) =
    meet (•-at (•-at (↑-at (M-at (- 1F) -1≢0 b z)) (DiagC-^ᶠ (CZ-diag h) (- 1F) (a ∷ - 1F * b ∷ z)))
               (↑-at (M-at (- 1F) -1≢0 (- 1F * b) z)))
         (CZ-diag h (a ∷ b ∷ z))
         (cong (λ q → a ∷ q ∷ z) (solve 1 (λ b → (:- con (ℤ.+ 1)) :* ((:- con (ℤ.+ 1)) :* b) := b) refl b))
         (solve 2 (λ a b → con (ℤ.+ 0) :+ (:- con (ℤ.+ 1)) :* (a :* ((:- con (ℤ.+ 1)) :* b)) :+ con (ℤ.+ 0)
                          := a :* b) refl a b)

  r29 : .(h : 2 ≤ lv) → _≐_ {₂₊ n} ⟦ CX • S h ↑ ⟧ ⟦ S h ↑ • CX ⟧
  r29 h (a ∷ b ∷ z) =
    meet (•-at (↑-at (S-at h b z)) (CX-at a b z)) (•-at (CX-at a b z) (↑-at (S-at h b z)))
         refl (sym (swap0 (binom2 b)))

  r30 : .(h : 2 ≤ lv) → _≐_ {₃₊ n} ⟦ CZ h • CX ↑ ⟧ ⟦ CX ↑ • CZ h • CZ₂₀ h ⟧
  r30 h (a ∷ b ∷ c ∷ z) =
    meet (•-at (↑-at (CX-at b c z)) (CZ-diag h (a ∷ b + c ∷ c ∷ z)))
         (•-at (•-at (CZ₂₀-diag h (a ∷ b ∷ c ∷ z)) (CZ-diag h (a ∷ b ∷ c ∷ z))) (↑-at (CX-at b c z)))
         refl
         (solve 3 (λ a b c → con (ℤ.+ 0) :+ a :* (b :+ c) := a :* c :+ a :* b :+ con (ℤ.+ 0)) refl a b c)

------------------------------------------------------------------------
-- CubicPhase_d (Figure 5), for p > 3

module Cube (big : 2 ≤ p-2) where

  open Big big
  open Quadratic (big⇒odd big)
  open Cubic big

  r31 : .(h : 3 ≤ lv) → _≐_ {₁₊ n} ⟦ T h ^ p ⟧ ⟦ ε ⟧
  r31 h (a ∷ z) = meet (DiagC-^ (T-diag h) p (a ∷ z)) (⟦⟧-ε (a ∷ z)) refl (p-×ᶠ (binom3 a))

  r32 : .(h : 3 ≤ lv) (x : F*) → _≐_ {₁₊ n}
          ⟦ M⟨ x ⟩ • S (quad₃ h) ^ᶠ (2F * proj₁ x * binom2 (proj₁ x)) •
            Z (lin₃ h) ^ᶠ binom3 (proj₁ x) • T h ^ᶠ (proj₁ x * proj₁ x * proj₁ x) ⟧
          ⟦ T h • M⟨ x ⟩ ⟧
  r32 h (x , nx) (a ∷ z) =
    meet (•-at (•-at (•-at (DiagC-^ᶠ (T-diag h) (x * x * x) (a ∷ z))
                           (DiagC-^ᶠ (Z-diag (lin₃ h)) (binom3 x) (a ∷ z)))
                     (DiagC-^ᶠ (S-diag (quad₃ h)) (2F * x * binom2 x) (a ∷ z)))
               (M-at x nx a z))
         (•-at (M-at x nx a z) (T-at h (x * a) z))
         refl
         (trans (solve 6 (λ x a B3a B2a b2x b3x →
                    x :* x :* x :* B3a :+ b3x :* a :+ con (ℤ.+ 2) :* x :* b2x :* B2a :+ con (ℤ.+ 0)
                    := con (ℤ.+ 0) :+ (x :* x :* x :* B3a :+ con (ℤ.+ 2) :* x :* b2x :* B2a :+ b3x :* a))
                  refl x a (binom3 a) (binom2 a) (binom2 x) (binom3 x))
                (cong (0F +_) (sym (binom3-scale x a))))

  r33 : .(h : 3 ≤ lv) → _≐_ {₁₊ n} ⟦ T h • S (quad₃ h) ⟧ ⟦ S (quad₃ h) • T h ⟧
  r33 h (a ∷ z) =
    meet (•-at (S-at (quad₃ h) a z) (T-at h a z)) (•-at (T-at h a z) (S-at (quad₃ h) a z))
         refl (FR.+-comm (binom2 a) (binom3 a))

  r34 : .(h : 3 ≤ lv) → _≐_ {₁₊ n} ⟦ T h • X ⟧ ⟦ X • T h • S (quad₃ h) ⟧
  r34 h (a ∷ z) =
    meet (•-at (X-at a z) (T-at h (a + 1F) z))
         (•-at (•-at (S-at (quad₃ h) a z) (T-at h a z)) (X-at a z))
         refl
         (trans (cong (0F +_) (binom3-shift a))
                (solve 2 (λ B3 B2 → con (ℤ.+ 0) :+ (B3 :+ B2) := B2 :+ B3 :+ con (ℤ.+ 0)) refl (binom3 a) (binom2 a)))

  r35 : .(h : 3 ≤ lv) (x : F*) → _≐_ {₂₊ n}
          ⟦ M⟨ x ⟩ • CZ (quad₃ h) ^ᶠ binom2 (proj₁ x) • CS h ^ᶠ (proj₁ x * proj₁ x) ⟧ ⟦ CS h • M⟨ x ⟩ ⟧
  r35 h (x , nx) (a ∷ b ∷ z) =
    meet (•-at (•-at (DiagC-^ᶠ (CS-diag h) (x * x) (a ∷ b ∷ z))
                     (DiagC-^ᶠ (CZ-diag (quad₃ h)) (binom2 x) (a ∷ b ∷ z)))
               (M-at x nx a (b ∷ z)))
         (•-at (M-at x nx a (b ∷ z)) (CS-diag h (x * a ∷ b ∷ z)))
         refl
         (trans (solve 5 (λ x a b B2a b2x →
                    x :* x :* (b :* B2a) :+ b2x :* (a :* b) :+ con (ℤ.+ 0)
                    := con (ℤ.+ 0) :+ b :* (x :* x :* B2a :+ b2x :* a))
                  refl x a b (binom2 a) (binom2 x))
                (cong (λ q → 0F + b * q) (sym (binom2-scale x a))))

  r36 : .(h : 3 ≤ lv) → _≐_ {₁₊ n} ⟦ T h • Z (lin₃ h) ⟧ ⟦ Z (lin₃ h) • T h ⟧
  r36 h (a ∷ z) =
    meet (•-at (Z-at (lin₃ h) a z) (T-at h a z)) (•-at (T-at h a z) (Z-at (lin₃ h) a z))
         refl (FR.+-comm a (binom3 a))

  r37 : .(h : 3 ≤ lv) (x : F*) → _≐_ {₂₊ n} ⟦ M⟨ x ⟩ ↑ • CS h ^ᶠ proj₁ x ⟧ ⟦ CS h • M⟨ x ⟩ ↑ ⟧
  r37 h (x , nx) (a ∷ b ∷ z) =
    meet (•-at (DiagC-^ᶠ (CS-diag h) x (a ∷ b ∷ z)) (↑-at (M-at x nx b z)))
         (•-at (↑-at (M-at x nx b z)) (CS-diag h (a ∷ x * b ∷ z)))
         refl
         (solve 3 (λ x b B2a → x :* (b :* B2a) :+ con (ℤ.+ 0) := con (ℤ.+ 0) :+ (x :* b) :* B2a)
                refl x b (binom2 a))

  r38 : .(h : 3 ≤ lv) → _≐_ {₃₊ n} ⟦ CX • CS₂₀ h • CS h ↑ • CCZ h ⟧ ⟦ CS₂₀ h • CX ⟧
  r38 h (a ∷ b ∷ c ∷ z) =
    meet (•-at (•-at (•-at (CCZ-diag h (a ∷ b ∷ c ∷ z)) (DiagC-↑ (CS-diag h) (a ∷ b ∷ c ∷ z)))
                     (CS₂₀-diag h (a ∷ b ∷ c ∷ z)))
               (CX-at a b (c ∷ z)))
         (•-at (CX-at a b (c ∷ z)) (CS₂₀-diag h (a + b ∷ b ∷ c ∷ z)))
         refl
         (trans (solve 6 (λ a b c A2 B2 _ →
                    a :* b :* c :+ c :* B2 :+ c :* A2 :+ con (ℤ.+ 0)
                    := con (ℤ.+ 0) :+ c :* (A2 :+ B2 :+ a :* b))
                  refl a b c (binom2 a) (binom2 b) 0F)
                (cong (λ q → 0F + c * q) (sym (binom2-add a b))))

  r39 : .(h : 3 ≤ lv) → _≐_ {₂₊ n} ⟦ CX • T h ↑ ⟧ ⟦ T h ↑ • CX ⟧
  r39 h (a ∷ b ∷ z) =
    meet (•-at (↑-at (T-at h b z)) (CX-at a b z)) (•-at (CX-at a b z) (↑-at (T-at h b z)))
         refl (sym (swap0 (binom3 b)))

  r40 : .(h : 3 ≤ lv) (x : F*) → _≐_ {₃₊ n} ⟦ M⟨ x ⟩ ↑ ↑ • CCZ h ^ᶠ proj₁ x ⟧ ⟦ CCZ h • M⟨ x ⟩ ↑ ↑ ⟧
  r40 h (x , nx) (a ∷ b ∷ c ∷ z) =
    meet (•-at (DiagC-^ᶠ (CCZ-diag h) x (a ∷ b ∷ c ∷ z)) (↑-at (↑-at (M-at x nx c z))))
         (•-at (↑-at (↑-at (M-at x nx c z))) (CCZ-diag h (a ∷ b ∷ x * c ∷ z)))
         refl
         (solve 4 (λ x a b c → x :* (a :* b :* c) :+ con (ℤ.+ 0) := con (ℤ.+ 0) :+ a :* b :* (x :* c))
                refl x a b c)

  r41 : .(h : 3 ≤ lv) → _≐_ {₄₊ n} ⟦ CX ↑ ↑ • CCZ₃₁₀ h • CCZ h ⟧ ⟦ CCZ h • CX ↑ ↑ ⟧
  r41 h (a ∷ b ∷ c ∷ d ∷ z) =
    meet (•-at (•-at (CCZ-diag h (a ∷ b ∷ c ∷ d ∷ z)) (CCZ₃₁₀-diag h (a ∷ b ∷ c ∷ d ∷ z)))
               (↑-at (↑-at (CX-at c d z))))
         (•-at (↑-at (↑-at (CX-at c d z))) (CCZ-diag h (a ∷ b ∷ c + d ∷ d ∷ z)))
         refl
         (solve 4 (λ a b c d → a :* b :* c :+ a :* b :* d :+ con (ℤ.+ 0) := con (ℤ.+ 0) :+ a :* b :* (c :+ d))
                refl a b c d)

  r42 : .(h : 3 ≤ lv) → _≐_ {₃₊ n} ⟦ CX ↑ • CS h • CS₂₀ h ⟧ ⟦ CS h • CX ↑ ⟧
  r42 h (a ∷ b ∷ c ∷ z) =
    meet (•-at (•-at (CS₂₀-diag h (a ∷ b ∷ c ∷ z)) (CS-diag h (a ∷ b ∷ c ∷ z))) (↑-at (CX-at b c z)))
         (•-at (↑-at (CX-at b c z)) (CS-diag h (a ∷ b + c ∷ c ∷ z)))
         refl
         (solve 3 (λ b c A2 → c :* A2 :+ b :* A2 :+ con (ℤ.+ 0) := con (ℤ.+ 0) :+ (b :+ c) :* A2)
                refl b c (binom2 a))

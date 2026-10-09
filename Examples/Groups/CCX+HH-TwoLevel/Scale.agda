------------------------------------------------------------------------
-- Presentations of groups
--
-- Scaled elements: a / 2ᵏ for a ∈ ℤ, written sc k a.  Every element of
-- 𝔻 = ℤ[1/2] is of this form (rep), and the scalar 1/2 of K raises the
-- exponent by one (½-sc).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Scale where

open import Data.Bool.Base using (T)
open import Data.Integer.Base as ℤ using (ℤ ; +_)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃₂ ; _,_)
import Data.Rational.Base as ℚ
open import Data.Rational.Unnormalised.Base as ℚᵘ using (*≡*)
import Data.Rational.Unnormalised.Properties as ℚᵘP
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality

open import Instances using (toℚ)
open import Quantum.Synthesis.Ring
  using (Dyadic' ; 2^ ; Canonical ; ToRationalDyadic ; SemiRingDyadic ; RingDyadic)
open import Quantum.Synthesis.Ring.Properties.Dyadic
  using (toℚ-injective ; toℚ-u ; u ; u-* ; dyadic-spec′ ; nz)

open import Examples.Groups.CCX+HH-TwoLevel.Ring

------------------------------------------------------------------------
-- Powers

infixr 8 _^ᴰ_

_^ᴰ_ : D → ℕ → D
_^ᴰ_ = DA._^_

-- 2ⁿ, as an integer, is the n-th power of 2.
ι-2^ : ∀ n → ι (+ 2^ n) ≡ 2ᴰ ^ᴰ n
ι-2^ zero = refl
ι-2^ (suc n) = begin
  ι (+ (2 ℕ.* 2^ n))              ≡⟨ cong ι (ℤP.pos-* 2 (2^ n)) ⟩
  ι (+ 2 ℤ.* + 2^ n)              ≡⟨ ι-* (+ 2) (+ 2^ n) ⟩
  ι (+ 2) DR.* ι (+ 2^ n)         ≡⟨ cong (2ᴰ DR.*_) (ι-2^ n) ⟩
  2ᴰ DR.* (2ᴰ ^ᴰ n)               ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Scaling
-- sc is opaque, and sc-def unfolds it.

opaque
  -- sc k a = a / 2ᵏ.
  sc : ℕ → ℤ → D
  sc k a = ι a DR.* (½ᴰ ^ᴰ k)

  sc-def : ∀ k a → sc k a ≡ ι a DR.* (½ᴰ ^ᴰ k)
  sc-def k a = refl

sc-+ : ∀ k a b → sc k (a ℤ.+ b) ≡ sc k a DR.+ sc k b
sc-+ k a b = begin
  sc k (a ℤ.+ b)                    ≡⟨ sc-def k (a ℤ.+ b) ⟩
  ι (a ℤ.+ b) DR.* X                ≡⟨ cong (DR._* X) (ι-+ a b) ⟩
  (ι a DR.+ ι b) DR.* X             ≡⟨ DR.distribʳ X (ι a) (ι b) ⟩
  ι a DR.* X DR.+ ι b DR.* X        ≡⟨ sym (cong₂ DR._+_ (sc-def k a) (sc-def k b)) ⟩
  sc k a DR.+ sc k b                ∎
  where
  open ≡-Reasoning
  X = ½ᴰ ^ᴰ k

sc-neg : ∀ k a → sc k (ℤ.- a) ≡ DR.- sc k a
sc-neg k a = begin
  sc k (ℤ.- a)              ≡⟨ sc-def k (ℤ.- a) ⟩
  ι (ℤ.- a) DR.* X          ≡⟨ cong (DR._* X) (ι-neg a) ⟩
  (DR.- ι a) DR.* X         ≡⟨ DA.-‿*-distrib X (ι a) ⟩
  DR.- (ι a DR.* X)         ≡⟨ cong DR.-_ (sym (sc-def k a)) ⟩
  DR.- sc k a               ∎
  where
  open ≡-Reasoning
  X = ½ᴰ ^ᴰ k

-- Integer scalars pass through.
sc-* : ∀ k c a → sc k (c ℤ.* a) ≡ ι c DR.* sc k a
sc-* k c a = begin
  sc k (c ℤ.* a)              ≡⟨ sc-def k (c ℤ.* a) ⟩
  ι (c ℤ.* a) DR.* X          ≡⟨ cong (DR._* X) (ι-* c a) ⟩
  (ι c DR.* ι a) DR.* X       ≡⟨ DR.*-assoc (ι c) (ι a) X ⟩
  ι c DR.* (ι a DR.* X)       ≡⟨ cong (ι c DR.*_) (sym (sc-def k a)) ⟩
  ι c DR.* sc k a             ∎
  where
  open ≡-Reasoning
  X = ½ᴰ ^ᴰ k

sc-0 : ∀ k → sc k (+ 0) ≡ DR.0#
sc-0 k = trans (sc-def k (+ 0)) (DR.zeroˡ (½ᴰ ^ᴰ k))

-- Dividing by 2 once more: the scalar of K.
½-sc : ∀ k a → ½ᴰ DR.* sc k a ≡ sc (suc k) a
½-sc k a = begin
  ½ᴰ DR.* sc k a                ≡⟨ cong (½ᴰ DR.*_) (sc-def k a) ⟩
  ½ᴰ DR.* (ι a DR.* X)          ≡⟨ DA.*-3 ½ᴰ (ι a) X ⟩
  ι a DR.* (½ᴰ DR.* X)          ≡⟨ sym (sc-def (suc k) a) ⟩
  sc (suc k) a                  ∎
  where
  open ≡-Reasoning
  X = ½ᴰ ^ᴰ k

-- A factor 2 in the numerator cancels one in the denominator.
sc-2 : ∀ k a → sc (suc k) (+ 2 ℤ.* a) ≡ sc k a
sc-2 k a = begin
  sc (suc k) (+ 2 ℤ.* a)                ≡⟨ sc-def (suc k) (+ 2 ℤ.* a) ⟩
  ι (+ 2 ℤ.* a) DR.* (½ᴰ DR.* X)        ≡⟨ cong (DR._* (½ᴰ DR.* X)) (ι-* (+ 2) a) ⟩
  (2ᴰ DR.* ι a) DR.* (½ᴰ DR.* X)        ≡⟨ DA.*-4 2ᴰ (ι a) ½ᴰ X ⟩
  (2ᴰ DR.* ½ᴰ) DR.* (ι a DR.* X)        ≡⟨ cong (DR._* (ι a DR.* X)) 2*½ ⟩
  DR.1# DR.* (ι a DR.* X)               ≡⟨ DR.*-identityˡ (ι a DR.* X) ⟩
  ι a DR.* X                            ≡⟨ sym (sc-def k a) ⟩
  sc k a                                ∎
  where
  open ≡-Reasoning
  X = ½ᴰ ^ᴰ k

-- 2ᵈ.
2^ᶻ : ℕ → ℤ
2^ᶻ d = + 2^ d

sc-2^ : ∀ d k a → sc (d ℕ.+ k) (2^ᶻ d ℤ.* a) ≡ sc k a
sc-2^ zero k a = cong (sc k) (ℤP.*-identityˡ a)
sc-2^ (suc d) k a = begin
  sc (suc (d ℕ.+ k)) (+ (2 ℕ.* 2^ d) ℤ.* a)       ≡⟨ cong (λ z → sc (suc (d ℕ.+ k)) (z ℤ.* a)) (ℤP.pos-* 2 (2^ d)) ⟩
  sc (suc (d ℕ.+ k)) ((+ 2 ℤ.* 2^ᶻ d) ℤ.* a)       ≡⟨ cong (sc (suc (d ℕ.+ k))) (ℤP.*-assoc (+ 2) (2^ᶻ d) a) ⟩
  sc (suc (d ℕ.+ k)) (+ 2 ℤ.* (2^ᶻ d ℤ.* a))       ≡⟨ sc-2 (d ℕ.+ k) (2^ᶻ d ℤ.* a) ⟩
  sc (d ℕ.+ k) (2^ᶻ d ℤ.* a)                      ≡⟨ sc-2^ d k a ⟩
  sc k a                                          ∎
  where open ≡-Reasoning

-- Raising the exponent.
sc-raise : ∀ d k a → sc k a ≡ sc (d ℕ.+ k) (2^ᶻ d ℤ.* a)
sc-raise d k a = sym (sc-2^ d k a)

-- The numerator is determined by the exponent.
sc-cancel : ∀ k a → sc k a DR.* (2ᴰ ^ᴰ k) ≡ ι a
sc-cancel k a = begin
  sc k a DR.* (2ᴰ ^ᴰ k)                 ≡⟨ cong (DR._* (2ᴰ ^ᴰ k)) (sc-def k a) ⟩
  (ι a DR.* X) DR.* (2ᴰ ^ᴰ k)           ≡⟨ DR.*-assoc (ι a) X (2ᴰ ^ᴰ k) ⟩
  ι a DR.* (X DR.* (2ᴰ ^ᴰ k))           ≡⟨ cong (ι a DR.*_) (DA.^-inverse ½ᴰ 2ᴰ k ½*2) ⟩
  ι a DR.* DR.1#                        ≡⟨ DR.*-identityʳ (ι a) ⟩
  ι a                                   ∎
  where
  open ≡-Reasoning
  X = ½ᴰ ^ᴰ k

sc-injective : ∀ k {a b} → sc k a ≡ sc k b → a ≡ b
sc-injective k {a} {b} eq =
  ι-injective (trans (sym (sc-cancel k a)) (trans (cong (DR._* (2ᴰ ^ᴰ k)) eq) (sc-cancel k b)))

------------------------------------------------------------------------
-- Every element of 𝔻 is some a / 2ᴷ

private
  -- (a / d) · (d / 1) = a / 1 in the unnormalised rationals.
  /-cancel : ∀ a d .{{_ : ℕ.NonZero d}} →
             (a ℚᵘ./ d) ℚᵘ.* ((+ d) ℚᵘ./ 1) ℚᵘ.≃ (a ℚᵘ./ 1)
  /-cancel a (suc d) = *≡* (begin
    (a ℤ.* + suc d) ℤ.* + 1        ≡⟨ ℤP.*-identityʳ _ ⟩
    a ℤ.* + suc d                  ≡⟨ cong (λ k → a ℤ.* + k) (sym (ℕP.*-identityʳ (suc d))) ⟩
    a ℤ.* + (suc d ℕ.* 1)          ∎)
    where open ≡-Reasoning

  -- A dyadic fraction a/2ⁿ times 2ⁿ is a.
  dyadic-cancel : ∀ a n .(c : T (Canonical a n)) → Dyadic' a n c 𝔻R.* ι₀ (+ 2^ n) ≡ ι₀ a
  dyadic-cancel a n c = toℚ-injective (begin
    toℚ (x 𝔻R.* y)            ≡⟨ toℚ-u (x 𝔻R.* y) ⟩
    ℚ.fromℚᵘ (u (x 𝔻R.* y))   ≡⟨ ℚP.fromℚᵘ-cong (ℚᵘP.≃-trans (u-* dyadic-spec′ x y)
                                                              (/-cancel a (2^ n) {{nz n}})) ⟩
    ℚ.fromℚᵘ (u (ι₀ a))       ≡⟨ sym (toℚ-u (ι₀ a)) ⟩
    toℚ (ι₀ a)                ∎)
    where
    open ≡-Reasoning
    x = Dyadic' a n c
    y = ι₀ (+ 2^ n)

opaque
  unfolding _*ᴰ_

  private
    dyadic-cancelᴰ : ∀ a n .(c : T (Canonical a n)) → Dyadic' a n c DR.* ι (+ 2^ n) ≡ ι a
    dyadic-cancelᴰ = dyadic-cancel

-- Opaque, so that clients see only its type.
opaque
  rep : (x : D) → ∃₂ λ K a → x ≡ sc K a
  rep x@(Dyadic' a n c) = n , a , (begin
    x                                     ≡⟨ sym (DR.*-identityʳ x) ⟩
    x DR.* DR.1#                          ≡⟨ cong (x DR.*_) (sym (DA.^-inverse 2ᴰ ½ᴰ n 2*½)) ⟩
    x DR.* ((2ᴰ ^ᴰ n) DR.* (½ᴰ ^ᴰ n))     ≡⟨ sym (DR.*-assoc x (2ᴰ ^ᴰ n) (½ᴰ ^ᴰ n)) ⟩
    (x DR.* (2ᴰ ^ᴰ n)) DR.* (½ᴰ ^ᴰ n)     ≡⟨ cong (λ z → (x DR.* z) DR.* (½ᴰ ^ᴰ n)) (sym (ι-2^ n)) ⟩
    (x DR.* ι (+ 2^ n)) DR.* (½ᴰ ^ᴰ n)    ≡⟨ cong (DR._* (½ᴰ ^ᴰ n)) (dyadic-cancelᴰ a n c) ⟩
    ι a DR.* (½ᴰ ^ᴰ n)                    ≡⟨ sym (sc-def n a) ⟩
    sc n a                                ∎)
    where
    open ≡-Reasoning

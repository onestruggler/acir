------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness of the rule [Case] (Amy, QPL 2018, figure 2, appendix A)
--
-- [Case] rewrites
--
--   1/√2^(m+2) Σ_{y ∈ Z₂^(m+2)} e^{2πiP} |f⟩  ⟶
--   1/√2^m Σ_{y ∈ Z₂^m} e^{2πi((1-X)R[y₁←Q] + X R′[y₀←Q′])} |f⟩
--
-- where P = ¼y₀X + ½y₀(y₁ + Q) + R = ¼y₁(1 - X) + ½y₁(y₀ + Q′) + R′
-- (PathSum.Reduction.General states this through the quarters of P).
-- The appendix argues by cases on the value of X, reducing each case to
-- [HH] and [Elim].  Here the argument is a direct calculation instead:
-- over each assignment to the other path variables, the four branches
-- of y₀ and y₁ hit the same states (both variables are internal) and
-- add up to twice a single power of ζ (PathSum.Pairs.quad), and that
-- power is the reduct's phase there.  So the amplitude of ξ is twice
-- the reduct's, and 2 = √2·√2 pays for the two units of normalisation
-- the rule consumes.  The case split on X happens inside quad, on
-- values; no path-sum is restricted to X = 0 or X = 1, which is what
-- the appendix's appeal to [HH] per case would need.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Reduction.CaseSound (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (zero; suc)
open import Data.Integer.Base using (ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (*-zeroʳ)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.Base using (PathSum; phase; out; y₀; head-part; tail-part)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; 0ᴬ; _·ᴬ_; zpow; Σᴮ-cong; ·ᴬ-Σᴮ; scale; scale-map; scale-·ᴬ;
   √2·-twice)
open import PathSum.Denotation M₀ using (Assign; hits; amp; _≋_)
open import PathSum.Pairs M₀ using (module Quad; quad)
open import PathSum.Polynomial using
  (Poly; y[_]; κ; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar; eval)
open import PathSum.Polynomial.Boolean using (BoolValued)
open import PathSum.Polynomial.Product using (_*ᴾ_; eval-*ᴾ)
open import PathSum.Polynomial.Properties using
  (eval-+ᴾ; eval-−ᴾ; eval-·ᴾ; eval-κ; eval-≈; eval-ext)
open import PathSum.Polynomial.Substitution using
  (q₀₀; q₀₁; q₁₀; q₁₁; drop₁; substHead; eval-substHead)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (¼; ½)
open import PathSum.Reduction.General M using (case-reduct)

import Relation.Binary.PropositionalEquality as Eq


------------------------------------------------------------------------
-- The calculation

module _ {n k m : ℕ} (ξ : PathSum n (suc (suc k)) (suc (suc m)))
         (X Q Q′ : Poly n m)
         (bX : BoolValued X) (bQ : BoolValued Q) (bQ′ : BoolValued Q′)
         (e11 : q₁₁ (phase ξ) ≈[ pow M ] κ ½)
         (e10 : q₁₀ (phase ξ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)))
         (e01 : q₀₁ (phase ξ) ≈[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)))
         (eqf₀ : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         (eqf₁ : ∀ w → NoVar (+ 2) y[ suc zero ] (out ξ w))
         where

  open Quad ξ eqf₀ eqf₁

  private
    xv qv q′v : Assign n → Assign m → ℤ
    xv  x y = eval X x y
    qv  x y = eval Q x y
    q′v x y = eval Q′ x y

    -- The three premises, read at a point.

    d-eval : ∀ x y → pow M ∣ (e₁₁ x y - ½)
    d-eval x y = Eq.subst (λ u → pow M ∣ (e₁₁ x y - u)) (eval-κ ½ x y)
      (eval-≈ (q₁₁ (phase ξ)) (κ ½) e11 x y)

    h-eval : ∀ x y → pow M ∣ (e₁₀ x y - ((¼ * xv x y) + (½ * qv x y)))
    h-eval x y = Eq.subst (λ u → pow M ∣ (e₁₀ x y - u))
      (trans (eval-+ᴾ (¼ ·ᴾ X) (½ ·ᴾ Q) x y)
             (cong₂ _+_ (eval-·ᴾ ¼ X x y) (eval-·ᴾ ½ Q x y)))
      (eval-≈ (q₁₀ (phase ξ)) ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) e10 x y)

    v-eval : ∀ x y →
             pow M ∣ (e₀₁ x y - ((¼ * (1ℤ - xv x y)) + (½ * q′v x y)))
    v-eval x y = Eq.subst (λ u → pow M ∣ (e₀₁ x y - u))
      (trans (eval-+ᴾ (¼ ·ᴾ (κ 1ℤ -ᴾ X)) (½ ·ᴾ Q′) x y)
        (cong₂ _+_
          (trans (eval-·ᴾ ¼ (κ 1ℤ -ᴾ X) x y)
                 (cong (λ u → ¼ * u)
                   (trans (eval-−ᴾ (κ 1ℤ) X x y)
                          (cong (λ u → u - xv x y) (eval-κ 1ℤ x y)))))
          (eval-·ᴾ ½ Q′ x y)))
      (eval-≈ (q₀₁ (phase ξ)) ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) e01 x y)

    -- The reduct's phase at a point: (1 - X)(R[y₁ ← Q]) + X(R′[y₀ ← Q′]).

    Ec : Assign n → Assign m → ℤ
    Ec x y = ((1ℤ - xv x y) * (e₀₀ x y + (qv x y * e₀₁ x y))) +
             (xv x y * (e₀₀ x y + (q′v x y * e₁₀ x y)))

    red-eval : ∀ x y → eval (phase (case-reduct ξ X Q Q′)) x y ≡ Ec x y
    red-eval x y = trans
      (eval-+ᴾ ((κ 1ℤ -ᴾ X) *ᴾ substHead (tail-part (phase ξ)) Q)
               (X *ᴾ substHead (drop₁ (phase ξ)) Q′) x y)
      (cong₂ _+_
        (trans (eval-*ᴾ (κ 1ℤ -ᴾ X) (substHead (tail-part (phase ξ)) Q) x y)
          (cong₂ _*_
            (trans (eval-−ᴾ (κ 1ℤ) X x y)
                   (cong (λ u → u - xv x y) (eval-κ 1ℤ x y)))
            (eval-substHead (tail-part (phase ξ)) Q x y)))
        (trans (eval-*ᴾ X (substHead (drop₁ (phase ξ)) Q′) x y)
          (cong (λ u → xv x y * u)
            (trans (eval-substHead (drop₁ (phase ξ)) Q′ x y)
              (cong₂ (λ a b → a + (q′v x y * b))
                (eval-ext (tail-part (drop₁ (phase ξ))) (q₀₀ (phase ξ))
                          (λ _ → refl) x y)
                (eval-ext (head-part (drop₁ (phase ξ))) (q₁₀ (phase ξ))
                          (λ _ → refl) x y))))))

    if-cong : ∀ {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
              (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
    if-cong {p = true}  refl a≐b = a≐b
    if-cong {p = false} refl _   = λ _ → refl

    ·ᴬ-if : ∀ (p : Bool) (a : Amp) →
            ((+ 2) ·ᴬ (if p then a else 0ᴬ)) ≐ (if p then ((+ 2) ·ᴬ a) else 0ᴬ)
    ·ᴬ-if true  a _ = refl
    ·ᴬ-if false a _ = *-zeroʳ (+ 2)

    -- The four branches collapse to twice the reduct's summand.

    Fq-2 : ∀ x z y → Fq x z y ≐
           (+ 2) ·ᴬ (if hitsQ x y z then zpow (Ec x y) else 0ᴬ)
    Fq-2 x z y w = trans (Fq-form x z y w)
      (trans (if-cong {p = hitsQ x y z} refl
               (quad (e₀₀ x y) (e₁₀ x y) (e₀₁ x y) (e₁₁ x y)
                     (xv x y) (qv x y) (q′v x y) (bX x y) (bQ x y) (bQ′ x y)
                     (d-eval x y) (h-eval x y) (v-eval x y)) w)
             (sym (·ᴬ-if (hitsQ x y z) (zpow (Ec x y)) w)))

    -- Stated over any ζ with the reduct's outputs and phase values, so
    -- that the reduct itself never unfolds in the proof.

    amp-gen : (ζ : PathSum n k m) →
              (∀ x y z → hits ζ x y z ≡ hitsQ x y z) →
              (∀ x y → eval (phase ζ) x y ≡ Ec x y) →
              ∀ x z → amp ξ x z ≐ (+ 2) ·ᴬ amp ζ x z
    amp-gen ζ hζ pζ x z w = trans (amp-quads x z w)
      (trans (Σᴮ-cong (λ y → Fq-2 x z y) w)
        (trans (sym (·ᴬ-Σᴮ (+ 2)
                      (λ y → if hitsQ x y z then zpow (Ec x y) else 0ᴬ) w))
               (cong (λ u → (+ 2) * u)
                 (Σᴮ-cong (λ y → if-cong (sym (hζ x y z))
                   (λ j → cong (λ e → zpow e j) (sym (pζ x y)))) w))))

  case-sound : ξ ≋ case-reduct ξ X Q Q′
  case-sound x z i = trans
    (scale-map k
      (amp-gen (case-reduct ξ X Q Q′) (λ _ _ _ → refl) red-eval x z) i)
    (trans (scale-·ᴬ k (+ 2) (amp (case-reduct ξ X Q Q′) x z) i)
           (sym (√2·-twice (scale k (amp (case-reduct ξ X Q Q′) x z)) i)))

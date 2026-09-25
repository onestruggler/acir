------------------------------------------------------------------------
-- Presentations of groups
--
-- Proposition 3.1 for all of figure 2 (Amy, QPL 2018)
--
-- Every rule of PathSum.Reduction.General preserves the denotation:
-- [Elim] is PathSum.Denotation's, [Case] is
-- PathSum.Reduction.CaseSound's, and [ω] and [HH] with Boolean-valued
-- quotients are proved here, by the calculations of appendix A.
--
-- [ω]: where the coefficient of y₀ is ¼ + ½Q, the two branches of y₀
-- add up to √2 ζ^(⅛ + t) where Q = 0 and to √2 ζ^(⅛ - ¼ + t) where
-- Q = 1, that is, to √2 ζ^(⅛ - ¼Q + t) in both cases because Q is
-- 0 or 1 -- which is why Q must be Boolean-valued and not merely
-- Boolean modulo 2.  (Appendix A arrives at ⅛ + ¾Q, which agrees with
-- figure 2's ⅛ - ¼Q modulo 1 for integer Q; the figure's is used.)
--
-- [HH]: where the coefficient of y₀ is ½(y_i + Q), the branches cancel
-- at the paths where y_i ≠ Q and double where y_i = Q.  Pairing each
-- path with the one differing from it at y_i, exactly one of the two
-- has y_i = Q (Q does not mention y_i), and there the reduct, which
-- substitutes Q for y_i, agrees with ξ.  So the amplitude of ξ is the
-- sum over those paths of twice ξ's summand, which is the sum over all
-- paths of the reduct's; the normalisation is unchanged, as in the
-- figure, the reduct keeping y_i as a dummy variable.
--
-- Proposition 3.1 follows for chains, by transitivity.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Reduction.Sound (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using
  (*-zeroʳ; *-identityʳ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (suc)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using ([_]ᶻ; ≔-here; ≔-there)
open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; y₀; head-part; tail-part)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; 0ᴬ; _+ᴬ_; _·ᴬ_; zpow; √2·; √2·-map; √2·-Σᴮ; Σᴮ-cong; Σᴮ-at;
   setᵗ; Respects; scale; scale-map; scale-√2)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; _≋_; ≋-refl; ≋-trans; hits-≗³; elim-sound)
open import PathSum.Pairs M₀ using
  (module Pair; half-even; half-odd; hits-eval)
open import PathSum.Polynomial using
  (Poly; y[_]; κ; μ; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar; eval)
open import PathSum.Polynomial.Boolean using (IsBit; BoolValued)
open import PathSum.Polynomial.Product using (eval-μᴾ)
open import PathSum.Polynomial.Properties using
  (eval-+ᴾ; eval-−ᴾ; eval-·ᴾ; eval-κ; eval-≈; eval-cong; eval-off; i∣0)
open import PathSum.Polynomial.Substitution using
  (Absent; substᴾ; eval-substᴾ-fixed; substᴾ-absent)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (⅛; ¼; ½)
open import PathSum.Reduction.General M using
  (ωᴳ-reduct; hhᴳ-reduct; _⟶ᴳ_; _⟶ᴳ*_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; εᴳ; _◅ᴳ_)

open import PathSum.Reduction.CaseSound M₀ public using (case-sound)

import Data.Integer.Divisibility.Signed as ℤDiv
import Relation.Binary.PropositionalEquality as Eq

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n k m k′ m′ : ℕ

  if-cong : ∀ {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
            (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
  if-cong {p = true}  refl a≐b = a≐b
  if-cong {p = false} refl _   = λ _ → refl


------------------------------------------------------------------------
-- Soundness of [ω]

module _ {n k m : ℕ} (ξ : PathSum n (suc k) (suc m)) (Q : Poly n m)
         (bQ : BoolValued Q)
         (eqP : head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q)))
         (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         where

  open Pair ξ eqf

  private
    qv : Assign n → Assign m → ℤ
    qv x y = eval Q x y

    head-eval : ∀ x y → pow M ∣ (hd x y - (¼ + (½ * qv x y)))
    head-eval x y = Eq.subst (λ u → pow M ∣ (hd x y - u))
      (trans (eval-+ᴾ (κ ¼) (½ ·ᴾ Q) x y)
             (cong₂ _+_ (eval-κ ¼ x y) (eval-·ᴾ ½ Q x y)))
      (eval-≈ (head-part (phase ξ)) (κ ¼ +ᴾ (½ ·ᴾ Q)) eqP x y)

    -- The exponent the pair collapses to.

    Eω : Assign n → Assign m → ℤ
    Eω x y = (⅛ - (¼ * qv x y)) + tv x y

    F-√2 : ∀ x z y →
           F x z y ≐ √2· (if hitsT x y z then zpow (Eω x y) else 0ᴬ)
    F-√2 x z y = by-bit (bQ x y)
      where
      guarded : ℤ → Amp
      guarded e = √2· (if hitsT x y z then zpow e else 0ᴬ)

      by-bit : IsBit (qv x y) →
               F x z y ≐ √2· (if hitsT x y z then zpow (Eω x y) else 0ᴬ)
      by-bit (inj₁ q≡0) w = trans (F-ω₀ x z y div w)
        (cong (λ e → guarded e w) (cong (λ u → u + tv x y) (sym at0)))
        where
        at0 : ⅛ - (¼ * qv x y) ≡ ⅛
        at0 = trans (cong (λ u → ⅛ - (¼ * u)) q≡0)
                    (trans (cong (λ u → ⅛ - u) (*-zeroʳ ¼)) (+-identityʳ ⅛))

        div : pow M ∣ (hd x y - ¼)
        div = Eq.subst (λ u → pow M ∣ (hd x y - u))
          (trans (cong (λ u → ¼ + (½ * u)) q≡0)
                 (trans (cong (λ u → ¼ + u) (*-zeroʳ ½)) (+-identityʳ ¼)))
          (head-eval x y)
      by-bit (inj₂ q≡1) w = trans (F-ω₁ x z y div w)
        (cong (λ e → guarded e w) (cong (λ u → u + tv x y) (sym at1)))
        where
        at1 : ⅛ - (¼ * qv x y) ≡ ⅛ - ¼
        at1 = trans (cong (λ u → ⅛ - (¼ * u)) q≡1)
                    (cong (λ u → ⅛ - u) (*-identityʳ ¼))

        div : pow M ∣ (hd x y - (¼ + ½))
        div = Eq.subst (λ u → pow M ∣ (hd x y - u))
          (trans (cong (λ u → ¼ + (½ * u)) q≡1)
                 (cong (λ u → ¼ + u) (*-identityʳ ½)))
          (head-eval x y)

    red-eval : ∀ x y → eval (phase (ωᴳ-reduct ξ Q)) x y ≡ Eω x y
    red-eval x y = trans
      (eval-+ᴾ (κ ⅛ -ᴾ (¼ ·ᴾ Q)) (tail-part (phase ξ)) x y)
      (cong (λ u → u + tv x y)
        (trans (eval-−ᴾ (κ ⅛) (¼ ·ᴾ Q) x y)
               (cong₂ _-_ (eval-κ ⅛ x y) (eval-·ᴾ ¼ Q x y))))

    -- Over any ζ carrying the reduct's outputs and phase values, so the
    -- reduct never unfolds in the proof.

    amp-gen : (ζ : PathSum n k m) →
              (∀ x y z → hits ζ x y z ≡ hitsT x y z) →
              (∀ x y → eval (phase ζ) x y ≡ Eω x y) →
              ∀ x z → amp ξ x z ≐ √2· (amp ζ x z)
    amp-gen ζ hζ pζ x z w = trans (amp-pairs x z w)
      (trans (Σᴮ-cong (λ y → F-√2 x z y) w)
        (trans (sym (√2·-Σᴮ
                  (λ y → if hitsT x y z then zpow (Eω x y) else 0ᴬ) w))
               (√2·-map (Σᴮ-cong (λ y → if-cong (sym (hζ x y z))
                          (λ j → cong (λ e → zpow e j) (sym (pζ x y))))) w)))

  ωᴳ-sound : ξ ≋ ωᴳ-reduct ξ Q
  ωᴳ-sound x z i = trans
    (scale-map k (amp-gen (ωᴳ-reduct ξ Q) (λ _ _ _ → refl) red-eval x z) i)
    (scale-√2 k (amp (ωᴳ-reduct ξ Q) x z) i)


------------------------------------------------------------------------
-- Soundness of [HH]

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (ℤDiv.∣⇒∣ᵤ h)
  ... | ()

  double : ∀ g → ((+ 2) * g) + 0ℤ ≡ g + g
  double = solve 1 (λ g → (con (+ 2) :* g) :+ con 0ℤ := g :+ g) refl

  double′ : ∀ g → 0ℤ + ((+ 2) * g) ≡ g + g
  double′ = solve 1 (λ g → con 0ℤ :+ (con (+ 2) :* g) := g :+ g) refl

module _ {n k m : ℕ} (ξ : PathSum n k (suc m)) (i : Fin m) (Q : Poly n m)
         (bQ : BoolValued Q) (absQ : Absent y[ i ] Q)
         (eqP : head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)))
         (eqf : ∀ w → NoVar (+ 2) y₀ (out ξ w))
         where

  open Pair ξ eqf

  private
    q s : Assign n → Assign m → ℤ
    q x y = eval Q x y
    s x y = [ y i ]ᶻ + q x y

    head-eval : ∀ x y → pow M ∣ (hd x y - (½ * s x y))
    head-eval x y = Eq.subst (λ u → pow M ∣ (hd x y - u))
      (trans (eval-·ᴾ ½ (μ y[ i ] +ᴾ Q) x y)
        (cong (λ u → ½ * u)
          (trans (eval-+ᴾ (μ y[ i ]) Q x y)
                 (cong (λ u → u + q x y) (eval-μᴾ y[ i ] x y)))))
      (eval-≈ (head-part (phase ξ)) (½ ·ᴾ (μ y[ i ] +ᴾ Q)) eqP x y)

    -- The head of the phase is ½(y_i + Q): a whole number where y_i = Q
    -- and a half where not.

    s-at : ∀ x y (b : Bool) (c : ℤ) → y i ≡ b → q x y ≡ c → s x y ≡ [ b ]ᶻ + c
    s-at x y b c eb ec = cong₂ (λ u v → [ u ]ᶻ + v) eb ec

    hd-whole : ∀ x y (b : Bool) (c : ℤ) → y i ≡ b → q x y ≡ c →
               (+ 2) ∣ ([ b ]ᶻ + c) → pow M ∣ hd x y
    hd-whole x y b c eb ec d =
      half-even {h = hd x y} {s = s x y} (head-eval x y)
        (Eq.subst ((+ 2) ∣_) (sym (s-at x y b c eb ec)) d)

    hd-half : ∀ x y (b : Bool) (c : ℤ) → y i ≡ b → q x y ≡ c →
              ¬ ((+ 2) ∣ ([ b ]ᶻ + c)) → pow M ∣ (hd x y - ½)
    hd-half x y b c eb ec nd = half-odd {h = hd x y} {s = s x y} (head-eval x y)
      (λ d → nd (Eq.subst ((+ 2) ∣_) (s-at x y b c eb ec) d))

    -- setᵗ i y is y with y_i set, which Q does not see.

    setᵗ-i : ∀ (y : Assign m) → setᵗ i y i ≡ true
    setᵗ-i y = ≔-here y i true

    setᵗ-off : ∀ (y : Assign m) j → ¬ (j ≡ i) → y j ≡ setᵗ i y j
    setᵗ-off y j j≢i = sym (≔-there y true j≢i)

    q-off : ∀ x y → q x y ≡ q x (setᵗ i y)
    q-off x y = eval-off Q i absQ x y (setᵗ i y) (setᵗ-off y)

    -- The reduct's summand, over any ζ with what the reduct has: no
    -- y_i anywhere, and ξ's tail wherever y_i = Q.

    module Reduct (ζ : PathSum n k m)
                  (abs-phase : Absent y[ i ] (phase ζ))
                  (abs-out : ∀ w → Absent y[ i ] (out ζ w))
                  (kept-phase : ∀ x u → [ u i ]ᶻ ≡ q x u →
                                eval (phase ζ) x u ≡ tv x u)
                  (kept-out : ∀ x u w → [ u i ]ᶻ ≡ q x u →
                              eval (out ζ w) x u ≡
                              eval (tail-part (out ξ w)) x u)
                  where

      G : Assign n → Assign n → Assign m → Amp
      G x z y = if hits ζ x y z then zpow (eval (phase ζ) x y) else 0ᴬ

      G-off : ∀ x z y → G x z y ≐ G x z (setᵗ i y)
      G-off x z y = if-cong
        (hits-eval ζ ζ x y (setᵗ i y) z (λ w →
          eval-off (out ζ w) i (abs-out w) x y (setᵗ i y) (setᵗ-off y)))
        (λ j → cong (λ u → zpow u j)
          (eval-off (phase ζ) i abs-phase x y (setᵗ i y) (setᵗ-off y)))

      -- ξ without y₀, whose hits are hitsT.
      ξᵗ : PathSum n k m
      ξᵗ = ⟨ tail-part (phase ξ) , (λ w → tail-part (out ξ w)) ⟩

      G-kept : ∀ x z u → [ u i ]ᶻ ≡ q x u →
               G x z u ≐ (if hitsT x u z then zpow (tv x u) else 0ᴬ)
      G-kept x z u cn = if-cong
        (hits-eval ζ ξᵗ x u u z (λ w → kept-out x u w cn))
        (λ j → cong (λ v → zpow v j) (kept-phase x u cn))

      G-resp : ∀ x z → Respects (G x z)
      G-resp x z y y′ agree = if-cong
        (hits-≗³ ζ {x} {x} {y} {y′} {z} {z} (λ _ → refl) agree (λ _ → refl))
        (λ j → cong (λ v → zpow v j)
          (eval-cong (phase ζ) {x} {x} {y} {y′} (λ _ → refl) agree))

      F-kept : ∀ x z u → [ u i ]ᶻ ≡ q x u → pow M ∣ hd x u →
               F x z u ≐ (+ 2) ·ᴬ G x z u
      F-kept x z u cn d w = trans (F-double x z u d w)
        (cong (λ v → (+ 2) * v) (sym (G-kept x z u cn w)))

      -- Of y and setᵗ i y (y i = false), the one where y_i = Q doubles
      -- and the other cancels.

      pair-q0 : ∀ x z y → y i ≡ false → q x y ≡ 0ℤ →
                (F x z y +ᴬ F x z (setᵗ i y)) ≐ (G x z y +ᴬ G x z (setᵗ i y))
      pair-q0 x z y ey q0 w = trans
        (cong₂ _+_ (F-kept x z y cn (hd-whole x y false 0ℤ ey q0 i∣0) w)
                   (F-cancel x z (setᵗ i y)
                      (hd-half x (setᵗ i y) true 0ℤ (setᵗ-i y) q′0 2∤1) w))
        (trans (double (G x z y w))
               (cong (λ v → G x z y w + v) (G-off x z y w)))
        where
        cn : [ y i ]ᶻ ≡ q x y
        cn = trans (cong [_]ᶻ ey) (sym q0)

        q′0 : q x (setᵗ i y) ≡ 0ℤ
        q′0 = trans (sym (q-off x y)) q0

      pair-q1 : ∀ x z y → y i ≡ false → q x y ≡ 1ℤ →
                (F x z y +ᴬ F x z (setᵗ i y)) ≐ (G x z y +ᴬ G x z (setᵗ i y))
      pair-q1 x z y ey q1 w = trans
        (cong₂ _+_ (F-cancel x z y (hd-half x y false 1ℤ ey q1 2∤1) w)
                   (F-kept x z (setᵗ i y) cn′
                      (hd-whole x (setᵗ i y) true 1ℤ (setᵗ-i y) q′1
                                ℤDiv.∣-refl) w))
        (trans (double′ (G x z (setᵗ i y) w))
               (cong (λ v → v + G x z (setᵗ i y) w) (sym (G-off x z y w))))
        where
        q′1 : q x (setᵗ i y) ≡ 1ℤ
        q′1 = trans (sym (q-off x y)) q1

        cn′ : [ setᵗ i y i ]ᶻ ≡ q x (setᵗ i y)
        cn′ = trans (cong [_]ᶻ (setᵗ-i y)) (sym q′1)

      pair-eq′ : ∀ x z y (b : Bool) → y i ≡ b →
                 (if b then 0ᴬ else (F x z y +ᴬ F x z (setᵗ i y))) ≐
                 (if b then 0ᴬ else (G x z y +ᴬ G x z (setᵗ i y)))
      pair-eq′ x z y true  _  _ = refl
      pair-eq′ x z y false ey   = by-q (bQ x y)
        where
        by-q : IsBit (q x y) →
               (F x z y +ᴬ F x z (setᵗ i y)) ≐ (G x z y +ᴬ G x z (setᵗ i y))
        by-q (inj₁ q0) = pair-q0 x z y ey q0
        by-q (inj₂ q1) = pair-q1 x z y ey q1

      -- Split both sums at i and match them pair by pair.

      amp-hh : ∀ x z → amp ξ x z ≐ amp ζ x z
      amp-hh x z w = trans (amp-pairs x z w)
        (trans (Σᴮ-at i (F x z) (F-resp x z) w)
          (trans (Σᴮ-cong (λ y → pair-eq′ x z y (y i) refl) w)
                 (sym (Σᴮ-at i (G x z) (G-resp x z) w))))

    open Reduct (hhᴳ-reduct ξ i Q)
      (substᴾ-absent (tail-part (phase ξ)) y[ i ] Q absQ)
      (λ w → substᴾ-absent (tail-part (out ξ w)) y[ i ] Q absQ)
      (λ x u cn → eval-substᴾ-fixed (tail-part (phase ξ)) y[ i ] Q x u cn)
      (λ x u w cn → eval-substᴾ-fixed (tail-part (out ξ w)) y[ i ] Q x u cn)

  hhᴳ-sound : ξ ≋ hhᴳ-reduct ξ i Q
  hhᴳ-sound x z = scale-map k (amp-hh x z)


------------------------------------------------------------------------
-- Proposition 3.1

⟶ᴳ-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ ζ → ξ ≋ ζ
⟶ᴳ-sound (elimᴳ ξ eqP eqf) = elim-sound ξ eqP eqf
⟶ᴳ-sound (ωᴳ ξ Q bQ eqP eqf) = ωᴳ-sound ξ Q bQ eqP eqf
⟶ᴳ-sound (hhᴳ ξ i Q bQ absQ eqP eqf) = hhᴳ-sound ξ i Q bQ absQ eqP eqf
⟶ᴳ-sound (caseᴳ ξ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ eqf₀ eqf₁) =
  case-sound ξ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ eqf₀ eqf₁

⟶ᴳ*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ* ζ → ξ ≋ ζ
⟶ᴳ*-sound (εᴳ {ξ = a}) = ≋-refl {ξ = a}
⟶ᴳ*-sound (_◅ᴳ_ {ξ = a} {ζ = b} {χ = d} s ss) =
  ≋-trans {ξ = a} {ζ = b} {χ = d} (⟶ᴳ-sound s) (⟶ᴳ*-sound ss)

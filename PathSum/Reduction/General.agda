------------------------------------------------------------------------
-- Presentations of groups
--
-- The reduction rules of figure 2 in full (Amy, QPL 2018)
--
-- PathSum.Reduction formalises [Elim], [ω] and [HH] with Z₂-linear
-- quotients, the shape a second-order phase produces and all that
-- lemma 4.3 needs, and leaves out [Case].  Here are all four rules of
-- figure 2 as the paper states them, as a second relation _⟶ᴳ_:
--
--   [Elim] unchanged (it has no quotient);
--   [ω]    ¼y₀ + ½y₀Q + R  ⟶  ⅛ - ¼Q + R;
--   [HH]   ½y₀(y_i + Q) + R  ⟶  R[y_i ← Q], and f[y_i ← Q];
--   [Case] ¼y₀X + ½y₀(y₁ + Q) + R = ¼y₁(1 - X) + ½y₁(y₀ + Q′) + R′
--          ⟶  (1 - X)·R[y₁ ← Q] + X·R′[y₀ ← Q′],
--
-- with Q, Q′ and X any Boolean-valued polynomials (BoolValued: {0,1}-
-- valued at every Boolean point; see PathSum.Polynomial.Boolean for
-- why "Boolean up to parity" would not do), and y_i free of Q in [HH]
-- exactly (Absent).  The paper's "for all rules, y₀ is internal" is
-- the hypothesis on the outputs; in [Case] both y₀ and y₁ are.
--
-- The old relation is left alone rather than extended, for three
-- reasons: PathSum.Denotation proves it sound and would have to prove
-- the new rules too; lemma 4.3 and corollary 4.4 are statements about
-- it that stay true; and its chains have an exact length (every rule
-- removes one path variable) which [Case], removing two, breaks.  It
-- embeds (⟶⇒⟶ᴳ): the linear [ω] and [HH] are the general ones at the
-- lifting of a linear form, with literally the same reducts, and only
-- the premise of [HH] needs converting -- ½·liftXor c S is ½·(y_i + the
-- lifting on S ∖ y_i) modulo 1, by PathSum.Polynomial.Boolean.
--
-- Departures from the paper, all in the statement of [Case]:
--
-- * The paper's x may be any Boolean-valued X free of y₀ and y₁ (here:
--   any X in the remaining variables); its instance is X = x_a.
-- * Its two decompositions of P say, of the quarters of P in y₀ and y₁
--   (PathSum.Polynomial.Substitution.q₀₀ ...), exactly three things:
--   the y₀y₁ coefficient is ½, the y₀ coefficient is ¼X + ½Q and the
--   y₁ coefficient is ¼(1 - X) + ½Q′.  The rule takes those three.  R
--   and R′ are then determined (R = q₀₀ + y₁q₀₁, R′ = q₀₀ + y₀q₁₀), so
--   the reduct is written with them.
-- * The rule consumes two units of normalisation, as the figure shows
--   (1/√2^(m+2) to 1/√2^m): the path-sum carries its own.
-- * y_i and y_j are the first two path variables, y₀ and y₁; like the
--   other rules, [Case] acts at the head.
--
-- As every rule removes at least one path variable the relation still
-- terminates, and a chain is no longer than the number of path
-- variables it starts with (proposition 3.2's bound); the count is no
-- longer exact.  Soundness (proposition 3.1 for this calculus) is
-- PathSum.Reduction.Sound.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Reduction.General (M : ℕ) where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 1ℤ; +_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_; divides; ∣n⇒∣m*n)
open import Data.Integer.Properties using (*-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _+_; _∸_; _≤_; s≤s)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)

open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; y₀; head-part; tail-part)
open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Polynomial using
  (Poly; y[_]; _∖ᵐ_; 0ᴾ; κ; μ; _+ᴾ_; _-ᴾ_; _·ᴾ_; _≈[_]_; NoVar; liftXor)
open import PathSum.Polynomial.Product using (_*ᴾ_; ≈-trans)
open import PathSum.Polynomial.Substitution using
  (Absent; substᴾ; q₀₀; q₀₁; q₁₀; q₁₁; drop₁; substHead)
open import PathSum.Polynomial.Boolean using
  (BoolValued; BoolValued-liftXor; liftXor-split-≈; liftXor-Absent)
open import PathSum.Reduction M using
  (⅛; ¼; ½; elim-reduct; _⟶_; _⟶*_; elim; ω; hh; ε; _◅_)

import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

open +-*-Solver using (solve; con; _:-_; _:*_; _:=_)

private
  variable
    n k m k′ m′ : ℕ


------------------------------------------------------------------------
-- The reducts

-- [Elim]'s is PathSum.Reduction.elim-reduct.  [ω] discards y₀ and adds
-- ⅛ - ¼Q; [HH] substitutes Q for y_i in the rest of the phase and in
-- the outputs.

ωᴳ-reduct : PathSum n (suc k) (suc m) → Poly n m → PathSum n k m
ωᴳ-reduct ξ Q =
  ⟨ (κ ⅛ -ᴾ (¼ ·ᴾ Q)) +ᴾ tail-part (phase ξ)
  , (λ w → tail-part (out ξ w)) ⟩

hhᴳ-reduct : PathSum n k (suc m) → Fin m → Poly n m → PathSum n k m
hhᴳ-reduct ξ i Q =
  ⟨ substᴾ (tail-part (phase ξ)) y[ i ] Q
  , (λ w → substᴾ (tail-part (out ξ w)) y[ i ] Q) ⟩

-- [Case] discards y₀ and y₁.  With y₀ gone, the phase is R, a
-- polynomial whose head variable is y₁; with y₁ gone it is R′, whose
-- head variable is y₀ (drop₁).  Substituting at the head of each gives
-- R[y₁ ← Q] and R′[y₀ ← Q′].  The outputs mention neither variable.

case-reduct : PathSum n (suc (suc k)) (suc (suc m)) →
              (X Q Q′ : Poly n m) → PathSum n k m
case-reduct ξ X Q Q′ =
  ⟨ ((κ 1ℤ -ᴾ X) *ᴾ substHead (tail-part (phase ξ)) Q) +ᴾ
    (X *ᴾ substHead (drop₁ (phase ξ)) Q′)
  , (λ w → q₀₀ (out ξ w)) ⟩


------------------------------------------------------------------------
-- The relation

infix 4 _⟶ᴳ_ _⟶ᴳ*_

data _⟶ᴳ_ {n : ℕ} : ∀ {k m k′ m′} →
                    PathSum n k m → PathSum n k′ m′ → Set where

  elimᴳ : ∀ {k m} (ξ : PathSum n (suc (suc k)) (suc m)) →
          head-part (phase ξ) ≈[ pow M ] 0ᴾ →
          (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
          ξ ⟶ᴳ elim-reduct ξ

  ωᴳ    : ∀ {k m} (ξ : PathSum n (suc k) (suc m)) (Q : Poly n m) →
          BoolValued Q →
          head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q)) →
          (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
          ξ ⟶ᴳ ωᴳ-reduct ξ Q

  hhᴳ   : ∀ {k m} (ξ : PathSum n k (suc m)) (i : Fin m) (Q : Poly n m) →
          BoolValued Q → Absent y[ i ] Q →
          head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)) →
          (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
          ξ ⟶ᴳ hhᴳ-reduct ξ i Q

  -- The paper's two decompositions of the phase, read off its
  -- quarters in y₀ and y₁.
  caseᴳ : ∀ {k m} (ξ : PathSum n (suc (suc k)) (suc (suc m)))
          (X Q Q′ : Poly n m) →
          BoolValued X → BoolValued Q → BoolValued Q′ →
          q₁₁ (phase ξ) ≈[ pow M ] κ ½ →
          q₁₀ (phase ξ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) →
          q₀₁ (phase ξ) ≈[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) →
          (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
          (∀ w → NoVar (+ 2) y[ suc zero ] (out ξ w)) →
          ξ ⟶ᴳ case-reduct ξ X Q Q′

data _⟶ᴳ*_ {n : ℕ} : ∀ {k m k′ m′} →
                     PathSum n k m → PathSum n k′ m′ → Set where
  εᴳ   : ∀ {k m} {ξ : PathSum n k m} → ξ ⟶ᴳ* ξ
  _◅ᴳ_ : ∀ {k m k′ m′ k″ m″} {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
         {χ : PathSum n k″ m″} → ξ ⟶ᴳ ζ → ζ ⟶ᴳ* χ → ξ ⟶ᴳ* χ

infixr 5 _◅ᴳ_


------------------------------------------------------------------------
-- The linear rules are instances

-- Half of an even number is a multiple of 2^M: ½ · 2 = 2^M when M > 0,
-- and every integer is a multiple of 2^0.

private
  pow∣½·2 : pow M ∣ (½ * (+ 2))
  pow∣½·2 = aux M
    where
    aux : ∀ e → pow e ∣ (pow (e ∸ 1) * (+ 2))
    aux zero    = divides (pow 0 * (+ 2)) (sym (*-identityʳ (pow 0 * (+ 2))))
    aux (suc e) =
      divides 1ℤ (trans (sym (pow-suc e)) (sym (*-identityˡ′ (pow (suc e)))))
      where
      *-identityˡ′ : ∀ z → 1ℤ * z ≡ z
      *-identityˡ′ = solve 1 (λ z → con 1ℤ :* z := z) refl

  shape : ∀ h p q r → p - q ≡ r * (+ 2) →
          (h * p) - (h * q) ≡ r * (h * (+ 2))
  shape h p q r eq = trans (distrib h p q)
    (trans (cong (λ u → h * u) eq) (swap h r))
    where
    distrib : ∀ h p q → (h * p) - (h * q) ≡ h * (p - q)
    distrib = solve 3 (λ h p q → (h :* p) :- (h :* q) := h :* (p :- q)) refl

    swap : ∀ h r → h * (r * (+ 2)) ≡ r * (h * (+ 2))
    swap = solve 2 (λ h r → h :* (r :* con (+ 2)) := r :* (h :* con (+ 2)))
                   refl

-- A congruence modulo 2 becomes one modulo 2^M after halving.

½·-≈ : {P Q : Poly n m} → P ≈[ + 2 ] Q → (½ ·ᴾ P) ≈[ pow M ] (½ ·ᴾ Q)
½·-≈ {P = P} {Q} P≈Q γ with P≈Q γ
... | divides r eq = Eq.subst (pow M ∣_) (sym (shape ½ (P γ) (Q γ) r eq))
                       (∣n⇒∣m*n r pow∣½·2)

-- The reducts of the linear [ω] and [HH] are, definitionally, the
-- general reducts at the lifting of the linear form, so only [HH]'s
-- premise needs work: y_i ∈ S is split off as ½(y_i + the rest).

⟶⇒⟶ᴳ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ ζ → ξ ⟶ᴳ ζ
⟶⇒⟶ᴳ (elim ξ eqP eqf) = elimᴳ ξ eqP eqf
⟶⇒⟶ᴳ (ω ξ c S eqP eqf) =
  ωᴳ ξ (liftXor c S) (BoolValued-liftXor c S) eqP eqf
⟶⇒⟶ᴳ (hh ξ i c S i∈S eqP eqf) =
  hhᴳ ξ i (liftXor c (S ∖ᵐ y[ i ]))
      (BoolValued-liftXor c (S ∖ᵐ y[ i ]))
      (liftXor-Absent c S y[ i ])
      (≈-trans {c = pow M} {P = head-part (phase ξ)}
               {Q = ½ ·ᴾ liftXor c S}
               {R = ½ ·ᴾ (μ y[ i ] +ᴾ liftXor c (S ∖ᵐ y[ i ]))}
               eqP
               (½·-≈ {P = liftXor c S}
                     {Q = μ y[ i ] +ᴾ liftXor c (S ∖ᵐ y[ i ])}
                     (liftXor-split-≈ c S y[ i ] i∈S)))
      eqf

⟶*⇒⟶ᴳ* : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶* ζ → ξ ⟶ᴳ* ζ
⟶*⇒⟶ᴳ* ε          = εᴳ
⟶*⇒⟶ᴳ* (s ◅ steps) = ⟶⇒⟶ᴳ s ◅ᴳ ⟶*⇒⟶ᴳ* steps


------------------------------------------------------------------------
-- Proposition 3.2: termination

-- Every rule removes at least one path variable ([Case] removes two),
-- so the number of path variables bounds the length of every chain.
-- (The bound is proved through the single step: matching a step inside
-- a chain makes the unifier normalise the reduct, which costs seconds
-- and gigabytes; matching it alone does not.)

⟶ᴳ-dec : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ ζ → suc m′ ≤ m
⟶ᴳ-dec (elimᴳ _ _ _)                   = ℕ.≤-refl
⟶ᴳ-dec (ωᴳ _ _ _ _ _)                  = ℕ.≤-refl
⟶ᴳ-dec (hhᴳ _ _ _ _ _ _ _)             = ℕ.≤-refl
⟶ᴳ-dec (caseᴳ _ _ _ _ _ _ _ _ _ _ _ _) = ℕ.n≤1+n _

lenᴳ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴳ* ζ → ℕ
lenᴳ εᴳ            = 0
lenᴳ (_ ◅ᴳ steps) = suc (lenᴳ steps)

⟶ᴳ*-length : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
             (steps : ξ ⟶ᴳ* ζ) → lenᴳ steps + m′ ≤ m
⟶ᴳ*-length εᴳ        = ℕ.≤-refl
⟶ᴳ*-length (s ◅ᴳ ss) = ℕ.≤-trans (s≤s (⟶ᴳ*-length ss)) (⟶ᴳ-dec s)

⟶ᴳ*-bounded : {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
              (steps : ξ ⟶ᴳ* ζ) → lenᴳ steps ≤ m
⟶ᴳ*-bounded steps =
  ℕ.≤-trans (ℕ.m≤m+n (lenᴳ steps) _) (⟶ᴳ*-length steps)

------------------------------------------------------------------------
-- Presentations of groups
--
-- A step of figure 2 with a quotient that is not linear raises the
-- order of the phase (for Amy, QPL 2018, lemma 2.13 and proposition
-- 3.2)
--
-- PathSum.Cost.Normalise proves the time bound of proposition 3.2 for
-- the rules with Z₂-linear quotients.  It leaves out [Case] and the
-- rules whose quotient is Boolean-valued but not linear, and its header
-- says why: every polynomial bound there rests on the order of the
-- phase staying at most d, and lemma 2.13 guarantees that only for
-- linear substitutions.  This module makes the reason concrete, at
-- precision M = 3.
--
-- The path-sum ξᴱ has inputs x₀, x₁, path variables y₀, y₁ and phase
--
--    ½ y₀y₁ + ½ y₀x₀x₁ + ⅛ y₁ ,
--
-- of order 3 (order-before).  Its quotient by y₀ is ½(y₁ + x₀x₁), so
-- figure 2's [HH] (PathSum.Reduction.General.hhᴳ) applies with the
-- Boolean-valued quotient x₀x₁ and substitutes it for y₁ (hh-step;
-- also a step of PathSum.Full's _⟶ᶠ_, full-step).  The reduct's phase
-- is ⅛ x₀x₁: its coefficient at x₀x₁ is the numerator 1
-- (reduct-at), and its order is 3 + 2 - 1 = 4, so it does not have
-- order 3 (order-after).  The same polynomials do the same at every
-- M ≥ 3 (stated here, proved at M = 3 only).  ξᴱ is not the path-sum
-- of a circuit (its normalisation is 0); that suffices, the time
-- theorem quantifying over every path-sum of order at most d.
--
-- So the order bound, and with it the bound on the degree and on the
-- number of terms that the cost model's bounds rest on, is not an
-- invariant of figure 2.  At order 2 this cannot happen: for Clifford
-- path-sums with internal path variables every rule of figure 2 keeps
-- the order at 2 (PathSum.Full.Clifford).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Cost.Excluded where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (inside; outside; ⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_; ∣⇒∣ᵤ)
open import Data.Integer.Properties using () renaming (_≟_ to _≟ℤ_)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary.Decidable using (toWitness; _→?_)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Anywhere 3 using (plain)
open import PathSum.Anywhere.Match 3 using (allMon?; _≈?[_]_; NoVar?)
open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; head-part; tail-part; y₀)
open import PathSum.Full 3 using (_⟶ᶠ_)
open import PathSum.Order 3 using (Ord≤; pow; val)
open import PathSum.Polynomial using
  (Mon; Poly; x[_]; y[_]; ∥_∥; _∈ᵐ?_; μ; _+ᴾ_; _·ᴾ_; _≈[_]_; NoVar)
open import PathSum.Polynomial.Boolean using (BoolValued-monoᴾ)
open import PathSum.Polynomial.Product using (monoᴾ)
open import PathSum.Polynomial.Substitution using (Absent; substᴾ)
open import PathSum.Reduction 3 using (⅛; ½)
open import PathSum.Reduction.General 3 using (_⟶ᴳ_; hhᴳ; hhᴳ-reduct)


------------------------------------------------------------------------
-- The path-sum

-- The monomials y₀y₁, y₀x₀x₁ and y₁.

y₀y₁ᵐ x₀x₁y₀ᵐ y₁ᵐ : Mon 2 2
y₀y₁ᵐ   = ⊥ , inside ∷ inside ∷ []
x₀x₁y₀ᵐ = inside ∷ inside ∷ [] , inside ∷ outside ∷ []
y₁ᵐ     = ⊥ , outside ∷ inside ∷ []

-- The phase ½ y₀y₁ + ½ y₀x₀x₁ + ⅛ y₁, and the identity outputs.

phaseᴱ : Poly 2 2
phaseᴱ = ((½ ·ᴾ monoᴾ y₀y₁ᵐ) +ᴾ (½ ·ᴾ monoᴾ x₀x₁y₀ᵐ)) +ᴾ (⅛ ·ᴾ monoᴾ y₁ᵐ)

ξᴱ : PathSum 2 0 2
ξᴱ = ⟨ phaseᴱ , (λ w → μ x[ w ]) ⟩

-- The quotient x₀x₁, over the variables left once y₀ is gone (y₁ is
-- then y[ zero ]).

x₀x₁ᵐ : Mon 2 1
x₀x₁ᵐ = inside ∷ inside ∷ [] , outside ∷ []

Qᴱ : Poly 2 1
Qᴱ = monoᴾ x₀x₁ᵐ


------------------------------------------------------------------------
-- The step

-- The premises of [HH] at y₀, each decided coefficient by coefficient.

Q-absent : Absent y[ zero ] Qᴱ
Q-absent = toWitness
  {a? = allMon? (λ γ → (y[ zero ] ∈ᵐ? γ) →? (Qᴱ γ ≟ℤ 0ℤ))} _

quotient : head-part phaseᴱ ≈[ pow 3 ] (½ ·ᴾ (μ y[ zero ] +ᴾ Qᴱ))
quotient = toWitness
  {a? = head-part phaseᴱ ≈?[ pow 3 ] (½ ·ᴾ (μ y[ zero ] +ᴾ Qᴱ))} _

outputs : ∀ w → NoVar (+ 2) y₀ (out ξᴱ w)
outputs zero       = toWitness {a? = NoVar? (+ 2) y₀ (out ξᴱ zero)} _
outputs (suc zero) = toWitness {a? = NoVar? (+ 2) y₀ (out ξᴱ (suc zero))} _

-- [HH] with the quotient x₀x₁, substituting it for y₁.

hh-step : ξᴱ ⟶ᴳ hhᴳ-reduct ξᴱ zero Qᴱ
hh-step = hhᴳ ξᴱ zero Qᴱ (BoolValued-monoᴾ x₀x₁ᵐ) Q-absent quotient outputs

full-step : ξᴱ ⟶ᶠ hhᴳ-reduct ξᴱ zero Qᴱ
full-step = plain (plain hh-step)


------------------------------------------------------------------------
-- The orders

-- Before: order 3.

order-before : Ord≤ 3 (phase ξᴱ)
order-before = toWitness
  {a? = allMon? (λ γ → pow (val 3 ∥ γ ∥) ∣? phaseᴱ γ)} _

-- After: the coefficient ⅛ at x₀x₁, of degree 2, is not a multiple of
-- 2^(3 - (4 - 2)) = 2, so the order is not 3.

reduct-at : phase (hhᴳ-reduct ξᴱ zero Qᴱ) x₀x₁ᵐ ≡ 1ℤ
reduct-at = refl

order-after : ¬ Ord≤ 3 (phase (hhᴳ-reduct ξᴱ zero Qᴱ))
order-after ord with ∣1⇒≡1 (∣⇒∣ᵤ (subst (pow 1 ∣_) reduct-at (ord x₀x₁ᵐ)))
... | ()

-- Together: a step of figure 2 from a phase of order 3 to one that is
-- not.

order-rises : Σ (PathSum 2 0 1) λ ζ →
              (ξᴱ ⟶ᶠ ζ) × Ord≤ 3 (phase ξᴱ) × ¬ Ord≤ 3 (phase ζ)
order-rises = hhᴳ-reduct ξᴱ zero Qᴱ , full-step , order-before , order-after

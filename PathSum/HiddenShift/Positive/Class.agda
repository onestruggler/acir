------------------------------------------------------------------------
-- Presentations of groups
--
-- Output-safe, Clifford-safe reductions: a class of strategies
--
-- A step of figure 2 (Amy, QPL 2018; PathSum.Full's _⟶ᶠ_) belongs to
-- the class when it does not do either of two things to the path
-- variables -- an [HH] that does may be followed by a stuck path-sum
-- (PathSum.HiddenShift.Stuck):
--
-- * output safety: no internal path variable may enter an output.  An
--   [HH] substitutes its quotient Q for y_i in the phase and in the
--   outputs; if y_i occurs in an output, Q must mention only path
--   variables that occur in outputs too (OutSafe).  Equivalently: if Q
--   mentions an internal variable, y_i is internal.
-- * Clifford safety: an internal path variable that occurs in the
--   phase only quadratically stays so.  "Quadratically" is read off
--   the quotient of the phase by the variable, which must be linear
--   modulo 1 (Clifᶜ: every coefficient of a monomial of degree at least
--   two vanishes modulo 1) -- for a phase of order 2 this holds of every
--   variable, so on Clifford path-sums the condition is vacuous.  An
--   [HH] must keep every internal such variable of its path-sum such
--   in its reduct (CliffSafe).
--
-- Nothing else is restricted: every [Elim], [ω] and [Case] step of
-- _⟶ᶠ_ is admissible, in each of _⟶ᶠ_'s shapes (at the head, after one
-- renumbering, after two), and an [HH] is admissible in each shape
-- exactly when the head rule it applies is output-safe and
-- Clifford-safe on the renumbered path-sum (Admᶠ).
--
-- Everything is decidable (Admᶠ?).  Chains of admissible steps are
-- _⟶ᴷ*_; a path-sum is maximal when no admissible step applies to it.
-- What is proved about the class, and what is not, is in
-- PathSum.HiddenShift.Positive's header (its "What is not proved").
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.Class (M₀ : ℕ) where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (+_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Nat.Base using (zero; suc; _≤_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Nullary.Decidable using (Dec; yes; no; _×?_; _→?_; ¬?)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Polynomial using (Poly; y[_]; ∥_∥; NoVar)
open import PathSum.Polynomial.Decidable using (NoVar?; Absent?; all-monomials?)
open import PathSum.Polynomial.Substitution using (Absent)
open import PathSum.Reorder using (_/ʸ_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (Anywhere; plain; at)
open import PathSum.Full M using (_⟶ᶠ_; _⟶ᶠ*_; εᶠ; _◅ᶠ_)
open import PathSum.Order M using (pow)
open import PathSum.Reduction.General M using
  (_⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ; hhᴳ-reduct)

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Internal and Clifford path variables

-- y_v occurs in no output, modulo 2.

Int : PathSum n k m → Fin m → Set
Int {n = n} ξ v = ∀ (w : Fin n) → NoVar (+ 2) y[ v ] (out ξ w)

-- The quotient of P by y_v is linear modulo 1: y_v occurs only in
-- monomials of degree at most two.

Clifᶜ : Poly n m → Fin m → Set
Clifᶜ {m = suc m} P v = ∀ γ → 2 ≤ ∥ γ ∥ → pow M ∣ (P /ʸ v) γ


------------------------------------------------------------------------
-- The class

-- For an [HH] on χ substituting Q for its variable y_(suc i) (i in the
-- numbering without the head y₀): if Q mentions an internal variable,
-- y_(suc i) is internal ...

OutSafe : PathSum n k (suc m) → Fin m → Poly n m → Set
OutSafe χ i Q = ∀ v → Int χ (suc v) → ¬ Absent y[ v ] Q → Int χ (suc i)

-- ... and every internal variable of χ whose quotient is linear has a
-- linear quotient in the reduct.

CliffSafe : PathSum n k (suc m) → Fin m → Poly n m → Set
CliffSafe χ i Q = ∀ v → Int χ (suc v) → Clifᶜ (phase χ) (suc v) →
                  Clifᶜ (phase (hhᴳ-reduct χ i Q)) v

-- Admissible head steps: [HH] both safe, the others always.

Adm : {χ : PathSum n k m} {ζ : PathSum n k′ m′} → χ ⟶ᴳ ζ → Set
Adm (elimᴳ _ _ _)                   = ⊤
Adm (ωᴳ _ _ _ _ _)                  = ⊤
Adm (hhᴳ χ i Q _ _ _ _)             = OutSafe χ i Q × CliffSafe χ i Q
Adm (caseᴳ _ _ _ _ _ _ _ _ _ _ _ _) = ⊤

-- A step of figure 2, in any of its shapes, is admissible when its
-- head step is.

Admᶠ : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᶠ ζ → Set
Admᶠ (plain (plain s)) = Adm s
Admᶠ (plain (at j s))  = Adm s
Admᶠ (at j (plain s))  = Adm s
Admᶠ (at j (at j′ s))  = Adm s

-- Chains of admissible steps, and the path-sums no admissible step
-- leaves.

infixr 5 _◅ᴷ_

data _⟶ᴷ*_ {n : ℕ} : ∀ {k m k′ m′} →
                     PathSum n k m → PathSum n k′ m′ → Set where
  εᴷ   : ∀ {k m} {ξ : PathSum n k m} → ξ ⟶ᴷ* ξ
  _◅ᴷ_ : ∀ {k m k′ m′ k″ m″} {ξ : PathSum n k m} {ζ : PathSum n k′ m′}
           {χ : PathSum n k″ m″} →
         Σ (ξ ⟶ᶠ ζ) Admᶠ → ζ ⟶ᴷ* χ → ξ ⟶ᴷ* χ

Maximal : PathSum n k m → Set
Maximal {n} ξ = ∀ {k′ m′} {ζ : PathSum n k′ m′} (s : ξ ⟶ᶠ ζ) → ¬ Admᶠ s

-- An admissible chain is a chain of figure 2.

forget : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᴷ* ζ → ξ ⟶ᶠ* ζ
forget εᴷ              = εᶠ
forget ((s , _) ◅ᴷ ss) = s ◅ᶠ forget ss


------------------------------------------------------------------------
-- Decidability

Int? : (ξ : PathSum n k m) (v : Fin m) → Dec (Int ξ v)
Int? ξ v = all? (λ w → NoVar? (+ 2) y[ v ] (out ξ w))

Clifᶜ? : (P : Poly n m) (v : Fin m) → Dec (Clifᶜ P v)
Clifᶜ? {m = suc m} P v =
  all-monomials? (λ γ → (2 ≤? ∥ γ ∥) →? (pow M ∣? (P /ʸ v) γ))

OutSafe? : (χ : PathSum n k (suc m)) (i : Fin m) (Q : Poly n m) →
           Dec (OutSafe χ i Q)
OutSafe? χ i Q = all? (λ v →
  Int? χ (suc v) →? (¬? (Absent? y[ v ] Q) →? Int? χ (suc i)))

CliffSafe? : (χ : PathSum n k (suc m)) (i : Fin m) (Q : Poly n m) →
             Dec (CliffSafe χ i Q)
CliffSafe? χ i Q = all? (λ v →
  Int? χ (suc v) →? (Clifᶜ? (phase χ) (suc v) →?
                        Clifᶜ? (phase (hhᴳ-reduct χ i Q)) v))

Adm? : {χ : PathSum n k m} {ζ : PathSum n k′ m′} (s : χ ⟶ᴳ ζ) → Dec (Adm s)
Adm? (elimᴳ _ _ _)                   = yes tt
Adm? (ωᴳ _ _ _ _ _)                  = yes tt
Adm? (hhᴳ χ i Q _ _ _ _)             = OutSafe? χ i Q ×? CliffSafe? χ i Q
Adm? (caseᴳ _ _ _ _ _ _ _ _ _ _ _ _) = yes tt

Admᶠ? : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} (s : ξ ⟶ᶠ ζ) →
        Dec (Admᶠ s)
Admᶠ? (plain (plain s)) = Adm? s
Admᶠ? (plain (at j s))  = Adm? s
Admᶠ? (at j (plain s))  = Adm? s
Admᶠ? (at j (at j′ s))  = Adm? s

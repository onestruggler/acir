------------------------------------------------------------------------
-- Presentations of groups
--
-- The premises of the reduction rules, decided, and rules that
-- discharge them by computation
--
-- Every premise of [Elim], [ω] and [HH] (PathSum.Reduction, figure 2
-- of Amy's paper) holds coefficient by coefficient: the quotient of
-- the phase by y₀ is congruent to 0, to ¼ + ½(c ⊕ ⨁F) or to
-- ½(c ⊕ ⨁F) modulo 2^M, the variable y_i to be substituted occurs in
-- F, and y₀ occurs in no output modulo 2.  Given the quotient -- the
-- constant c and the set F the paper writes down at each step -- they
-- are therefore decidable (elim?, ω?, hh?), and for a closed path-sum
-- the decision computes.  The rules elim!, ω! and hh! take the
-- premises as an implicit True argument, so a reduction chain is
-- written with the paper's data and nothing else; if a premise fails,
-- the implicit argument has type ⊥ and the chain is rejected.  elimAt!,
-- ωAt! and hhAt! are the same at any path variable y_j
-- (PathSum.Anywhere): the premises are decided on front j ξ, whose
-- head is y_j.  Definition 2.11's order bound is decided too (Ord≤?).
--
-- The rules and their reducts are PathSum.Reduction's, unchanged; the
-- premise that y₀ occurs in no output is PathSum.Anywhere.Match's
-- Internal₀, decided by its Internal₀?.  Nothing here finds the
-- quotient: matching a rule is PathSum.Anywhere.Match's business, and
-- this module is for checking a chain someone has written down, in
-- the time it takes to evaluate its premises on every monomial.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Reduction.Decidable (M : ℕ) where

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Divisibility.Signed using (_∣?_)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Relation.Nullary.Decidable using
  (Dec; True; toWitness; _×?_)

open import PathSum.Base
open import PathSum.Order M using (pow; val; Ord≤)
open import PathSum.Polynomial
open import PathSum.Polynomial.Decidable
open import PathSum.Reduction M using
  (_⟶_; elim; ω; hh; elim-reduct; ω-reduct; hh-reduct; ¼; ½)
open import PathSum.Reorder using (front)
open import PathSum.Anywhere M using (_⟶ᵍ_; at)
open import PathSum.Anywhere.Match M public using
  (Internal₀; Internal₀?)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Definition 2.11, decided

Ord≤? : (d : ℕ) (P : Poly n m) → Dec (Ord≤ d P)
Ord≤? d P = all-monomials? (λ γ → pow (val d ∥ γ ∥) ∣? P γ)


------------------------------------------------------------------------
-- The premises of the head rules

-- [Elim]: y₀ does not occur in the phase.

elim? : (ξ : PathSum n k (suc m)) →
        Dec (head-part (phase ξ) ≈[ pow M ] 0ᴾ × Internal₀ ξ)
elim? ξ = (head-part (phase ξ) ≈?[ pow M ] 0ᴾ) ×? Internal₀? ξ

-- [ω]: the quotient is ¼ + ½(c ⊕ ⨁F).

ω? : (ξ : PathSum n k (suc m)) (c : Bool) (F : Mon n m) →
     Dec (head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c F)) ×
          Internal₀ ξ)
ω? ξ c F =
  (head-part (phase ξ) ≈?[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ liftXor c F))) ×?
  Internal₀? ξ

-- [HH]: the quotient is ½(c ⊕ ⨁F), and y_i, the variable that is
-- solved for, occurs in F.

hh? : (ξ : PathSum n k (suc m)) (i : Fin m) (c : Bool) (F : Mon n m) →
      Dec (y[ i ] ∈ᵐ F ×
           head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c F) ×
           Internal₀ ξ)
hh? ξ i c F =
  (y[ i ] ∈ᵐ? F) ×?
  (head-part (phase ξ) ≈?[ pow M ] (½ ·ᴾ liftXor c F)) ×?
  Internal₀? ξ


------------------------------------------------------------------------
-- The head rules, premises discharged by computation

elim! : (ξ : PathSum n (suc (suc k)) (suc m)) →
        {True (elim? ξ)} → ξ ⟶ elim-reduct ξ
elim! ξ {t} = elim ξ (proj₁ w) (proj₂ w)
  where
  w = toWitness {a? = elim? ξ} t

ω! : (ξ : PathSum n (suc k) (suc m)) (c : Bool) (F : Mon n m) →
     {True (ω? ξ c F)} → ξ ⟶ ω-reduct ξ c F
ω! ξ c F {t} = ω ξ c F (proj₁ w) (proj₂ w)
  where
  w = toWitness {a? = ω? ξ c F} t

hh! : (ξ : PathSum n k (suc m)) (i : Fin m) (c : Bool) (F : Mon n m) →
      {True (hh? ξ i c F)} → ξ ⟶ hh-reduct ξ i c F
hh! ξ i c F {t} =
  hh ξ i c F (proj₁ w) (proj₁ (proj₂ w)) (proj₂ (proj₂ w))
  where
  w = toWitness {a? = hh? ξ i c F} t


------------------------------------------------------------------------
-- The rules at any path variable

-- A rule at y_j is the head rule on front j ξ, which lists y_j first
-- and the other variables in their original order; F and i are given
-- in that order with y_j removed, which is the reduct's numbering.

elimAt! : (ξ : PathSum n (suc (suc k)) (suc m)) (j : Fin (suc m)) →
          {True (elim? (front j ξ))} → ξ ⟶ᵍ elim-reduct (front j ξ)
elimAt! ξ j {t} = at j (elim! (front j ξ) {t})

ωAt! : (ξ : PathSum n (suc k) (suc m)) (j : Fin (suc m)) (c : Bool)
       (F : Mon n m) →
       {True (ω? (front j ξ) c F)} → ξ ⟶ᵍ ω-reduct (front j ξ) c F
ωAt! ξ j c F {t} = at j (ω! (front j ξ) c F {t})

hhAt! : (ξ : PathSum n k (suc m)) (j : Fin (suc m)) (i : Fin m)
        (c : Bool) (F : Mon n m) →
        {True (hh? (front j ξ) i c F)} →
        ξ ⟶ᵍ hh-reduct (front j ξ) i c F
hhAt! ξ j i c F {t} = at j (hh! (front j ξ) i c F {t})

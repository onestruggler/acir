------------------------------------------------------------------------
-- Presentations of groups
--
-- The premises of all four rules of figure 2, decided, and rules that
-- discharge them by computation
--
-- PathSum.Reduction.General states figure 2 of Amy's paper in full:
-- [Elim], and [ω], [HH] and [Case] with Boolean-valued quotients.
-- Given the quotients -- the polynomials the paper writes down at each
-- step -- every premise is decidable:
--
--  * that a quotient is Boolean-valued, by evaluating it at every
--    point (PathSum.Polynomial.Decidable.BoolValued?);
--  * that the substituted variable y_i does not occur in [HH]'s
--    quotient, coefficient by coefficient (Absent?);
--  * that the phase has the rule's shape in y₀ (and, for [Case], in
--    y₁), a congruence modulo 2^M coefficient by coefficient;
--  * that y₀ (and, for [Case], y₁) occurs in no output modulo 2
--    (Internal₀, Internal₁).
--
-- elimᴳ?, ωᴳ?, hhᴳ? and caseᴳ? decide them, and elimᴳ!, ωᴳ!, hhᴳ! and
-- caseᴳ! take them as an implicit True argument, so a chain of general
-- rules is written with the paper's quotients and nothing else; a
-- failing premise leaves an argument of type ⊥, and the chain is
-- rejected.  The rules act at the head (y₀, and y₁ for [Case]), as
-- PathSum.Reduction.General states them; the worked examples list
-- their path variables in the paper's order, which is the order the
-- paper eliminates them in, so no reordering is needed here, and the
-- general rules at an arbitrary path variable (the counterpart of
-- PathSum.Anywhere for the linear ones) are not provided.
--
-- Nothing here finds the quotient, and nothing is efficient: a premise
-- is checked by evaluating polynomials on every monomial or at every
-- point, which for a closed path-sum on n inputs and m path variables
-- is some multiple of 2^(n+m) (4^(n+m) for a value check) integer
-- operations, each coefficient of a reduct costing what its definition
-- costs to unfold.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Reduction.General.Decidable (M : ℕ) where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (1ℤ; +_)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Relation.Nullary.Decidable using
  (Dec; True; toWitness; _×?_)

open import PathSum.Base
open import PathSum.Order M using (pow)
open import PathSum.Polynomial
open import PathSum.Polynomial.Decidable using
  (_≈?[_]_; NoVar?; Absent?; BoolValued?)
open import PathSum.Polynomial.Boolean using (BoolValued)
open import PathSum.Polynomial.Substitution using
  (Absent; q₀₁; q₁₀; q₁₁)
open import PathSum.Reduction M using (elim-reduct; ¼; ½)
open import PathSum.Reduction.General M using
  (ωᴳ-reduct; hhᴳ-reduct; case-reduct; _⟶ᴳ_; elimᴳ; ωᴳ; hhᴳ; caseᴳ)
open import PathSum.Reduction.Decidable M public using
  (Internal₀; Internal₀?; elim?)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- The premises

-- [Elim] has the premises of PathSum.Reduction's (elim?, re-exported).

-- [ω]: the coefficient of y₀ is ¼ + ½Q, with Q Boolean-valued.

ωᴳ? : (ξ : PathSum n k (suc m)) (Q : Poly n m) →
      Dec (BoolValued Q ×
           head-part (phase ξ) ≈[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q)) ×
           Internal₀ ξ)
ωᴳ? ξ Q =
  BoolValued? Q ×?
  (head-part (phase ξ) ≈?[ pow M ] (κ ¼ +ᴾ (½ ·ᴾ Q))) ×?
  Internal₀? ξ

-- [HH]: the coefficient of y₀ is ½(y_i + Q), with Q Boolean-valued and
-- free of y_i.

hhᴳ? : (ξ : PathSum n k (suc m)) (i : Fin m) (Q : Poly n m) →
       Dec (Absent y[ i ] Q × BoolValued Q ×
            head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q)) ×
            Internal₀ ξ)
hhᴳ? ξ i Q =
  Absent? y[ i ] Q ×? BoolValued? Q ×?
  (head-part (phase ξ) ≈?[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))) ×?
  Internal₀? ξ

-- [Case]: the quarters of the phase in y₀ and y₁ have the rule's
-- shape, and neither variable occurs in an output.

Internal₁ : PathSum n k (suc (suc m)) → Set
Internal₁ {n} ξ = ∀ (w : Fin n) → NoVar (+ 2) y[ suc zero ] (out ξ w)

Internal₁? : (ξ : PathSum n k (suc (suc m))) → Dec (Internal₁ ξ)
Internal₁? ξ = all? (λ w → NoVar? (+ 2) y[ suc zero ] (out ξ w))

caseᴳ? : (ξ : PathSum n k (suc (suc m))) (X Q Q′ : Poly n m) →
         Dec (BoolValued X × BoolValued Q × BoolValued Q′ ×
              q₁₁ (phase ξ) ≈[ pow M ] κ ½ ×
              q₁₀ (phase ξ) ≈[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q)) ×
              q₀₁ (phase ξ) ≈[ pow M ]
                ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′)) ×
              Internal₀ ξ × Internal₁ ξ)
caseᴳ? ξ X Q Q′ =
  BoolValued? X ×? BoolValued? Q ×? BoolValued? Q′ ×?
  (q₁₁ (phase ξ) ≈?[ pow M ] κ ½) ×?
  (q₁₀ (phase ξ) ≈?[ pow M ] ((¼ ·ᴾ X) +ᴾ (½ ·ᴾ Q))) ×?
  (q₀₁ (phase ξ) ≈?[ pow M ] ((¼ ·ᴾ (κ 1ℤ -ᴾ X)) +ᴾ (½ ·ᴾ Q′))) ×?
  Internal₀? ξ ×? Internal₁? ξ


------------------------------------------------------------------------
-- The rules, premises discharged by computation

elimᴳ! : (ξ : PathSum n (suc (suc k)) (suc m)) →
         {True (elim? ξ)} → ξ ⟶ᴳ elim-reduct ξ
elimᴳ! ξ {t} = elimᴳ ξ (proj₁ w) (proj₂ w)
  where
  w = toWitness {a? = elim? ξ} t

ωᴳ! : (ξ : PathSum n (suc k) (suc m)) (Q : Poly n m) →
      {True (ωᴳ? ξ Q)} → ξ ⟶ᴳ ωᴳ-reduct ξ Q
ωᴳ! ξ Q {t} = ωᴳ ξ Q (proj₁ w) (proj₁ (proj₂ w)) (proj₂ (proj₂ w))
  where
  w = toWitness {a? = ωᴳ? ξ Q} t

hhᴳ! : (ξ : PathSum n k (suc m)) (i : Fin m) (Q : Poly n m) →
       {True (hhᴳ? ξ i Q)} → ξ ⟶ᴳ hhᴳ-reduct ξ i Q
hhᴳ! ξ i Q {t} =
  hhᴳ ξ i Q (proj₁ (proj₂ w)) (proj₁ w) (proj₁ (proj₂ (proj₂ w)))
      (proj₂ (proj₂ (proj₂ w)))
  where
  w = toWitness {a? = hhᴳ? ξ i Q} t

caseᴳ! : (ξ : PathSum n (suc (suc k)) (suc (suc m))) (X Q Q′ : Poly n m) →
         {True (caseᴳ? ξ X Q Q′)} → ξ ⟶ᴳ case-reduct ξ X Q Q′
caseᴳ! ξ X Q Q′ {t} =
  caseᴳ ξ X Q Q′ bX bQ bQ′ e₁₁ e₁₀ e₀₁ o₀ o₁
  where
  w = toWitness {a? = caseᴳ? ξ X Q Q′} t
  bX  = proj₁ w
  bQ  = proj₁ (proj₂ w)
  bQ′ = proj₁ (proj₂ (proj₂ w))
  e₁₁ = proj₁ (proj₂ (proj₂ (proj₂ w)))
  e₁₀ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
  e₀₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w)))))
  o₀  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))))
  o₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))))

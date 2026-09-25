------------------------------------------------------------------------
-- Presentations of groups
--
-- Moving a pair of path variables to the front
--
-- The rule [Case] of figure 2 in Amy's paper (QPL 2018) involves two
-- internal path variables y_i and y_j at once, any two distinct ones.
-- PathSum.Reduction.General states it at the first two, y_i = y₀ and
-- y_j = y₁.  This module supplies the renumbering that transports it
-- to any ordered pair: front₂ i j i≢j moves y_i to position 0, y_j to
-- position 1, and keeps the other variables in their original order.
--
-- It is two single renumberings (PathSum.Reorder.front): first y_j to
-- the front, then y_i to the front of that.  Among the variables other
-- than y_j, y_i is the (skip i≢j)-th (Data.Fin's punchOut), so the
-- second renumbering is at position suc (skip i≢j).  Position 0 of the
-- result is the old punchIn j (skip i≢j), which is i (punchIn-skip);
-- position 1 is the old j; and position l + 2 is the old
-- punchIn j (punchIn (skip i≢j) l), the others in order.
--
-- By definition, the coefficient of a renumbered monomial a ∷ b ∷ s is
-- the original coefficient of mon₂ i j i≢j a b s, the monomial that
-- contains y_i when a says so, y_j when b says so, and reads the other
-- variables off s in order (mon₂-i, mon₂-j, mon₂-rest).  The quarters
-- of a polynomial in y_i and y_j, q₀₀ʸ ... q₁₁ʸ, are the quarters of
-- PathSum.Polynomial.Substitution at the renumbered polynomial: q₁₀ʸ,
-- say, collects the coefficients of the monomials that contain y_i and
-- not y_j, as polynomials in the other variables.  They are what the
-- premises of [Case] at (y_i , y_j) are about (PathSum.Full.caseAtᶠ).
--
-- A variable absent from a polynomial stays absent under renumbering
-- (NoVar-front₂-i, -j, -rest), so front₂ keeps every path variable
-- internal (Internal-front₂).  Nothing here depends on M or on the
-- semantics; that front₂ preserves the denotation is
-- PathSum.Full.Sound.front₂-≋.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Reorder.Pair where

open import Data.Fin.Base using (Fin; zero; suc; punchIn; punchOut)
open import Data.Fin.Properties using (punchIn-punchOut)
open import Data.Fin.Subset using (Subset; Side)
open import Data.Integer.Base using (ℤ)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (_∷_; insertAt; lookup)
open import Data.Vec.Properties using (insertAt-lookup; insertAt-punchIn)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; sym; trans; subst; ≢-sym)

open import PathSum.Base using (PathSum; Internal)
open import PathSum.Polynomial using (Poly; y[_]; NoVar)
open import PathSum.Polynomial.Substitution using (q₀₀; q₀₁; q₁₀; q₁₁)
open import PathSum.Reorder using
  (frontᴾ; front; NoVar-front; NoVar-front-suc; Internal-front)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- The position of y_i once y_j is set aside

-- skip i≢j is the index of y_i among the variables other than y_j,
-- which punchIn j sends back to i.

skip : {i j : Fin (suc (suc m))} → i ≢ j → Fin (suc m)
skip i≢j = punchOut (≢-sym i≢j)

punchIn-skip : {i j : Fin (suc (suc m))} (i≢j : i ≢ j) →
               punchIn j (skip i≢j) ≡ i
punchIn-skip i≢j = punchIn-punchOut (≢-sym i≢j)


------------------------------------------------------------------------
-- Polynomials and path-sums

-- y_j to the front, then y_i to the front of that.

frontᴾ₂ : (i j : Fin (suc (suc m))) → i ≢ j →
          Poly n (suc (suc m)) → Poly n (suc (suc m))
frontᴾ₂ i j i≢j P = frontᴾ (suc (skip i≢j)) (frontᴾ j P)

front₂ : (i j : Fin (suc (suc m))) → i ≢ j →
         PathSum n k (suc (suc m)) → PathSum n k (suc (suc m))
front₂ i j i≢j ξ = front (suc (skip i≢j)) (front j ξ)

-- The original monomial behind the renumbered a ∷ b ∷ s: the
-- coefficient of a ∷ b ∷ s in frontᴾ₂ i j i≢j P is, by definition,
-- that of mon₂ i j i≢j a b s in P.

mon₂ : (i j : Fin (suc (suc m))) → i ≢ j → Side → Side → Subset m →
       Subset (suc (suc m))
mon₂ i j i≢j a b s = insertAt (insertAt s (skip i≢j) a) j b

-- It holds a at y_i, b at y_j, and s, in order, everywhere else.

mon₂-i : (i j : Fin (suc (suc m))) (i≢j : i ≢ j) (a b : Side)
         (s : Subset m) → lookup (mon₂ i j i≢j a b s) i ≡ a
mon₂-i i j i≢j a b s =
  subst (λ t → lookup (mon₂ i j i≢j a b s) t ≡ a) (punchIn-skip i≢j)
    (trans (insertAt-punchIn (insertAt s (skip i≢j) a) j b (skip i≢j))
           (insertAt-lookup s (skip i≢j) a))

mon₂-j : (i j : Fin (suc (suc m))) (i≢j : i ≢ j) (a b : Side)
         (s : Subset m) → lookup (mon₂ i j i≢j a b s) j ≡ b
mon₂-j i j i≢j a b s = insertAt-lookup (insertAt s (skip i≢j) a) j b

mon₂-rest : (i j : Fin (suc (suc m))) (i≢j : i ≢ j) (a b : Side)
            (s : Subset m) (l : Fin m) →
            lookup (mon₂ i j i≢j a b s) (punchIn j (punchIn (skip i≢j) l)) ≡
            lookup s l
mon₂-rest i j i≢j a b s l = trans
  (insertAt-punchIn (insertAt s (skip i≢j) a) j b (punchIn (skip i≢j) l))
  (insertAt-punchIn s (skip i≢j) a l)


------------------------------------------------------------------------
-- The quarters of a polynomial in y_i and y_j

-- P = q₀₀ʸ + y_j q₀₁ʸ + y_i q₁₀ʸ + y_i y_j q₁₁ʸ, each quarter a
-- polynomial in the other variables, in their original order.

q₀₀ʸ q₀₁ʸ q₁₀ʸ q₁₁ʸ : (i j : Fin (suc (suc m))) → i ≢ j →
                      Poly n (suc (suc m)) → Poly n m
q₀₀ʸ i j i≢j P = q₀₀ (frontᴾ₂ i j i≢j P)
q₀₁ʸ i j i≢j P = q₀₁ (frontᴾ₂ i j i≢j P)
q₁₀ʸ i j i≢j P = q₁₀ (frontᴾ₂ i j i≢j P)
q₁₁ʸ i j i≢j P = q₁₁ (frontᴾ₂ i j i≢j P)


------------------------------------------------------------------------
-- Occurrences of the moved variables

-- y_i lands at position 0, y_j at position 1, and the others, in
-- order, after them.

NoVar-front₂-i : {c : ℤ} (i j : Fin (suc (suc m))) (i≢j : i ≢ j)
                 (P : Poly n (suc (suc m))) →
                 NoVar c y[ i ] P → NoVar c y[ zero ] (frontᴾ₂ i j i≢j P)
NoVar-front₂-i {c = c} i j i≢j P h =
  NoVar-front (suc (skip i≢j)) (frontᴾ j P)
    (NoVar-front-suc j (skip i≢j) P
      (subst (λ t → NoVar c y[ t ] P) (sym (punchIn-skip i≢j)) h))

NoVar-front₂-j : {c : ℤ} (i j : Fin (suc (suc m))) (i≢j : i ≢ j)
                 (P : Poly n (suc (suc m))) →
                 NoVar c y[ j ] P →
                 NoVar c y[ suc zero ] (frontᴾ₂ i j i≢j P)
NoVar-front₂-j i j i≢j P h =
  NoVar-front-suc (suc (skip i≢j)) zero (frontᴾ j P) (NoVar-front j P h)

NoVar-front₂-rest : {c : ℤ} (i j : Fin (suc (suc m))) (i≢j : i ≢ j)
                    (l : Fin m) (P : Poly n (suc (suc m))) →
                    NoVar c y[ punchIn j (punchIn (skip i≢j) l) ] P →
                    NoVar c y[ suc (suc l) ] (frontᴾ₂ i j i≢j P)
NoVar-front₂-rest i j i≢j l P h =
  NoVar-front-suc (suc (skip i≢j)) (suc l) (frontᴾ j P)
    (NoVar-front-suc j (punchIn (skip i≢j) l) P h)

-- Hence renumbering a pair keeps every path variable internal.

Internal-front₂ : (i j : Fin (suc (suc m))) (i≢j : i ≢ j)
                  (ξ : PathSum n k (suc (suc m))) →
                  Internal ξ → Internal (front₂ i j i≢j ξ)
Internal-front₂ i j i≢j ξ int =
  Internal-front (suc (skip i≢j)) (front j ξ) (Internal-front j ξ int)

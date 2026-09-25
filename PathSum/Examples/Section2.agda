------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 2: the Hadamard's path-sum (example 2.2), and the order of
-- three polynomials (example 2.12)
--
-- Example 2.2 gives the path-sum of the Hadamard gate,
--
--    H : |x⟩ ↦ 1/√2 Σ_y e^{2πi xy/2} |y⟩,
--
-- which is, coefficient by coefficient, the circuit's own path-sum
-- ⟦ H ⟧ (definition 2.9); hence the two are equivalent.  The other
-- gates of example 2.2 are not over {H, S, CZ}.
--
-- Example 2.12 computes
--
--    ord (1/2) = 0,  ord (½x₁ + ½x₂) = 1,  ord (3/2 x₂ + ½x₁x₂x₃) = 3,
--
-- where a term (a/2^b) x^α with a odd has order b + |α| - 1 and a
-- polynomial the largest order of its terms (definition 2.11).
-- PathSum.Order formalises the bound Ord≤ d rather than the order
-- itself, so "ord P = d" is stated as Ord≤ d P together with
-- ¬ Ord≤ (d - 1) P.  For d = 0 there is no bound below; the order of a
-- polynomial with no terms is not defined, and "ord (1/2) = 0" is read
-- as Ord≤ 0 together with 1/2 not vanishing modulo 1.  The coefficient
-- 3/2 is 1/2 in D/Z, and the order does not see the difference.  All
-- six facts are decided by computation, at M = 3 (numerators over 8).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Section2 where

open import Data.Fin.Base using (zero; suc)
open import Data.Integer.Base using (+_)
open import Data.List.Base using ([])
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Polynomial
open import PathSum.Polynomial.Decidable using (refute-by-eval)
open import PathSum.Order 3 using (pow; Ord≤)
open import PathSum.Reduction 3 using (½)
open import PathSum.Reduction.Decidable 3 using (Ord≤?)
open import PathSum.Denotation 0 using (_≋_)
open import PathSum.Congruence 0 using (Congruent; congruent?)
open import PathSum.Examples.Base using
  (xᵐ; yᵐ; _⋆_; H₁; ⟦_⟧; circuit-renumbered-≋)


------------------------------------------------------------------------
-- Example 2.2: the Hadamard gate

-- ½xy, output y.

Hᵖ : PathSum 1 1 1
Hᵖ = ⟨ (+ 4) ⋆ (xᵐ zero ∪ᵐ yᵐ zero) , (λ _ → μ y[ zero ]) ⟩

H-literal : Congruent ⟦ H₁ ⟧ Hᵖ
H-literal = toWitness {a? = congruent? ⟦ H₁ ⟧ Hᵖ} tt

H-≋ : ⟦ H₁ ⟧ ≋ Hᵖ
H-≋ = circuit-renumbered-≋ H₁ Hᵖ [] refl refl


------------------------------------------------------------------------
-- Example 2.12: ord (1/2) = 0

ord-½ : Ord≤ 0 (κ {1} {0} ½) × ¬ (κ {1} {0} ½ ≈[ pow 3 ] 0ᴾ)
ord-½ = toWitness {a? = Ord≤? 0 (κ {1} {0} ½)} tt ,
        refute-by-eval (κ ½) (pow 3) 0ᴾ


------------------------------------------------------------------------
-- Example 2.12: ord (½x₁ + ½x₂) = 1

P-lin : Poly 2 0
P-lin = (+ 4) ⋆ xᵐ zero +ᴾ (+ 4) ⋆ xᵐ (suc zero)

ord-lin : Ord≤ 1 P-lin × ¬ Ord≤ 0 P-lin
ord-lin = toWitness {a? = Ord≤? 1 P-lin} tt ,
          toWitnessFalse {a? = Ord≤? 0 P-lin} tt


------------------------------------------------------------------------
-- Example 2.12: ord (3/2 x₂ + ½x₁x₂x₃) = 3

P-cubic : Poly 3 0
P-cubic = (+ 12) ⋆ xᵐ (suc zero) +ᴾ
          (+ 4) ⋆ (xᵐ zero ∪ᵐ xᵐ (suc zero) ∪ᵐ xᵐ (suc (suc zero)))

ord-cubic : Ord≤ 3 P-cubic × ¬ Ord≤ 2 P-cubic
ord-cubic = toWitness {a? = Ord≤? 3 P-cubic} tt ,
            toWitnessFalse {a? = Ord≤? 2 P-cubic} tt

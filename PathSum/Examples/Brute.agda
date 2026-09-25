------------------------------------------------------------------------
-- Presentations of groups
--
-- The worked examples by brute force: cross-checks
--
-- PathSum.Brute decides equivalence by evaluating every entry of both
-- operators.  That is not the paper's method, and it is exponential;
-- each fact below is one closed computation, which at these sizes (at
-- most four inputs and four path variables) takes seconds.  It is used
-- here for cross-checks only: every fact below is also proved by the
-- paper's method, or by renumbering path variables, in another example
-- module.
--
-- Sections 3.1 and B.1:
--
--  * (SH)³ = ω I about the circuit;
--  * the circuits' path-sums of HH and (SH)³ against the paper's
--    literals;
--  * example B.1 as printed, which is the identity and not ω I.
--
-- Examples 3.3, 3.4 and B.2, which PathSum.Examples.Toffoli,
-- .ControlledT and .Adder derive with the general rules of figure 2:
--
--  * example 3.3, the Toffoli path-sum is |x1 x2 (x3 ⊕ x1x2)⟩;
--  * example 3.4, the controlled-T path-sum (its ancilla a third
--    input on which it does not depend) is
--    |x1 x2 x3⟩ ↦ ω^{x1x2} |x1 x2 0⟩;
--  * example B.2, the full adder's path-sum is its reversible
--    specification;
--
-- and the instance of [Case] in PathSum.Examples.General.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Brute where

open import Data.Nat.Base using (ℕ)
open import Relation.Nullary.Decidable using (True)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Brute 0 using (≋?; ≋-by-eval; ≋-refute)
open import PathSum.Denotation 0 using (_≋_)
open import PathSum.Examples.Base using (ωI; Circuit; HH; SH³; ⟦_⟧)
open import PathSum.Examples.Section3 using (HHᵖ)
open import PathSum.Examples.AppendixB using (SH³ᵖ; B1ᵖ)
open import PathSum.Examples.Toffoli using (Toffoliᵖ; Toffoliˢ)
open import PathSum.Examples.ControlledT using (cTᵖ; cTˢ)
open import PathSum.Examples.Adder using (Adderᵖ; Adderˢ)
open import PathSum.Examples.General using (Caseᵖ)

private
  variable
    n k′ m′ : ℕ


------------------------------------------------------------------------
-- Sections 3.1 and B.1

-- A circuit's path-sum against any path-sum, by brute force.  Stated
-- for any circuit: ≋-by-eval applied to a closed ⟦ C ⟧ elaborates
-- its normalisation partly reduced, and Agda then matches the
-- conclusion against the declared ⟦ C ⟧ ≋ ζ by unfolding ζ's
-- amplitudes -- 42 s for (SH)³ against the paper's literal, against a
-- second or two through this.

circuit-by-eval : (C : Circuit n) (ζ : PathSum n k′ m′) →
                  {True (≋? ⟦ C ⟧ ζ)} → ⟦ C ⟧ ≋ ζ
circuit-by-eval C ζ {t} = ≋-by-eval ⟦ C ⟧ ζ {t}

-- (SH)³ = ω I (PathSum.Examples.AppendixB proves it by [ω, HH, Elim],
-- both at any path variable and through the restriction).

SH³-ω-brute : ⟦ SH³ ⟧ ≋ ωI
SH³-ω-brute = circuit-by-eval SH³ ωI

-- The circuits' path-sums are the paper's literals (proved there by
-- renumbering).

SH³-literal-brute : ⟦ SH³ ⟧ ≋ SH³ᵖ
SH³-literal-brute = circuit-by-eval SH³ SH³ᵖ

HH-literal-brute : ⟦ HH ⟧ ≋ HHᵖ
HH-literal-brute = circuit-by-eval HH HHᵖ

-- Example B.1 as printed is the identity, not ω I.

B1ᵖ-id-brute : B1ᵖ ≋ idPS
B1ᵖ-id-brute = ≋-by-eval B1ᵖ idPS

B1ᵖ-not-ω-brute : ¬ (B1ᵖ ≋ ωI)
B1ᵖ-not-ω-brute = ≋-refute B1ᵖ ωI


------------------------------------------------------------------------
-- Examples 3.3, 3.4 and B.2, and the [Case] instance

Toffoli-spec-brute : Toffoliᵖ ≋ Toffoliˢ
Toffoli-spec-brute = ≋-by-eval Toffoliᵖ Toffoliˢ

cT-spec-brute : cTᵖ ≋ cTˢ
cT-spec-brute = ≋-by-eval cTᵖ cTˢ

Adder-spec-brute : Adderᵖ ≋ Adderˢ
Adder-spec-brute = ≋-by-eval Adderᵖ Adderˢ

Case-id-brute : Caseᵖ ≋ idPS
Case-id-brute = ≋-by-eval Caseᵖ idPS

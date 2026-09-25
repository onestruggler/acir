------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford identities and non-identities, by corollary 4.4's method
--
-- Section 4.3 decides whether a Clifford circuit C is the identity by
-- reducing the isometry restriction of its path-sum, ⟦ C ⟧ᴿ: each step
-- is a rule of figure 2, or lemma 4.2 (destructive interference)
-- refutes the circuit, and when no path variable is left the reduct is
-- the identity or it is not (PathSum.Corollary).  This module runs the
-- method on small circuits, writing each chain out with the quotients
-- the paper's lemma 4.3 would find.
--
-- Identities: CZ² is the identity with nothing to reduce, and X² and
-- CNOT² each need one [HH] -- solving the middle Hadamard's variable
-- as 1 ⊕ x and as x₁ ⊕ x₂ -- after which [Elim] removes the rest.
--
-- Non-identities, each refuted the way section 4.3 would:
--
--  * H: its restriction has no path variables but keeps a unit of
--    normalisation (its diagonal is ±1/√2), so it is not the identity;
--  * S, and HH followed by S after one [Elim]: the phase ¼x does not
--    vanish at x = 1;
--  * X and CNOT: lemma 4.2, the variant of [HH] "where Q contains only
--    input variables", with Q = 1 and Q = x₁ -- summing the path
--    variable makes the two branches cancel at some input.
--
-- Lemma 4.2 speaks of ⟦ C ⟧ᴿ, whose path variables are internal; lemma
-- 4.1 at the circuit (PathSum.Corollary.lemma-4-1-circuit) carries the
-- refutation to ⟦ C ⟧.  Finally corollary 4.4's decision procedure,
-- PathSum.Corollary.circuit-decidable, is run on these circuits: its
-- verdicts are computed, and agree.  Deciding the question is
-- elementary in any case -- the matrix is finite -- and nothing here
-- measures the running time the paper claims for the procedure.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Clifford where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (zero; suc)
open import Data.Integer.Divisibility.Signed using (_∣?_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using
  (True; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base
open import PathSum.Polynomial
open import PathSum.Polynomial.Decidable using (by-eval)
open import PathSum.Order 3 using (pow)
open import PathSum.Reduction 3 using
  (_⟶*_; ε; _◅_; elim-reduct; hh-reduct; ½)
open import PathSum.Reduction.Decidable 3 using (elim!; hh!)
open import PathSum.Denotation 0 using (Assign; _≋_; interference-lemma)
open import PathSum.Identity 0 using (not-id-phase)
open import PathSum.Decide 0 using (id-no-norm)
open import PathSum.Corollary 0 using
  (lemma-4-1-circuit; circuit-not-id; circuit-decidable)
open import PathSum.Examples.Base using
  (xᵐ; yᵐ; HH; SH³; X; X²; CZ²; CNOT; CNOT²; HHS; H₁; S₁;
   ⟦_⟧; ⟦_⟧ᴿ; ⟦⟧ᴿ-Internal; circuit-id!)

private
  y∅ : Assign 0
  y∅ ()

  one : Assign 1
  one _ = true


------------------------------------------------------------------------
-- Identities

-- Two CZs: the phase ½x₁x₂ + ½x₁x₂ is already 0 modulo 1.

CZ²-id : ⟦ CZ² ⟧ ≋ idPS
CZ²-id = circuit-id! CZ² ε

-- X² = H S² H H S² H.  The restriction has three path variables, the
-- newest first; the quotient of the newest is ½(1 ⊕ x ⊕ y), y being the
-- variable of the middle Hadamards, so [HH] solves y = 1 ⊕ x.  The
-- phase then vanishes, and [Elim] removes the two remaining variables.

X²ᴿ₁ : PathSum 1 4 2
X²ᴿ₁ = hh-reduct ⟦ X² ⟧ᴿ zero true (xᵐ zero ∪ᵐ yᵐ zero)

X²ᴿ₂ : PathSum 1 2 1
X²ᴿ₂ = elim-reduct X²ᴿ₁

X²ᴿ₃ : PathSum 1 0 0
X²ᴿ₃ = elim-reduct X²ᴿ₂

X²-reduces : ⟦ X² ⟧ᴿ ⟶* X²ᴿ₃
X²-reduces =
  hh! ⟦ X² ⟧ᴿ zero true (xᵐ zero ∪ᵐ yᵐ zero) ◅
  (elim! X²ᴿ₁ ◅ (elim! X²ᴿ₂ ◅ ε))

X²-id : ⟦ X² ⟧ ≋ idPS
X²-id = circuit-id! X² X²-reduces

-- CNOT² on two qubits: [HH] solves the middle variable as x₁ ⊕ x₂.

CNOT²ᴿ₁ : PathSum 2 4 2
CNOT²ᴿ₁ = hh-reduct ⟦ CNOT² ⟧ᴿ zero false
            (xᵐ zero ∪ᵐ xᵐ (suc zero) ∪ᵐ yᵐ zero)

CNOT²ᴿ₂ : PathSum 2 2 1
CNOT²ᴿ₂ = elim-reduct CNOT²ᴿ₁

CNOT²ᴿ₃ : PathSum 2 0 0
CNOT²ᴿ₃ = elim-reduct CNOT²ᴿ₂

CNOT²-reduces : ⟦ CNOT² ⟧ᴿ ⟶* CNOT²ᴿ₃
CNOT²-reduces =
  hh! ⟦ CNOT² ⟧ᴿ zero false (xᵐ zero ∪ᵐ xᵐ (suc zero) ∪ᵐ yᵐ zero) ◅
  (elim! CNOT²ᴿ₁ ◅ (elim! CNOT²ᴿ₂ ◅ ε))

CNOT²-id : ⟦ CNOT² ⟧ ≋ idPS
CNOT²-id = circuit-id! CNOT² CNOT²-reduces


------------------------------------------------------------------------
-- Refutations without path variables

-- H: nothing to reduce, and a unit of normalisation left over.

H-not-id : ¬ (⟦ H₁ ⟧ ≋ idPS)
H-not-id = circuit-not-id H₁ ε (id-no-norm ⟦ H₁ ⟧ᴿ)

-- S: the phase ¼x is ¼ at x = 1.

S-not-id : ¬ (⟦ S₁ ⟧ ≋ idPS)
S-not-id = circuit-not-id S₁ ε
  (not-id-phase ⟦ S₁ ⟧ᴿ one y∅ refl
    (toWitnessFalse {a? = pow 3 ∣? eval (phase ⟦ S₁ ⟧ᴿ) one y∅} tt))

-- HH then S: [Elim] removes the Hadamards' variable, and S's phase
-- remains.

HHS-reduces : ⟦ HHS ⟧ᴿ ⟶* elim-reduct ⟦ HHS ⟧ᴿ
HHS-reduces = elim! ⟦ HHS ⟧ᴿ ◅ ε

HHS-not-id : ¬ (⟦ HHS ⟧ ≋ idPS)
HHS-not-id = circuit-not-id HHS HHS-reduces
  (not-id-phase (elim-reduct ⟦ HHS ⟧ᴿ) one y∅ refl
    (toWitnessFalse
      {a? = pow 3 ∣? eval (phase (elim-reduct ⟦ HHS ⟧ᴿ)) one y∅} tt))


------------------------------------------------------------------------
-- Refutations by lemma 4.2

-- X: the quotient of its single path variable is ½·1, a non-zero form
-- in no path variable.

X-quotient : head-part (phase ⟦ X ⟧ᴿ) ≈[ pow 3 ] (½ ·ᴾ liftXor true 1ᵐ)
X-quotient =
  by-eval (head-part (phase ⟦ X ⟧ᴿ)) (pow 3) (½ ·ᴾ liftXor true 1ᵐ)

X-not-id : ¬ (⟦ X ⟧ ≋ idPS)
X-not-id eq =
  interference-lemma ⟦ X ⟧ᴿ true 1ᵐ X-quotient (⟦⟧ᴿ-Internal X zero)
    refl (λ { (() , _) })
    (Equivalence.to (lemma-4-1-circuit X) eq)

-- CNOT: the quotient is ½x₁.

CNOT-quotient :
  head-part (phase ⟦ CNOT ⟧ᴿ) ≈[ pow 3 ] (½ ·ᴾ liftXor false (xᵐ zero))
CNOT-quotient = by-eval (head-part (phase ⟦ CNOT ⟧ᴿ)) (pow 3)
                        (½ ·ᴾ liftXor false (xᵐ zero))

CNOT-not-id : ¬ (⟦ CNOT ⟧ ≋ idPS)
CNOT-not-id eq =
  interference-lemma ⟦ CNOT ⟧ᴿ false (xᵐ zero) CNOT-quotient
    (⟦⟧ᴿ-Internal CNOT zero) refl (λ { (_ , ()) })
    (Equivalence.to (lemma-4-1-circuit CNOT) eq)


------------------------------------------------------------------------
-- Corollary 4.4's procedure, run

HH-decided : True (circuit-decidable HH)
HH-decided = tt

CZ²-decided : True (circuit-decidable CZ²)
CZ²-decided = tt

X²-decided : True (circuit-decidable X²)
X²-decided = tt

CNOT²-decided : True (circuit-decidable CNOT²)
CNOT²-decided = tt

H-decided : False (circuit-decidable H₁)
H-decided = tt

S-decided : False (circuit-decidable S₁)
S-decided = tt

HHS-decided : False (circuit-decidable HHS)
HHS-decided = tt

X-decided : False (circuit-decidable X)
X-decided = tt

CNOT-decided : False (circuit-decidable CNOT)
CNOT-decided = tt

SH³-decided : False (circuit-decidable SH³)
SH³-decided = tt

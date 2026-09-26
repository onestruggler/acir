------------------------------------------------------------------------
-- Presentations of groups
--
-- Translation validation at work (Amy, QPL 2018, section 5.1)
--
-- Small instances of PathSum.CRK.Validation, at the precision of the
-- other worked examples (M₀ = 0, so phases count eighths; see
-- PathSum.Examples.Base), over the paper's gate set with T = R 3,
-- S = R 2 and Z = R 1.  Each runs the procedure of section 5.1 on the
-- miter C₁ ++ C₂ † of two one- or two-qubit circuits: Gaussian
-- elimination reifies the miter's isometry restriction (computed by
-- Agda, the equation ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) holding by
-- refl), a chain of rules of figure 2 reduces it, and every side
-- condition is discharged by computing its decision.
--
--  * T;T ≡ S: the miter T T S† has no Hadamard, so no path variable,
--    and the restriction is already the identity's polynomials (the
--    empty chain; phase 1/8 + 1/8 - 2/8 = 0).
--  * T;H;H ≡ T: the miter T H H T† has two path variables; elimination
--    solves the last for x, and [Elim] removes the other, whose
--    coefficient xy/2 + xy/2 is an integer; what is left is the
--    identity's polynomials.  A Clifford+T identity, by the whole
--    procedure of section 5.1: elimination, a rule, the syntactic test.
--  * X ≢ I, for X = H Z H: elimination solves the second path variable
--    for x and leaves the phase ½y + xy, which is ½y₀·1 + R with 1
--    odd: lemma 4.2 (corrected) refutes.
--  * CNOT ≢ I on two qubits: no path variable can make the target's
--    output x₁ ⊕ x₂ equal to x₂, and elimination refutes.
--
-- Not here: an instance of the composed miter ⟦ C† ⟧ ∘ ζ of section 3
-- (PathSum.CRK.Specification, checking a circuit against a
-- specification ζ as section 5.2 does).  A composite's polynomials are
-- built by substitution, which is opaque (PathSum.Polynomial.Bind), so
-- on a closed instance its coefficients do not compute and the
-- syntactic test cannot be discharged by computation; the circuit form
-- C₁ ++ C₂ † of the miter, built by the state machine, has no such
-- obstacle.
--
-- Each fact is stated through the name Equivalent, and derived by a
-- wrapper stated for any two circuits, so that the closed instance is
-- matched against the wrapper's conclusion by its arguments (see
-- PathSum.Examples.Base for why).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Validation where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (+_; 1ℤ)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using
  (True; False; toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Base using (PathSum; phase; out; head-part; y₀)
open import PathSum.Polynomial using (Poly; κ; 0ᴾ; y[_]; _·ᴾ_)
open import PathSum.Polynomial.Decidable using (_≈?[_]_; NoVar?)
open import PathSum.Order 3 using (pow)
open import PathSum.Reduction 3 using (½)
open import PathSum.Reduction.General.Decidable 3 using (elimᴳ!)
open import PathSum.Denotation 0 using (_≋_)
open import PathSum.Congruence 0 using (id-syntactic?)
open import PathSum.Full 3 using (_⟶ᶠ*_; εᶠ; _◅ᶠ_; ⟶ᴳ⇒⟶ᶠ)
open import PathSum.Examples.Base using (module CRK)
open import PathSum.CRK.Adjoint 3 using (_†)
open import PathSum.Gauss.Corollary 0 using (⟦_⟧ᴿ)
open import PathSum.CRK.Validation 0 using
  (validation-sound; validation-refuted-gauss;
   validation-refuted-interference)

private
  variable
    n m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- The procedure, for any two circuits

-- Two circuits are equivalent.

Equivalent : CRK.Circuit n → CRK.Circuit n → Set
Equivalent C₁ C₂ = CRK.⟦ C₁ ⟧ ≋ CRK.⟦ C₂ ⟧

-- A chain from the miter's restriction to the identity's polynomials,
-- the last checked by computation, proves the circuits equivalent.

validate! : (C₁ C₂ : CRK.Circuit n)
  {ξ : PathSum n (CRK.norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ′ : PathSum n 0 0} → ξ ⟶ᶠ* ξ′ → {True (id-syntactic? ξ′)} →
  Equivalent C₁ C₂
validate! C₁ C₂ eq {ξ′} steps {t} =
  validation-sound C₁ C₂ eq steps (proj₁ w) (proj₂ w)
  where
  w = toWitness {a? = id-syntactic? ξ′} t

-- The elimination refutes.

refuted-gauss! : (C₁ C₂ : CRK.Circuit n) → ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ nothing →
                 ¬ Equivalent C₁ C₂
refuted-gauss! C₁ C₂ eq = validation-refuted-gauss C₁ C₂ eq

-- A reduct matches lemma 4.2 at y₀ with the quotient Q, each premise
-- checked by computation.

refuted-interference! : (C₁ C₂ : CRK.Circuit n)
  {ξ : PathSum n (CRK.norm (C₁ ++ C₂ †)) m′} →
  ⟦ C₁ ++ C₂ † ⟧ᴿ ≡ just (m′ , ξ) →
  {ξ″ : PathSum n k″ (suc m″)} → ξ ⟶ᶠ* ξ″ → (Q : Poly n m″) →
  {True (head-part (phase ξ″) ≈?[ pow 3 ] (½ ·ᴾ Q))} →
  {True (all? (λ w → NoVar? (+ 2) y₀ (out ξ″ w)))} →
  {True (all? (λ j → NoVar? (+ 2) y[ j ] Q))} →
  {False (Q ≈?[ + 2 ] 0ᴾ)} →
  ¬ Equivalent C₁ C₂
refuted-interference! C₁ C₂ eq {ξ″} steps Q {t₁} {t₂} {t₃} {f} =
  validation-refuted-interference C₁ C₂ eq steps Q
    (toWitness {a? = head-part (phase ξ″) ≈?[ pow 3 ] (½ ·ᴾ Q)} t₁)
    (toWitness {a? = all? (λ w → NoVar? (+ 2) y₀ (out ξ″ w))} t₂)
    (toWitness {a? = all? (λ j → NoVar? (+ 2) y[ j ] Q)} t₃)
    (toWitnessFalse {a? = Q ≈?[ + 2 ] 0ᴾ} f)


------------------------------------------------------------------------
-- The circuits

private
  a b : Fin 2
  a = zero
  b = suc zero

  q : Fin 1
  q = zero

-- T;T and S, the latter as R_2.  (Named R₂: S₁ is the S of
-- PathSum.Examples.Base, over {H , S , CZ}.)

TT : CRK.Circuit 1
TT = CRK.R 3 q ∷ CRK.R 3 q ∷ []

R₂ : CRK.Circuit 1
R₂ = CRK.R 2 q ∷ []

-- T;H;H and T.

THH : CRK.Circuit 1
THH = CRK.R 3 q ∷ CRK.H q ∷ CRK.H q ∷ []

T₁ : CRK.Circuit 1
T₁ = CRK.R 3 q ∷ []

-- X = H Z H, and the empty circuit.

X₁ : CRK.Circuit 1
X₁ = CRK.H q ∷ CRK.R 1 q ∷ CRK.H q ∷ []

I₁ : CRK.Circuit 1
I₁ = []

-- CNOT with control a and target b, and the empty circuit.

CNOT₂ : CRK.Circuit 2
CNOT₂ = CRK.CNOT a b (λ ()) ∷ []

I₂ : CRK.Circuit 2
I₂ = []


------------------------------------------------------------------------
-- The verdicts

TT≡S : Equivalent TT R₂
TT≡S = validate! TT R₂ refl εᶠ

THH≡T : Equivalent THH T₁
THH≡T = validate! THH T₁ refl (⟶ᴳ⇒⟶ᶠ (elimᴳ! _) ◅ᶠ εᶠ)

X≢I : ¬ Equivalent X₁ I₁
X≢I = refuted-interference! X₁ I₁ refl εᶠ (κ 1ℤ)

CNOT≢I : ¬ Equivalent CNOT₂ I₂
CNOT≢I = refuted-gauss! CNOT₂ I₂ refl


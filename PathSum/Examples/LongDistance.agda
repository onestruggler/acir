------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 2.1: a T gate and a T† gate on the same parity, far apart,
-- cancel in the path-sum
--
-- A two-qubit instance of PathSum.CRK.Cancellation, at the examples'
-- precision M₀ = 0 (T = R 3, eighths).  The circuit
--
--    LD = CNOT₁₂ ; T₂ ; CNOT₁₂ ; CNOT₂₁ ; T†₁ ; CNOT₂₁
--
-- applies T to the second wire while it holds x1 ⊕ x2, moves that
-- parity onto the first wire with CNOTs, and applies T† there.  The two
-- phase gates are on different wires and no two adjacent gates cancel,
-- but they act on the same logical state, so their phase terms
-- ⅛(x1 ⊕ x2) = ⅛(x1 + x2 − 2x1x2) cancel in the path-sum:
--
-- * LD-folds: the interpretation states of LD and of its CNOTs alone
--   agree (PathSum.CRK.Cancellation.long-distance; its hypothesis, that
--   the CNOTs carry the form on the second wire to the first, is
--   checked on forms by refl).
-- * LD-literally-id: the path-sum of LD is literally the identity's:
--   normalisation 0, no path variable, phase 0 at every monomial and
--   the outputs μ x_w at every monomial (as integers, not only modulo
--   1 and 2), hence congruent to |x⟩ ↦ |x⟩ (LD-congruent, PathSum.
--   Congruence).  So it is the identity with no rule of figure 2
--   applied (LD-syntactic).
-- * LD-matrix: the matrix route reaches the same verdict by computing
--   LD's 4×4 matrix gate by gate (PathSum.CRK.Expand.matrix-id?), a
--   computation exponential in the number of qubits; the path-sum
--   needed none.
--
-- The statements about the closed circuit are made through names whose
-- arguments are the circuit (Implements, MatrixId, Agree of runs), as
-- PathSum.Examples.Base recommends.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.LongDistance where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using (inside; outside)
open import Data.Integer.Base using (0ℤ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness)

open import PathSum.Base using (PathSum; phase; out; idPS)
open import PathSum.Examples.Base using
  (module CRK; Implements; crk-implements)
open import PathSum.Linear using (liftᴸ; varᴸ)
open import PathSum.Polynomial using (x[_]; μ)

import PathSum.Congruence as Cg
import PathSum.CRK.Cancellation as Cn
import PathSum.CRK.Expand as E


------------------------------------------------------------------------
-- The circuit

a b : Fin 2
a = zero
b = suc zero

-- Before the T gate, between the two phase gates, and after T†.

C₁ C₃ : CRK.Circuit 2
C₁ = CRK.CNOT a b (λ ()) ∷ []
C₃ = CRK.CNOT b a (λ ()) ∷ []

D : List (Cn.PGate 0 2)
D = Cn.cnot a b (λ ()) ∷ Cn.cnot b a (λ ()) ∷ []

-- T on the second wire, T† on the first.

LD : CRK.Circuit 2
LD = C₁ ++ CRK.R 3 b ∷ Cn.circ 0 D ++ CRK.R† 3 a ∷ C₃

-- Gate by gate.

LD-gates : LD ≡ CRK.CNOT a b (λ ()) ∷ CRK.R 3 b ∷ CRK.CNOT a b (λ ()) ∷
                CRK.CNOT b a (λ ()) ∷ CRK.R† 3 a ∷ CRK.CNOT b a (λ ()) ∷ []
LD-gates = refl

-- Its CNOTs alone.

LD₀ : CRK.Circuit 2
LD₀ = C₁ ++ Cn.circ 0 D ++ C₃


------------------------------------------------------------------------
-- The cancellation

-- The CNOTs carry x1 ⊕ x2 from the second wire to the first, so LD and
-- its CNOTs have agreeing interpretation states.

LD-folds : Cn.Agree 0 (CRK.run LD CRK.init) (CRK.run LD₀ CRK.init)
LD-folds = Cn.long-distance 0 C₁ C₃ D 3 b a refl

-- The path-sum of LD is the identity's, coefficient by coefficient: no
-- path variable, phase 0, and the inputs on the wires.

LD-phase : ∀ γ → phase CRK.⟦ LD ⟧ γ ≡ 0ℤ
LD-phase (outside ∷ outside ∷ [] , []) = refl
LD-phase (outside ∷ inside  ∷ [] , []) = refl
LD-phase (inside  ∷ outside ∷ [] , []) = refl
LD-phase (inside  ∷ inside  ∷ [] , []) = refl

LD-outs : ∀ w → out CRK.⟦ LD ⟧ w ≡ liftᴸ (varᴸ x[ w ])
LD-outs zero       = refl
LD-outs (suc zero) = refl

-- Literally the identity's path-sum: normalisation 0, no path
-- variable, the identity's phase and outputs coefficient by
-- coefficient (as integers), hence congruent to it.

LD-outs-μ : ∀ w γ → out CRK.⟦ LD ⟧ w γ ≡ μ x[ w ] γ
LD-outs-μ zero       (outside ∷ outside ∷ [] , []) = refl
LD-outs-μ zero       (outside ∷ inside  ∷ [] , []) = refl
LD-outs-μ zero       (inside  ∷ outside ∷ [] , []) = refl
LD-outs-μ zero       (inside  ∷ inside  ∷ [] , []) = refl
LD-outs-μ (suc zero) (outside ∷ outside ∷ [] , []) = refl
LD-outs-μ (suc zero) (outside ∷ inside  ∷ [] , []) = refl
LD-outs-μ (suc zero) (inside  ∷ outside ∷ [] , []) = refl
LD-outs-μ (suc zero) (inside  ∷ inside  ∷ [] , []) = refl

LD-congruent : Cg.Congruent 0 CRK.⟦ LD ⟧ idPS
LD-congruent = toWitness {a? = Cg.congruent? 0 CRK.⟦ LD ⟧ idPS} tt

LD-literally-id :
  CRK.norm LD ≡ 0 × CRK.paths LD ≡ 0 ×
  (∀ γ → phase CRK.⟦ LD ⟧ γ ≡ phase idPS γ) ×
  (∀ w γ → out CRK.⟦ LD ⟧ w γ ≡ out idPS w γ) ×
  Cg.Congruent 0 CRK.⟦ LD ⟧ idPS
LD-literally-id = refl , refl , LD-phase , LD-outs-μ , LD-congruent

-- So it is |x⟩ ↦ |x⟩ syntactically, with no rule applied.

LD-syntactic : Implements LD idPS
LD-syntactic = crk-implements LD idPS [] refl refl

-- The matrix route: LD's 4 × 4 matrix, computed gate by gate, is the
-- identity.

LD-matrix : E.MatrixId 0 LD
LD-matrix = toWitness {a? = E.matrix-id? 0 LD} tt

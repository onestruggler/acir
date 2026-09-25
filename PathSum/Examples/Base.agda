------------------------------------------------------------------------
-- Presentations of groups
--
-- The setting of the worked examples: Clifford+T precision, notation
-- for literal path-sums, and the circuits
--
-- The paper's examples (Amy, QPL 2018, sections 2 and 3 and appendix
-- B) are instances: fixed circuits on one to four qubits, fixed
-- polynomials.  They are checked here at the precision M₀ = 0 of the
-- denotation, which makes M = 3: phase numerators count eighths, ζ is
-- e^{2πi/8}, and ½, ¼ and ⅛ are the numerators 4, 2 and 1 -- exactly
-- the precision of the Clifford+T examples in the paper.  Nothing in
-- the example modules is a general theorem; each is a fact about one
-- closed path-sum, and each premise of a rewrite rule is discharged by
-- computing its decision (PathSum.Reduction.Decidable for the linear
-- rules, PathSum.Reduction.General.Decidable for the general ones).
--
-- A literal path-sum is written with _⋆_: c ⋆ γ is the term (c/8)·γ
-- for a monomial γ built from xᵐ i (the input x_(i+1)) and yᵐ j (the
-- path variable y_j) with _∪ᵐ_.  The paper numbers its path variables
-- y1, y2, ... from 1 in the order the Hadamards introduce them; its y1
-- is yᵐ zero here.  A circuit's path-sum ⟦ C ⟧ lists them the other way
-- round (the newest first), and its restriction ⟦ C ⟧ᴿ keeps only the
-- ones that are not the last on their wire (PathSum.Circuit).  A
-- circuit is a list of gates, the head applied first.  The paper's own
-- names x₁ … x₄ and y₁ … y₄ are provided for the monomials of its
-- inputs and path variables.
--
-- The circuits of examples 3.3, 3.4 and B.2 are over {H, CNOT, T, T†}
-- (with S = R 2 and S† = R† 2 as well) and are stated with
-- PathSum.CRK.Circuit, of which this module also fixes one shared
-- instance, CRK.  A circuit's path-sum is matched with the paper's
-- literal by renumbering its path variables, and a circuit with an
-- ancilla by first setting that input to 0 (PathSum.Ancilla).  For the
-- larger circuits the facts are stated through names -- Implements,
-- Literal₀, Implements₀, Clean₀ -- each unfolding by refl to the
-- statement it names (see the last section for why).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Base where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; +_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst)
open import Relation.Nullary.Decidable using (True; toWitness)

open import PathSum.Base
open import PathSum.Polynomial hiding (subst)
open import PathSum.Order 3 using (pow)
open import PathSum.Reduction 3 using (_⟶*_; ⅛; ¼; ½)
open import PathSum.Denotation 0 using (Assign; amp; _≋_; ≋-trans)
open import PathSum.Ancilla 0 using (set0; set0-≋; _≋[_]₀_; clean-ancilla)
open import PathSum.Cyclotomic 0 using (_≐_; 0ᴬ)
open import PathSum.Corollary 0 using (circuit-id)

-- One instance of the circuit semantics and of the global phase, shared
-- by every example module and re-exported from here: two instances of
-- a parameterised module give two copies of each definition, and a
-- statement ⟦ C ⟧ ≋ ζ elaborated with one copy of ⟦_⟧ is matched
-- against the same statement with the other only by unfolding both
-- into amplitudes -- 40 s for (SH)³.

open import PathSum.Circuit 3 public using
  (Circuit; H; S; CZ; norm; paths; pathsᵁ; ⟦_⟧; ⟦_⟧ᴿ; ⟦⟧ᴿ-Internal;
   mono)

import PathSum.Congruence
module Cong = PathSum.Congruence 0

open Cong public using (phasePS)
open Cong using
  (congruent?; fronts; renumbered-≋; id-syntactic?; phase-syntactic?)

import PathSum.GlobalPhase
module GP = PathSum.GlobalPhase 0

private
  variable
    n m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Precision

-- M₀ = 0 gives M = 3: a phase numerator counts eighths.

_ : pow 3 ≡ + 8
_ = refl

_ : ½ ≡ + 4
_ = refl

_ : ¼ ≡ + 2
_ = refl

_ : ⅛ ≡ + 1
_ = refl


------------------------------------------------------------------------
-- Literal path-sums

-- The monomial of a single input or path variable, each taking the
-- numbers of inputs and of path variables implicitly, in that order.

xᵐ : Fin n → Mon n m
xᵐ i = ⟪ x[ i ] ⟫

yᵐ : ∀ {n m} → Fin m → Mon n m
yᵐ j = ⟪ y[ j ] ⟫

-- c ⋆ γ is the term (c/8) γ.

infix 7 _⋆_

_⋆_ : ℤ → Mon n m → Poly n m
c ⋆ γ = c ·ᴾ mono γ

-- The paper's names for the first four inputs and path variables.

x₁ : ∀ {n m} → Mon (suc n) m
x₁ = xᵐ zero

x₂ : ∀ {n m} → Mon (suc (suc n)) m
x₂ = xᵐ (suc zero)

x₃ : ∀ {n m} → Mon (suc (suc (suc n))) m
x₃ = xᵐ (suc (suc zero))

x₄ : ∀ {n m} → Mon (suc (suc (suc (suc n)))) m
x₄ = xᵐ (suc (suc (suc zero)))

y₁ : ∀ {n m} → Mon n (suc m)
y₁ = yᵐ zero

y₂ : ∀ {n m} → Mon n (suc (suc m))
y₂ = yᵐ (suc zero)

y₃ : ∀ {n m} → Mon n (suc (suc (suc m)))
y₃ = yᵐ (suc (suc zero))

y₄ : ∀ {n m} → Mon n (suc (suc (suc (suc m))))
y₄ = yᵐ (suc (suc (suc zero)))

-- The global phase ω = e^{2πi/8} on one qubit.  (Not named ω: that is
-- the rule.)

ωI : PathSum 1 0 0
ωI = phasePS ⅛


------------------------------------------------------------------------
-- The circuits

HH : Circuit 1
HH = H zero ∷ H zero ∷ []

-- (SH)³: a Hadamard first, as in the paper's path-sum for it.

SH³ : Circuit 1
SH³ = H zero ∷ S zero ∷ H zero ∷ S zero ∷ H zero ∷ S zero ∷ []

-- (S†H)³, with S† = S³.

S†H³ : Circuit 1
S†H³ = H zero ∷ S zero ∷ S zero ∷ S zero ∷
       H zero ∷ S zero ∷ S zero ∷ S zero ∷
       H zero ∷ S zero ∷ S zero ∷ S zero ∷ []

-- X = H S² H = HZH.

X : Circuit 1
X = H zero ∷ S zero ∷ S zero ∷ H zero ∷ []

X² : Circuit 1
X² = X ++ X

CZ² : Circuit 2
CZ² = CZ zero (suc zero) ∷ CZ zero (suc zero) ∷ []

-- CNOT with control x₁ and target x₂: a CZ conjugated by Hadamards on
-- the target.

CNOT : Circuit 2
CNOT = H (suc zero) ∷ CZ zero (suc zero) ∷ H (suc zero) ∷ []

CNOT² : Circuit 2
CNOT² = CNOT ++ CNOT

HHS : Circuit 1
HHS = H zero ∷ H zero ∷ S zero ∷ []

H₁ : Circuit 1
H₁ = H zero ∷ []

S₁ : Circuit 1
S₁ = S zero ∷ []


------------------------------------------------------------------------
-- Corollary 4.4's test, by computation

-- A chain of head rules from the restriction to a path-sum without
-- path variables whose polynomials are the identity's -- checked by
-- computing the decision -- proves the circuit is the identity
-- (PathSum.Corollary.circuit-id, which uses lemma 4.1).

circuit-id! : (C : Circuit n) {ξ′ : PathSum n 0 0} → ⟦ C ⟧ᴿ ⟶* ξ′ →
              {True (id-syntactic? ξ′)} → ⟦ C ⟧ ≋ idPS
circuit-id! C {ξ′} steps {t} = circuit-id C steps (proj₁ w) (proj₂ w)
  where
  w = toWitness {a? = id-syntactic? ξ′} t


------------------------------------------------------------------------
-- The same test up to a global phase

-- A chain from the restriction to the polynomials of |x⟩ ↦ ζ^e|x⟩
-- proves the circuit is that global phase (lemma 4.1 at the phase,
-- PathSum.GlobalPhase).  Conversely, whatever chain from the
-- restriction ends without path variables, the circuit is the phase
-- exactly when that end is.  Both restate PathSum.GlobalPhase at the
-- examples' shared instance, generically in C, so that at a closed
-- circuit the conclusion is literally the declared type.

circuit-phase! : (C : Circuit n) (e : ℤ) {ξ′ : PathSum n 0 0} →
                 ⟦ C ⟧ᴿ ⟶* ξ′ → {True (phase-syntactic? e ξ′)} →
                 ⟦ C ⟧ ≋ phasePS e
circuit-phase! C e steps {t} = GP.circuit-phase! C e steps {t}

corollary-4-4-phase : (C : Circuit n) (e : ℤ) {ξ′ : PathSum n k′ 0} →
  ⟦ C ⟧ᴿ ⟶* ξ′ →
  (⟦ C ⟧ ≋ phasePS e ⇔
   (k′ ≡ 0 ×
    (∀ w → out ξ′ w ≈[ + 2 ] μ x[ w ]) × phase ξ′ ≈[ pow 3 ] κ e))
corollary-4-4-phase C e steps = GP.corollary-4-4-phase C e steps


------------------------------------------------------------------------
-- The circuit's path-sum against a literal

-- ⟦ C ⟧ is equivalent to a literal that is congruent to it once its
-- path variables are renumbered (PathSum.Congruence.renumbered-≋),
-- the congruence checked by computation.  Stated for any circuit, so
-- that at a closed one the conclusion is literally ⟦ C ⟧ ≋ ζ with C
-- substituted.  (Applied to a closed ⟦ C ⟧ as a term, renumbered-≋
-- concludes a statement that Agda matches against ⟦ C ⟧ ≋ ζ only by
-- unfolding both into amplitudes.)

circuit-renumbered-≋ :
  (C : Circuit n) (ζ : PathSum n k′ m′) (js : List (Fin (pathsᵁ C))) →
  (k≡k′ : norm C ≡ k′) (m′≡p : m′ ≡ pathsᵁ C) →
  {True (congruent? (fronts js ⟦ C ⟧) (subst (PathSum n k′) m′≡p ζ))} →
  ⟦ C ⟧ ≋ ζ
circuit-renumbered-≋ C ζ js k≡k′ m′≡p {t} =
  renumbered-≋ ⟦ C ⟧ ζ js k≡k′ m′≡p {t}


------------------------------------------------------------------------
-- Circuits over {H, CNOT, R_k, R_k†}

-- One shared instance, for the reason above; its gates are used
-- qualified (CRK.H, CRK.CNOT, CRK.R, CRK.R†), the Clifford ones being
-- this module's.

import PathSum.CRK.Circuit
module CRK = PathSum.CRK.Circuit 3

-- A circuit's path-sum against a literal, by renumbering its path
-- variables; transitivity from a circuit's path-sum.  Both are stated
-- for any circuit, as circuit-renumbered-≋ is: applied to a closed
-- ⟦ C ⟧ directly, renumbered-≋ and ≋-trans elaborate its normalisation
-- as a numeral, and Agda then matches the conclusion against the
-- declared CRK.⟦ C ⟧ ≋ ζ by unfolding both into amplitudes (86 s and
-- 107 s for the Toffoli circuit, against under one through these).

crk-renumbered-≋ :
  (C : CRK.Circuit n) (ζ : PathSum n k′ m′)
  (js : List (Fin (CRK.paths C))) →
  (k≡k′ : CRK.norm C ≡ k′) (m′≡p : m′ ≡ CRK.paths C) →
  {True (congruent? (fronts js CRK.⟦ C ⟧)
                    (subst (PathSum n k′) m′≡p ζ))} →
  CRK.⟦ C ⟧ ≋ ζ
crk-renumbered-≋ C ζ js k≡k′ m′≡p {t} =
  renumbered-≋ CRK.⟦ C ⟧ ζ js k≡k′ m′≡p {t}

crk-≋-trans : (C : CRK.Circuit n) (ζ : PathSum n k′ m′)
              (χ : PathSum n k″ m″) →
              CRK.⟦ C ⟧ ≋ ζ → ζ ≋ χ → CRK.⟦ C ⟧ ≋ χ
crk-≋-trans C ζ χ = ≋-trans {ξ = CRK.⟦ C ⟧} {ζ = ζ} {χ = χ}

-- Statements about a larger circuit, by name.  A type such as
-- CRK.⟦ C ⟧ ≋ ζ written out at a closed C is not recognised as the type
-- a lemma concludes, even through the wrappers above, once the circuit
-- is large: Agda compares the two by unfolding them, which for the
-- seventeen-column controlled-T circuit of example 3.4 had not finished
-- after ten minutes (the seven-T Toffoli circuit takes a second).
-- Stated through these names, whose arguments are the circuit itself,
-- a closed instance is matched by its arguments, in a second.  Each
-- name unfolds to what it says (by refl).

-- The circuit's path-sum is ζ.

Implements : CRK.Circuit n → PathSum n k′ m′ → Set
Implements C ζ = CRK.⟦ C ⟧ ≋ ζ

-- With input i set to 0, the circuit's path-sum is ζ.

Literal₀ : CRK.Circuit n → Fin n → PathSum n k′ m′ → Set
Literal₀ C i ζ = set0 i CRK.⟦ C ⟧ ≋ ζ

-- On the inputs whose qubit i is |0⟩ (an ancilla), the circuit is ζ.

Implements₀ : CRK.Circuit n → Fin n → PathSum n k′ m′ → Set
Implements₀ C i ζ = CRK.⟦ C ⟧ ≋[ i ]₀ ζ

-- From an input whose qubit i is |0⟩ the circuit never reaches an
-- output whose qubit i is |1⟩: it returns the ancilla clean.

Clean₀ : CRK.Circuit n → Fin n → Set
Clean₀ {n} C i = ∀ (x z : Assign n) → x i ≡ false → z i ≡ true →
                 amp CRK.⟦ C ⟧ x z ≐ 0ᴬ

-- The same wrappers as above, concluding with these names.

crk-implements :
  (C : CRK.Circuit n) (ζ : PathSum n k′ m′)
  (js : List (Fin (CRK.paths C))) →
  (k≡k′ : CRK.norm C ≡ k′) (m′≡p : m′ ≡ CRK.paths C) →
  {True (congruent? (fronts js CRK.⟦ C ⟧)
                    (subst (PathSum n k′) m′≡p ζ))} →
  Implements C ζ
crk-implements C ζ js k≡k′ m′≡p {t} =
  renumbered-≋ CRK.⟦ C ⟧ ζ js k≡k′ m′≡p {t}

crk-implements-trans : (C : CRK.Circuit n) (ζ : PathSum n k′ m′)
                       (χ : PathSum n k″ m″) →
                       Implements C ζ → ζ ≋ χ → Implements C χ
crk-implements-trans C ζ χ = ≋-trans {ξ = CRK.⟦ C ⟧} {ζ = ζ} {χ = χ}

crk-literal₀ :
  (C : CRK.Circuit n) (i : Fin n) (ζ : PathSum n k′ m′)
  (js : List (Fin (CRK.paths C))) →
  (k≡k′ : CRK.norm C ≡ k′) (m′≡p : m′ ≡ CRK.paths C) →
  {True (congruent? (fronts js (set0 i CRK.⟦ C ⟧))
                    (subst (PathSum n k′) m′≡p ζ))} →
  Literal₀ C i ζ
crk-literal₀ C i ζ js k≡k′ m′≡p {t} =
  renumbered-≋ (set0 i CRK.⟦ C ⟧) ζ js k≡k′ m′≡p {t}

crk-implements₀ : (C : CRK.Circuit n) (i : Fin n) (ζ : PathSum n k′ m′)
                  (χ : PathSum n k″ m″) →
                  Literal₀ C i ζ → ζ ≋ χ → Implements₀ C i χ
crk-implements₀ C i ζ χ e₁ e₂ = set0-≋ i CRK.⟦ C ⟧ χ
  (≋-trans {ξ = set0 i CRK.⟦ C ⟧} {ζ = ζ} {χ = χ} e₁ e₂)

crk-clean₀ : (C : CRK.Circuit n) (i : Fin n) (ζ : PathSum n k′ m′) →
             Implements₀ C i ζ →
             (∀ (x : Assign n) (y : Assign m′) → eval (out ζ i) x y ≡ 0ℤ) →
             Clean₀ C i
crk-clean₀ C i ζ eq out0 =
  clean-ancilla {ξ = CRK.⟦ C ⟧} {ζ = ζ} i eq out0

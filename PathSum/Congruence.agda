------------------------------------------------------------------------
-- Presentations of groups
--
-- Syntactically congruent path-sums are equivalent, and the end of a
-- reduction checked by computation
--
-- Two path-sums with the same normalisation and the same number of
-- path variables denote the same operator when their phases agree
-- modulo 2^M and their outputs modulo 2, coefficient by coefficient:
-- then every path carries the same phase and hits the same state
-- (amp-≈, ≈-≋).  This is PathSum.Identity's criterion id-if with the
-- identity replaced by any path-sum; Congruent is the hypothesis, and
-- being coefficient-wise it is decidable (congruent?).  The same holds
-- after renumbering the path variables of one side (renumbered-≋, by
-- PathSum.Anywhere.Sound.front-≋), which is how a circuit's path-sum,
-- whose variables come newest first, is matched with the paper's
-- literal, whose variables come in the order the Hadamards introduce
-- them.
--
-- A reduction chain is checked by that means at its end.  phasePS e is
-- the global phase |x⟩ ↦ e^{2πi e/2^M} |x⟩, with idPS its case e = 0.
-- When a chain ξ ⟶* ξ′ ends at a path-sum without path variables that
-- is congruent to idPS or to phasePS e, proposition 3.1 along the chain
-- makes ξ equivalent to it (reduces-to-id!, reduces-to-phase!, and
-- their counterparts for the rules at any path variable,
-- reduces-to-idᵍ! and reduces-to-phaseᵍ!).  The congruence is an
-- implicit True argument, filled in by computing the decision, so
-- a worked example is its chain and nothing else.
--
-- Congruence is sufficient, not necessary: path-sums with path
-- variables can be equivalent without being congruent (the whole
-- point of the rewrite rules).  At no normalisation and no path
-- variables it is also necessary for the identity
-- (PathSum.Syntactic.id⇔syntactic).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Congruence (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (all?)
open import Data.Integer.Base using (ℤ; +_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; subst)
open import Relation.Nullary.Decidable using
  (Dec; True; toWitness; _×?_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Polynomial hiding (subst)
open import PathSum.Polynomial.Properties using (eval-≈)
open import PathSum.Polynomial.Decidable using (_≈?[_]_)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (_⟶*_)
open import PathSum.Reorder using (front)
open import PathSum.Anywhere M using (_⟶ᵍ*_)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; 0ᴬ; zpow-cong; Σᴮ-cong; scale-map)
open import PathSum.Denotation M₀ using
  (amp; _≋_; ≋-refl; ≋-trans; hits-cong; semantics)
open import PathSum.Anywhere.Sound M₀ using (≋-front; ⟶ᵍ*-sound)

import PathSum.Clifford
module Cliff = PathSum.Clifford M₀ semantics

private
  variable
    n k k′ m : ℕ


------------------------------------------------------------------------
-- Syntactic congruence

-- Outputs congruent modulo 2 and phases modulo 2^M.  The two
-- normalisations may differ; equivalence needs them equal.

Congruent : PathSum n k m → PathSum n k′ m → Set
Congruent ξ ζ =
  (∀ w → out ξ w ≈[ + 2 ] out ζ w) × phase ξ ≈[ pow M ] phase ζ

congruent? : (ξ : PathSum n k m) (ζ : PathSum n k′ m) →
             Dec (Congruent ξ ζ)
congruent? ξ ζ =
  all? (λ w → out ξ w ≈?[ + 2 ] out ζ w) ×?
  (phase ξ ≈?[ pow M ] phase ζ)


------------------------------------------------------------------------
-- Congruent path-sums have the same amplitudes

private
  if-cong : {b b′ : Bool} {a a′ : Amp} → b ≡ b′ → a ≐ a′ →
            (if b then a else 0ᴬ) ≐ (if b′ then a′ else 0ᴬ)
  if-cong {b = true}  {true}  _ h i = h i
  if-cong {b = false} {false} _ _ i = refl

-- Path by path: the same state is hit, with the same power of ζ.  The
-- modulus 2^M of the phases is the order N of ζ.

amp-≈ : (ξ : PathSum n k m) (ζ : PathSum n k′ m) →
        (∀ w → out ξ w ≈[ + 2 ] out ζ w) → phase ξ ≈[ pow M ] phase ζ →
        ∀ x z → amp ξ x z ≐ amp ζ x z
amp-≈ ξ ζ eqf eqP x z = Σᴮ-cong (λ y →
  if-cong (hits-cong ξ ζ eqf x y z)
          (zpow-cong {eval (phase ξ) x y} {eval (phase ζ) x y}
                     (eval-≈ (phase ξ) (phase ζ) eqP x y)))

≈-≋ : (ξ ζ : PathSum n k m) →
      (∀ w → out ξ w ≈[ + 2 ] out ζ w) → phase ξ ≈[ pow M ] phase ζ →
      ξ ≋ ζ
≈-≋ {k = k} ξ ζ eqf eqP x z = scale-map k (amp-≈ ξ ζ eqf eqP x z)

-- The normalisations are separate indices, equated by a proof, so
-- that the conclusion is stated at the normalisations of ξ's and ζ's
-- own types: a worked example often has one written as a numeral and
-- the other as the norm of a circuit.

congruent-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m) → k ≡ k′ →
              Congruent ξ ζ → ξ ≋ ζ
congruent-≋ ξ ζ refl (eqf , eqP) = ≈-≋ ξ ζ eqf eqP

-- With the congruence checked by computation.

congruent-≋! : (ξ : PathSum n k m) (ζ : PathSum n k′ m) → k ≡ k′ →
               {True (congruent? ξ ζ)} → ξ ≋ ζ
congruent-≋! ξ ζ k≡k′ {t} =
  congruent-≋ ξ ζ k≡k′ (toWitness {a? = congruent? ξ ζ} t)


------------------------------------------------------------------------
-- Congruent after renumbering

-- A sequence of moves of path variables to the front
-- (PathSum.Reorder.front), applied from the left.

fronts : List (Fin m) → PathSum n k m → PathSum n k m
fronts {m = zero}  js       ξ = ξ
fronts {m = suc m} []       ξ = ξ
fronts {m = suc m} (j ∷ js) ξ = fronts js (front j ξ)

fronts-≋ : (js : List (Fin m)) (ξ : PathSum n k m) → ξ ≋ fronts js ξ
fronts-≋ {m = zero}  js       ξ = ≋-refl {ξ = ξ}
fronts-≋ {m = suc m} []       ξ = ≋-refl {ξ = ξ}
fronts-≋ {m = suc m} (j ∷ js) ξ =
  ≋-trans {ξ = ξ} {ζ = front j ξ} {χ = fronts js (front j ξ)}
    (≋-front j ξ) (fronts-≋ js (front j ξ))

-- A path-sum that some renumbering makes congruent to ζ is equivalent
-- to ζ.  Both normalisations and both numbers of path variables are
-- separate indices, equated by proofs, so that the conclusion is
-- stated at the indices of ξ's and ζ's own types.  (Two statements of
-- the same equivalence that differ in such an index, or in anything
-- else, are compared by unfolding _≋_ into the amplitudes, which for
-- a closed path-sum costs tens of seconds.)

renumbered-≋ : ∀ {k′ m′} (ξ : PathSum n k m) (ζ : PathSum n k′ m′)
               (js : List (Fin m)) (k≡k′ : k ≡ k′) (m′≡m : m′ ≡ m) →
               {True (congruent? (fronts js ξ)
                                 (subst (PathSum n k′) m′≡m ζ))} →
               ξ ≋ ζ
renumbered-≋ ξ ζ js refl refl {t} =
  ≋-trans {ξ = ξ} {ζ = fronts js ξ} {χ = ζ} (fronts-≋ js ξ)
    (congruent-≋ (fronts js ξ) ζ refl
                 (toWitness {a? = congruent? (fronts js ξ) ζ} t))


------------------------------------------------------------------------
-- The identity and global phases, syntactically

-- |x⟩ ↦ e^{2πi e/2^M} |x⟩; phasePS 0ℤ is idPS up to the congruence.

phasePS : ℤ → PathSum n 0 0
phasePS e = ⟨ κ e , (λ w → μ x[ w ]) ⟩

-- The identity's polynomials, and a global phase's.

Id-syntactic : PathSum n 0 0 → Set
Id-syntactic ξ = Congruent ξ idPS

id-syntactic? : (ξ : PathSum n 0 0) → Dec (Id-syntactic ξ)
id-syntactic? ξ = congruent? ξ idPS

Phase-syntactic : ℤ → PathSum n 0 0 → Set
Phase-syntactic e ξ = Congruent ξ (phasePS e)

phase-syntactic? : (e : ℤ) (ξ : PathSum n 0 0) →
                   Dec (Phase-syntactic e ξ)
phase-syntactic? e ξ = congruent? ξ (phasePS e)

id-syntactic-≋ : (ξ : PathSum n 0 0) → Id-syntactic ξ → ξ ≋ idPS
id-syntactic-≋ ξ = congruent-≋ ξ idPS refl

phase-syntactic-≋ : (e : ℤ) (ξ : PathSum n 0 0) → Phase-syntactic e ξ →
                    ξ ≋ phasePS e
phase-syntactic-≋ e ξ = congruent-≋ ξ (phasePS e) refl


------------------------------------------------------------------------
-- The end of a reduction chain, checked by computation

-- Proposition 3.1 along the chain, then the syntactic end.  The
-- path-sums are passed to ≋-trans explicitly, since _≋_ matches on
-- both normalisations and none of them is recoverable by unification.

reduces-to-id! : ∀ {k m} {ξ : PathSum n k m} {ξ′ : PathSum n 0 0} →
                 ξ ⟶* ξ′ → {True (id-syntactic? ξ′)} → ξ ≋ idPS
reduces-to-id! {ξ = ξ} {ξ′} steps {t} =
  ≋-trans {ξ = ξ} {ζ = ξ′} {χ = idPS} (Cliff.⟶*-sound steps)
          (id-syntactic-≋ ξ′ (toWitness {a? = id-syntactic? ξ′} t))

reduces-to-phase! : ∀ {k m} {ξ : PathSum n k m} {ξ′ : PathSum n 0 0}
                    (e : ℤ) → ξ ⟶* ξ′ → {True (phase-syntactic? e ξ′)} →
                    ξ ≋ phasePS e
reduces-to-phase! {ξ = ξ} {ξ′} e steps {t} =
  ≋-trans {ξ = ξ} {ζ = ξ′} {χ = phasePS e} (Cliff.⟶*-sound steps)
    (phase-syntactic-≋ e ξ′ (toWitness {a? = phase-syntactic? e ξ′} t))

-- The same for chains of rules at any path variable.

reduces-to-idᵍ! : ∀ {k m} {ξ : PathSum n k m} {ξ′ : PathSum n 0 0} →
                  ξ ⟶ᵍ* ξ′ → {True (id-syntactic? ξ′)} → ξ ≋ idPS
reduces-to-idᵍ! {ξ = ξ} {ξ′} steps {t} =
  ≋-trans {ξ = ξ} {ζ = ξ′} {χ = idPS} (⟶ᵍ*-sound steps)
          (id-syntactic-≋ ξ′ (toWitness {a? = id-syntactic? ξ′} t))

reduces-to-phaseᵍ! : ∀ {k m} {ξ : PathSum n k m} {ξ′ : PathSum n 0 0}
                     (e : ℤ) → ξ ⟶ᵍ* ξ′ →
                     {True (phase-syntactic? e ξ′)} → ξ ≋ phasePS e
reduces-to-phaseᵍ! {ξ = ξ} {ξ′} e steps {t} =
  ≋-trans {ξ = ξ} {ζ = ξ′} {χ = phasePS e} (⟶ᵍ*-sound steps)
    (phase-syntactic-≋ e ξ′ (toWitness {a? = phase-syntactic? e ξ′} t))

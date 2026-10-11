------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 37.2: RCliff₂ is minimal
--
-- The separators of Figure 8(b).  The weighted ones are here; (CF) and
-- (CZr) are separated by projective substitutions (Projective).
-- arg det₂ weighs −1, H and Z by multiples of 2π, and CNOT and σ by π.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Real-Clifford.Minimality where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Real-Clifford.Syntactics
import Examples.Independence.Real-Clifford.Projective as Projective
open import Examples.Independence.Model Gate
open Separators arity lhs rhs

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- What the separators look at

is-neg is-H is-Z is-CX : Gate n → Bool
is-neg m-gate = true
is-neg _      = false
is-H H-gate   = true
is-H _        = false
is-Z Z-gate   = true
is-Z _        = false
is-CX CX-gate = true
is-CX _       = false

#neg #Z none : Gate n → ℕ
#neg m-gate = 1
#neg _      = 0
#Z Z-gate   = 1
#Z _        = 0
none _ = 0

-- arg det in units of π/4: every gate has determinant −1.
ad : Gate n → ℕ
ad _ = 4

------------------------------------------------------------------------
-- The weighted separators (Figure 8(b))

-- (−²): ?−.
module Sep-−² where
  open Weighted has (occurs is-neg) refl
  open Sep −² 0
  open Check (λ
    { −² ne _ → ⊥-elim (ne refl) ; H² _ () ; Z² _ () ; F _ () ; CX² _ ()
    ; B _ () ; ZC _ () ; CZr _ () ; CF _ () ; I _ () })

  independent : Independent-axiom −²
  independent = separates z≤n (λ ())

-- (H²): ?H.
module Sep-H² where
  open Weighted has (occurs is-H) refl
  open Sep H² 1
  open Check (λ
    { −² _ _ → refl ; H² ne _ → ⊥-elim (ne refl) ; Z² _ _ → refl
    ; F _ _ → refl ; CX² _ (s≤s ()) ; B _ (s≤s ()) ; ZC _ (s≤s ())
    ; CZr _ (s≤s ()) ; CF _ (s≤s ()) ; I _ (s≤s ()) })

  independent : Independent-axiom H²
  independent = separates (s≤s z≤n) (λ ())

-- (Z²): ?Z.
module Sep-Z² where
  open Weighted has (occurs is-Z) refl
  open Sep Z² 1
  open Check (λ
    { −² _ _ → refl ; H² _ _ → refl ; Z² ne _ → ⊥-elim (ne refl)
    ; F _ _ → refl ; CX² _ (s≤s ()) ; B _ (s≤s ()) ; ZC _ (s≤s ())
    ; CZr _ (s≤s ()) ; CF _ (s≤s ()) ; I _ (s≤s ()) })

  independent : Independent-axiom Z²
  independent = separates (s≤s z≤n) (λ ())

-- (F): #{−}[2].
module Sep-F where
  open Weighted (count 2) (counts #neg 0) refl
  open Sep F 1
  open Check (λ
    { −² _ _ → refl ; H² _ _ → refl ; Z² _ _ → refl
    ; F ne _ → ⊥-elim (ne refl) ; CX² _ (s≤s ()) ; B _ (s≤s ())
    ; ZC _ (s≤s ()) ; CZr _ (s≤s ()) ; CF _ (s≤s ()) ; I _ (s≤s ()) })

  independent : Independent-axiom F
  independent = separates (s≤s z≤n) (λ ())

-- (CX²): ?CX.
module Sep-CX² where
  open Weighted has (occurs is-CX) refl
  open Sep CX² 2
  open Check (λ
    { −² _ _ → refl ; H² _ _ → refl ; Z² _ _ → refl ; F _ _ → refl
    ; CX² ne _ → ⊥-elim (ne refl) ; B _ _ → refl ; ZC _ _ → refl
    ; CZr _ _ → refl ; CF _ _ → refl ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom CX²
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (B): #{σ}[2].
module Sep-B where
  open Weighted (count 2) (counts none 1) refl
  open Sep B 2
  open Check (λ
    { −² _ _ → refl ; H² _ _ → refl ; Z² _ _ → refl ; F _ _ → refl
    ; CX² _ _ → refl ; B ne _ → ⊥-elim (ne refl) ; ZC _ _ → refl
    ; CZr _ _ → refl ; CF _ _ → refl ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom B
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (ZC): #{Z}[2].
module Sep-ZC where
  open Weighted (count 2) (counts #Z 0) refl
  open Sep ZC 2
  open Check (λ
    { −² _ _ → refl ; H² _ _ → refl ; Z² _ _ → refl ; F _ _ → refl
    ; CX² _ _ → refl ; B _ _ → refl ; ZC ne _ → ⊥-elim (ne refl)
    ; CZr _ _ → refl ; CF _ _ → refl ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom ZC
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (I): arg det₂.
module Sep-I where
  open Weighted (count 8) (argdet 2 ad) refl
  open Sep I 3
  open Check (λ
    { −² _ _ → refl ; H² _ _ → refl ; Z² _ _ → refl ; F _ _ → refl
    ; CX² _ _ → refl ; B _ _ → refl ; ZC _ _ → refl ; CZr _ _ → refl
    ; CF _ _ → refl ; I ne _ → ⊥-elim (ne refl) })

  independent : Independent-axiom I
  independent = separates (s≤s (s≤s (s≤s z≤n))) (λ ())

------------------------------------------------------------------------
-- Theorem 37.2

minimal : Minimal
minimal −²  = Sep-−².independent
minimal H²  = Sep-H².independent
minimal Z²  = Sep-Z².independent
minimal F   = Sep-F.independent
minimal CX² = Sep-CX².independent
minimal B   = Sep-B.independent
minimal ZC  = Sep-ZC.independent
minimal CZr = Projective.Sep-CZr.independent
minimal CF  = Projective.Sep-CF.independent
minimal I   = Sep-I.independent

------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 37.1: Cliff₂ is minimal
--
-- One separator per axiom, those of Figure 8(a): an occurrence
-- detector ?g, a count #{…}[m], or the determinant phase arg det₂.
-- Each module checks the other axioms of arity at most that of the
-- separated one, by evaluation, and then that the separated one
-- fails; Separators turns this into independence from all the other
-- axioms, whatever their arity.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford.Minimality where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Negation using (¬_)

open import Examples.Independence.Clifford.Syntactics
open import Examples.Independence.Model Gate
open Separators _SRel,_===_

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- What the separators look at

is-ω is-H is-S is-CX : Gate n → Bool
is-ω ω-gate  = true
is-ω _       = false
is-H H-gate  = true
is-H _       = false
is-S S-gate  = true
is-S _       = false
is-CX CX-gate = true
is-CX _       = false

#H #CX : Gate n → ℕ
#H H-gate   = 1
#H _        = 0
#CX CX-gate = 1
#CX _       = 0

none : Gate n → ℕ
none _ = 0

-- arg det of each gate, in units of π/4: det ω = e^{iπ/4},
-- det H = −1, det S = i, det CX = −1.
ad : Gate n → ℕ
ad ω-gate  = 1
ad H-gate  = 4
ad S-gate  = 2
ad CX-gate = 4

------------------------------------------------------------------------
-- The separators (Figure 8(a))

-- (ω⁸): ?ω.
module Sep-ω⁸ where
  open Weighted has (occurs is-ω) refl
  open Sep ω⁸ 0
  open Check (λ
    { ω⁸ ne _ → ⊥-elim (ne refl) ; H² _ () ; S⁴ _ () ; E _ ()
    ; CPh _ () ; B _ () ; CZ _ () ; I _ () })

  independent : Independent-axiom ω⁸
  independent = separates z≤n (λ ())

-- (H²): ?H.
module Sep-H² where
  open Weighted has (occurs is-H) refl
  open Sep H² 1
  open Check (λ
    { ω⁸ _ _ → refl ; H² ne _ → ⊥-elim (ne refl) ; S⁴ _ _ → refl
    ; E _ _ → refl ; CPh _ (s≤s ()) ; B _ (s≤s ()) ; CZ _ (s≤s ())
    ; I _ (s≤s ()) })

  independent : Independent-axiom H²
  independent = separates (s≤s z≤n) (λ ())

-- (S⁴): ?S.
module Sep-S⁴ where
  open Weighted has (occurs is-S) refl
  open Sep S⁴ 1
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ ne _ → ⊥-elim (ne refl)
    ; E _ _ → refl ; CPh _ (s≤s ()) ; B _ (s≤s ()) ; CZ _ (s≤s ())
    ; I _ (s≤s ()) })

  independent : Independent-axiom S⁴
  independent = separates (s≤s z≤n) (λ ())

-- (E): #{H}[2].
module Sep-E where
  open Weighted (count 2) (counts #H 0) refl
  open Sep E 1
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl
    ; E ne _ → ⊥-elim (ne refl) ; CPh _ (s≤s ()) ; B _ (s≤s ())
    ; CZ _ (s≤s ()) ; I _ (s≤s ()) })

  independent : Independent-axiom E
  independent = separates (s≤s z≤n) (λ ())

-- (CPh): ?CX.
module Sep-CPh where
  open Weighted has (occurs is-CX) refl
  open Sep CPh 2
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl ; E _ _ → refl
    ; CPh ne _ → ⊥-elim (ne refl) ; B _ _ → refl ; CZ _ _ → refl
    ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom CPh
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (B): #{σ}[2].
module Sep-B where
  open Weighted (count 2) (counts none 1) refl
  open Sep B 2
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl ; E _ _ → refl
    ; CPh _ _ → refl ; B ne _ → ⊥-elim (ne refl) ; CZ _ _ → refl
    ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom B
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (CZ): #{CX, σ}[2].  It does not respect (I), whose sides carry three
-- CNOTs and two swaps against two CNOTs (not-a-model-of-I); but (I)
-- acts on three wires, and a derivation of the two-wire (CZ) cannot
-- use it.
module Sep-CZ where
  open Weighted (count 2) (counts #CX 1) refl
  open Sep CZ 2

  not-a-model-of-I : ¬ Respects I
  not-a-model-of-I ()
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl ; E _ _ → refl
    ; CPh _ _ → refl ; B _ _ → refl ; CZ ne _ → ⊥-elim (ne refl)
    ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom CZ
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (I): arg det₂.
module Sep-I where
  open Weighted (count 8) (argdet 2 ad) refl
  open Sep I 3
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl ; E _ _ → refl
    ; CPh _ _ → refl ; B _ _ → refl ; CZ _ _ → refl
    ; I ne _ → ⊥-elim (ne refl) })

  independent : Independent-axiom I
  independent = separates (s≤s (s≤s (s≤s z≤n))) (λ ())

------------------------------------------------------------------------
-- Theorem 37.1

minimal : Minimal
minimal ω⁸  = Sep-ω⁸.independent
minimal H²  = Sep-H².independent
minimal S⁴  = Sep-S⁴.independent
minimal E   = Sep-E.independent
minimal CPh = Sep-CPh.independent
minimal B   = Sep-B.independent
minimal CZ  = Sep-CZ.independent
minimal I   = Sep-I.independent

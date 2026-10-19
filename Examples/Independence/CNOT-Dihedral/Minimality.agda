------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 37.6: CNOTdihe₂ is minimal
--
-- The separators of Figure 8(f), all weighted: occurrence detectors,
-- counts, and arg det₃, which weighs T by π and every other generator
-- by a multiple of 2π.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.CNOT-Dihedral.Minimality where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.CNOT-Dihedral.Syntactics
open import Examples.Independence.Model Gate
open Separators _SRel,_===_

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- What the separators look at

is-ω is-X is-T is-CX : Gate n → Bool
is-ω ω-gate   = true
is-ω _        = false
is-X X-gate   = true
is-X _        = false
is-T T-gate   = true
is-T _        = false
is-CX CX-gate = true
is-CX _       = false

#ω #X #CX #T2ω none : Gate n → ℕ
#ω ω-gate   = 1
#ω _        = 0
#X X-gate   = 1
#X _        = 0
#CX CX-gate = 1
#CX _       = 0
-- #{T, ω, ω}: T once, ω twice.
#T2ω T-gate = 1
#T2ω ω-gate = 2
#T2ω _      = 0
none _ = 0

-- arg det in units of π/4: det ω = e^{iπ/4}, det X = −1,
-- det T = e^{iπ/4}, det CX = −1.
ad : Gate n → ℕ
ad ω-gate  = 1
ad X-gate  = 4
ad T-gate  = 1
ad CX-gate = 4

------------------------------------------------------------------------
-- The separators (Figure 8(f))

-- (ω⁸): ?ω.
module Sep-ω⁸ where
  open Weighted has (occurs is-ω) refl
  open Sep ω⁸ 0
  open Check (λ
    { ω⁸ ne _ → ⊥-elim (ne refl) ; X² _ () ; T⁸ _ () ; TX _ () ; XC _ ()
    ; B _ () ; ZC _ () ; CPh _ () ; I _ () ; C²T _ () ; C³T _ () })

  independent : Independent-axiom ω⁸
  independent = separates z≤n (λ ())

-- (X²): ?X.
module Sep-X² where
  open Weighted has (occurs is-X) refl
  open Sep X² 1
  open Check (λ
    { ω⁸ _ _ → refl ; X² ne _ → ⊥-elim (ne refl) ; T⁸ _ _ → refl
    ; TX _ _ → refl ; XC _ (s≤s ()) ; B _ (s≤s ()) ; ZC _ (s≤s ())
    ; CPh _ (s≤s ()) ; I _ (s≤s ()) ; C²T _ (s≤s ()) ; C³T _ (s≤s ()) })

  independent : Independent-axiom X²
  independent = separates (s≤s z≤n) (λ ())

-- (T⁸): ?T.
module Sep-T⁸ where
  open Weighted has (occurs is-T) refl
  open Sep T⁸ 1
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ ne _ → ⊥-elim (ne refl)
    ; TX _ _ → refl ; XC _ (s≤s ()) ; B _ (s≤s ()) ; ZC _ (s≤s ())
    ; CPh _ (s≤s ()) ; I _ (s≤s ()) ; C²T _ (s≤s ()) ; C³T _ (s≤s ()) })

  independent : Independent-axiom T⁸
  independent = separates (s≤s z≤n) (λ ())

-- (TX): #{ω}[2].
module Sep-TX where
  open Weighted (count 2) (counts #ω 0) refl
  open Sep TX 1
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ _ _ → refl
    ; TX ne _ → ⊥-elim (ne refl) ; XC _ (s≤s ()) ; B _ (s≤s ())
    ; ZC _ (s≤s ()) ; CPh _ (s≤s ()) ; I _ (s≤s ()) ; C²T _ (s≤s ())
    ; C³T _ (s≤s ()) })

  independent : Independent-axiom TX
  independent = separates (s≤s z≤n) (λ ())

-- (XC): #{X}[2].
module Sep-XC where
  open Weighted (count 2) (counts #X 0) refl
  open Sep XC 2
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ _ _ → refl ; TX _ _ → refl
    ; XC ne _ → ⊥-elim (ne refl) ; B _ _ → refl ; ZC _ _ → refl
    ; CPh _ _ → refl ; I _ (s≤s (s≤s ())) ; C²T _ (s≤s (s≤s ()))
    ; C³T _ (s≤s (s≤s ())) })

  independent : Independent-axiom XC
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (CPh): ?CX.
module Sep-CPh where
  open Weighted has (occurs is-CX) refl
  open Sep CPh 2
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ _ _ → refl ; TX _ _ → refl
    ; XC _ _ → refl ; B _ _ → refl ; ZC _ _ → refl
    ; CPh ne _ → ⊥-elim (ne refl) ; I _ (s≤s (s≤s ()))
    ; C²T _ (s≤s (s≤s ())) ; C³T _ (s≤s (s≤s ())) })

  independent : Independent-axiom CPh
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (B): #{σ}[2].
module Sep-B where
  open Weighted (count 2) (counts none 1) refl
  open Sep B 2
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ _ _ → refl ; TX _ _ → refl
    ; XC _ _ → refl ; B ne _ → ⊥-elim (ne refl) ; ZC _ _ → refl
    ; CPh _ _ → refl ; I _ (s≤s (s≤s ())) ; C²T _ (s≤s (s≤s ()))
    ; C³T _ (s≤s (s≤s ())) })

  independent : Independent-axiom B
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (ZC): #{T, ω, ω}[8].
module Sep-ZC where
  open Weighted (count 8) (counts #T2ω 0) refl
  open Sep ZC 2
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ _ _ → refl ; TX _ _ → refl
    ; XC _ _ → refl ; B _ _ → refl ; ZC ne _ → ⊥-elim (ne refl)
    ; CPh _ _ → refl ; I _ (s≤s (s≤s ())) ; C²T _ (s≤s (s≤s ()))
    ; C³T _ (s≤s (s≤s ())) })

  independent : Independent-axiom ZC
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (I): #{CX, σ}[2].
module Sep-I where
  open Weighted (count 2) (counts #CX 1) refl
  open Sep I 3
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ _ _ → refl ; TX _ _ → refl
    ; XC _ _ → refl ; B _ _ → refl ; ZC _ _ → refl ; CPh _ _ → refl
    ; I ne _ → ⊥-elim (ne refl) ; C²T _ _ → refl
    ; C³T _ (s≤s (s≤s (s≤s ()))) })

  independent : Independent-axiom I
  independent = separates (s≤s (s≤s (s≤s z≤n))) (λ ())

-- (C²T): #{T, ω, ω}[4].
module Sep-C²T where
  open Weighted (count 4) (counts #T2ω 0) refl
  open Sep C²T 3
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ _ _ → refl ; TX _ _ → refl
    ; XC _ _ → refl ; B _ _ → refl ; ZC _ _ → refl ; CPh _ _ → refl
    ; I _ _ → refl ; C²T ne _ → ⊥-elim (ne refl)
    ; C³T _ (s≤s (s≤s (s≤s ()))) })

  independent : Independent-axiom C²T
  independent = separates (s≤s (s≤s (s≤s z≤n))) (λ ())

-- (C³T): arg det₃.
module Sep-C³T where
  open Weighted (count 8) (argdet 3 ad) refl
  open Sep C³T 4
  open Check (λ
    { ω⁸ _ _ → refl ; X² _ _ → refl ; T⁸ _ _ → refl ; TX _ _ → refl
    ; XC _ _ → refl ; B _ _ → refl ; ZC _ _ → refl ; CPh _ _ → refl
    ; I _ _ → refl ; C²T _ _ → refl ; C³T ne _ → ⊥-elim (ne refl) })

  independent : Independent-axiom C³T
  independent = separates (s≤s (s≤s (s≤s (s≤s z≤n)))) (λ ())

------------------------------------------------------------------------
-- Theorem 37.6

minimal : Minimal
minimal ω⁸  = Sep-ω⁸.independent
minimal X²  = Sep-X².independent
minimal T⁸  = Sep-T⁸.independent
minimal TX  = Sep-TX.independent
minimal XC  = Sep-XC.independent
minimal B   = Sep-B.independent
minimal ZC  = Sep-ZC.independent
minimal CPh = Sep-CPh.independent
minimal I   = Sep-I.independent
minimal C²T = Sep-C²T.independent
minimal C³T = Sep-C³T.independent

------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 37.4: CliffT₂ is minimal up to one qubit, and its two-qubit
-- axioms (CPh), (B) and (CZ) are independent
--
-- The separators of Figure 8(d).  The paper has none for (CSH), (HT²)
-- and (HTH), but the two-qubit separators are checked against them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford+T.Minimality where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Clifford+T.Syntactics
open import Examples.Independence.Model Gate
open Separators _SRel,_===_

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- What the separators look at

is-ω is-H is-T is-CX : Gate n → Bool
is-ω ω-gate   = true
is-ω _        = false
is-H H-gate   = true
is-H _        = false
is-T T-gate   = true
is-T _        = false
is-CX CX-gate = true
is-CX _       = false

#H #HTω #CX none : Gate n → ℕ
#H H-gate    = 1
#H _         = 0
#HTω CX-gate = 0
#HTω _       = 1
#CX CX-gate  = 1
#CX _        = 0
none _ = 0

------------------------------------------------------------------------
-- The separators (Figure 8(d))

-- (ω⁸): ?ω.
module Sep-ω⁸ where
  open Weighted has (occurs is-ω) refl
  open Sep ω⁸ 0
  open Check (λ
    { ω⁸ ne _ → ⊥-elim (ne refl) ; T⁸ _ () ; H² _ () ; E _ () ; TX _ ()
    ; CPh _ () ; B _ () ; CZ _ () ; CSH _ () ; HT² _ () ; HTH _ () })

  independent : Independent-axiom ω⁸
  independent = separates z≤n (λ ())

-- (H²): ?H.
module Sep-H² where
  open Weighted has (occurs is-H) refl
  open Sep H² 1
  open Check (λ
    { ω⁸ _ _ → refl ; T⁸ _ _ → refl ; H² ne _ → ⊥-elim (ne refl)
    ; E _ _ → refl ; TX _ _ → refl ; CPh _ (s≤s ()) ; B _ (s≤s ())
    ; CZ _ (s≤s ()) ; CSH _ (s≤s ()) ; HT² _ (s≤s ()) ; HTH _ (s≤s ()) })

  independent : Independent-axiom H²
  independent = separates (s≤s z≤n) (λ ())

-- (T⁸): ?T.
module Sep-T⁸ where
  open Weighted has (occurs is-T) refl
  open Sep T⁸ 1
  open Check (λ
    { ω⁸ _ _ → refl ; T⁸ ne _ → ⊥-elim (ne refl) ; H² _ _ → refl
    ; E _ _ → refl ; TX _ _ → refl ; CPh _ (s≤s ()) ; B _ (s≤s ())
    ; CZ _ (s≤s ()) ; CSH _ (s≤s ()) ; HT² _ (s≤s ()) ; HTH _ (s≤s ()) })

  independent : Independent-axiom T⁸
  independent = separates (s≤s z≤n) (λ ())

-- (E): #{H}[2].
module Sep-E where
  open Weighted (count 2) (counts #H 0) refl
  open Sep E 1
  open Check (λ
    { ω⁸ _ _ → refl ; T⁸ _ _ → refl ; H² _ _ → refl
    ; E ne _ → ⊥-elim (ne refl) ; TX _ _ → refl ; CPh _ (s≤s ())
    ; B _ (s≤s ()) ; CZ _ (s≤s ()) ; CSH _ (s≤s ()) ; HT² _ (s≤s ())
    ; HTH _ (s≤s ()) })

  independent : Independent-axiom E
  independent = separates (s≤s z≤n) (λ ())

-- (TX): #{H, T, ω}[2].
module Sep-TX where
  open Weighted (count 2) (counts #HTω 0) refl
  open Sep TX 1
  open Check (λ
    { ω⁸ _ _ → refl ; T⁸ _ _ → refl ; H² _ _ → refl ; E _ _ → refl
    ; TX ne _ → ⊥-elim (ne refl) ; CPh _ (s≤s ()) ; B _ (s≤s ())
    ; CZ _ (s≤s ()) ; CSH _ (s≤s ()) ; HT² _ (s≤s ()) ; HTH _ (s≤s ()) })

  independent : Independent-axiom TX
  independent = separates (s≤s z≤n) (λ ())

-- (CPh): ?CX.
module Sep-CPh where
  open Weighted has (occurs is-CX) refl
  open Sep CPh 2
  open Check (λ
    { ω⁸ _ _ → refl ; T⁸ _ _ → refl ; H² _ _ → refl ; E _ _ → refl
    ; TX _ _ → refl ; CPh ne _ → ⊥-elim (ne refl) ; B _ _ → refl
    ; CZ _ _ → refl ; CSH _ _ → refl ; HT² _ _ → refl ; HTH _ _ → refl })

  independent : Independent-axiom CPh
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (B): #{σ}[2].
module Sep-B where
  open Weighted (count 2) (counts none 1) refl
  open Sep B 2
  open Check (λ
    { ω⁸ _ _ → refl ; T⁸ _ _ → refl ; H² _ _ → refl ; E _ _ → refl
    ; TX _ _ → refl ; CPh _ _ → refl ; B ne _ → ⊥-elim (ne refl)
    ; CZ _ _ → refl ; CSH _ _ → refl ; HT² _ _ → refl ; HTH _ _ → refl })

  independent : Independent-axiom B
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (CZ): #{CX, σ}[2].
module Sep-CZ where
  open Weighted (count 2) (counts #CX 1) refl
  open Sep CZ 2
  open Check (λ
    { ω⁸ _ _ → refl ; T⁸ _ _ → refl ; H² _ _ → refl ; E _ _ → refl
    ; TX _ _ → refl ; CPh _ _ → refl ; B _ _ → refl
    ; CZ ne _ → ⊥-elim (ne refl) ; CSH _ _ → refl ; HT² _ _ → refl
    ; HTH _ _ → refl })

  independent : Independent-axiom CZ
  independent = separates (s≤s (s≤s z≤n)) (λ ())

------------------------------------------------------------------------
-- Theorem 37.4

minimal-upto-1 : Minimal-upto 1
minimal-upto-1 ω⁸ _ = Sep-ω⁸.independent
minimal-upto-1 T⁸ _ = Sep-T⁸.independent
minimal-upto-1 H² _ = Sep-H².independent
minimal-upto-1 E  _ = Sep-E.independent
minimal-upto-1 TX _ = Sep-TX.independent
minimal-upto-1 CPh (s≤s ())
minimal-upto-1 B   (s≤s ())
minimal-upto-1 CZ  (s≤s ())
minimal-upto-1 CSH (s≤s ())
minimal-upto-1 HT² (s≤s ())
minimal-upto-1 HTH (s≤s ())

CPh-independent : Independent-axiom CPh
CPh-independent = Sep-CPh.independent

B-independent : Independent-axiom B
B-independent = Sep-B.independent

CZ-independent : Independent-axiom CZ
CZ-independent = Sep-CZ.independent

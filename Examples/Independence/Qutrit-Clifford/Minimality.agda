------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 37.3: Cliff₃ is minimal up to two qutrits
--
-- The separators of Figure 8(c).  The weighted ones are here; (SS′) is
-- separated by a projective substitution (Projective, Proposition 38).
-- The paper has none for the three-qutrit (I).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Qutrit-Clifford.Minimality where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Qutrit-Clifford.Syntactics
import Examples.Independence.Qutrit-Clifford.Projective as Projective
open import Examples.Independence.Model Gate
open Separators _SRel,_===_

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- What the separators look at

is-ω is-H is-S is-CX : Gate n → Bool
is-ω ω-gate   = true
is-ω _        = false
is-H H-gate   = true
is-H _        = false
is-S S-gate   = true
is-S _        = false
is-CX CX-gate = true
is-CX _       = false

#H #S #CX none : Gate n → ℕ
#H H-gate   = 1
#H _        = 0
#S S-gate   = 1
#S _        = 0
#CX CX-gate = 1
#CX _       = 0
none _ = 0

------------------------------------------------------------------------
-- The weighted separators (Figure 8(c))

-- (ω¹²): ?ω₁₂.
module Sep-ω¹² where
  open Weighted has (occurs is-ω) refl
  open Sep ω¹² 0
  open Check (λ
    { ω¹² ne _ → ⊥-elim (ne refl) ; H⁴ _ () ; S³ _ () ; E _ () ; SS′ _ ()
    ; CPh _ () ; KC _ () ; CZ _ () ; B _ () ; I _ () })

  independent : Independent-axiom ω¹²
  independent = separates z≤n (λ ())

-- (H⁴): ?H.
module Sep-H⁴ where
  open Weighted has (occurs is-H) refl
  open Sep H⁴ 1
  open Check (λ
    { ω¹² _ _ → refl ; H⁴ ne _ → ⊥-elim (ne refl) ; S³ _ _ → refl
    ; E _ _ → refl ; SS′ _ _ → refl ; CPh _ (s≤s ()) ; KC _ (s≤s ())
    ; CZ _ (s≤s ()) ; B _ (s≤s ()) ; I _ (s≤s ()) })

  independent : Independent-axiom H⁴
  independent = separates (s≤s z≤n) (λ ())

-- (S³): ?S.
module Sep-S³ where
  open Weighted has (occurs is-S) refl
  open Sep S³ 1
  open Check (λ
    { ω¹² _ _ → refl ; H⁴ _ _ → refl ; S³ ne _ → ⊥-elim (ne refl)
    ; E _ _ → refl ; SS′ _ _ → refl ; CPh _ (s≤s ()) ; KC _ (s≤s ())
    ; CZ _ (s≤s ()) ; B _ (s≤s ()) ; I _ (s≤s ()) })

  independent : Independent-axiom S³
  independent = separates (s≤s z≤n) (λ ())

-- (E): #{H}[2].
module Sep-E where
  open Weighted (count 2) (counts #H 0) refl
  open Sep E 1
  open Check (λ
    { ω¹² _ _ → refl ; H⁴ _ _ → refl ; S³ _ _ → refl
    ; E ne _ → ⊥-elim (ne refl) ; SS′ _ _ → refl ; CPh _ (s≤s ())
    ; KC _ (s≤s ()) ; CZ _ (s≤s ()) ; B _ (s≤s ()) ; I _ (s≤s ()) })

  independent : Independent-axiom E
  independent = separates (s≤s z≤n) (λ ())

-- (CPh): ?CX.
module Sep-CPh where
  open Weighted has (occurs is-CX) refl
  open Sep CPh 2
  open Check (λ
    { ω¹² _ _ → refl ; H⁴ _ _ → refl ; S³ _ _ → refl ; E _ _ → refl
    ; SS′ _ _ → refl ; CPh ne _ → ⊥-elim (ne refl) ; KC _ _ → refl
    ; CZ _ _ → refl ; B _ _ → refl ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom CPh
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (B): #{σ}[2].
module Sep-B where
  open Weighted (count 2) (counts none 1) refl
  open Sep B 2
  open Check (λ
    { ω¹² _ _ → refl ; H⁴ _ _ → refl ; S³ _ _ → refl ; E _ _ → refl
    ; SS′ _ _ → refl ; CPh _ _ → refl ; KC _ _ → refl ; CZ _ _ → refl
    ; B ne _ → ⊥-elim (ne refl) ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom B
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (CZ): #{S}[3].
module Sep-CZ where
  open Weighted (count 3) (counts #S 0) refl
  open Sep CZ 2
  open Check (λ
    { ω¹² _ _ → refl ; H⁴ _ _ → refl ; S³ _ _ → refl ; E _ _ → refl
    ; SS′ _ _ → refl ; CPh _ _ → refl ; KC _ _ → refl
    ; CZ ne _ → ⊥-elim (ne refl) ; B _ _ → refl ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom CZ
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (KC): #{CX}[2].
module Sep-KC where
  open Weighted (count 2) (counts #CX 0) refl
  open Sep KC 2
  open Check (λ
    { ω¹² _ _ → refl ; H⁴ _ _ → refl ; S³ _ _ → refl ; E _ _ → refl
    ; SS′ _ _ → refl ; CPh _ _ → refl ; KC ne _ → ⊥-elim (ne refl)
    ; CZ _ _ → refl ; B _ _ → refl ; I _ (s≤s (s≤s ())) })

  independent : Independent-axiom KC
  independent = separates (s≤s (s≤s z≤n)) (λ ())

------------------------------------------------------------------------
-- Theorem 37.3

minimal-upto-2 : Minimal-upto 2
minimal-upto-2 ω¹² _ = Sep-ω¹².independent
minimal-upto-2 H⁴  _ = Sep-H⁴.independent
minimal-upto-2 S³  _ = Sep-S³.independent
minimal-upto-2 E   _ = Sep-E.independent
minimal-upto-2 SS′ _ = Projective.Sep-SS′.independent
minimal-upto-2 CPh _ = Sep-CPh.independent
minimal-upto-2 KC  _ = Sep-KC.independent
minimal-upto-2 CZ  _ = Sep-CZ.independent
minimal-upto-2 B   _ = Sep-B.independent
minimal-upto-2 I   (s≤s (s≤s ()))

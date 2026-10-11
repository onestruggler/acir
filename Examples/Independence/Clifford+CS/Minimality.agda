------------------------------------------------------------------------
-- Presentations of groups
--
-- Theorem 37.5, CliffCS₂ is minimal up to two qubits and its axiom (I)
-- is independent: the weighted separators
--
-- The rows of Figure 8(e) other than (CSr) and (CE), whose separators
-- are projective substitutions, and (SH_k), for which the paper has
-- none.  arg det₂ weighs ω and S by π, H by 2π, CS by π/2 and σ by π.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Clifford+CS.Minimality where

open import Data.Bool using (Bool ; true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Independence.Clifford+CS.Syntactics
open import Examples.Independence.Model Gate
open Separators arity lhs rhs

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- What the separators look at

is-ω is-H is-S is-CS : Gate n → Bool
is-ω ω-gate   = true
is-ω _        = false
is-H H-gate   = true
is-H _        = false
is-S S-gate   = true
is-S _        = false
is-CS CS-gate = true
is-CS _       = false

#H #SH none : Gate n → ℕ
#H H-gate  = 1
#H _       = 0
#SH S-gate = 1
#SH H-gate = 1
#SH _      = 0
none _ = 0

-- arg det in units of π/4: det ω = e^{iπ/4}, det H = −1, det S = i,
-- det CS = i.
ad : Gate n → ℕ
ad ω-gate  = 1
ad H-gate  = 4
ad S-gate  = 2
ad CS-gate = 2

------------------------------------------------------------------------
-- The weighted separators (Figure 8(e))

-- (ω⁸): ?ω.
module Sep-ω⁸ where
  open Weighted has (occurs is-ω) refl
  open Sep ω⁸ 0
  open Check (λ
    { ω⁸ ne _ → ⊥-elim (ne refl) ; H² _ () ; S⁴ _ () ; E _ () ; CPh _ ()
    ; CSr _ () ; B _ () ; XCS _ () ; CE _ () ; I _ () ; SH₀ _ ()
    ; SH₁ _ () ; SH₂ _ () ; SH₃ _ () })

  independent : Independent-axiom ω⁸
  independent = separates z≤n (λ ())

-- (H²): ?H.
module Sep-H² where
  open Weighted has (occurs is-H) refl
  open Sep H² 1
  open Check (λ
    { ω⁸ _ _ → refl ; H² ne _ → ⊥-elim (ne refl) ; S⁴ _ _ → refl
    ; E _ _ → refl ; CPh _ (s≤s ()) ; CSr _ (s≤s ()) ; B _ (s≤s ())
    ; XCS _ (s≤s ()) ; CE _ (s≤s ()) ; I _ (s≤s ()) ; SH₀ _ (s≤s ())
    ; SH₁ _ (s≤s ()) ; SH₂ _ (s≤s ()) ; SH₃ _ (s≤s ()) })

  independent : Independent-axiom H²
  independent = separates (s≤s z≤n) (λ ())

-- (S⁴): ?S.
module Sep-S⁴ where
  open Weighted has (occurs is-S) refl
  open Sep S⁴ 1
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ ne _ → ⊥-elim (ne refl)
    ; E _ _ → refl ; CPh _ (s≤s ()) ; CSr _ (s≤s ()) ; B _ (s≤s ())
    ; XCS _ (s≤s ()) ; CE _ (s≤s ()) ; I _ (s≤s ()) ; SH₀ _ (s≤s ())
    ; SH₁ _ (s≤s ()) ; SH₂ _ (s≤s ()) ; SH₃ _ (s≤s ()) })

  independent : Independent-axiom S⁴
  independent = separates (s≤s z≤n) (λ ())

-- (E): #{H}[2].
module Sep-E where
  open Weighted (count 2) (counts #H 0) refl
  open Sep E 1
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl
    ; E ne _ → ⊥-elim (ne refl) ; CPh _ (s≤s ()) ; CSr _ (s≤s ())
    ; B _ (s≤s ()) ; XCS _ (s≤s ()) ; CE _ (s≤s ()) ; I _ (s≤s ())
    ; SH₀ _ (s≤s ()) ; SH₁ _ (s≤s ()) ; SH₂ _ (s≤s ()) ; SH₃ _ (s≤s ()) })

  independent : Independent-axiom E
  independent = separates (s≤s z≤n) (λ ())

-- (CPh): ?CS.
module Sep-CPh where
  open Weighted has (occurs is-CS) refl
  open Sep CPh 2
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl ; E _ _ → refl
    ; CPh ne _ → ⊥-elim (ne refl) ; CSr _ _ → refl ; B _ _ → refl
    ; XCS _ _ → refl ; CE _ _ → refl ; I _ (s≤s (s≤s ()))
    ; SH₀ _ (s≤s (s≤s ())) ; SH₁ _ (s≤s (s≤s ())) ; SH₂ _ (s≤s (s≤s ()))
    ; SH₃ _ (s≤s (s≤s ())) })

  independent : Independent-axiom CPh
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (B): #{σ}[2].
module Sep-B where
  open Weighted (count 2) (counts none 1) refl
  open Sep B 2
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl ; E _ _ → refl
    ; CPh _ _ → refl ; CSr _ _ → refl ; B ne _ → ⊥-elim (ne refl)
    ; XCS _ _ → refl ; CE _ _ → refl ; I _ (s≤s (s≤s ()))
    ; SH₀ _ (s≤s (s≤s ())) ; SH₁ _ (s≤s (s≤s ())) ; SH₂ _ (s≤s (s≤s ()))
    ; SH₃ _ (s≤s (s≤s ())) })

  independent : Independent-axiom B
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (XCS): #{S, H}[2].
module Sep-XCS where
  open Weighted (count 2) (counts #SH 0) refl
  open Sep XCS 2
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl ; E _ _ → refl
    ; CPh _ _ → refl ; CSr _ _ → refl ; B _ _ → refl
    ; XCS ne _ → ⊥-elim (ne refl) ; CE _ _ → refl ; I _ (s≤s (s≤s ()))
    ; SH₀ _ (s≤s (s≤s ())) ; SH₁ _ (s≤s (s≤s ())) ; SH₂ _ (s≤s (s≤s ()))
    ; SH₃ _ (s≤s (s≤s ())) })

  independent : Independent-axiom XCS
  independent = separates (s≤s (s≤s z≤n)) (λ ())

-- (I): arg det₂.
module Sep-I where
  open Weighted (count 8) (argdet 2 ad) refl
  open Sep I 3
  open Check (λ
    { ω⁸ _ _ → refl ; H² _ _ → refl ; S⁴ _ _ → refl ; E _ _ → refl
    ; CPh _ _ → refl ; CSr _ _ → refl ; B _ _ → refl ; XCS _ _ → refl
    ; CE _ _ → refl ; I ne _ → ⊥-elim (ne refl) ; SH₀ _ _ → refl
    ; SH₁ _ _ → refl ; SH₂ _ _ → refl ; SH₃ _ _ → refl })

  independent : Independent-axiom I
  independent = separates (s≤s (s≤s (s≤s z≤n))) (λ ())

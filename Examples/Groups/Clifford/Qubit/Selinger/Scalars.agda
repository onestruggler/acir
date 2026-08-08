------------------------------------------------------------------------
-- Presentations of groups
--
-- ExactData.scalars: a Clifford word acting trivially on P4 is a power
-- of ω  (p = 2).
--
-- Qubit.ExactExtension.ExactData asks for
--
--     scalars : w ≈ᶜ ε  →  ∃ k ∈ ℤ/8,  ωᵏ ≈ᶠ w,
--
-- where ≈ᶜ is equality of the P4-action and ≈ᶠ is Figure-8 equality.
-- Two steps separate the two:
--
--   1. from the SEMANTIC hypothesis to a syntactic one — a word acting
--      trivially is trivial modulo scalars.  That is completeness of
--      Figure 8 mod scalars, which is Selinger.Iso composed with the
--      presentation theorem for the extension relation _Clifford,_===_;
--      it is not yet available, so it is taken here as the explicit
--      hypothesis `Complete-mod-scalars`;
--   2. from there to the scalar itself — Selinger.ScalarKernel.kernel-ε,
--      which gives ωᵏ with k a natural number.
--
-- What this module adds is the second step's bookkeeping: ℤ/8 rather
-- than ℕ.  ω has order 8 (C1), so the exponent may be reduced mod 8,
-- which is what turns kernel-ε's ℕ into ExactData's ℤ/8.  With the
-- hypothesis discharged, `scalars` is one of the three fields of
-- ExactData; the others are `sound` (Selinger.Soundness has the
-- per-relation lemmas but not the assembled induction) and `ω-faithful`
-- (not a syntactic statement at all).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Selinger.Scalars where

open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (ℕ ; _+_ ; _*_)
open import Data.Nat.DivMod using (_%_ ; _/_ ; m%n<n ; m≡m%n+[m/n]*n)
open import Data.Nat.Properties using (*-comm)
open import Data.Product using (∃ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties

open import Zp.ModularArithmetic using (ℤ)

open import Examples.Groups.Clifford.Qubit.CliffordGroup
  using (p-2 ; p-prime ; _≈ᶜ_)
open import Examples.Groups.Clifford.Qubit.ExactExtension using (scalar ; _≈ᶠ_)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic using (Gen)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8 using (ω)
import Examples.Groups.Clifford.Qubit.Selinger.ScalarKernel p-2 p-prime as SK
open SK using (_≈ᵐˢ_ ; kernel-ε ; Ω-8)

private
  variable
    n : ℕ

  module P (m : ℕ) = Presentation.Properties (m F8.CRel,_===_)

------------------------------------------------------------------------
-- The missing input
--
-- Completeness of Figure 8 modulo scalars, for the P4 action.  This is
-- the semantic-to-syntactic step; everything else below is arithmetic.

Complete-mod-scalars : Set
Complete-mod-scalars =
  ∀ {n} (w : Word (Gen (₁₊ n))) → w ≈ᶜ ε → w ≈ᵐˢ ε

------------------------------------------------------------------------
-- Reducing the exponent mod 8
--
-- ScalarKernel.Ω-8 says ω^(8q) = 1, which is C1 iterated; splitting
-- k = k%8 + (k/8)·8 therefore collapses everything but the remainder.

ω^-mod : (k : ℕ) → ((ω {n}) ^ (k % 8)) ≈ᶠ ((ω {n}) ^ k)
ω^-mod {n} k = PB.sym
  (PB.trans (PB.refl' ((₁₊ n) F8.CRel,_===_)
                      (Eq.cong (ω ^_) (m≡m%n+[m/n]*n k 8)))
    (PB.trans (P.^-+ (₁₊ n) ω (k % 8) ((k / 8) * 8))
      (PB.trans (PB.cong PB.refl vanish) PB.right-unit)))
  where
  -- (k/8)·8 = 8·(k/8), and Ω-8 kills the latter.
  vanish : ((ω {n}) ^ ((k / 8) * 8)) ≈ᶠ ε
  vanish = PB.trans
    (PB.refl' ((₁₊ n) F8.CRel,_===_)
              (Eq.cong (ω ^_) (*-comm (k / 8) 8)))
    (Ω-8 (₁₊ n) (k / 8))

------------------------------------------------------------------------
-- The field itself

scalars : Complete-mod-scalars →
          ∀ {n} (w : Word (Gen (₁₊ n))) → w ≈ᶜ ε →
          ∃ λ (k : ℤ 8) → scalar k ≈ᶠ w
scalars complete {n} w triv with kernel-ε (complete w triv)
... | k , d = k' , PB.trans reduce (PB.sym d)
  where
  k' : ℤ 8
  k' = fromℕ< (m%n<n k 8)

  -- scalar k' is ω^(k mod 8), which is ω^k, which is w.
  reduce : (scalar {n} k') ≈ᶠ ((ω {n}) ^ k)
  reduce = PB.trans
    (PB.refl' ((₁₊ n) F8.CRel,_===_)
              (Eq.cong (ω ^_) (toℕ-fromℕ< (m%n<n k 8))))
    (ω^-mod k)

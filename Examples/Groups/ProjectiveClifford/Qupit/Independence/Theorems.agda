------------------------------------------------------------------------
-- Presentations of groups
--
-- Independence of rules of the qupit Clifford presentation
--
-- Paper-V1 states the paper's Figure 1 as fifteen gate-specific rules,
-- lifted to every width and every position by the structural rules of
-- Circuit.Base.  This module collects the rules shown independent: for
-- each, an instance that is not derivable from the instances of the
-- other fourteen rules — at every width and every shift — together with
-- every structural rule.  Selection says what that means; each proof is
-- a model in which every other rule holds and the instance fails, and
-- each section names the module the model lives in.
--
-- Only order-CZ is shown independent at every odd prime, and only for
-- an odd primitive root.  The others are shown at a fixed prime and
-- root, by models whose soundness is checked by computation; at other
-- primes the same rule may well be redundant (the survey in
-- local/paper-v1-minimality found blake-c12 so at p = 5).
--
-- Every instance below is at the smallest width its rule lives at: a
-- derivation at that width uses no instance of a wider rule, which is
-- what lets each model give up from the next width on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qupit.Independence.Theorems where

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Base using (parity)
open import Data.Nat.Primality using (Prime)
open import Data.Parity.Base using (1ℙ)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Notations using (₀ ; ₁₊)
open import ForStdlib.Data.Fin.Mod using (ℤ ; ℤ* ; _^′_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat using (module PrimeModulus')

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics as Syn
import Examples.Groups.ProjectiveClifford.Qupit.Independence.Selection as Sel
open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Parameters
  using ( prime-3 ; root-3 ; root-3-gen
        ; prime-5 ; root-5 ; root-5-gen ; root-5' ; root-5'-gen )
import Examples.Groups.ProjectiveClifford.Qupit.Independence.OrderCZ as OrderCZ
import Examples.Groups.ProjectiveClifford.Qupit.Independence.SCount as SCount
import Examples.Groups.ProjectiveClifford.Qupit.Independence.MPower as MPower
import Examples.Groups.ProjectiveClifford.Qupit.Independence.SemiMCZ3 as SemiMCZ3
import Examples.Groups.ProjectiveClifford.Qupit.Independence.SemiMCZ5 as SemiMCZ5

------------------------------------------------------------------------
-- order-CZ, at every odd prime, for an odd primitive root
--
-- Home: Independence.OrderCZ.  Count CZ letters mod 2: every other
-- rule changes the count by an even number at width 2 — semi-M↑CZ by
-- toℕ g − 1, which is where g must be odd — and order-CZ by p.  That p
-- is odd is a theorem, from p = 3 + p-3 being prime; that g is odd is
-- the hypothesis.

module Every-Odd-Prime
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (2+ p-2))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

  open Syn p-3 p-prime g* g-gen using (module Clifford-Relations)
  open Clifford-Relations using (module Base ; srel)
  open Sel p-3 p-prime g* g-gen using (order-CZ ; _IndependentOf_)

  -- CZ ^ p = ε, at width 2, does not follow from the other rules.
  order-CZ-independent : parity (toℕ g) ≡ 1ℙ →
                         srel (Base.order-CZ {0}) IndependentOf order-CZ
  order-CZ-independent = OrderCZ.order-CZ-independent p-3 p-prime g* g-gen

------------------------------------------------------------------------
-- p = 3, g = 2
--
-- Home: Independence.SCount for blake-c12 and semi-Ex-S↑, which count
-- S letters mod 3 (all of them, or those on wire 0); Independence.
-- SemiMCZ3 for semi-M↑CZ, whose model is the affine symplectic group
-- (Independence.Affine) with CZ twisted by a Pauli.

module At-Three where

  open Syn 0 prime-3 root-3 root-3-gen using (module Clifford-Relations)
  open Clifford-Relations using (module Base ; srel)
  open Sel 0 prime-3 root-3 root-3-gen
    using (blake-c12 ; semi-Ex-S↑ ; semi-M↑CZ ; _IndependentOf_)

  blake-c12-independent :
    srel (Base.blake-c12 {0}) IndependentOf blake-c12
  blake-c12-independent = SCount.All-S.blake-c12-independent

  semi-Ex-S↑-independent :
    srel (Base.semi-Ex-S↑ {0}) IndependentOf semi-Ex-S↑
  semi-Ex-S↑-independent = SCount.Wire₀-S.semi-Ex-S↑-independent

  semi-M↑CZ-independent :
    srel (Base.semi-M↑CZ {0}) IndependentOf semi-M↑CZ
  semi-M↑CZ-independent = SemiMCZ3.semi-M↑CZ-independent

------------------------------------------------------------------------
-- p = 5, g = 2
--
-- Home: Independence.MPower for M-power: weigh H as 3 and S as 1 in
-- ℤ/5ℤ, at width 1; every other one-wire rule balances, and M-power at
-- k = 0, ε = (S • H) ^ 3, does not.  Independence.SemiMCZ5 for
-- semi-M↑CZ, by the same twisted model as at p = 3.

module At-Five where

  open Syn 2 prime-5 root-5 root-5-gen using (module Clifford-Relations)
  open Clifford-Relations using (module Base ; srel)
  open Sel 2 prime-5 root-5 root-5-gen
    using (M-power ; semi-M↑CZ ; _IndependentOf_)

  M-power-independent :
    srel (Base.M-power {0} ₀) IndependentOf M-power
  M-power-independent = MPower.M-power-independent

  semi-M↑CZ-independent :
    srel (Base.semi-M↑CZ {0}) IndependentOf semi-M↑CZ
  semi-M↑CZ-independent = SemiMCZ5.semi-M↑CZ-independent

------------------------------------------------------------------------
-- p = 5, g = 3
--
-- Home: Independence.OrderCZ, at a root that is odd, so that its
-- hypothesis is discharged by computation.

module At-Five-Root-Three where

  open Syn 2 prime-5 root-5' root-5'-gen using (module Clifford-Relations)
  open Clifford-Relations using (module Base ; srel)
  open Sel 2 prime-5 root-5' root-5'-gen using (order-CZ ; _IndependentOf_)

  order-CZ-independent : srel (Base.order-CZ {0}) IndependentOf order-CZ
  order-CZ-independent =
    OrderCZ.order-CZ-independent 2 prime-5 root-5' root-5'-gen refl

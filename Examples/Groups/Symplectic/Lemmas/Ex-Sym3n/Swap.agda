------------------------------------------------------------------------
-- Presentations of groups
--
-- Ex-Sym3n, part 2: the SWAP rewrite system.
--
-- step-swap and its engine Rewriting-Swap are the expensive part of
-- the original file -- 39 of its 59 CPU seconds, in 250 lines -- so
-- they are kept apart from the powers half, which needs none of them.
-- Thirteen importers open Rewriting-Swap, so this half cannot be
-- avoided by most of them; what the split buys is that editing either
-- engine no longer forces the other to be rechecked.
--
-- Depends on part 1 for the modules Lemmas and Lemmas2 and for
-- lemma-Ex-Ex↑-CZ / lemma-Ex↑-Ex-CZ↑.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}


import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq


open import Data.Product using (_,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)

open import Data.Maybe

open import Word.Base as WB hiding (wfoldl)
import Presentation.Base as PB
import Presentation.Properties as PP
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full


open import Data.Fin using (toℕ)
import Data.Nat.Properties as NP
open import Presentation.GroupLike
open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality


module Examples.Groups.Symplectic.Lemmas.Ex-Sym3n.Swap (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where


private
  variable
    n : ℕ

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Lemmas-2Qupit-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
open Lemmas0a
open Lemmas0b hiding (lemma-comm-Ex-H')


open Symplectic
open Lemmas-Sym

open Symplectic-GroupLike

open import Data.Fin.Properties


open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3 p-2 p-prime
open Lemmas0c

open Lemmas0b hiding (lemma-comm-Ex-H')

open Duality



open import Examples.Groups.Symplectic.Lemmas.Ex-Sym3n.Powers p-2 p-prime

module Swap-Rewriting where

-- This module provides a complete rewrite system for 1-qubit
-- Swap operators. It is specialized toward relations on qubit 0
-- (but can also be applied to qubit 1 via duality).
open Symplectic
open Rewriting
open Lemmas0
open Lemmas2

lemma-comm-Ex-S↑↑ : let open PB ((₃₊ n) QRel,_===_) in
  Ex • S ↑ ↑ ≈ S ↑ ↑ • Ex
lemma-comm-Ex-S↑↑ {n} = general-comm auto
  where
  open Commuting-Symplectic (₁₊ n)

lemma-comm-Ex↑-S : let open PB ((₃₊ n) QRel,_===_) in
  Ex ↑ • S ≈ S • Ex ↑
lemma-comm-Ex↑-S {n} = general-comm auto
  where
  open Commuting-Symplectic (₁₊ n)

lemma-comm-Ex-H↑↑ : let open PB ((₃₊ n) QRel,_===_) in
  Ex • H ↑ ↑ ≈ H ↑ ↑ • Ex
lemma-comm-Ex-H↑↑ {n} = general-comm auto
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Commuting-Symplectic (₁₊ n)

lemma-comm-Ex↑-H : let open PB ((₃₊ n) QRel,_===_) in
  Ex ↑ • H ≈ H • Ex ↑
lemma-comm-Ex↑-H {n} = general-comm auto
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open Commuting-Symplectic (₁₊ n)


step-swap : ∀ {n} → let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

-- Order of generators.
step-swap ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-H))
step-swap ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-H)))
step-swap ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-H))))

step-swap ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (PB.axiom order-SH))
step-swap ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ order-SH)))
step-swap ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (PB.axiom (cong↑ (cong↑ order-SH))))

step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex-n))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex-n)))


step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( (lemma-Ex-Ex↑-CZ)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-Ex↑-Ex-CZ↑)))


step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ-n)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-CZ-n))))

step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H-n)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-H-n))))

step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-S))))

step-swap {₁₊ n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑-n {n}))))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-S↑-n))

step-swap {₁₊ n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑-n {n}))))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-H↑-n))


-- Trivial commutations.
step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-S↑↑)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ∷ xs) = just (S-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-S))))
step-swap (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-H↑↑)))
step-swap (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ∷ xs) = just (H-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-H))))

-- Catch-all
step-swap _ = nothing


module Rewriting-Swap (m : ℕ) where
  open Symplectic
  open Rewriting
  open Swap-Rewriting
  open Rewriting.Step (step-cong (step-swap {m})) renaming (general-rewrite to rewrite-swap) public


module Swap0-Rewriting where


  open Symplectic
  open Rewriting
  open Lemmas0
  open Lemmas2

  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Swap0 relations

  step-swap0 : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex-n))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (xs , at-head ( (lemma-cong↑ _ _ lemma-order-Ex-n)))


  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ-n)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ xs) = just (CZ-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-CZ-n))))

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H-n)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-H-n))))

  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (PB.sym ( (lemma-cong↑ _ _ lemma-comm-Ex-S))))

  step-swap0 {₁₊ n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑-n {n}))))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-S↑-n))

  step-swap0 {₁₊ n} (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑-n {n}))))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head (lemma-cong↑ _ _ lemma-Ex-H↑-n))


  -- Trivial commutations.
  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-S↑↑)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ∷ xs) = just (S-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-S))))
  step-swap0 (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-H↑↑)))
  step-swap0 (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ∷ xs) = just (H-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-H))))

  -- Catch-all
  step-swap0 _ = nothing


module Rewriting-Swap0 (n : ℕ) where
  open Symplectic
  open Rewriting
  open Swap0-Rewriting
  open Rewriting.Step (step-cong (step-swap0 {n})) renaming (general-rewrite to rewrite-swap0) public


open Symplectic
--  open Rewriting-Symplectic
open Rewriting


lemma-comm-Ex-w↑↑ : ∀ {n} w → let open PB ((₂₊ n) QRel,_===_) in

  Ex • w ↑ ↑ ≈ w ↑ ↑ • Ex

lemma-comm-Ex-w↑↑ {n} [ H-gen ]ʷ = rewrite-sym0 (₁₊ n) 1000 auto
  where
  open Sym0-Rewriting
lemma-comm-Ex-w↑↑ {n} [ S-gen ]ʷ = rewrite-sym0 (₁₊ n) 1000 auto
  where
  open Sym0-Rewriting
lemma-comm-Ex-w↑↑ {n} [ CZ-gen ]ʷ = rewrite-sym0 (₁₊ n) 1000 auto
  where
  open Sym0-Rewriting
-- lemma-comm-Ex-w↑↑ {n} [ EX-gen ]ʷ = rewrite-sym0 (₁₊ n) 1000 auto
--   where
--   open Sym0-Rewriting
lemma-comm-Ex-w↑↑ {n} [ x ↥ ]ʷ = begin
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • (([ x ↥ ]ʷ ↑) ↑) ≈⟨ by-assoc auto ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑ ≈⟨ cong refl (sym (axiom (cong↑ comm-H))) ⟩
  (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑ ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • H ↑ ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • H ↑ ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
  ((CZ • H ↓ • H ↑ • CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑ • CZ) • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
  ((CZ • H ↓ • H ↑ • CZ) • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓ • H ↑) • CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-CZ))) refl ⟩
  ((CZ • H ↓ • H ↑) • [ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  ((CZ • H ↓) • H ↑ • [ x ↥ ]ʷ ↑ ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom (cong↑ comm-H)))) refl ⟩
  ((CZ • H ↓) • [ x ↥ ]ʷ ↑ ↑ • H ↑) • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  (CZ • H ↓ • [ x ↥ ]ʷ ↑ ↑) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong (cong refl (sym (axiom comm-H))) refl ⟩
  (CZ • [ x ↥ ]ʷ ↑ ↑ • H ↓) • (H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  (CZ • [ x ↥ ]ʷ ↑ ↑) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ cong ( (sym (axiom comm-CZ))) refl ⟩
  ([ x ↥ ]ʷ ↑ ↑ • CZ) • (H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ by-assoc auto ⟩
  [ x ↥ ]ʷ ↑ ↑ • (CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑ • CZ • H ↓ • H ↑) ≈⟨ refl ⟩
  (([ x ↥ ]ʷ ↑) ↑) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-comm-Ex-w↑↑ {n} ε = PB.trans PB.right-unit (PB.sym PB.left-unit)
lemma-comm-Ex-w↑↑ {n} (w • v) = begin
  Ex • (((w • v) ↑) ↑) ≈⟨ refl ⟩
  Ex • w ↑ ↑ • v ↑ ↑ ≈⟨ sym assoc ⟩
  (Ex • w ↑ ↑) • v ↑ ↑ ≈⟨ cong (lemma-comm-Ex-w↑↑ w) refl ⟩
  (w ↑ ↑ • Ex) • v ↑ ↑ ≈⟨ assoc ⟩
  w ↑ ↑ • Ex • v ↑ ↑ ≈⟨ cong refl (lemma-comm-Ex-w↑↑ v) ⟩
  w ↑ ↑ • v ↑ ↑ • Ex ≈⟨ sym assoc ⟩
  (((w • v) ↑) ↑) • Ex ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid


open import Algebra.Properties.Ring (+-*-ring p-2)

lemma-semi-CXCZ^ : let open PB ((₂₊ n) QRel,_===_) in ∀ (k : ℤ ₚ) →

  CX • CZ^ k ≈ S^ (- k + - k) ↑ • CZ^ k • CX

lemma-semi-CXCZ^ {n} k@₀ = begin
  CX • CZ^ k ≈⟨ right-unit ⟩
  CX ≈⟨ sym left-unit ⟩
  S^ ₀ ↑ • CX ≡⟨ Eq.cong (\ xx → S^ xx ↑ • CX) (Eq.sym (Eq.trans (Eq.cong₂ _+_ -0#≈0# -0#≈0#) auto)) ⟩
  S^ (- k + - k) ↑ • CX ≈⟨ sym (cong refl left-unit) ⟩
  S^ (- k + - k) ↑ • CZ^ k • CX ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-semi-CXCZ^ {n} k@(₁₊ k') = by-emb' (lemma-semi-CXCZ^k (k , (λ ()))) (cright lemma-f* CZ (toℕ k)) (cong (lemma-f*-Sᵏ↑ (toℕ (- k + - k))) (cleft lemma-f* CZ (toℕ k)))
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open import Examples.Groups.Symplectic.Lemmas.Embedding-2n p-2 p-prime n


lemma-semi-CXCZ^-alt : let open PB ((₂₊ n) QRel,_===_) in ∀ (k : ℤ ₚ) →

  CX • CZ^ k ≈ S^ k • CX • S^ (- k) • S^ (- k) ↑ 

lemma-semi-CXCZ^-alt {n} k@₀ = begin
  CX • CZ^ k ≈⟨ right-unit ⟩
  CX ≈⟨ by-assoc auto ⟩
  CX • S^ (₀) • S^ (₀) ↑ ≡⟨ Eq.cong (\ xx → CX • S^ (xx) • S^ (xx) ↑) (Eq.sym -0#≈0#) ⟩
  CX • S^ (- k) • S^ (- k) ↑ ≈⟨ sym left-unit ⟩
  S^ k • CX • S^ (- k) • S^ (- k) ↑ ∎
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)
  open SR word-setoid
lemma-semi-CXCZ^-alt {n} k@(₁₊ k') = by-emb' (lemma-CXCZ^k (k , (λ ()))) (cright lemma-f* CZ (toℕ k)) (cong (lemma-f* S (toℕ k)) (cright cong (lemma-f* S (toℕ (- k))) (lemma-f*-Sᵏ↑ (toℕ (- k)))))
  where
  open PB ((₂₊ n) QRel,_===_)
  open PP ((₂₊ n) QRel,_===_)

  open import Examples.Groups.Symplectic.Lemmas.Embedding-2n p-2 p-prime n


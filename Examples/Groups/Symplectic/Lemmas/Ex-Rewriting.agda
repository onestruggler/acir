{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --termination-depth=2 #-}




open import Data.Product using (_,_)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)
open import Data.List hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)

open import Data.Maybe

import Presentation.Base as PB
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full



open import Presentation.Tactic.Rewriting hiding ([_])
open import Data.Nat.Primality



module Examples.Groups.Symplectic.Lemmas.Ex-Rewriting (p-2 : ℕ) (p-prime : Prime (2+ p-2))  where





open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2 p-2 p-prime
open Lemmas0b
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym p-2 p-prime
open Lemmas0a
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym1 p-2 p-prime
open import Examples.Groups.Symplectic.Lemmas.Ex-Sym2n p-2 p-prime
open Lemmas0a1

module Ex-Rewriting where

  -- This module provides a complete rewrite system for 1-qubit
  -- Ex operators. It is specialized toward relations on qubit 0
  -- (but can also be applied to qubit 1 via duality).
  private
    variable
      n : ℕ

  open Symplectic
  open Rewriting
  open Lemmas0 
--  open Lemmas2 hiding (n)
  
  -- ----------------------------------------------------------------------
  -- * Rewrite rules for 1-qubit Ex relations
  
  step-ex : let open PB ((₂₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₂₊ n))  ((₂₊ n) QRel,_===_)

--  step-ex {n}  (EX-gen ∷ xs) = just (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.axiom def-EX))
  
  step-ex {n}  (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs) = just (xs , at-head (lemma-order-Ex-n))



  step-ex {n}  (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ xs) = just (CZ-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-CZ-n)))


  step-ex {n}  (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ∷ xs) = just (H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-H-n)))


  step-ex {n}  (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ∷ xs) = just (S-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (PB.sym (lemma-comm-Ex-S)))


  step-ex {n}  (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ∷ xs) = just (S-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-S↑-n))))


  step-ex {n}  (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ∷ xs) = just (H-gen ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head (((lemma-Ex-H↑-n))))



  -- -- Trivial commutations.
  -- step-ex (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ S-gen ↥ ↥ ∷ xs) = just (S-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-S↑↑)))
  -- step-ex (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ S-gen ∷ xs) = just (S-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-S))))
  -- step-ex (CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs) = just (H-gen ↥ ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ CZ-gen ∷ H-gen ∷ H-gen ↥ ∷ xs , at-head ( (lemma-comm-Ex-H↑↑)))
  -- step-ex (CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ H-gen ∷ xs) = just (H-gen ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ CZ-gen ↥ ∷ H-gen ↥ ∷ H-gen ↥ ↥ ∷ xs , at-head ( ( (lemma-comm-Ex↑-H))))

  -- Catch-all
  step-ex _ = nothing


module Rewriting-Ex (n : ℕ)  where
  open Symplectic
  open Rewriting
  open Ex-Rewriting
  open Rewriting.Step (step-cong (step-ex {n})) renaming (general-rewrite to rewrite-ex) public

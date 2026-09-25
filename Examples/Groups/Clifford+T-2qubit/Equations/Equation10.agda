------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 10 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation10 where

open import Data.Product.Base using (_,_)

open import Notations using (auto)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Words
open import Examples.Groups.Clifford+T-2qubit.Generator
import Examples.Groups.Clifford+T-2qubit.Clifford-Lemmas as Clifford-Lemmas
open import Examples.Groups.Clifford+T-2qubit.CliffordT-Lemmas
import Examples.Groups.Clifford+T-2qubit.PauliRotations as PauliRotations

open Clifford+T
open Monoid-Equational
open InContext
open Associative
open Clifford-Lemmas.Clifford-Rewriting
open PauliRotations.Pauli
open PauliRotations.PauliRotRep
open PauliRotations.Commutativity
open PauliRotations.Combine
open PauliRotations.Correction

private module C = PauliRotations.Clifford

eqn10 : Clifford+T.Rel ⊢ X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε === ε
eqn10 = 
  equational X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by in-context 5 1 auto lemma-R-T0⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by in-context 7 1 auto lemma-R-T1⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by in-context 15 1 auto lemma-R-T0⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by in-context 17 1 auto lemma-R-T1⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by in-context 25 1 auto lemma-R-T0⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by in-context 27 1 auto lemma-R-T1⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • T0 • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • T0⁻¹ • T1⁻¹ • W • ε
          by in-context 35 1 auto lemma-R-T0⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • ε
          by in-context 37 1 auto lemma-R-T1⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 0 3 auto (lemma-R (C.X0 • C.CX0) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • X0 • CX0 • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by clifford-tactic 1 4 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 2 2 auto (lemma-R (C.S0⁻¹) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • S0⁻¹ • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 3 6 auto (lemma-R (C.S0⁻¹ • C.S1⁻¹ • C.W • C.X0 • C.CX0) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • S0⁻¹ • S1⁻¹ • W • X0 • CX0 • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 4 8 auto (lemma-R (C.S0⁻¹ • C.S1⁻¹ • C.W • C.X0 • C.CX0 • C.CX0 • C.X0) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • S0⁻¹ • S1⁻¹ • W • X0 • CX0 • CX0 • X0 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by clifford-tactic 5 8 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S1 • S1 • S1 • W • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 5 7 auto (lemma-R (C.S0 • C.S0 • C.S1 • C.S1 • C.S1 • C.W) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • S0 • S0 • S1 • S1 • S1 • W • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by clifford-tactic 6 10 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • H0 • CZ • S0 • S0 • H0 • S0 • S0 • W ^ 6 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 6 9 auto (lemma-R (C.H0 • C.CZ • C.S0 • C.S0 • C.H0 • C.S0 • C.S0 • C.W ^ 6) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • H0 • CZ • S0 • S0 • H0 • S0 • S0 • W ^ 6 • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by clifford-tactic 7 10 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • S0 • S0 • S1 • S1 • W ^ 2 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 7 6 auto (lemma-R (C.S0 • C.S0 • C.S1 • C.S1 • C.W ^ 2) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S1 • S1 • W ^ 2 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by clifford-tactic 9 5 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • S0 • S1 • S1 • W ^ 2 • R (plus , I⊗Z) • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 8 5 auto (lemma-R (C.S0 • C.S1 • C.S1 • C.W ^ 2) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • S0 • S1 • S1 • W ^ 2 • S1⁻¹ • W • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 9 9 auto (lemma-R (C.S0 • C.S1 • C.S1 • C.W ^ 2 • C.S1⁻¹ • C.W • C.X0 • C.CX0) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • S0 • S1 • S1 • W ^ 2 • S1⁻¹ • W • X0 • CX0 • CX0 • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by clifford-tactic 12 8 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • S0 • S1 • W ^ 3 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 10 4 auto (lemma-R (C.S0 • C.S1 • C.W ^ 3) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • S0 • S1 • W ^ 3 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by clifford-tactic 11 4 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • S1 • W ^ 3 • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 11 3 auto (lemma-R (C.S1 • C.W ^ 3) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • S1 • W ^ 3 • S1⁻¹ • W • ε
          by clifford-tactic 12 4 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 1 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 0 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 4 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 3 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 1 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 7 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 6 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 5 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 4 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 3 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • W ^ 4 • ε
          by in-context 10 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 9 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 8 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 7 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 6 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 5 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 4 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 3 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 4 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 6 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 5 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 8 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 7 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 6 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • W ^ 4 • ε
          by in-context 10 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 9 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 8 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 7 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 0 2 auto (lemma-combine plus plus I⊗Z)
      equals Swap • S0 • Swap • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 3 2 auto (lemma-combine plus plus I⊗Z)
      equals Swap • S0 • Swap • Swap • S0 • Swap • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 6 2 auto (lemma-combine plus plus Z⊗I)
      equals Swap • S0 • Swap • Swap • S0 • Swap • S0 • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 7 2 auto (lemma-combine plus plus Z⊗I)
      equals Swap • S0 • Swap • Swap • S0 • Swap • S0 • S0 • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 8 2 auto (lemma-combine minus minus Z⊗Z)
      equals Swap • S0 • Swap • Swap • S0 • Swap • S0 • S0 • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • R (minus , Z⊗Z) • R (minus , Z⊗Z) • W ^ 4 • ε
          by in-context 16 2 auto (lemma-combine minus minus Z⊗Z)
      equals Swap • S0 • Swap • Swap • S0 • Swap • S0 • S0 • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • W ^ 4 • ε
          by clifford-tactic 0 25 10000 auto
      equals ε



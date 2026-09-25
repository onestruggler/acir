------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 30 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation30 where

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

eqn30 : Clifford+T.Rel ⊢ X0 • CH1 • X0 • T1 • CX1 • T1⁻¹ • ε === T1 • CX1 • T1⁻¹ • X0 • CH1 • X0 • ε
eqn30 = 
  equational X0 • CH1 • X0 • T1 • CX1 • T1⁻¹ • ε
          by general-assoc auto
      equals X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • T1 • CX1 • T1⁻¹ • ε
          by in-context 3 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • T1 • CX1 • T1⁻¹ • ε
          by in-context 5 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • T1 • CX1 • T1⁻¹ • ε
          by in-context 10 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , I⊗Z) • CX1 • T1⁻¹ • ε
          by in-context 12 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 0 4 auto (lemma-R (C.X0 • C.S1 • C.H1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 1 5 auto (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by clifford-tactic 2 8 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • CZ • H1 • W⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 2 4 auto (lemma-R (C.CZ • C.H1 • C.W⁻¹) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗X) • CZ • H1 • W⁻¹ • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by clifford-tactic 3 4 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗X) • H1 • W⁻¹ • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 3 3 auto (lemma-R (C.H1 • C.W⁻¹) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗X) • R (plus , I⊗X) • H1 • W⁻¹ • S1⁻¹ • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (plus , I⊗X) (plus , Z⊗X) auto))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , I⊗X) • R (plus , Z⊗X) • H1 • W⁻¹ • S1⁻¹ • ε
          by in-context 1 1 auto (lemma-correction Z⊗Y)
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • S1 • H1 • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , I⊗X) • R (plus , Z⊗X) • H1 • W⁻¹ • S1⁻¹ • ε
          by clifford-tactic 4 10 10000 auto
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • H1 • R (plus , I⊗X) • R (plus , Z⊗X) • H1 • W⁻¹ • S1⁻¹ • ε
          by in-context 2 10 auto (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S0 • C.S0 • C.H1 • C.S1 • C.H1) (plus , I⊗X))
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • H1 • R (plus , Z⊗X) • H1 • W⁻¹ • S1⁻¹ • ε
          by in-context 3 10 auto (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S0 • C.S0 • C.H1 • C.S1 • C.H1) (plus , Z⊗X))
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • H1 • H1 • W⁻¹ • S1⁻¹ • ε
          by clifford-tactic 11 5 10000 auto
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto))
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 0 0 10000 auto
      equals H0 • CZ • H0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 3 0 auto (symm lemma-order-T0)
      equals H0 • CZ • H0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals H0 • CZ • H0 • T0⁻¹ • T0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 4 0 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • T0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 7 0 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 9 0 auto (symm lemma-rel-A)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 9 1 auto lemma-R-T1
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 11 1 auto lemma-R-T1⁻¹
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 15 1 auto lemma-R-T1
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • T1⁻¹ • CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 17 1 auto lemma-R-T1⁻¹
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • T1 • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 20 1 auto lemma-R-T1
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • R (plus , I⊗Z) • H1 • T1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 22 1 auto lemma-R-T1⁻¹
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • T1 • H1 • T1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 26 1 auto lemma-R-T1
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • T1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 28 1 auto lemma-R-T1⁻¹
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 10 2 auto (lemma-R (C.H1) (plus , I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • H1 • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 11 5 auto (lemma-R (C.H1 • C.S1⁻¹ • C.CX1 • C.X1) (plus , I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • H1 • S1⁻¹ • CX1 • X1 • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 12 6 auto (lemma-R (C.H1 • C.S1⁻¹ • C.CX1 • C.X1 • C.H1) (plus , I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Y) • H1 • S1⁻¹ • CX1 • X1 • H1 • S1⁻¹ • CX1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 13 8 auto (lemma-R (C.H1 • C.S1⁻¹ • C.CX1 • C.X1 • C.H1 • C.S1⁻¹ • C.CX1) (plus , I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Y) • R (plus , Z⊗Y) • H1 • S1⁻¹ • CX1 • X1 • H1 • S1⁻¹ • CX1 • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 9 auto (lemma-R (C.H1 • C.S1⁻¹ • C.CX1 • C.X1 • C.H1 • C.S1⁻¹ • C.CX1 • C.H1) (plus , I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , Z⊗Z) • H1 • S1⁻¹ • CX1 • X1 • H1 • S1⁻¹ • CX1 • H1 • S1⁻¹ • CX1 • X1 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 15 11 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , Z⊗Z) • S0 • S1 • S1 • W ^ 5 • R (plus , I⊗Z) • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 15 5 auto (lemma-R (C.S0 • C.S1 • C.S1 • C.W ^ 5) (plus , I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , Z⊗Z) • R (plus , I⊗Z) • S0 • S1 • S1 • W ^ 5 • H1 • R (plus , I⊗Z) • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 16 6 auto (lemma-R (C.S0 • C.S1 • C.S1 • C.W ^ 5 • C.H1) (plus , I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 11 1 auto (lemma-correction Z⊗X)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H1 • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 12 11 auto (lemma-R (C.H1 • C.H0 • C.CZ • C.H0 • C.S0⁻¹ • C.W • C.H0 • C.CZ • C.H0 • C.H1) (plus , I⊗Y))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , Z⊗Z) • H1 • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 12 1 auto (lemma-correction Z⊗Z)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 13 18 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • H1 • CZ • S0 • S0 • S0 • S1 • W • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 13 8 auto (lemma-R (C.H1 • C.CZ • C.S0 • C.S0 • C.S0 • C.S1 • C.W) (plus , Z⊗Y))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (minus , I⊗Z) • H1 • CZ • S0 • S0 • S0 • S1 • W • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 13 1 auto (lemma-correction I⊗Z)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • Swap • S0⁻¹ • W • Swap • H1 • CZ • S0 • S0 • S0 • S1 • W • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 14 11 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • S1 • H1 • CZ • S0 • H1 • S1 • S1 • H1 • S1 • W ^ 2 • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 11 auto (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.H1 • C.S1 • C.S1 • C.H1 • C.S1 • C.W ^ 2) (plus , I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Y) • S1 • H1 • CZ • S0 • H1 • S1 • S1 • H1 • S1 • W ^ 2 • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 1 auto (lemma-correction I⊗Y)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Y) • S1 • H1 • Swap • S0⁻¹ • W • Swap • H1 • S1⁻¹ • S1 • H1 • CZ • S0 • H1 • S1 • S1 • H1 • S1 • W ^ 2 • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 17 16 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Y) • S1 • H1 • CZ • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W ^ 5 • R (minus , Z⊗Z) • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 15 12 auto (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.H1 • C.W ^ 5) (minus , Z⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CZ • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W ^ 5 • R (minus , I⊗X) • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 16 12 auto (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.H1 • C.W ^ 5) (minus , I⊗X))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W ^ 5 • S0 • S1 • S1 • W ^ 5 • H1 • S1⁻¹ • CX1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 17 18 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 17 7 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S1 • S1 • H1 • S1 • S1 • S1 • W ^ 6 • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 16 12 auto (symm (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.S1 • C.W ^ 6) (minus , I⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CZ • S0 • S1 • S1 • H1 • S1 • S1 • S1 • W ^ 6 • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 15 12 auto (symm (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.S1 • C.W ^ 6) (plus , Z⊗Y)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Y) • S1 • H1 • CZ • S0 • S1 • S1 • H1 • S1 • S1 • S1 • W ^ 6 • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 12 auto (symm (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.S1 • C.W ^ 6) (plus , I⊗Y)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • S1 • H1 • CZ • S0 • S1 • S1 • H1 • S1 • S1 • S1 • W ^ 6 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 14 11 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (plus , I⊗Z) • Swap • S0⁻¹ • W • Swap • H1 • CZ • S0 • S0 • S0 • S1 • S1 • H1 • S1 • W • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 13 5 auto (symm (lemma-correction I⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • R (minus , I⊗Z) • H1 • CZ • S0 • S0 • S0 • S1 • S1 • H1 • S1 • W • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 13 11 auto (symm (lemma-R (C.H1 • C.CZ • C.S0 • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.W) (plus , Z⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • H1 • CZ • S0 • S0 • S0 • S1 • S1 • H1 • S1 • W • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 13 10 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (plus , Z⊗Z) • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • CZ • S0 • S0 • S0 • S1 • S1 • H1 • W ^ 2 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 12 9 auto (symm (lemma-correction Z⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , Z⊗Z) • H1 • CZ • S0 • S0 • S0 • S1 • S1 • H1 • W ^ 2 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 12 10 auto (symm (lemma-R (C.H1 • C.CZ • C.S0 • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.W ^ 2) (plus , I⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H1 • CZ • S0 • S0 • S0 • S1 • S1 • H1 • W ^ 2 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 13 8 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H1 • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • S1 • H1 • S1 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 11 11 auto (symm (lemma-correction Z⊗X))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • S1 • H1 • S1 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 11 4 auto (symm (lemma-R (C.S1 • C.H1 • C.S1) (minus , Z⊗X)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • S1 • H1 • S1 • R (minus , Z⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 11 3 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , I⊗X) • H1 • Swap • S0⁻¹ • W • Swap • H1 • R (minus , Z⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 10 7 auto (symm (lemma-correction I⊗X))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 2 auto (tactic-pauli-commute (plus , I⊗Y) (plus , Z⊗Y) auto)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , I⊗X) • R (minus , Z⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 10 2 auto (tactic-pauli-commute (minus , I⊗X) (minus , Z⊗X) auto)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , Z⊗X) • R (minus , I⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • W ^ 2 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 17 7 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , Z⊗X) • R (minus , I⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (minus , I⊗Z) • CZ • S0 • S1 • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 16 4 auto (symm (lemma-R (C.CZ • C.S0 • C.S1) (minus , I⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , Z⊗X) • R (minus , I⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • CZ • S0 • S1 • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 15 4 auto (symm (lemma-R (C.CZ • C.S0 • C.S1) (plus , Z⊗X)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , Z⊗X) • R (minus , I⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • CZ • S0 • S1 • R (plus , Z⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 4 auto (symm (lemma-R (C.CZ • C.S0 • C.S1) (plus , I⊗X)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , Z⊗X) • R (minus , I⊗X) • R (plus , I⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S1 • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 13 4 auto (symm (lemma-R (C.CZ • C.S0 • C.S1) (plus , Z⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , Z⊗X) • R (minus , I⊗X) • R (plus , I⊗Z) • CZ • S0 • S1 • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 12 4 auto (symm (lemma-R (C.CZ • C.S0 • C.S1) (plus , I⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , Z⊗X) • R (minus , I⊗X) • CZ • S0 • S1 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 11 4 auto (symm (lemma-R (C.CZ • C.S0 • C.S1) (plus , Z⊗Y)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (minus , Z⊗X) • CZ • S0 • S1 • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 10 4 auto (symm (lemma-R (C.CZ • C.S0 • C.S1) (plus , I⊗Y)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • CZ • S0 • S1 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 10 3 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • H0 • CZ • H0 • S0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 10 7 auto (symm (lemma-combine plus plus Z⊗Z))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 16 2 auto (tactic-pauli-commute (plus , I⊗X) (plus , Z⊗X) auto)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗X) • R (plus , I⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗X) • R (plus , I⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 12 2 auto (tactic-pauli-commute (plus , I⊗Y) (plus , Z⊗Y) auto)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗X) • R (plus , I⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 9 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗X) • R (plus , I⊗X) • R (minus , I⊗Z) • H1 • CZ • S0 • S1 • S1 • H1 • S1 • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 19 7 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗X) • R (plus , I⊗X) • R (minus , I⊗Z) • H0 • CZ • S0 • S0 • H0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W ^ 4 • Swap • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 18 15 auto (symm (lemma-R (C.H0 • C.CZ • C.S0 • C.S0 • C.H0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.H1 • C.W ^ 4 • C.Swap) (plus , Z⊗I)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗X) • R (plus , I⊗X) • H0 • CZ • S0 • S0 • H0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W ^ 4 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 18 13 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗X) • R (plus , I⊗X) • H1 • CZ • S0 • S0 • S1 • S1 • S1 • Swap • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 17 9 auto (symm (lemma-R (C.H1 • C.CZ • C.S0 • C.S0 • C.S1 • C.S1 • C.S1 • C.Swap) (plus , Z⊗I)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗X) • H1 • CZ • S0 • S0 • S1 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 17 5 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗X) • S0 • S0 • S0 • Swap • CZ • H0 • H1 • CZ • H1 • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 16 10 auto (symm (lemma-R (C.S0 • C.S0 • C.S0 • C.Swap • C.CZ • C.H0 • C.H1 • C.CZ • C.H1) (plus , Z⊗I)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • R (plus , I⊗Z) • S0 • S0 • S0 • Swap • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 15 5 auto (symm (lemma-R (C.S0 • C.S0 • C.S0 • C.Swap) (plus , Z⊗I)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • S0 • S0 • S0 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 15 3 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • R (plus , Z⊗Z) • CZ • S1 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 14 6 auto (symm (lemma-R (C.CZ • C.S1 • C.H0 • C.CZ • C.H0) (plus , Z⊗I)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • R (plus , I⊗Y) • CZ • S1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 13 3 auto (symm (lemma-R (C.CZ • C.S1) (plus , Z⊗X)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Y) • CZ • S1 • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 12 3 auto (symm (lemma-R (C.CZ • C.S1) (plus , I⊗X)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • CZ • S1 • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 11 3 auto (symm (lemma-R (C.CZ • C.S1) (plus , Z⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • R (plus , I⊗Z) • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 10 3 auto (symm (lemma-R (C.CZ • C.S1) (plus , I⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • R (plus , Z⊗Z) • CZ • S1 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 9 3 auto (symm (lemma-R (C.CZ • C.S1) (plus , Z⊗Z)))
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0 • H0 • H1 • CZ • S0 • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W ^ 6 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 46 14 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 36 9 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H1 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 30 5 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • Swap • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 20 9 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 83 2 auto (symm lemma-R-T0⁻¹)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 67 2 auto (symm lemma-R-T0⁻¹)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 49 2 auto (symm lemma-R-T0⁻¹)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 33 2 auto (symm lemma-R-T0⁻¹)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • R (plus , Z⊗I) • S0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 19 2 auto (symm lemma-R-T0⁻¹)
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 7 4 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • T0 • H0 • CZ • H0 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 4 6 10000 auto
      equals H0 • CZ • H0 • T0⁻¹ • T0 • H0 • CZ • H0 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals H0 • CZ • H0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • H0 • CZ • H0 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 3 8 auto lemma-order-T0
      equals H0 • CZ • H0 • H0 • CZ • H0 • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 0 6 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • S1⁻¹ • CZ • CZ • S1 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 71 4 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • R (plus , Z⊗Z) • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • T0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 68 6 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0⁻¹ • T0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 67 8 auto lemma-order-T0
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 64 6 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 53 22 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • T0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 52 8 auto lemma-order-T0
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 41 22 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , Z⊗Y) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • T0 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 36 10 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0⁻¹ • T0 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 35 8 auto lemma-order-T0
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • S1 • H1 • H0 • CZ • H0 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 30 10 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 21 18 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0⁻¹ • T0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 20 8 auto lemma-order-T0
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • H0 • CZ • H0 • H1 • CZ • H1 • H0 • CZ • H0 • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 11 18 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • H0 • CZ • H0 • H0 • CZ • H0 • T0 • H0 • CZ • H0 • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 8 6 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0⁻¹ • T0 • H0 • CZ • H0 • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • T0 • H0 • CZ • H0 • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by in-context 7 8 auto lemma-order-T0
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H0 • CZ • H0 • H0 • CZ • H0 • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 4 6 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W⁻¹ • ε
          by clifford-tactic 4 8 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (plus , Z⊗X) • H1 • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • CX1 • S1⁻¹ • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 3 11 auto (symm (lemma-correction Z⊗X))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • CX1 • S1⁻¹ • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 3 7 auto (symm (lemma-R (C.CX1 • C.S1⁻¹ • C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗X) • CX1 • S1⁻¹ • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 2 6 auto (symm (lemma-R (C.CX1 • C.S1⁻¹ • C.X0 • C.S1 • C.H1) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 2 auto (symm (lemma-R (C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 9 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 7 1 auto (symm lemma-R-T1)
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • X0 • CH1 • X0 • ε
          by in-context 2 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , I⊗Z) • CX1 • T1⁻¹ • X0 • CH1 • X0 • ε
          by in-context 0 1 auto (symm lemma-R-T1)
      equals T1 • CX1 • T1⁻¹ • X0 • CH1 • X0 • ε



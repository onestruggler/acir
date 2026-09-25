------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 40 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation40 where

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

eqn40 : Clifford+T.Rel ⊢ X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CH1 • X0 • ε === X0 • CH1 • X0 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
eqn40 = 
  equational X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CH1 • X0 • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CH1 • X0 • ε
          by in-context 7 1 auto lemma-R-T0⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CH1 • X0 • ε
          by in-context 9 1 auto lemma-R-T1⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CH1 • X0 • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 17 1 auto lemma-R-T1
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 19 1 auto lemma-R-T1⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 0 3 auto (lemma-R (C.X0 • C.CX0) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • X0 • CX0 • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 1 6 10000 auto
      equals R (minus , Z⊗Z) • H1 • CZ • S1 • S1 • H1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 6 auto (lemma-R (C.H1 • C.CZ • C.S1 • C.S1 • C.H1) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • H1 • CZ • S1 • S1 • H1 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 2 7 auto (lemma-R (C.H1 • C.CZ • C.S1 • C.S1 • C.H1 • C.S0⁻¹) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • H1 • CZ • S1 • S1 • H1 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 3 13 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • CZ • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 3 10 auto (lemma-R (C.CZ • C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗X) • CZ • H0 • S0 • S0 • H0 • S1 • S1 • H1 • W⁻¹ • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 4 10 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗X) • H0 • S0 • S0 • H0 • H1 • W⁻¹ • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 4 7 auto (lemma-R (C.H0 • C.S0 • C.S0 • C.H0 • C.H1 • C.W⁻¹) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗X) • R (plus , I⊗X) • H0 • S0 • S0 • H0 • H1 • W⁻¹ • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 5 10 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗X) • R (plus , I⊗X) • S1 • H1 • W ^ 6 • ε
          by in-context 0 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , Z⊗X) • R (plus , I⊗X) • S1 • H1 • W ^ 6 • ε
          by in-context 3 2 auto (symm (tactic-pauli-commute (plus , I⊗X) (minus , Z⊗X) auto))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • S1 • H1 • W ^ 6 • ε
          by in-context 1 2 auto (lemma-combine minus minus Z⊗Z)
      equals R (plus , Z⊗I) • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • R (plus , I⊗X) • R (minus , Z⊗X) • S1 • H1 • W ^ 6 • ε
          by in-context 1 9 auto (lemma-R (C.H0 • C.CZ • C.H0 • C.S0⁻¹ • C.W ^ 2 • C.H0 • C.CZ • C.H0) (plus , I⊗X))
      equals R (plus , Z⊗I) • R (minus , Z⊗Y) • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • R (minus , Z⊗X) • S1 • H1 • W ^ 6 • ε
          by in-context 2 9 auto (lemma-R (C.H0 • C.CZ • C.H0 • C.S0⁻¹ • C.W ^ 2 • C.H0 • C.CZ • C.H0) (minus , Z⊗X))
      equals R (plus , Z⊗I) • R (minus , Z⊗Y) • R (plus , I⊗Y) • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • S1 • H1 • W ^ 6 • ε
          by clifford-tactic 3 11 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Y) • R (plus , I⊗Y) • CZ • S0 • S0 • S0 • H1 • ε
          by in-context 1 2 auto (symm (tactic-pauli-commute (plus , I⊗Y) (minus , Z⊗Y) auto))
      equals R (plus , Z⊗I) • R (plus , I⊗Y) • R (minus , Z⊗Y) • CZ • S0 • S0 • S0 • H1 • ε
          by in-context 0 2 auto (symm (tactic-pauli-commute (plus , I⊗Y) (plus , Z⊗I) auto))
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • R (minus , Z⊗Y) • CZ • S0 • S0 • S0 • H1 • ε
          by clifford-tactic 3 5 10000 auto
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • R (minus , Z⊗Y) • H1 • Swap • S0⁻¹ • W ^ 2 • Swap • H1 • S1 • S1 • H1 • W⁻¹ • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 3 6 auto (symm (lemma-combine minus minus I⊗X))
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • R (minus , Z⊗Y) • R (minus , I⊗X) • R (minus , I⊗X) • S1 • S1 • H1 • W⁻¹ • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Y) auto)
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗I) • R (minus , I⊗X) • R (minus , I⊗X) • S1 • S1 • H1 • W⁻¹ • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , I⊗X) auto)
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗X) • R (plus , Z⊗I) • R (minus , I⊗X) • S1 • S1 • H1 • W⁻¹ • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 4 6 auto (symm (lemma-R (C.S1 • C.S1 • C.H1 • C.W⁻¹ • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗X) • R (plus , Z⊗I) • S1 • S1 • H1 • W⁻¹ • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 3 5 auto (symm (lemma-R (C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , Z⊗I)))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗X) • S1 • S1 • H1 • W⁻¹ • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by clifford-tactic 3 4 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗X) • CZ • H0 • H1 • CZ • S0 • S0 • H0 • W⁻¹ • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 2 9 auto (symm (lemma-R (C.CZ • C.H0 • C.H1 • C.CZ • C.S0 • C.S0 • C.H0 • C.W⁻¹) (plus , Z⊗I)))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • CZ • H0 • H1 • CZ • S0 • S0 • H0 • W⁻¹ • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by clifford-tactic 2 8 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 1 5 auto (symm (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 0 4 auto (symm (lemma-R (C.X0 • C.S1 • C.H1) (plus , I⊗Z)))
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 19 2 auto (symm lemma-R-T1⁻¹)
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
          by in-context 17 2 auto (symm lemma-R-T0⁻¹)
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
          by in-context 5 2 auto (symm lemma-R-T1⁻¹)
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
          by in-context 3 1 auto (symm lemma-R-T1)
      equals X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
          by general-assoc auto
      equals X0 • CH1 • X0 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε



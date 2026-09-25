------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 39 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation39 where

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

eqn39 : Clifford+T.Rel ⊢ T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε === X0 • CH1 • X0 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • ε
eqn39 = 
  equational T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
          by in-context 0 1 auto lemma-R-T0⁻¹
      equals R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
          by in-context 2 1 auto lemma-R-T1⁻¹
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
          by general-assoc auto
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 17 1 auto lemma-R-T1
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 19 1 auto lemma-R-T1⁻¹
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 10 7 10000 auto
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 2 auto (lemma-R (C.S0⁻¹) (plus , I⊗Z))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 2 8 auto (lemma-R (C.S0⁻¹ • C.S1⁻¹ • C.W • C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 3 13 10000 auto
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S0 • H1 • W⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 3 8 auto (lemma-R (C.H0 • C.S0 • C.S0 • C.H0 • C.S0 • C.H1 • C.W⁻¹) (plus , I⊗Z))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗X) • H0 • S0 • S0 • H0 • S0 • H1 • W⁻¹ • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 4 9 auto (lemma-R (C.H0 • C.S0 • C.S0 • C.H0 • C.S0 • C.H1 • C.W⁻¹ • C.CX1) (plus , I⊗Z))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • H0 • S0 • S0 • H0 • S0 • H1 • W⁻¹ • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 5 12 10000 auto
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by in-context 0 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗X) • R (minus , Z⊗X) • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by in-context 1 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗X) • R (minus , Z⊗X) • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (plus , I⊗X) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗X) • R (plus , Z⊗I) • R (minus , Z⊗X) • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by in-context 0 2 auto (lemma-combine plus plus I⊗Z)
      equals Swap • S0 • Swap • R (plus , I⊗X) • R (plus , Z⊗I) • R (minus , Z⊗X) • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by clifford-tactic 0 3 10000 auto
      equals S1 • R (plus , I⊗X) • R (plus , Z⊗I) • R (minus , Z⊗X) • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by in-context 0 2 auto (lemma-R (C.S1) (plus , I⊗X))
      equals R (plus , I⊗Y) • S1 • R (plus , Z⊗I) • R (minus , Z⊗X) • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by in-context 1 2 auto (lemma-R (C.S1) (plus , Z⊗I))
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • S1 • R (minus , Z⊗X) • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by in-context 2 2 auto (lemma-R (C.S1) (minus , Z⊗X))
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • R (minus , Z⊗Y) • S1 • CZ • S0 • S0 • S0 • S1 • S1 • S1 • H1 • ε
          by clifford-tactic 3 8 10000 auto
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • R (minus , Z⊗Y) • CZ • S0 • S0 • S0 • H1 • ε
          by clifford-tactic 3 5 10000 auto
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • R (minus , Z⊗Y) • H1 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • S1 • S1 • ε
          by in-context 3 9 auto (symm (lemma-combine plus plus Z⊗X))
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • R (minus , Z⊗Y) • R (plus , Z⊗X) • R (plus , Z⊗X) • CZ • S0 • S0 • S0 • H1 • S1 • S1 • S1 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Y) auto)
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗I) • R (plus , Z⊗X) • R (plus , Z⊗X) • CZ • S0 • S0 • S0 • H1 • S1 • S1 • S1 • ε
          by clifford-tactic 6 7 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗I) • R (plus , Z⊗X) • R (plus , Z⊗X) • CZ • H1 • W⁻¹ • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • CX0 • X0 • X1 • CX1 • ε
          by in-context 4 11 auto (symm (lemma-R (C.CZ • C.H1 • C.W⁻¹ • C.S0⁻¹ • C.S1⁻¹ • C.W • C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I)))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗I) • R (plus , Z⊗X) • CZ • H1 • W⁻¹ • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • ε
          by in-context 3 5 auto (symm (lemma-R (C.CZ • C.H1 • C.W⁻¹ • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗I) • CZ • H1 • W⁻¹ • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • ε
          by in-context 2 4 auto (symm (lemma-R (C.CZ • C.H1 • C.W⁻¹) (plus , Z⊗I)))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • CZ • H1 • W⁻¹ • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • ε
          by clifford-tactic 2 3 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • ε
          by in-context 1 5 auto (symm (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • ε
          by in-context 0 4 auto (symm (lemma-R (C.X0 • C.S1 • C.H1) (plus , I⊗Z)))
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • ε
          by in-context 12 2 auto (symm lemma-R-T1⁻¹)
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • ε
          by in-context 10 2 auto (symm lemma-R-T0⁻¹)
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • ε
          by in-context 5 2 auto (symm lemma-R-T1⁻¹)
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • ε
          by in-context 3 1 auto (symm lemma-R-T1)
      equals X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • ε
          by general-assoc auto
      equals X0 • CH1 • X0 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • ε



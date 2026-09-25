------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 7 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation7 where

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

eqn7 : Clifford+T.Rel ⊢ T1 • ε === X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
eqn7 = 
  equational T1 • ε
          by in-context 0 1 auto lemma-R-T1
      equals R (plus , I⊗Z) • ε
          by clifford-tactic 1 0 10000 auto
      equals R (plus , I⊗Z) • S0 • H0 • CZ • H0 • W • H0 • CZ • H0 • S0 • S0 • S0 • W⁻¹ • ε
          by in-context 2 7 auto (symm (lemma-combine plus minus Z⊗Z))
      equals R (plus , I⊗Z) • S0 • R (plus , Z⊗Z) • R (minus , Z⊗Z) • S0 • S0 • S0 • W⁻¹ • ε
          by in-context 1 1 auto (symm (lemma-combine plus plus Z⊗I))
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • S0 • S0 • S0 • W⁻¹ • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , Z⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • S0 • S0 • S0 • W⁻¹ • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • S0 • S0 • S0 • W⁻¹ • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • W⁻¹ • ε
          by in-context 0 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • W⁻¹ • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • W⁻¹ • ε
          by clifford-tactic 8 1 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • H1 • S1 • S1 • H1 • W⁻¹ • H1 • S1 • S1 • H1 • ε
          by in-context 4 9 auto (symm (lemma-R (C.S0 • C.S0 • C.S0 • C.H1 • C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S0 • S0 • S0 • H1 • S1 • S1 • H1 • W⁻¹ • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 4 8 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • CZ • S1 • W⁻¹ • CX1 • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 3 5 auto (symm (lemma-R (C.CZ • C.S1 • C.W⁻¹ • C.CX1) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • CZ • S1 • W⁻¹ • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 2 4 auto (symm (lemma-R (C.CZ • C.S1 • C.W⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • CZ • S1 • W⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 2 3 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • X1 • CX1 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 1 4 auto (symm (lemma-R (C.X1 • C.CX1 • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • X1 • CX1 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 0 3 auto (symm (lemma-R (C.X1 • C.CX1) (plus , Z⊗I)))
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 19 4 10000 auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 11 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 9 1 auto (symm lemma-R-T1)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 4 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 2 2 auto (symm lemma-R-T0⁻¹)
      equals X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε



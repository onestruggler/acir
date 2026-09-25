------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 8 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation8 where

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

eqn8 : Clifford+T.Rel ⊢ CZ • ε === CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
eqn8 = 
  equational CZ • ε
          by clifford-tactic 0 1 10000 auto
      equals Swap • S0 • Swap • Swap • S0 • Swap • Swap • S0⁻¹ • W ^ 2 • Swap • S0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • W ^ 6 • ε
          by in-context 25 7 auto (symm (lemma-combine plus plus Z⊗Z))
      equals Swap • S0 • Swap • Swap • S0 • Swap • Swap • S0⁻¹ • W ^ 2 • Swap • S0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 18 7 auto (symm (lemma-combine plus plus Z⊗Z))
      equals Swap • S0 • Swap • Swap • S0 • Swap • Swap • S0⁻¹ • W ^ 2 • Swap • S0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 11 7 auto (symm (lemma-combine plus plus Z⊗Z))
      equals Swap • S0 • Swap • Swap • S0 • Swap • Swap • S0⁻¹ • W ^ 2 • Swap • S0 • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 10 1 auto (symm (lemma-combine plus plus Z⊗I))
      equals Swap • S0 • Swap • Swap • S0 • Swap • Swap • S0⁻¹ • W ^ 2 • Swap • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 6 4 auto (symm (lemma-combine minus minus I⊗Z))
      equals Swap • S0 • Swap • Swap • S0 • Swap • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 3 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals Swap • S0 • Swap • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 0 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 9 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 10 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 11 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • W ^ 6 • ε
          by in-context 12 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 9 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 9 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 10 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 9 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 0 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • ε
          by clifford-tactic 14 1 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • W ^ 6 • H1 • S1 • S1 • H1 • ε
          by in-context 13 6 auto (symm (lemma-R (C.H1 • C.S1 • C.S1 • C.H1 • C.W ^ 6) (plus , Z⊗I)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • H1 • S1 • S1 • H1 • W ^ 6 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 13 5 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S1 • W ^ 6 • CX1 • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 12 6 auto (symm (lemma-R (C.CZ • C.S0 • C.S1 • C.W ^ 6 • C.CX1) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • CZ • S0 • S1 • W ^ 6 • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 11 5 auto (symm (lemma-R (C.CZ • C.S0 • C.S1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • CZ • S0 • S1 • W ^ 6 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 14 1 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • CZ • S0 • S1 • S1 • W ^ 6 • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 10 6 auto (symm (lemma-R (C.CZ • C.S0 • C.S1 • C.S1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S1 • S1 • W ^ 6 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 10 5 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • H1 • S1 • W ^ 6 • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 9 7 auto (symm (lemma-R (C.S1 • C.H1 • C.CZ • C.H1 • C.S1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • S1 • H1 • CZ • H1 • S1 • W ^ 6 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 9 6 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • H0 • CZ • H0 • S0 • H1 • S1 • S1 • H1 • W⁻¹ • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 8 10 auto (symm (lemma-R (C.H0 • C.CZ • C.H0 • C.S0 • C.H1 • C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • H0 • CZ • H0 • S0 • H1 • S1 • S1 • H1 • W⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 12 5 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • H0 • CZ • H0 • S0 • S0 • H1 • S1 • S1 • H1 • W⁻¹ • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 7 11 auto (symm (lemma-R (C.H0 • C.CZ • C.H0 • C.S0 • C.S0 • C.H1 • C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , Z⊗I)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • H0 • CZ • H0 • S0 • S0 • H1 • S1 • S1 • H1 • W⁻¹ • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 7 10 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W⁻¹ • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 6 10 auto (symm (lemma-R (C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , Z⊗I)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W⁻¹ • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 6 9 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • W⁻¹ • S1⁻¹ • CX1 • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 5 8 auto (symm (lemma-R (C.CZ • C.S0 • C.S0 • C.S0 • C.W⁻¹ • C.S1⁻¹ • C.CX1) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • CZ • S0 • S0 • S0 • W⁻¹ • S1⁻¹ • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 4 7 auto (symm (lemma-R (C.CZ • C.S0 • C.S0 • C.S0 • C.W⁻¹ • C.S1⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • CZ • S0 • S0 • S0 • W⁻¹ • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 3 6 auto (symm (lemma-R (C.CZ • C.S0 • C.S0 • C.S0 • C.W⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • W⁻¹ • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 3 5 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • H1 • S1 • S1 • S1 • W⁻¹ • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 2 9 auto (symm (lemma-R (C.S1 • C.H1 • C.CZ • C.H1 • C.S1 • C.S1 • C.S1 • C.W⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • S1 • H1 • CZ • H1 • S1 • S1 • S1 • W⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 2 8 10000 auto
      equals R (plus , Z⊗Z) • R (minus , I⊗Z) • CX1 • Swap • X1 • CX1 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 1 6 auto (symm (lemma-R (C.CX1 • C.Swap • C.X1 • C.CX1 • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗Z) • CX1 • Swap • X1 • CX1 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 0 5 auto (symm (lemma-R (C.CX1 • C.Swap • C.X1 • C.CX1) (plus , Z⊗I)))
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 53 4 10000 auto
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by clifford-tactic 26 5 10000 auto
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 50 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 48 1 auto (symm lemma-R-T1)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 46 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 44 1 auto (symm lemma-R-T1)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 38 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 36 2 auto (symm lemma-R-T0⁻¹)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 18 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 16 1 auto (symm lemma-R-T1)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 14 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 12 1 auto (symm lemma-R-T1)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 6 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 4 2 auto (symm lemma-R-T0⁻¹)
      equals CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε



------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 5 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation5 where

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

eqn5 : Clifford+T.Rel ⊢ S1 • ε === X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
eqn5 = 
  equational S1 • ε
          by clifford-tactic 0 1 10000 auto
      equals Swap • S0 • Swap • Swap • W • Swap • S0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • H0 • CZ • H0 • W • H0 • CZ • H0 • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 14 7 auto (symm (lemma-combine plus minus Z⊗Z))
      equals Swap • S0 • Swap • Swap • W • Swap • S0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 7 7 auto (symm (lemma-combine plus plus Z⊗Z))
      equals Swap • S0 • Swap • Swap • W • Swap • S0 • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 6 1 auto (symm (lemma-combine plus plus Z⊗I))
      equals Swap • S0 • Swap • Swap • W • Swap • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 3 3 auto (symm (lemma-combine plus minus I⊗Z))
      equals Swap • S0 • Swap • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 0 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (plus , Z⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (plus , Z⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , Z⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (minus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 0 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by clifford-tactic 13 4 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • H1 • S1 • S1 • H1 • S1 • W ^ 4 • H1 • S1 • S1 • H1 • ε
          by in-context 9 10 auto (symm (lemma-R (C.CZ • C.S0 • C.S0 • C.H1 • C.S1 • C.S1 • C.H1 • C.S1 • C.W ^ 4) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • H1 • S1 • S1 • H1 • S1 • W ^ 4 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 9 9 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S0 • S0 • S0 • W ^ 6 • CX1 • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 8 6 auto (symm (lemma-R (C.S0 • C.S0 • C.S0 • C.W ^ 6 • C.CX1) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • S0 • S0 • S0 • W ^ 6 • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 7 5 auto (symm (lemma-R (C.S0 • C.S0 • C.S0 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • S0 • S0 • S0 • W ^ 6 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 10 1 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • S0 • S0 • S0 • S1 • W ^ 6 • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 6 6 auto (symm (lemma-R (C.S0 • C.S0 • C.S0 • C.S1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • S0 • S0 • S0 • S1 • W ^ 6 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 6 5 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W ^ 6 • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 5 9 auto (symm (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S0 • C.S0 • C.H1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • W ^ 6 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 5 8 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W⁻¹ • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 4 14 auto (symm (lemma-R (C.S0 • C.H0 • C.CZ • C.H0 • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S0 • H0 • CZ • H0 • S0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 10 7 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S0 • H0 • CZ • H0 • S0 • S0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W⁻¹ • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 3 15 auto (symm (lemma-R (C.S0 • C.H0 • C.CZ • C.H0 • C.S0 • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • S0 • H0 • CZ • H0 • S0 • S0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • W⁻¹ • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 3 14 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • X1 • CX1 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 2 12 auto (symm (lemma-R (C.X1 • C.CX1 • C.S0⁻¹ • C.S1⁻¹ • C.W • C.X1 • C.CX1 • C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • X1 • CX1 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 1 4 auto (symm (lemma-R (C.X1 • C.CX1 • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • X1 • CX1 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 0 3 auto (symm (lemma-R (C.X1 • C.CX1) (plus , Z⊗I)))
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 44 4 10000 auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 36 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 34 1 auto (symm lemma-R-T1)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 32 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 30 1 auto (symm lemma-R-T1)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 24 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 22 2 auto (symm lemma-R-T0⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 4 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 2 2 auto (symm lemma-R-T0⁻¹)
      equals X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε



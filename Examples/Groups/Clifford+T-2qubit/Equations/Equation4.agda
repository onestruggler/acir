------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 4 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation4 where

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

eqn4 : Clifford+T.Rel ⊢ S0 • ε === Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
eqn4 = 
  equational S0 • ε
          by clifford-tactic 0 1 10000 auto
      equals Swap • S0 • Swap • Swap • W • Swap • S0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • H0 • CZ • H0 • W • H0 • CZ • H0 • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 14 7 auto (symm (lemma-combine plus minus Z⊗Z))
      equals Swap • S0 • Swap • Swap • W • Swap • S0 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 7 7 auto (symm (lemma-combine plus plus Z⊗Z))
      equals Swap • S0 • Swap • Swap • W • Swap • S0 • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 6 1 auto (symm (lemma-combine plus plus Z⊗I))
      equals Swap • S0 • Swap • Swap • W • Swap • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 3 3 auto (symm (lemma-combine plus minus I⊗Z))
      equals Swap • S0 • Swap • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 0 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (plus , Z⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (plus , Z⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , Z⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 7 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 8 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (minus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , I⊗Z) auto)
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CZ • S0 • S0 • S0 • S1 • S1 • W ^ 6 • ε
          by clifford-tactic 10 7 10000 auto
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • W ^ 6 • S1⁻¹ • CX1 • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • H1 • S1 • S1 • H1 • ε
          by in-context 9 10 auto (symm (lemma-R (C.W ^ 6 • C.S1⁻¹ • C.CX1 • C.S1⁻¹ • C.Swap • C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I)))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • W ^ 6 • S1⁻¹ • CX1 • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 8 4 auto (symm (lemma-R (C.W ^ 6 • C.S1⁻¹ • C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • W ^ 6 • S1⁻¹ • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 7 3 auto (symm (lemma-R (C.W ^ 6 • C.S1⁻¹) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • W ^ 6 • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 6 2 auto (symm (lemma-R (C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • W ^ 6 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 6 1 10000 auto
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • H1 • CZ • H1 • W ^ 6 • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 5 5 auto (symm (lemma-R (C.H1 • C.CZ • C.H1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • H1 • CZ • H1 • W ^ 6 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 5 4 10000 auto
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , I⊗Z) • H0 • CZ • H0 • H1 • S1 • S1 • H1 • S1 • W ^ 5 • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 4 10 auto (symm (lemma-R (C.H0 • C.CZ • C.H0 • C.H1 • C.S1 • C.S1 • C.H1 • C.S1 • C.W ^ 5) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • H0 • CZ • H0 • H1 • S1 • S1 • H1 • S1 • W ^ 5 • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 7 6 10000 auto
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • H0 • CZ • H0 • S0 • H1 • S1 • S1 • H1 • S1 • W ^ 5 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 3 11 auto (symm (lemma-R (C.H0 • C.CZ • C.H0 • C.S0 • C.H1 • C.S1 • C.S1 • C.H1 • C.S1 • C.W ^ 5) (plus , Z⊗I)))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • H0 • CZ • H0 • S0 • H1 • S1 • S1 • H1 • S1 • W ^ 5 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 3 10 10000 auto
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • S1 • H1 • CZ • S0 • S0 • S1 • S1 • H1 • S1 • W ^ 5 • H1 • CZ • H0 • H1 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 2 11 auto (symm (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.W ^ 5) (plus , Z⊗I)))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • S1 • H1 • CZ • S0 • S0 • S1 • S1 • H1 • S1 • W ^ 5 • R (plus , Z⊗I) • H1 • CZ • H0 • H1 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 2 10 10000 auto
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • Swap • X1 • CX1 • S0⁻¹ • H0 • CZ • S0 • S0 • H0 • S1 • S1 • S1 • W • R (plus , Z⊗I) • H1 • CZ • H0 • H1 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 1 5 auto (symm (lemma-R (C.Swap • C.X1 • C.CX1 • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • Swap • X1 • CX1 • S0⁻¹ • R (plus , I⊗Z) • H0 • CZ • S0 • S0 • H0 • S1 • S1 • S1 • W • R (plus , Z⊗I) • H1 • CZ • H0 • H1 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 0 4 auto (symm (lemma-R (C.Swap • C.X1 • C.CX1) (plus , Z⊗I)))
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • H0 • CZ • S0 • S0 • H0 • S1 • S1 • S1 • W • R (plus , Z⊗I) • H1 • CZ • H0 • H1 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 46 4 10000 auto
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • H0 • CZ • S0 • S0 • H0 • S1 • S1 • S1 • W • R (plus , Z⊗I) • H1 • CZ • H0 • H1 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by clifford-tactic 16 8 10000 auto
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • H0 • CZ • S0 • S0 • H0 • S1 • S1 • S1 • W • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by clifford-tactic 6 9 10000 auto
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 40 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 38 1 auto (symm lemma-R-T1)
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 36 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 34 1 auto (symm lemma-R-T1)
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 28 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 26 2 auto (symm lemma-R-T0⁻¹)
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 5 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 3 2 auto (symm lemma-R-T0⁻¹)
      equals Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε



------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 41 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation41 where

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

eqn41 : Clifford+T.Rel ⊢ X0 • CH1 • X0 • X1 • CX1 • ε === X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
eqn41 = 
  equational X0 • CH1 • X0 • X1 • CX1 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • X1 • CX1 • ε
          by in-context 3 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • X1 • CX1 • ε
          by in-context 5 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X1 • CX1 • ε
          by in-context 0 4 auto (lemma-R (C.X0 • C.S1 • C.H1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X1 • CX1 • ε
          by in-context 1 5 auto (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • X1 • CX1 • ε
          by clifford-tactic 2 10 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • S1 • S1 • H1 • W⁻¹ • ε
          by in-context 0 2 auto (tactic-pauli-commute (plus , I⊗Y) (minus , Z⊗Y) auto)
      equals R (minus , Z⊗Y) • R (plus , I⊗Y) • S1 • S1 • H1 • W⁻¹ • ε
          by clifford-tactic 2 4 10000 auto
      equals R (minus , Z⊗Y) • R (plus , I⊗Y) • CZ • W ^ 2 • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 1 3 auto (symm (lemma-R (C.CZ • C.W ^ 2) (plus , Z⊗Y)))
      equals R (minus , Z⊗Y) • CZ • W ^ 2 • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 0 3 auto (symm (lemma-R (C.CZ • C.W ^ 2) (minus , I⊗Y)))
      equals CZ • W ^ 2 • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by clifford-tactic 0 2 10000 auto
      equals Swap • S0 • Swap • S0 • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 4 8 auto (symm (lemma-combine minus minus Z⊗Z))
      equals Swap • S0 • Swap • S0 • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 3 1 auto (symm (lemma-combine plus plus Z⊗I))
      equals Swap • S0 • Swap • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 0 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 0 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • S1 • S1 • H1 • W ^ 5 • ε
          by clifford-tactic 9 4 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Y) • R (plus , Z⊗Y) • CZ • H0 • S0 • S0 • H0 • S1 • H1 • W ^ 6 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 7 9 auto (symm (lemma-R (C.CZ • C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.H1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Y) • CZ • H0 • S0 • S0 • H0 • S1 • H1 • W ^ 6 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 7 8 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (minus , I⊗Y) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • W ^ 6 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 6 10 auto (symm (lemma-R (C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.S1 • C.S1 • C.H1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • H1 • W ^ 6 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 7 8 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • H0 • CZ • S0 • S0 • H0 • S1 • S1 • W ^ 6 • Swap • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 5 10 auto (symm (lemma-R (C.H0 • C.CZ • C.S0 • C.S0 • C.H0 • C.S1 • C.S1 • C.W ^ 6 • C.Swap) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • H0 • CZ • S0 • S0 • H0 • S1 • S1 • W ^ 6 • Swap • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 5 9 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • H1 • CZ • S0 • S0 • S1 • S1 • H1 • S1 • S1 • S1 • W • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 4 12 auto (symm (lemma-R (C.H1 • C.CZ • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.S1 • C.W) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • H1 • CZ • S0 • S0 • S1 • S1 • H1 • S1 • S1 • S1 • W • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 8 7 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • H1 • CZ • S0 • S0 • S0 • S1 • S1 • H1 • S1 • S1 • S1 • W • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 3 13 auto (symm (lemma-R (C.H1 • C.CZ • C.S0 • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.S1 • C.W) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • H1 • CZ • S0 • S0 • S0 • S1 • S1 • H1 • S1 • S1 • S1 • W • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 3 12 10000 auto
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • X1 • CX1 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 2 12 auto (symm (lemma-R (C.X1 • C.CX1 • C.S0⁻¹ • C.S1⁻¹ • C.W • C.X1 • C.CX1 • C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • X1 • CX1 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 4 auto (symm (lemma-R (C.X1 • C.CX1 • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • X1 • CX1 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 0 3 auto (symm (lemma-R (C.X1 • C.CX1) (plus , Z⊗I)))
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • CZ • S0 • H0 • H1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 31 6 10000 auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H0 • CZ • S0 • S0 • H0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 14 5 10000 auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 41 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 39 1 auto (symm lemma-R-T1)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by general-assoc auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
          by in-context 22 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
          by in-context 20 2 auto (symm lemma-R-T0⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
          by general-assoc auto
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
          by in-context 4 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε
          by in-context 2 2 auto (symm lemma-R-T0⁻¹)
      equals X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • X0 • CH1 • X0 • ε



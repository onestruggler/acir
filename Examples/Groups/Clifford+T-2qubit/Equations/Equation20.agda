------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 20 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation20 where

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

eqn20 : Clifford+T.Rel ⊢ X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε === X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • ε
eqn20 = 
  equational X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
          by in-context 7 1 auto lemma-R-T0⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • ε
          by in-context 9 1 auto lemma-R-T1⁻¹
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 0 3 auto (lemma-R (C.X0 • C.CX0) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • X0 • CX0 • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by clifford-tactic 1 6 10000 auto
      equals R (minus , Z⊗Z) • H1 • CZ • S1 • S1 • H1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 1 6 auto (lemma-R (C.H1 • C.CZ • C.S1 • C.S1 • C.H1) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • H1 • CZ • S1 • S1 • H1 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • ε
          by in-context 2 7 auto (lemma-R (C.H1 • C.CZ • C.S1 • C.S1 • C.H1 • C.S0⁻¹) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • H1 • CZ • S1 • S1 • H1 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • ε
          by clifford-tactic 3 10 10000 auto
      equals R (minus , Z⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • CZ • S1 • W⁻¹ • ε
          by in-context 0 2 auto (symm (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto))
      equals R (plus , Z⊗I) • R (minus , Z⊗Z) • R (minus , Z⊗Z) • CZ • S1 • W⁻¹ • ε
          by in-context 1 2 auto (lemma-combine minus minus Z⊗Z)
      equals R (plus , Z⊗I) • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • CZ • S1 • W⁻¹ • ε
          by clifford-tactic 1 11 10000 auto
      equals R (plus , Z⊗I) • S0 • S0 • S0 • W • ε
          by clifford-tactic 1 3 10000 auto
      equals R (plus , Z⊗I) • S1 • S0⁻¹ • S1⁻¹ • W • ε
          by in-context 0 2 auto (symm (lemma-R (C.S1) (plus , Z⊗I)))
      equals S1 • R (plus , Z⊗I) • S0⁻¹ • S1⁻¹ • W • ε
          by clifford-tactic 0 1 10000 auto
      equals Swap • S0 • Swap • R (plus , Z⊗I) • S0⁻¹ • S1⁻¹ • W • ε
          by in-context 0 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • S0⁻¹ • S1⁻¹ • W • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • S0⁻¹ • S1⁻¹ • W • ε
          by in-context 2 2 auto (symm (lemma-R (C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by clifford-tactic 1 0 10000 auto
      equals R (plus , I⊗Z) • X1 • CX1 • X0 • CX0 • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 0 5 auto (symm (lemma-R (C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I)))
      equals X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 11 2 auto (symm lemma-R-T1⁻¹)
      equals X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • ε
          by in-context 9 2 auto (symm lemma-R-T0⁻¹)
      equals X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • ε
          by general-assoc auto
      equals X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • ε



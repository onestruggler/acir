------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 1 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation1 where

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

eqn1 : Clifford+T.Rel ⊢ W • ε === T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
eqn1 = 
  equational W • ε
          by clifford-tactic 0 1 10000 auto
      equals Swap • S0 • Swap • Swap • S0 • Swap • S0 • H0 • CZ • H0 • W • H0 • CZ • H0 • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 7 7 auto (symm (lemma-combine plus minus Z⊗Z))
      equals Swap • S0 • Swap • Swap • S0 • Swap • S0 • R (plus , Z⊗Z) • R (minus , Z⊗Z) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 6 1 auto (symm (lemma-combine plus plus Z⊗I))
      equals Swap • S0 • Swap • Swap • S0 • Swap • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 3 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals Swap • S0 • Swap • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 0 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (plus , Z⊗Z) • R (minus , Z⊗Z) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , Z⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 5 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 3 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 4 2 auto (tactic-pauli-commute (plus , I⊗Z) (minus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • S1 • S1 • ε
          by in-context 0 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • S1 • S1 • ε
          by clifford-tactic 13 0 10000 auto
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • S0 • S0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • H1 • S1 • S1 • H1 • ε
          by in-context 7 10 auto (symm (lemma-R (C.S0 • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.S1 • C.S1 • C.H1) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • S0 • S0 • S0 • S1 • S1 • H1 • S1 • S1 • H1 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 7 9 10000 auto
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • CZ • S1 • S1 • S1 • CX1 • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 6 6 auto (symm (lemma-R (C.CZ • C.S1 • C.S1 • C.S1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • R (plus , I⊗Z) • CZ • S1 • S1 • S1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 5 5 auto (symm (lemma-R (C.CZ • C.S1 • C.S1 • C.S1) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • CZ • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 5 4 10000 auto
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (minus , Z⊗Z) • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 4 9 auto (symm (lemma-R (C.S0⁻¹ • C.S1⁻¹ • C.W • C.X1 • C.CX1 • C.X0 • C.CX0 • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , I⊗Z) • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 3 8 auto (symm (lemma-R (C.S0⁻¹ • C.S1⁻¹ • C.W • C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • R (plus , I⊗Z) • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 2 8 auto (symm (lemma-R (C.S0⁻¹ • C.S1⁻¹ • C.W • C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I)))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • S0⁻¹ • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by in-context 1 2 auto (symm (lemma-R (C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • H1 • S1 • S1 • H1 • ε
          by clifford-tactic 28 4 10000 auto
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by clifford-tactic 10 0 10000 auto
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 27 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • R (plus , I⊗Z) • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 25 1 auto (symm lemma-R-T1)
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 19 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 17 2 auto (symm lemma-R-T0⁻¹)
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by general-assoc auto
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 2 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε
          by in-context 0 2 auto (symm lemma-R-T0⁻¹)
      equals T0⁻¹ • T1⁻¹ • W • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • X1 • CX1 • T0⁻¹ • T1⁻¹ • W • X1 • CX1 • Swap • T1 • CX1 • T1⁻¹ • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • CX1 • ε



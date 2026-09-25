------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 29 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation29 where

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

eqn29 : Clifford+T.Rel ⊢ X0 • CH1 • X0 • CX1 • ε === CX1 • X0 • CH1 • X0 • ε
eqn29 = 
  equational X0 • CH1 • X0 • CX1 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • CX1 • ε
          by in-context 3 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • CX1 • ε
          by in-context 5 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • CX1 • ε
          by in-context 0 4 auto (lemma-R (C.X0 • C.S1 • C.H1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • CX1 • ε
          by in-context 1 5 auto (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • CX1 • ε
          by clifford-tactic 2 9 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • H1 • W⁻¹ • ε
          by in-context 1 1 auto (lemma-correction Z⊗Y)
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • S1 • H1 • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • S1⁻¹ • H1 • W⁻¹ • ε
          by clifford-tactic 4 11 10000 auto
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • W⁻¹ • ε
          by clifford-tactic 3 8 10000 auto
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • S1 • S1 • H1 • CX1 • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 4 auto (symm (lemma-R (C.S1 • C.S1 • C.H1) (plus , Z⊗Y)))
      equals R (plus , I⊗Y) • S1 • S1 • H1 • R (plus , Z⊗Y) • CX1 • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 2 2 10000 auto
      equals R (plus , I⊗Y) • S1 • H1 • Swap • S0⁻¹ • W • Swap • H1 • S1⁻¹ • R (plus , Z⊗Y) • CX1 • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 0 9 auto (symm (lemma-correction I⊗Y))
      equals R (minus , I⊗Y) • R (plus , Z⊗Y) • CX1 • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 0 2 auto (tactic-pauli-commute (minus , I⊗Y) (plus , Z⊗Y) auto)
      equals R (plus , Z⊗Y) • R (minus , I⊗Y) • CX1 • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 6 auto (symm (lemma-R (C.CX1 • C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , Z⊗Y) • CX1 • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 0 5 auto (symm (lemma-R (C.CX1 • C.X0 • C.S1 • C.H1) (plus , I⊗Z)))
      equals CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 6 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 4 1 auto (symm lemma-R-T1)
      equals CX1 • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by general-assoc auto
      equals CX1 • X0 • CH1 • X0 • ε



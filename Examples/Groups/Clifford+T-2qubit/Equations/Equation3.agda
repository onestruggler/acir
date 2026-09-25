------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 3 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation3 where

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

eqn3 : Clifford+T.Rel ⊢ H1 • ε === Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • ε
eqn3 = 
  equational H1 • ε
          by clifford-tactic 0 1 10000 auto
      equals S1 • H1 • Swap • W • Swap • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • S0 • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • W ^ 6 • ε
          by in-context 7 11 auto (symm (lemma-combine plus plus Z⊗Y))
      equals S1 • H1 • Swap • W • Swap • H1 • S1⁻¹ • R (plus , Z⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • W ^ 6 • ε
          by in-context 0 7 auto (symm (lemma-combine plus minus I⊗Y))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • W ^ 6 • ε
          by in-context 1 2 auto (tactic-pauli-commute (minus , I⊗Y) (plus , Z⊗Y) auto)
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (minus , I⊗Y) (plus , Z⊗Y) auto)
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Y) • S1 • H1 • CZ • S0 • S0 • S0 • H1 • S1 • W ^ 6 • ε
          by clifford-tactic 6 7 10000 auto
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Y) • R (minus , I⊗Y) • S1 • H1 • CX1 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 3 12 auto (symm (lemma-R (C.S1 • C.H1 • C.CX1 • C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.S1 • C.S1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CX1 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 2 11 auto (symm (lemma-R (C.S1 • C.H1 • C.CX1 • C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.S1 • C.S1) (plus , I⊗Z)))
      equals R (plus , I⊗Y) • R (plus , Z⊗Y) • S1 • H1 • CX1 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 4 auto (symm (lemma-R (C.S1 • C.H1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Y) • S1 • H1 • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 0 3 auto (symm (lemma-R (C.S1 • C.H1) (plus , I⊗Z)))
      equals S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 5 7 10000 auto
      equals S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 0 0 10000 auto
      equals Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 25 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 23 1 auto (symm lemma-R-T1)
      equals Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by general-assoc auto
      equals Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • ε
          by in-context 10 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • ε
          by in-context 8 1 auto (symm lemma-R-T1)
      equals Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • ε
          by general-assoc auto
      equals Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • ε



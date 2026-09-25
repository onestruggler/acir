------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 22 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation22 where

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

eqn22 : Clifford+T.Rel ⊢ Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • X0 • CH1 • X0 • ε === X0 • CH1 • X0 • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • ε
eqn22 = 
  equational Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • X0 • CH1 • X0 • ε
          by general-assoc auto
      equals Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 14 1 auto lemma-R-T1
      equals Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 16 1 auto lemma-R-T1⁻¹
      equals Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 0 6 auto (lemma-R (C.Swap • C.X1 • C.CX1 • C.X0 • C.CX0) (plus , Z⊗I))
      equals R (plus , Z⊗I) • Swap • X1 • CX1 • X0 • CX0 • CX0 • X0 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 1 11 10000 auto
      equals R (plus , Z⊗I) • H0 • S0 • S0 • H0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 7 auto (lemma-R (C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.H1) (plus , I⊗Z))
      equals R (plus , Z⊗I) • R (plus , I⊗Y) • H0 • S0 • S0 • H0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 2 8 auto (lemma-R (C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z))
      equals R (plus , Z⊗I) • R (plus , I⊗Y) • R (minus , Z⊗Y) • H0 • S0 • S0 • H0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 3 11 10000 auto
      equals R (plus , Z⊗I) • R (plus , I⊗Y) • R (minus , Z⊗Y) • CZ • H1 • W⁻¹ • ε
          by in-context 0 2 auto (symm (tactic-pauli-commute (plus , I⊗Y) (plus , Z⊗I) auto))
      equals R (plus , I⊗Y) • R (plus , Z⊗I) • R (minus , Z⊗Y) • CZ • H1 • W⁻¹ • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , Z⊗I) (minus , Z⊗Y) auto)
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗I) • CZ • H1 • W⁻¹ • ε
          by clifford-tactic 3 3 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , Z⊗I) • S1 • S1 • H1 • W⁻¹ • CX0 • X0 • X1 • CX1 • Swap • ε
          by in-context 2 5 auto (symm (lemma-R (C.S1 • C.S1 • C.H1 • C.W⁻¹) (plus , Z⊗I)))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • S1 • S1 • H1 • W⁻¹ • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • ε
          by clifford-tactic 2 4 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • ε
          by in-context 1 5 auto (symm (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • ε
          by in-context 0 4 auto (symm (lemma-R (C.X0 • C.S1 • C.H1) (plus , I⊗Z)))
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • X1 • CX1 • Swap • ε
          by general-assoc auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • ε
          by in-context 5 2 auto (symm lemma-R-T1⁻¹)
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • ε
          by in-context 3 1 auto (symm lemma-R-T1)
      equals X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • ε
          by general-assoc auto
      equals X0 • CH1 • X0 • Swap • X1 • CX1 • X0 • CX0 • T0 • CX0 • X0 • X1 • CX1 • Swap • ε



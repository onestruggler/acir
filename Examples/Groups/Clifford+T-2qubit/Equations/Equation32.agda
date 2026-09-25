------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 32 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation32 where

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

eqn32 : Clifford+T.Rel ⊢ X1 • CX1 • T1 • CX1 • T1⁻¹ • ε === T1 • CX1 • T1⁻¹ • X1 • CX1 • ε
eqn32 = 
  equational X1 • CX1 • T1 • CX1 • T1⁻¹ • ε
          by in-context 2 1 auto lemma-R-T1
      equals X1 • CX1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • ε
          by in-context 4 1 auto lemma-R-T1⁻¹
      equals X1 • CX1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 0 3 auto (lemma-R (C.X1 • C.CX1) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • X1 • CX1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 1 4 auto (lemma-R (C.X1 • C.CX1 • C.CX1) (plus , I⊗Z))
      equals R (minus , Z⊗Z) • R (minus , I⊗Z) • X1 • CX1 • CX1 • S1⁻¹ • ε
          by in-context 0 2 auto (symm (tactic-pauli-commute (minus , I⊗Z) (minus , Z⊗Z) auto))
      equals R (minus , I⊗Z) • R (minus , Z⊗Z) • X1 • CX1 • CX1 • S1⁻¹ • ε
          by in-context 0 1 auto (lemma-correction I⊗Z)
      equals R (plus , I⊗Z) • Swap • S0⁻¹ • W • Swap • R (minus , Z⊗Z) • X1 • CX1 • CX1 • S1⁻¹ • ε
          by in-context 1 5 auto (lemma-R (C.Swap • C.S0⁻¹ • C.W • C.Swap) (minus , Z⊗Z))
      equals R (plus , I⊗Z) • R (minus , Z⊗Z) • Swap • S0⁻¹ • W • Swap • X1 • CX1 • CX1 • S1⁻¹ • ε
          by in-context 1 1 auto (lemma-correction Z⊗Z)
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • Swap • S0⁻¹ • W • Swap • X1 • CX1 • CX1 • S1⁻¹ • ε
          by clifford-tactic 2 16 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • CZ • S0 • S0 • S0 • H1 • S1 • S1 • H1 • S1 • W ^ 6 • ε
          by clifford-tactic 2 10 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • X1 • CX1 • ε
          by in-context 1 2 auto (symm (lemma-R (C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • X1 • CX1 • ε
          by in-context 2 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , I⊗Z) • CX1 • T1⁻¹ • X1 • CX1 • ε
          by in-context 0 1 auto (symm lemma-R-T1)
      equals T1 • CX1 • T1⁻¹ • X1 • CX1 • ε



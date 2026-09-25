------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 18 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation18 where

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

eqn18 : Clifford+T.Rel ⊢ T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • ε === ε
eqn18 = 
  equational T1 • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • ε
          by in-context 0 1 auto lemma-R-T1
      equals R (plus , I⊗Z) • CX1 • T1⁻¹ • T1 • CX1 • T1⁻¹ • ε
          by in-context 2 1 auto lemma-R-T1⁻¹
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • T1 • CX1 • T1⁻¹ • ε
          by in-context 4 1 auto lemma-R-T1
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • T1⁻¹ • ε
          by in-context 6 1 auto lemma-R-T1⁻¹
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 1 2 auto (lemma-R (C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 2 3 auto (lemma-R (C.CX1 • C.S1⁻¹) (plus , I⊗Z))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 3 4 auto (lemma-R (C.CX1 • C.S1⁻¹ • C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • CX1 • S1⁻¹ • CX1 • S1⁻¹ • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • CX1 • S1⁻¹ • ε
          by in-context 1 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • CX1 • S1⁻¹ • ε
          by in-context 0 2 auto (lemma-combine plus plus I⊗Z)
      equals Swap • S0 • Swap • R (plus , Z⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • CX1 • S1⁻¹ • ε
          by in-context 3 2 auto (lemma-combine plus plus Z⊗Z)
      equals Swap • S0 • Swap • H0 • CZ • H0 • S0 • H0 • CZ • H0 • CX1 • S1⁻¹ • CX1 • S1⁻¹ • ε
          by clifford-tactic 0 14 10000 auto
      equals ε



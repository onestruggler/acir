------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 36 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation36 where

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

eqn36 : Clifford+T.Rel ⊢ Swap • T1 • CX1 • T1⁻¹ • Swap • ε === T1 • CX1 • T1⁻¹ • Swap • T1 • CX1 • T1⁻¹ • ε
eqn36 = 
  equational Swap • T1 • CX1 • T1⁻¹ • Swap • ε
          by in-context 1 1 auto lemma-R-T1
      equals Swap • R (plus , I⊗Z) • CX1 • T1⁻¹ • Swap • ε
          by in-context 3 1 auto lemma-R-T1⁻¹
      equals Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • ε
          by in-context 0 2 auto (lemma-R (C.Swap) (plus , I⊗Z))
      equals R (plus , Z⊗I) • Swap • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • ε
          by in-context 1 3 auto (lemma-R (C.Swap • C.CX1) (plus , I⊗Z))
      equals R (plus , Z⊗I) • R (plus , Z⊗Z) • Swap • CX1 • S1⁻¹ • Swap • ε
          by clifford-tactic 2 4 10000 auto
      equals R (plus , Z⊗I) • R (plus , Z⊗Z) • H0 • CZ • H0 • S0 • S0 • S0 • ε
          by clifford-tactic 2 6 10000 auto
      equals R (plus , Z⊗I) • R (plus , Z⊗Z) • S1 • CX1 • S1⁻¹ • Swap • CX1 • S1⁻¹ • ε
          by in-context 1 2 auto (symm (lemma-R (C.S1) (plus , Z⊗Z)))
      equals R (plus , Z⊗I) • S1 • R (plus , Z⊗Z) • CX1 • S1⁻¹ • Swap • CX1 • S1⁻¹ • ε
          by in-context 0 2 auto (symm (lemma-R (C.S1) (plus , Z⊗I)))
      equals S1 • R (plus , Z⊗I) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • Swap • CX1 • S1⁻¹ • ε
          by clifford-tactic 0 1 10000 auto
      equals Swap • S0 • Swap • R (plus , Z⊗I) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • Swap • CX1 • S1⁻¹ • ε
          by in-context 0 3 auto (symm (lemma-combine plus plus I⊗Z))
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • Swap • CX1 • S1⁻¹ • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , Z⊗I) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CX1 • S1⁻¹ • Swap • CX1 • S1⁻¹ • ε
          by in-context 1 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , I⊗Z) • R (plus , Z⊗I) • CX1 • S1⁻¹ • Swap • CX1 • S1⁻¹ • ε
          by in-context 2 2 auto (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • R (plus , I⊗Z) • CX1 • S1⁻¹ • Swap • CX1 • S1⁻¹ • ε
          by in-context 3 5 auto (symm (lemma-R (C.CX1 • C.S1⁻¹ • C.Swap • C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (plus , Z⊗I) • CX1 • S1⁻¹ • Swap • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 2 4 auto (symm (lemma-R (C.CX1 • C.S1⁻¹ • C.Swap) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 1 2 auto (symm (lemma-R (C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • ε
          by in-context 7 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • R (plus , I⊗Z) • CX1 • T1⁻¹ • ε
          by in-context 5 1 auto (symm lemma-R-T1)
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • Swap • T1 • CX1 • T1⁻¹ • ε
          by in-context 2 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , I⊗Z) • CX1 • T1⁻¹ • Swap • T1 • CX1 • T1⁻¹ • ε
          by in-context 0 1 auto (symm lemma-R-T1)
      equals T1 • CX1 • T1⁻¹ • Swap • T1 • CX1 • T1⁻¹ • ε



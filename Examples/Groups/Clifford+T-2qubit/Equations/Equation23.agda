------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 23 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation23 where

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

eqn23 : Clifford+T.Rel ⊢ T0⁻¹ • T1⁻¹ • W • Swap • ε === Swap • T0⁻¹ • T1⁻¹ • W • ε
eqn23 = 
  equational T0⁻¹ • T1⁻¹ • W • Swap • ε
          by in-context 0 1 auto lemma-R-T0⁻¹
      equals R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • Swap • ε
          by in-context 2 1 auto lemma-R-T1⁻¹
      equals R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • Swap • ε
          by in-context 1 2 auto (lemma-R (C.S0⁻¹) (plus , I⊗Z))
      equals R (plus , Z⊗I) • R (plus , I⊗Z) • S0⁻¹ • S1⁻¹ • W • Swap • ε
          by in-context 0 2 auto (symm (tactic-pauli-commute (plus , I⊗Z) (plus , Z⊗I) auto))
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • S0⁻¹ • S1⁻¹ • W • Swap • ε
          by clifford-tactic 2 4 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • CZ • H0 • H1 • CZ • H0 • H1 • CZ • H0 • S0 • S0 • S0 • H1 • S1 • S1 • S1 • W • ε
          by clifford-tactic 2 15 10000 auto
      equals R (plus , I⊗Z) • R (plus , Z⊗I) • Swap • S0⁻¹ • S1⁻¹ • W • ε
          by in-context 1 3 auto (symm (lemma-R (C.Swap • C.S0⁻¹) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • Swap • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 0 2 auto (symm (lemma-R (C.Swap) (plus , Z⊗I)))
      equals Swap • R (plus , Z⊗I) • S0⁻¹ • R (plus , I⊗Z) • S1⁻¹ • W • ε
          by in-context 3 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • R (plus , Z⊗I) • S0⁻¹ • T1⁻¹ • W • ε
          by in-context 1 2 auto (symm lemma-R-T0⁻¹)
      equals Swap • T0⁻¹ • T1⁻¹ • W • ε



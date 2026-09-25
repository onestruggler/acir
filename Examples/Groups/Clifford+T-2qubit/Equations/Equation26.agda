------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 26 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation26 where

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

eqn26 : Clifford+T.Rel ⊢ X0 • CX0 • T0 • CX0 • X0 • CX1 • ε === T1 • CX1 • T1⁻¹ • X0 • CX0 • T0 • CX0 • X0 • ε
eqn26 = 
  equational X0 • CX0 • T0 • CX0 • X0 • CX1 • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • CX1 • ε
          by in-context 0 3 auto (lemma-R (C.X0 • C.CX0) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • X0 • CX0 • CX0 • X0 • CX1 • ε
          by clifford-tactic 1 5 10000 auto
      equals R (minus , Z⊗Z) • H1 • CZ • H1 • ε
          by in-context 0 1 auto (lemma-correction Z⊗Z)
      equals R (plus , Z⊗Z) • H0 • CZ • H0 • S0⁻¹ • W • H0 • CZ • H0 • H1 • CZ • H1 • ε
          by clifford-tactic 1 11 10000 auto
      equals R (plus , Z⊗Z) • H1 • CZ • H1 • S1 • S1 • S1 • W • ε
          by clifford-tactic 1 7 10000 auto
      equals R (plus , Z⊗Z) • W • CX1 • S1⁻¹ • X0 • CX0 • CX0 • X0 • ε
          by in-context 0 2 auto (symm (lemma-R (C.W) (plus , Z⊗Z)))
      equals W • R (plus , Z⊗Z) • CX1 • S1⁻¹ • X0 • CX0 • CX0 • X0 • ε
          by clifford-tactic 0 1 10000 auto
      equals Swap • W • Swap • R (plus , Z⊗Z) • CX1 • S1⁻¹ • X0 • CX0 • CX0 • X0 • ε
          by in-context 0 3 auto (symm (lemma-combine plus minus I⊗Z))
      equals R (plus , I⊗Z) • R (minus , I⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • X0 • CX0 • CX0 • X0 • ε
          by in-context 1 2 auto (tactic-pauli-commute (minus , I⊗Z) (plus , Z⊗Z) auto)
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • R (minus , I⊗Z) • CX1 • S1⁻¹ • X0 • CX0 • CX0 • X0 • ε
          by in-context 2 5 auto (symm (lemma-R (C.CX1 • C.S1⁻¹ • C.X0 • C.CX0) (plus , Z⊗I)))
      equals R (plus , I⊗Z) • R (plus , Z⊗Z) • CX1 • S1⁻¹ • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • ε
          by in-context 1 2 auto (symm (lemma-R (C.CX1) (plus , I⊗Z)))
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • ε
          by general-assoc auto
      equals R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • X0 • CX0 • T0 • CX0 • X0 • ε
          by in-context 2 2 auto (symm lemma-R-T1⁻¹)
      equals R (plus , I⊗Z) • CX1 • T1⁻¹ • X0 • CX0 • T0 • CX0 • X0 • ε
          by in-context 0 1 auto (symm lemma-R-T1)
      equals T1 • CX1 • T1⁻¹ • X0 • CX0 • T0 • CX0 • X0 • ε



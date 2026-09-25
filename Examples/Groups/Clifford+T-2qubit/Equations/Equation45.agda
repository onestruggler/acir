------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 45 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation45 where

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

eqn45 : Clifford+T.Rel ⊢ X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε === Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
eqn45 = 
  equational X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by in-context 3 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by in-context 5 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by in-context 18 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by in-context 20 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by in-context 34 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by in-context 36 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • ε
          by in-context 49 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • ε
          by in-context 51 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • ε
          by clifford-tactic 6 12 10000 auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • ε
          by clifford-tactic 16 13 10000 auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • ε
          by clifford-tactic 26 12 10000 auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • ε
          by clifford-tactic 36 8 10000 auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by in-context 0 4 auto (lemma-R (C.X0 • C.S1 • C.H1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by in-context 1 5 auto (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by clifford-tactic 2 11 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • CZ • H1 • S1 • H1 • W⁻¹ • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by in-context 2 6 auto (lemma-R (C.CZ • C.H1 • C.S1 • C.H1 • C.W⁻¹) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • CZ • H1 • S1 • H1 • W⁻¹ • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by in-context 3 7 auto (lemma-R (C.CZ • C.H1 • C.S1 • C.H1 • C.W⁻¹ • C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • CZ • H1 • S1 • H1 • W⁻¹ • CX1 • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by clifford-tactic 4 10 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • S1 • H1 • CZ • S0 • S0 • H0 • H1 • S1 • S1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by in-context 4 13 auto (lemma-R (C.S1 • C.H1 • C.CZ • C.S0 • C.S0 • C.H0 • C.H1 • C.S1 • C.S1 • C.S1 • C.W ^ 6 • C.Swap) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , X⊗Y) • S1 • H1 • CZ • S0 • S0 • H0 • H1 • S1 • S1 • S1 • W ^ 6 • Swap • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by clifford-tactic 5 13 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , X⊗Y) • H0 • CZ • H0 • H1 • CZ • S1 • H1 • S1 • W ^ 5 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by in-context 5 10 auto (lemma-R (C.H0 • C.CZ • C.H0 • C.H1 • C.CZ • C.S1 • C.H1 • C.S1 • C.W ^ 5) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • H0 • CZ • H0 • H1 • CZ • S1 • H1 • S1 • W ^ 5 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by clifford-tactic 6 16 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • H1 • CZ • H0 • S0 • H0 • S1 • S1 • H1 • W ^ 5 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by in-context 6 11 auto (lemma-R (C.H1 • C.CZ • C.H0 • C.S0 • C.H0 • C.S1 • C.S1 • C.H1 • C.W ^ 5 • C.Swap) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (minus , Y⊗X) • H1 • CZ • H0 • S0 • H0 • S1 • S1 • H1 • W ^ 5 • Swap • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by clifford-tactic 7 11 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (minus , Y⊗X) • H0 • CZ • S0 • S0 • H0 • S1 • H1 • S1 • W ^ 4 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by in-context 7 10 auto (lemma-R (C.H0 • C.CZ • C.S0 • C.S0 • C.H0 • C.S1 • C.H1 • C.S1 • C.W ^ 4) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (minus , Y⊗X) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • S1 • H1 • S1 • W ^ 4 • H1 • S1 • H1 • W⁻¹ • Swap • ε
          by clifford-tactic 13 8 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (minus , Y⊗X) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (minus , I⊗Y) (minus , Z⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , I⊗Y) • R (minus , Z⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (minus , Y⊗X) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 1 2 auto (symm (tactic-pauli-commute (minus , I⊗Y) (minus , Z⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (minus , Y⊗X) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 4 2 auto (symm (tactic-pauli-commute (minus , Y⊗X) (minus , X⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 3 2 auto (symm (tactic-pauli-commute (minus , Y⊗X) (minus , Z⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Y⊗X) • R (minus , Z⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (minus , Y⊗X) (minus , Z⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (minus , Y⊗X) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 5 2 auto (symm (tactic-pauli-commute (minus , Y⊗X) (minus , X⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (minus , Y⊗X) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 4 2 auto (symm (tactic-pauli-commute (minus , Y⊗X) (minus , Z⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (minus , Y⊗X) • R (minus , Z⊗Y) • R (minus , Y⊗X) • R (minus , Z⊗Y) • R (minus , X⊗Y) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 3 2 auto (symm (tactic-pauli-commute (minus , Y⊗X) (minus , Z⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (minus , Y⊗X) • R (minus , Y⊗X) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (minus , X⊗Y) • R (plus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 6 2 auto (symm (tactic-pauli-commute (plus , X⊗Y) (minus , X⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , I⊗Y) • R (minus , Y⊗X) • R (minus , Y⊗X) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (plus , X⊗Y) • R (minus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 0 2 auto (lemma-combine plus minus I⊗Y)
      equals S1 • H1 • Swap • W • Swap • H1 • S1⁻¹ • R (minus , Y⊗X) • R (minus , Y⊗X) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (plus , X⊗Y) • R (minus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 7 2 auto (lemma-combine minus minus Y⊗X)
      equals S1 • H1 • Swap • W • Swap • H1 • S1⁻¹ • H1 • S0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • S0⁻¹ • H1 • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (plus , X⊗Y) • R (minus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 17 2 auto (lemma-combine minus minus Z⊗Y)
      equals S1 • H1 • Swap • W • Swap • H1 • S1⁻¹ • H1 • S0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • S0⁻¹ • H1 • S1 • H1 • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • H1 • S1⁻¹ • R (plus , X⊗Y) • R (minus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by in-context 29 2 auto (lemma-combine plus minus X⊗Y)
      equals S1 • H1 • Swap • W • Swap • H1 • S1⁻¹ • H1 • S0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • S0⁻¹ • H1 • S1 • H1 • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • CZ • H0 • W • H0 • CZ • H1 • S1⁻¹ • H0 • CZ • S0 • S0 • H0 • W ^ 4 • Swap • ε
          by clifford-tactic 0 45 10000 auto
      equals H0 • H1 • ε
          by clifford-tactic 0 2 10000 auto
      equals S0 • H0 • W • H0 • S0⁻¹ • S1 • H1 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H1 • S1⁻¹ • S0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • S0⁻¹ • H1 • S0 • CZ • H0 • W • H0 • CZ • S0⁻¹ • H1 • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 23 9 auto (symm (lemma-combine plus minus Y⊗X))
      equals S0 • H0 • W • H0 • S0⁻¹ • S1 • H1 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H1 • S1⁻¹ • S0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • S0⁻¹ • R (plus , Y⊗X) • R (minus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 15 8 auto (symm (lemma-combine minus minus Y⊗Z))
      equals S0 • H0 • W • H0 • S0⁻¹ • S1 • H1 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H1 • S1⁻¹ • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (plus , Y⊗X) • R (minus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 5 10 auto (symm (lemma-combine minus minus X⊗Y))
      equals S0 • H0 • W • H0 • S0⁻¹ • R (minus , X⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (plus , Y⊗X) • R (minus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 0 5 auto (symm (lemma-combine plus minus Y⊗I))
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (minus , X⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (plus , Y⊗X) • R (minus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 6 2 auto (tactic-pauli-commute (plus , Y⊗X) (minus , Y⊗X) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (minus , X⊗Y) • R (minus , X⊗Y) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗X) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 3 2 auto (tactic-pauli-commute (minus , X⊗Y) (minus , Y⊗Z) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (minus , X⊗Y) • R (minus , Y⊗Z) • R (minus , X⊗Y) • R (minus , Y⊗Z) • R (minus , Y⊗X) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 4 2 auto (tactic-pauli-commute (minus , X⊗Y) (minus , Y⊗Z) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (minus , X⊗Y) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 5 2 auto (tactic-pauli-commute (minus , X⊗Y) (minus , Y⊗X) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (minus , X⊗Y) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 2 2 auto (tactic-pauli-commute (minus , X⊗Y) (minus , Y⊗Z) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (minus , Y⊗Z) • R (minus , X⊗Y) • R (minus , Y⊗Z) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 3 2 auto (tactic-pauli-commute (minus , X⊗Y) (minus , Y⊗Z) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , X⊗Y) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 4 2 auto (tactic-pauli-commute (minus , X⊗Y) (minus , Y⊗X) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (minus , X⊗Y) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 1 2 auto (tactic-pauli-commute (minus , Y⊗I) (minus , Y⊗Z) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (minus , X⊗Y) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by in-context 2 2 auto (tactic-pauli-commute (minus , Y⊗I) (minus , Y⊗Z) auto)
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (minus , X⊗Y) • R (plus , Y⊗X) • H1 • CZ • S1 • S1 • H1 • W ^ 4 • Swap • ε
          by clifford-tactic 8 7 10000 auto
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (minus , X⊗Y) • R (plus , Y⊗X) • H0 • CZ • S0 • S0 • H0 • H1 • S1 • H1 • W ^ 5 • CX1 • H1 • S1 • H1 • W⁻¹ • ε
          by in-context 7 11 auto (symm (lemma-R (C.H0 • C.CZ • C.S0 • C.S0 • C.H0 • C.H1 • C.S1 • C.H1 • C.W ^ 5 • C.CX1) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • R (minus , Y⊗X) • R (minus , X⊗Y) • R (minus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • H1 • S1 • H1 • W ^ 5 • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by in-context 6 10 auto (symm (lemma-R (C.H0 • C.CZ • C.S0 • C.S0 • C.H0 • C.H1 • C.S1 • C.H1 • C.W ^ 5) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • R (minus , Y⊗X) • R (minus , X⊗Y) • H0 • CZ • S0 • S0 • H0 • H1 • S1 • H1 • W ^ 5 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by clifford-tactic 8 7 10000 auto
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • R (minus , Y⊗X) • R (minus , X⊗Y) • H0 • CZ • H0 • S1 • S1 • S1 • H1 • W ^ 6 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by in-context 5 9 auto (symm (lemma-R (C.H0 • C.CZ • C.H0 • C.S1 • C.S1 • C.S1 • C.H1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • R (minus , Y⊗X) • H0 • CZ • H0 • S1 • S1 • S1 • H1 • W ^ 6 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by clifford-tactic 5 8 10000 auto
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • R (minus , Y⊗X) • S0 • H0 • CZ • H0 • S0 • S0 • S0 • S1 • S1 • H1 • W ^ 6 • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by in-context 4 12 auto (symm (lemma-R (C.S0 • C.H0 • C.CZ • C.H0 • C.S0 • C.S0 • C.S0 • C.S1 • C.S1 • C.H1 • C.W ^ 6) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • S0 • H0 • CZ • H0 • S0 • S0 • S0 • S1 • S1 • H1 • W ^ 6 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by clifford-tactic 4 11 10000 auto
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • R (minus , Y⊗I) • CZ • H0 • S0 • H0 • W⁻¹ • Swap • CX1 • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by in-context 3 8 auto (symm (lemma-R (C.CZ • C.H0 • C.S0 • C.H0 • C.W⁻¹ • C.Swap • C.CX1) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • R (minus , Y⊗Z) • CZ • H0 • S0 • H0 • W⁻¹ • Swap • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by in-context 2 7 auto (symm (lemma-R (C.CZ • C.H0 • C.S0 • C.H0 • C.W⁻¹ • C.Swap) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • CZ • H0 • S0 • H0 • W⁻¹ • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by clifford-tactic 2 6 10000 auto
      equals R (plus , Y⊗I) • R (minus , Y⊗Z) • Swap • X0 • S1 • H1 • CX1 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by in-context 1 6 auto (symm (lemma-R (C.Swap • C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • Swap • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by in-context 0 5 auto (symm (lemma-R (C.Swap • C.X0 • C.S1 • C.H1) (plus , I⊗Z)))
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H1 • S1 • H1 • W⁻¹ • ε
          by clifford-tactic 37 4 10000 auto
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by clifford-tactic 27 7 10000 auto
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S0 • H0 • S1 • H1 • S1 • W ^ 6 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by clifford-tactic 17 7 10000 auto
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by clifford-tactic 7 7 10000 auto
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by in-context 50 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by in-context 48 1 auto (symm lemma-R-T1)
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by general-assoc auto
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by in-context 35 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by in-context 33 1 auto (symm lemma-R-T1)
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by general-assoc auto
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by in-context 21 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by in-context 19 1 auto (symm lemma-R-T1)
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by general-assoc auto
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by in-context 6 2 auto (symm lemma-R-T1⁻¹)
      equals Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by in-context 4 1 auto (symm lemma-R-T1)
      equals Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε
          by general-assoc auto
      equals Swap • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • X0 • CH1 • X0 • Swap • CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • ε



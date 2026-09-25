------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 2 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation2 where

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

eqn2 : Clifford+T.Rel ⊢ H0 • ε === CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • Swap • ε
eqn2 = 
  equational H0 • ε
          by clifford-tactic 0 1 10000 auto
      equals S0 • H0 • W • H0 • S0⁻¹ • S0 • CZ • H0 • S0 • H0 • CZ • S0⁻¹ • S0 • H0 • CZ • H0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 5 7 auto (symm (lemma-combine plus plus Y⊗Z))
      equals S0 • H0 • W • H0 • S0⁻¹ • R (plus , Y⊗Z) • R (plus , Y⊗Z) • S0 • H0 • CZ • H0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 0 5 auto (symm (lemma-combine plus minus Y⊗I))
      equals R (plus , Y⊗I) • R (minus , Y⊗I) • R (plus , Y⊗Z) • R (plus , Y⊗Z) • S0 • H0 • CZ • H0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 1 2 auto (tactic-pauli-commute (minus , Y⊗I) (plus , Y⊗Z) auto)
      equals R (plus , Y⊗I) • R (plus , Y⊗Z) • R (minus , Y⊗I) • R (plus , Y⊗Z) • S0 • H0 • CZ • H0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 2 2 auto (tactic-pauli-commute (minus , Y⊗I) (plus , Y⊗Z) auto)
      equals R (plus , Y⊗I) • R (plus , Y⊗Z) • R (plus , Y⊗Z) • R (minus , Y⊗I) • S0 • H0 • CZ • H0 • S0 • S1 • S1 • S1 • W ^ 6 • ε
          by clifford-tactic 6 7 10000 auto
      equals R (plus , Y⊗I) • R (plus , Y⊗Z) • R (plus , Y⊗Z) • R (minus , Y⊗I) • S0 • H0 • Swap • CX1 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by in-context 3 13 auto (symm (lemma-R (C.S0 • C.H0 • C.Swap • C.CX1 • C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.S1 • C.S1 • C.CX1) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • R (plus , Y⊗Z) • R (plus , Y⊗Z) • S0 • H0 • Swap • CX1 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by in-context 2 12 auto (symm (lemma-R (C.S0 • C.H0 • C.Swap • C.CX1 • C.H0 • C.S0 • C.S0 • C.H0 • C.S1 • C.S1 • C.S1) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • R (plus , Y⊗Z) • S0 • H0 • Swap • CX1 • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by in-context 1 5 auto (symm (lemma-R (C.S0 • C.H0 • C.Swap • C.CX1) (plus , I⊗Z)))
      equals R (plus , Y⊗I) • S0 • H0 • Swap • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by in-context 0 4 auto (symm (lemma-R (C.S0 • C.H0 • C.Swap) (plus , I⊗Z)))
      equals S0 • H0 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • H0 • S0 • S0 • H0 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by clifford-tactic 6 7 10000 auto
      equals S0 • H0 • Swap • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by clifford-tactic 0 3 10000 auto
      equals CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by in-context 24 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by in-context 22 1 auto (symm lemma-R-T1)
      equals CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • ε
          by general-assoc auto
      equals CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • Swap • ε
          by in-context 9 2 auto (symm lemma-R-T1⁻¹)
      equals CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • Swap • ε
          by in-context 7 1 auto (symm lemma-R-T1)
      equals CX1 • X1 • CX1 • Swap • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • Swap • ε
          by general-assoc auto
      equals CX1 • X1 • CX1 • Swap • X0 • CH1 • X0 • Swap • X1 • CX1 • CX1 • Swap • X0 • CH1 • X0 • Swap • ε



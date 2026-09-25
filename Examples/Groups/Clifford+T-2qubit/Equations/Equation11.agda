------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 11 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation11 where

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

eqn11 : Clifford+T.Rel ⊢ X0 • CH1 • X0 • X0 • CH1 • X0 • ε === ε
eqn11 = 
  equational X0 • CH1 • X0 • X0 • CH1 • X0 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CH1 • X0 • ε
          by in-context 3 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CH1 • X0 • ε
          by in-context 5 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • CH1 • X0 • ε
          by general-assoc auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • S1 • H1 • T1 • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 13 1 auto lemma-R-T1
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • T1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 15 1 auto lemma-R-T1⁻¹
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 6 7 10000 auto
      equals X0 • S1 • H1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 0 4 auto (lemma-R (C.X0 • C.S1 • C.H1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • R (plus , I⊗Z) • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 1 5 auto (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • S1 • S1 • S1 • R (plus , I⊗Z) • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 2 8 auto (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1 • C.S1 • C.S1 • C.S1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • X0 • S1 • H1 • CX1 • S1 • S1 • S1 • CX1 • R (plus , I⊗Z) • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by in-context 3 9 auto (lemma-R (C.X0 • C.S1 • C.H1 • C.CX1 • C.S1 • C.S1 • C.S1 • C.CX1) (plus , I⊗Z))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (plus , I⊗Y) • X0 • S1 • H1 • CX1 • S1 • S1 • S1 • CX1 • S1⁻¹ • H1 • S1⁻¹ • X0 • ε
          by clifford-tactic 4 12 10000 auto
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • R (plus , I⊗Y) • S1 • H1 • CZ • S0 • H1 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 2 2 auto (symm (tactic-pauli-commute (plus , I⊗Y) (minus , Z⊗Y) auto))
      equals R (plus , I⊗Y) • R (minus , Z⊗Y) • R (plus , I⊗Y) • R (minus , Z⊗Y) • S1 • H1 • CZ • S0 • H1 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 1 2 auto (symm (tactic-pauli-commute (plus , I⊗Y) (minus , Z⊗Y) auto))
      equals R (plus , I⊗Y) • R (plus , I⊗Y) • R (minus , Z⊗Y) • R (minus , Z⊗Y) • S1 • H1 • CZ • S0 • H1 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 0 2 auto (lemma-combine plus plus I⊗Y)
      equals S1 • H1 • Swap • S0 • Swap • H1 • S1⁻¹ • R (minus , Z⊗Y) • R (minus , Z⊗Y) • S1 • H1 • CZ • S0 • H1 • S1 • S1 • S1 • W ^ 6 • ε
          by in-context 7 2 auto (lemma-combine minus minus Z⊗Y)
      equals S1 • H1 • Swap • S0 • Swap • H1 • S1⁻¹ • S1 • H1 • H0 • CZ • H0 • S0⁻¹ • W ^ 2 • H0 • CZ • H0 • H1 • S1⁻¹ • S1 • H1 • CZ • S0 • H1 • S1 • S1 • S1 • W ^ 6 • ε
          by clifford-tactic 0 28 10000 auto
      equals ε



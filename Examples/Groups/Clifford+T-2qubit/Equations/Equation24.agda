------------------------------------------------------------------------
-- Presentations of groups
--
-- Equation 24 of the 46 relations the Reidemeister-Schreier theorem
-- requires for 2-qubit Clifford+T operators (see Completeness), from
-- the relations of Figure 1.  A computer-generated equational proof,
-- ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Equations.Equation24 where

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

eqn24 : Clifford+T.Rel ⊢ X0 • CX0 • T0 • CX0 • X0 • Swap • ε === Swap • X0 • CX0 • T0 • CX0 • X0 • ε
eqn24 = 
  equational X0 • CX0 • T0 • CX0 • X0 • Swap • ε
          by general-assoc auto
      equals X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • Swap • ε
          by in-context 0 3 auto (lemma-R (C.X0 • C.CX0) (plus , Z⊗I))
      equals R (minus , Z⊗Z) • X0 • CX0 • CX0 • X0 • Swap • ε
          by clifford-tactic 1 4 10000 auto
      equals R (minus , Z⊗Z) • Swap • ε
          by clifford-tactic 2 0 10000 auto
      equals R (minus , Z⊗Z) • Swap • X0 • CX0 • CX0 • X0 • ε
          by in-context 0 4 auto (symm (lemma-R (C.Swap • C.X0 • C.CX0) (plus , Z⊗I)))
      equals Swap • X0 • CX0 • R (plus , Z⊗I) • CX0 • X0 • ε
          by general-assoc auto
      equals Swap • X0 • CX0 • T0 • CX0 • X0 • ε



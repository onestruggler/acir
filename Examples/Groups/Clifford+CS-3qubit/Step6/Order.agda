------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Presentation.Tactics.Lists
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words

open Monoid-Equational
open Rewriting
open Associative
open InContext

open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Examples.Groups.Clifford+CS-3qubit.MaybeEq-Instances
open import Examples.Groups.Clifford+CS-3qubit.CosetNF
open import Examples.Groups.Clifford+CS-3qubit.Gate

open import Examples.Groups.Clifford+CS-3qubit.Step6.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step6.PLemmas

module Examples.Groups.Clifford+CS-3qubit.Step6.Order where

  lemma-Swap01-Swap01=ε : Rel ⊢ Swap01 • Swap01 === ε
  lemma-Swap01-Swap01=ε =
    equational Swap01 • Swap01
      by cong (axiom ax-Swap01=CX01-CX10-CX01) (axiom ax-Swap01=CX01-CX10-CX01)
    equals (CX01 • CX10 • CX01) • CX01 • CX10 • CX01
      by general-assoc auto
    equals CX01 • CX10 • (CX01 • CX01) • CX10 • CX01
      by right right left axiom ax-CX01-CX01=ε
    equals CX01 • CX10 • (ε) • CX10 • CX01
      by general-assoc auto
    equals CX01 • (CX10 • CX10) • CX01
      by right left axiom ax-CX10-CX10=ε
    equals CX01 • (ε) • CX01
      by general-assoc auto
    equals CX01 • CX01
      by axiom ax-CX01-CX01=ε
    equals ε


  lemma-Swap12-Swap12=ε : Rel ⊢ Swap12 • Swap12 === ε
  lemma-Swap12-Swap12=ε =
    equational Swap12 • Swap12
      by cong (axiom ax-Swap12=CX12-CX21-CX12) (axiom ax-Swap12=CX12-CX21-CX12)
    equals (CX12 • CX21 • CX12) • CX12 • CX21 • CX12
      by general-assoc auto
    equals CX12 • CX21 • (CX12 • CX12) • CX21 • CX12
      by right right left axiom ax-CX12-CX12=ε
    equals CX12 • CX21 • (ε) • CX21 • CX12
      by general-assoc auto
    equals CX12 • (CX21 • CX21) • CX12
      by right left axiom ax-CX21-CX21=ε
    equals CX12 • (ε) • CX12
      by general-assoc auto
    equals CX12 • CX12
      by axiom ax-CX12-CX12=ε
    equals ε


  order-step : Step-Function Gate Rel
  order-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  order-step (CCX1-gen ∷ CCX1-gen ∷ xs) = just (xs , at-head (lemma-CCX1-CCX1=ε))
  order-step (CCX2-gen ∷ CCX2-gen ∷ xs) = just (xs , at-head (lemma-CCX2-CCX2=ε))
  order-step (CX01-gen ∷ CX01-gen ∷ xs) = just (xs , at-head (axiom ax-CX01-CX01=ε))
  order-step (CX10-gen ∷ CX10-gen ∷ xs) = just (xs , at-head (axiom ax-CX10-CX10=ε))
  order-step (CX12-gen ∷ CX12-gen ∷ xs) = just (xs , at-head (axiom ax-CX12-CX12=ε))
  order-step (CX21-gen ∷ CX21-gen ∷ xs) = just (xs , at-head (axiom ax-CX21-CX21=ε))
  order-step (CX02-gen ∷ CX02-gen ∷ xs) = just (xs , at-head (lemma-CX02-CX02=ε))
  order-step (CX20-gen ∷ CX20-gen ∷ xs) = just (xs , at-head (lemma-CX20-CX20=ε))
  order-step (X0-gen ∷ X0-gen ∷ xs) = just (xs , at-head (axiom ax-X0-X0=ε))
  order-step (X1-gen ∷ X1-gen ∷ xs) = just (xs , at-head (lemma-X1-X1=ε))
  order-step (X2-gen ∷ X2-gen ∷ xs) = just (xs , at-head (lemma-X2-X2=ε))
  order-step (Swap01-gen ∷ Swap01-gen ∷ xs) = just (xs , at-head (lemma-Swap01-Swap01=ε))
  order-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (lemma-Swap12-Swap12=ε))
  order-step (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom ax-S0-S0-S0-S0=ε))
  order-step (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ xs) = just (xs , at-head (lemma-S1-S1-S1-S1=ε))
  order-step (S2-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ xs) = just (xs , at-head (lemma-S2-S2-S2-S2=ε))
  order-step (CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs) = just (xs , at-head (axiom ax-CS01-CS01-CS01-CS01=ε))
  order-step (CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ xs) = just (xs , at-head (axiom ax-CS12-CS12-CS12-CS12=ε))
  order-step (CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ xs) = just (xs , at-head (lemma-CS02-CS02-CS02-CS02=ε))
  order-step (CCZ-gen ∷ CCZ-gen ∷ xs) = just (xs , at-head (axiom ax-CCZ-CCZ=ε))
  order-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  order-step (K0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K0-K0=iI-iI-iI))
  order-step _ = nothing

  module Order = Rewriting.Step (step-cong order-step)



  order-K0-step : Step-Function Gate Rel
  order-K0-step (K0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K0-K0=iI-iI-iI))
  order-K0-step _ = nothing

  module Order-K0 = Rewriting.Step (step-cong order-K0-step)

 

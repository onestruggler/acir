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

open import Examples.Groups.Clifford+CS-3qubit.Step7.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step7.Basis-Change

module Examples.Groups.Clifford+CS-3qubit.Step7.Order where

  lemma-CCX1=Swap01-CCX0-Swap01 : Rel ⊢ CCX1 === Swap01 • CCX0 • Swap01
  lemma-CCX1=Swap01-CCX0-Swap01 = up-to-swap 100 auto (refl' {w = CCX1} auto)

  lemma-CCX2=Swap12-Swap01-CCX0-Swap01-Swap12 : Rel ⊢ CCX2 === Swap12 • Swap01 • CCX0 • Swap01 • Swap12
  lemma-CCX2=Swap12-Swap01-CCX0-Swap01-Swap12 = up-to-swap 100 auto (refl' {w = CCX2} auto)
  lemma-CX10=Swap01-CX01-Swap01 : Rel ⊢ CX10 === Swap01 • CX01 • Swap01
  lemma-CX10=Swap01-CX01-Swap01 = up-to-swap 100 auto (refl' {w = CX10} auto)
  lemma-CX12=Swap01-Swap12-CX01-Swap12-Swap01 : Rel ⊢ CX12 === Swap01 • Swap12 • CX01 • Swap12 • Swap01
  lemma-CX12=Swap01-Swap12-CX01-Swap12-Swap01 = up-to-swap 100 auto (refl' {w = CX12} auto)
  lemma-CX21=Swap12-Swap01-Swap12-CX01-Swap12-Swap01-Swap12 : Rel ⊢ CX21 === Swap12 • Swap01 • Swap12 • CX01 • Swap12 • Swap01 • Swap12
  lemma-CX21=Swap12-Swap01-Swap12-CX01-Swap12-Swap01-Swap12 = up-to-swap 100 auto (refl' {w = CX21} auto)
  lemma-CX02=Swap12-CX01-Swap12 : Rel ⊢ CX02 === Swap12 • CX01 • Swap12
  lemma-CX02=Swap12-CX01-Swap12 = up-to-swap 100 auto (refl' {w = CX02} auto)
  lemma-CX20=Swap12-Swap01-CX01-Swap01-Swap12 : Rel ⊢ CX20 === Swap12 • Swap01 • CX01 • Swap01 • Swap12
  lemma-CX20=Swap12-Swap01-CX01-Swap01-Swap12 = up-to-swap 100 auto (refl' {w = CX20} auto)
  lemma-X1=Swap01-X0-Swap01 : Rel ⊢ X1 === Swap01 • X0 • Swap01
  lemma-X1=Swap01-X0-Swap01 = up-to-swap 100 auto (refl' {w = X1} auto)
  lemma-X2=Swap12-Swap01-X0-Swap01-Swap12 : Rel ⊢ X2 === Swap12 • Swap01 • X0 • Swap01 • Swap12
  lemma-X2=Swap12-Swap01-X0-Swap01-Swap12 = up-to-swap 100 auto (refl' {w = X2} auto)
  lemma-S1=Swap01-S0-Swap01 : Rel ⊢ S1 === Swap01 • S0 • Swap01
  lemma-S1=Swap01-S0-Swap01 = up-to-swap 100 auto (refl' {w = S1} auto)
  lemma-S2=Swap12-Swap01-S0-Swap01-Swap12 : Rel ⊢ S2 === Swap12 • Swap01 • S0 • Swap01 • Swap12
  lemma-S2=Swap12-Swap01-S0-Swap01-Swap12 = up-to-swap 100 auto (refl' {w = S2} auto)
  lemma-CS12=Swap01-Swap12-CS01-Swap12-Swap01 : Rel ⊢ CS12 === Swap01 • Swap12 • CS01 • Swap12 • Swap01
  lemma-CS12=Swap01-Swap12-CS01-Swap12-Swap01 = up-to-swap 100 auto (refl' {w = CS12} auto)
  lemma-CS02=Swap12-CS01-Swap12 : Rel ⊢ CS02 === Swap12 • CS01 • Swap12
  lemma-CS02=Swap12-CS01-Swap12 = up-to-swap 100 auto (refl' {w = CS02} auto)


  order0-step : Step-Function Gate Rel
  order0-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  order0-step (CX01-gen ∷ CX01-gen ∷ xs) = just (xs , at-head (axiom ax-CX01-CX01=ε))
  order0-step (X0-gen ∷ X0-gen ∷ xs) = just (xs , at-head (axiom ax-X0-X0=ε))
  order0-step (Swap01-gen ∷ Swap01-gen ∷ xs) = just (xs , at-head (axiom ax-Swap01-Swap01=ε))
  order0-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (axiom ax-Swap12-Swap12=ε))
  order0-step (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom ax-S0-S0-S0-S0=ε))
  order0-step (CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs) = just (xs , at-head (axiom ax-CS01-CS01-CS01-CS01=ε))
  order0-step (CCZ-gen ∷ CCZ-gen ∷ xs) = just (xs , at-head (axiom ax-CCZ-CCZ=ε))
  order0-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  order0-step (K0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K0-K0=iI-iI-iI))
  order0-step _ = nothing

  module Order0 = Rewriting.Step (step-cong order0-step)


  def-step : Step-Function Gate Rel
  def-step (CCX1-gen ∷ xs) = just (Swap01-gen ∷ CCX0-gen ∷ Swap01-gen ∷ xs , at-head (lemma-CCX1=Swap01-CCX0-Swap01))
  def-step (CCX2-gen ∷ xs) = just (Swap12-gen ∷ Swap01-gen ∷ CCX0-gen ∷ Swap01-gen ∷ Swap12-gen ∷ xs , at-head (lemma-CCX2=Swap12-Swap01-CCX0-Swap01-Swap12))
  def-step (CX10-gen ∷ xs) = just (Swap01-gen ∷ CX01-gen ∷ Swap01-gen ∷ xs , at-head (lemma-CX10=Swap01-CX01-Swap01))
  def-step (CX12-gen ∷ xs) = just (Swap01-gen ∷ Swap12-gen ∷ CX01-gen ∷ Swap12-gen ∷ Swap01-gen ∷ xs , at-head (lemma-CX12=Swap01-Swap12-CX01-Swap12-Swap01))
  def-step (CX21-gen ∷ xs) = just (Swap12-gen ∷ Swap01-gen ∷ Swap12-gen ∷ CX01-gen ∷ Swap12-gen ∷ Swap01-gen ∷ Swap12-gen ∷ xs , at-head (lemma-CX21=Swap12-Swap01-Swap12-CX01-Swap12-Swap01-Swap12))
  def-step (CX02-gen ∷ xs) = just (Swap12-gen ∷ CX01-gen ∷ Swap12-gen ∷ xs , at-head (lemma-CX02=Swap12-CX01-Swap12))
  def-step (CX20-gen ∷ xs) = just (Swap12-gen ∷ Swap01-gen ∷ CX01-gen ∷ Swap01-gen ∷ Swap12-gen ∷ xs , at-head (lemma-CX20=Swap12-Swap01-CX01-Swap01-Swap12))
  def-step (X1-gen ∷ xs) = just (Swap01-gen ∷ X0-gen ∷ Swap01-gen ∷ xs , at-head (lemma-X1=Swap01-X0-Swap01))
  def-step (X2-gen ∷ xs) = just (Swap12-gen ∷ Swap01-gen ∷ X0-gen ∷ Swap01-gen ∷ Swap12-gen ∷ xs , at-head (lemma-X2=Swap12-Swap01-X0-Swap01-Swap12))
  def-step (S1-gen ∷ xs) = just (Swap01-gen ∷ S0-gen ∷ Swap01-gen ∷ xs , at-head (lemma-S1=Swap01-S0-Swap01))
  def-step (S2-gen ∷ xs) = just (Swap12-gen ∷ Swap01-gen ∷ S0-gen ∷ Swap01-gen ∷ Swap12-gen ∷ xs , at-head (lemma-S2=Swap12-Swap01-S0-Swap01-Swap12))
  def-step (CS12-gen ∷ xs) = just (Swap01-gen ∷ Swap12-gen ∷ CS01-gen ∷ Swap12-gen ∷ Swap01-gen ∷ xs , at-head (lemma-CS12=Swap01-Swap12-CS01-Swap12-Swap01))
  def-step (CS02-gen ∷ xs) = just (Swap12-gen ∷ CS01-gen ∷ Swap12-gen ∷ xs , at-head (lemma-CS02=Swap12-CS01-Swap12))
  def-step _ = nothing

  module DO = Rewriting.Step (step-cong (order0-step then def-step))


  lemma-CCX1-CCX1=ε : Rel ⊢ CCX1 • CCX1 === ε
  lemma-CCX1-CCX1=ε = DO.general-rewrite 20 auto

  lemma-CCX2-CCX2=ε : Rel ⊢ CCX2 • CCX2 === ε
  lemma-CCX2-CCX2=ε = DO.general-rewrite 20 auto

  lemma-CX10-CX10=ε : Rel ⊢ CX10 • CX10 === ε
  lemma-CX10-CX10=ε = DO.general-rewrite 20 auto

  lemma-CX20-CX20=ε : Rel ⊢ CX20 • CX20 === ε
  lemma-CX20-CX20=ε = DO.general-rewrite 20 auto


  lemma-CX12-CX12=ε : Rel ⊢ CX12 • CX12 === ε
  lemma-CX12-CX12=ε = DO.general-rewrite 20 auto

  lemma-CX21-CX21=ε : Rel ⊢ CX21 • CX21 === ε
  lemma-CX21-CX21=ε = DO.general-rewrite 20 auto


  lemma-CX02-CX02=ε : Rel ⊢ CX02 • CX02 === ε
  lemma-CX02-CX02=ε = DO.general-rewrite 20 auto


  lemma-X1-X1=ε : Rel ⊢ X1 • X1 === ε
  lemma-X1-X1=ε = DO.general-rewrite 20 auto

  lemma-X2-X2=ε : Rel ⊢ X2 • X2 === ε
  lemma-X2-X2=ε = DO.general-rewrite 20 auto

  lemma-S1-S1-S1-S1=ε : Rel ⊢ S1 • S1 • S1 • S1 === ε
  lemma-S1-S1-S1-S1=ε = DO.general-rewrite 20 auto

  lemma-S2-S2-S2-S2=ε : Rel ⊢ S2 • S2 • S2 • S2 === ε
  lemma-S2-S2-S2-S2=ε = DO.general-rewrite 20 auto

  lemma-CS12-CS12-CS12-CS12=ε : Rel ⊢ CS12 • CS12 • CS12 • CS12 === ε
  lemma-CS12-CS12-CS12-CS12=ε = DO.general-rewrite 20 auto

  lemma-CS02-CS02-CS02-CS02=ε : Rel ⊢ CS02 • CS02 • CS02 • CS02 === ε
  lemma-CS02-CS02-CS02-CS02=ε = DO.general-rewrite 20 auto


  lemma-Swap01-Swap01=ε : Rel ⊢ Swap01 • Swap01 === ε
  lemma-Swap01-Swap01=ε =
    equational Swap01 • Swap01
      by cong (axiom ax-Swap01=CX01-CX10-CX01) (axiom ax-Swap01=CX01-CX10-CX01)
    equals (CX01 • CX10 • CX01) • (CX01 • CX10 • CX01)
      by general-assoc auto
    equals (CX01 • CX10) • (CX01 • CX01) • (CX10 • CX01)
      by right left axiom ax-CX01-CX01=ε
    equals (CX01 • CX10) • (ε) • (CX10 • CX01)
      by general-assoc auto
    equals CX01 • (CX10 • CX10) • CX01
      by right left lemma-CX10-CX10=ε
    equals CX01 • (ε) • CX01
      by general-assoc auto
    equals CX01 • CX01
      by axiom ax-CX01-CX01=ε
    equals ε


  lemma-Swap12-Swap12=ε : Rel ⊢ Swap12 • Swap12 === ε
  lemma-Swap12-Swap12=ε =
    equational Swap12 • Swap12
      by cong (axiom ax-Swap12=CX12-CX21-CX12) (axiom ax-Swap12=CX12-CX21-CX12)
    equals (CX12 • CX21 • CX12) • (CX12 • CX21 • CX12)
      by general-assoc auto
    equals (CX12 • CX21) • (CX12 • CX12) • (CX21 • CX12)
      by right left lemma-CX12-CX12=ε
    equals (CX12 • CX21) • (ε) • (CX21 • CX12)
      by general-assoc auto
    equals CX12 • (CX21 • CX21) • CX12
      by right left lemma-CX21-CX21=ε
    equals CX12 • (ε) • CX12
      by general-assoc auto
    equals CX12 • CX12
      by lemma-CX12-CX12=ε
    equals ε


  order-step : Step-Function Gate Rel
  order-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  order-step (CCX1-gen ∷ CCX1-gen ∷ xs) = just (xs , at-head (lemma-CCX1-CCX1=ε))
  order-step (CCX2-gen ∷ CCX2-gen ∷ xs) = just (xs , at-head (lemma-CCX2-CCX2=ε))
  order-step (CX01-gen ∷ CX01-gen ∷ xs) = just (xs , at-head (axiom ax-CX01-CX01=ε))
  order-step (CX10-gen ∷ CX10-gen ∷ xs) = just (xs , at-head (lemma-CX10-CX10=ε))
  order-step (CX12-gen ∷ CX12-gen ∷ xs) = just (xs , at-head (lemma-CX12-CX12=ε))
  order-step (CX21-gen ∷ CX21-gen ∷ xs) = just (xs , at-head (lemma-CX21-CX21=ε))
  order-step (CX02-gen ∷ CX02-gen ∷ xs) = just (xs , at-head (lemma-CX02-CX02=ε))
  order-step (CX20-gen ∷ CX20-gen ∷ xs) = just (xs , at-head (lemma-CX20-CX20=ε))
  order-step (X0-gen ∷ X0-gen ∷ xs) = just (xs , at-head (axiom ax-X0-X0=ε))
  order-step (X1-gen ∷ X1-gen ∷ xs) = just (xs , at-head (lemma-X1-X1=ε))
  order-step (X2-gen ∷ X2-gen ∷ xs) = just (xs , at-head (lemma-X2-X2=ε))
  order-step (Swap01-gen ∷ Swap01-gen ∷ xs) = just (xs , at-head (axiom ax-Swap01-Swap01=ε))
  order-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (axiom ax-Swap12-Swap12=ε))
  order-step (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom ax-S0-S0-S0-S0=ε))
  order-step (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ xs) = just (xs , at-head lemma-S1-S1-S1-S1=ε)
  order-step (S2-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ xs) = just (xs , at-head (lemma-S2-S2-S2-S2=ε))
  order-step (CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs) = just (xs , at-head (axiom ax-CS01-CS01-CS01-CS01=ε))
  order-step (CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ xs) = just (xs , at-head (lemma-CS12-CS12-CS12-CS12=ε))
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

 

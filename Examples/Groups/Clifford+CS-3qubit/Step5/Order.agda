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

open import Examples.Groups.Clifford+CS-3qubit.Step5.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step5.Comm

module Examples.Groups.Clifford+CS-3qubit.Step5.Order where

  order-step : Step-Function Gate Rel
  order-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  order-step (CCX1-gen ∷ CCX1-gen ∷ xs) = just (xs , at-head (axiom ax-CCX1-CCX1=ε))
  order-step (CCX2-gen ∷ CCX2-gen ∷ xs) = just (xs , at-head (axiom ax-CCX2-CCX2=ε))
  order-step (CX01-gen ∷ CX01-gen ∷ xs) = just (xs , at-head (axiom ax-CX01-CX01=ε))
  order-step (CX10-gen ∷ CX10-gen ∷ xs) = just (xs , at-head (axiom ax-CX10-CX10=ε))
  order-step (CX12-gen ∷ CX12-gen ∷ xs) = just (xs , at-head (axiom ax-CX12-CX12=ε))
  order-step (CX21-gen ∷ CX21-gen ∷ xs) = just (xs , at-head (axiom ax-CX21-CX21=ε))
  order-step (CX02-gen ∷ CX02-gen ∷ xs) = just (xs , at-head (axiom ax-CX02-CX02=ε))
  order-step (CX20-gen ∷ CX20-gen ∷ xs) = just (xs , at-head (axiom ax-CX20-CX20=ε))
  order-step (X0-gen ∷ X0-gen ∷ xs) = just (xs , at-head (axiom ax-X0-X0=ε))
  order-step (X1-gen ∷ X1-gen ∷ xs) = just (xs , at-head (axiom ax-X1-X1=ε))
  order-step (X2-gen ∷ X2-gen ∷ xs) = just (xs , at-head (axiom ax-X2-X2=ε))
  order-step (Swap01-gen ∷ Swap01-gen ∷ xs) = just (xs , at-head (axiom ax-Swap01-Swap01=ε))
  order-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (axiom ax-Swap12-Swap12=ε))
  order-step (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom ax-S0-S0-S0-S0=ε))
  order-step (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ xs) = just (xs , at-head (axiom ax-S1-S1-S1-S1=ε))
  order-step (S2-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ xs) = just (xs , at-head (axiom ax-S2-S2-S2-S2=ε))
  order-step (CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs) = just (xs , at-head (axiom ax-CS01-CS01-CS01-CS01=ε))
  order-step (CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ xs) = just (xs , at-head (axiom ax-CS12-CS12-CS12-CS12=ε))
  order-step (CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ xs) = just (xs , at-head (axiom ax-CS02-CS02-CS02-CS02=ε))
  order-step (CCZ-gen ∷ CCZ-gen ∷ xs) = just (xs , at-head (axiom ax-CCZ-CCZ=ε))
  order-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  order-step (K0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K0-K0=iI-iI-iI))
  order-step _ = nothing

  module Order = Rewriting.Step (step-cong order-step)

  nf-order : ListNF Rel
  nf-order = record { listnf = Order.multistep 1000 ; lemma-listnf = Order.lemma-multistep 1000 } ∘ nf-comm

  nf-order-rep : ListNF Rel
  nf-order-rep = rep 20 (record { listnf = Order.multistep 1000 ; lemma-listnf = Order.lemma-multistep 1000 } ∘ nf-comm)


  order-K0-step : Step-Function Gate Rel
  order-K0-step (K0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K0-K0=iI-iI-iI))
  order-K0-step _ = nothing

  module Order-K0 = Rewriting.Step (step-cong order-K0-step)

  nf-order-K0 : ListNF Rel
  nf-order-K0 = record { listnf = Order-K0.multistep 1000 ; lemma-listnf = Order-K0.lemma-multistep 1000 } ∘ nf-comm

  nf-order-K0-rep : ListNF Rel
  nf-order-K0-rep = rep 20 (record { listnf = Order-K0.multistep 1000 ; lemma-listnf = Order-K0.lemma-multistep 1000 } ∘ nf-comm)

 

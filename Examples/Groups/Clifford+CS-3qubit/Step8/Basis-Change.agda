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
open import Examples.Groups.Clifford+CS-3qubit.Theorem
open CliffordCS

open import Examples.Groups.Clifford+CS-3qubit.Step8.Comm
open import Examples.Groups.Clifford+CS-3qubit.Step8.Monoidal
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap2
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap3


module Examples.Groups.Clifford+CS-3qubit.Step8.Basis-Change where


  lemma-Swap12-Swap12=ε : Rel ⊢ Swap12 • Swap12 === ε
  lemma-Swap12-Swap12=ε = Order.general-rewrite 100 auto


  lemma-Swap01-Swap01=ε : Rel ⊢ Swap01 • Swap01 === ε
  lemma-Swap01-Swap01=ε = Order.general-rewrite 100 auto

  lemma-Swap12-K0=K0-Swap12 : Rel ⊢ Swap12 • K0 === K0 • Swap12
  lemma-Swap12-K0=K0-Swap12 = general-comm auto


  lemma-Swap12-S0=S0-Swap12 : Rel ⊢ Swap12 • S0 === S0 • Swap12
  lemma-Swap12-S0=S0-Swap12 = general-comm auto

  lemma-Swap12-iI=iI-Swap12 : Rel ⊢ Swap12 • iI === iI • Swap12
  lemma-Swap12-iI=iI-Swap12 = general-comm auto


  lemma-Swap12-K1=K2-Swap12 : Rel ⊢ Swap12 • K1 === K2 • Swap12
  lemma-Swap12-K1=K2-Swap12 =
    equational Swap12 • K1
      by general-comm auto
    equals K2 • (CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1) • K2 • iI ^ 3
      by right left lemma-Swap12-K1=K2-Swap12'
    equals K2 • (K2 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12) • K2 • iI ^ 3
      by general-comm auto
    equals K2 • Swap12


  mvSwap12-step : Step-Function Gen Rel

  mvSwap12-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ xs) = just (xs , at-head (lemma-Swap12-Swap12=ε))
  mvSwap12-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap12-K0=K0-Swap12))
  mvSwap12-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap12-S0=S0-Swap12))
  mvSwap12-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ S1-gen ∷ xs) = just (S2-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap12-S1=S2-Swap12))
  mvSwap12-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ S2-gen ∷ xs) = just (S1-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap12-S2=S1-Swap12))
  mvSwap12-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap12-iI=iI-Swap12))
  mvSwap12-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ xs) = just (K2-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap12-K1=K2-Swap12))
  mvSwap12-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K2-gen ∷ xs) = just (K1-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap12-K2=K1-Swap12))


  mvSwap12-step _ = nothing

  module MvSwap12 = Rewriting.Step (step-cong mvSwap12-step)







  lemma-Swap01-K2=K2-Swap01 : Rel ⊢ Swap01 • K2 === K2 • Swap01
  lemma-Swap01-K2=K2-Swap01 = general-comm auto


  lemma-Swap01-S2=S2-Swap01 : Rel ⊢ Swap01 • S2 === S2 • Swap01
  lemma-Swap01-S2=S2-Swap01 = general-comm auto

  lemma-Swap01-iI=iI-Swap01 : Rel ⊢ Swap01 • iI === iI • Swap01
  lemma-Swap01-iI=iI-Swap01 = general-comm auto



  lemma-Swap01-K0=K1-Swap01 : Rel ⊢ Swap01 • K0 === K1 • Swap01
  lemma-Swap01-K0=K1-Swap01 =
    equational Swap01 • K0
      by general-comm auto
    equals K1 • (CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0) • K1 • iI ^ 3
      by right left lemma-Swap01-K0=K1-Swap01'-u
    equals K1 • (K1 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01) • K1 • iI ^ 3
      by general-comm auto
    equals K1 • Swap01

 

  mvSwap01-step : Step-Function Gen Rel

  mvSwap01-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ xs) = just (xs , at-head (lemma-Swap01-Swap01=ε))
  mvSwap01-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K2-gen ∷ xs) = just (K2-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap01-K2=K2-Swap01))
  mvSwap01-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap01-S2=S2-Swap01))
  mvSwap01-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ S0-gen ∷ xs) = just (S1-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap01-S0=S1-Swap01))
  mvSwap01-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ S1-gen ∷ xs) = just (S0-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap01-S1=S0-Swap01))
  mvSwap01-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap01-iI=iI-Swap01))
  mvSwap01-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ xs) = just (K1-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap01-K0=K1-Swap01))
  mvSwap01-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K1-gen ∷ xs) = just (K0-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ iI-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ iI-gen ∷ xs , at-head (lemma-Swap01-K1=K0-Swap01))


  mvSwap01-step _ = nothing

  module MvSwap01 = Rewriting.Step (step-cong mvSwap01-step)


  


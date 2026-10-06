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

module Examples.Groups.Clifford+CS-3qubit.Step8.Monoidal where

  mvI-step : Step-Function Gen Rel
  mvI-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  mvI-step (iI-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S0=S0-iI))
  mvI-step (iI-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S1=S1-iI))
  mvI-step (iI-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S2=S2-iI))
  mvI-step (iI-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-K0=K0-iI))
  mvI-step (iI-gen ∷ K1-gen ∷ xs) = just (K1-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-K1=K1-iI))
  mvI-step (iI-gen ∷ K2-gen ∷ xs) = just (K2-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-K2=K2-iI))
  mvI-step (iI-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS01=CS01-iI))
  mvI-step (iI-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS12=CS12-iI))
  mvI-step _ = nothing

  module mvI = Rewriting.Step (step-cong mvI-step)

  monoidal-step : Step-Function Gen Rel
  monoidal-step (S1-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-S0=S0-S1))
  monoidal-step (S2-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-S0=S0-S2))
  monoidal-step (S2-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-S1=S1-S2))
  monoidal-step (K1-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ K1-gen ∷ xs , at-head (axiom ax-K1-K0=K0-K1))
  monoidal-step (K2-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ K2-gen ∷ xs , at-head (axiom ax-K2-K0=K0-K2))
  monoidal-step (K2-gen ∷ K1-gen ∷ xs) = just (K1-gen ∷ K2-gen ∷ xs , at-head (axiom ax-K2-K1=K1-K2))
  monoidal-step (CS01-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-S0=S0-CS01))
  monoidal-step (CS12-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-S0=S0-CS12))
  monoidal-step (CS01-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-S1=S1-CS01))
  monoidal-step (CS12-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-S1=S1-CS12))
  monoidal-step (CS12-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-CS01=CS01-CS12))
  monoidal-step (CS01-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-S2=S2-CS01))
  monoidal-step (CS12-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-S2=S2-CS12))
  monoidal-step (S1-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-K0=K0-S1))
  monoidal-step (S2-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-K0=K0-S2))
  monoidal-step (S2-gen ∷ K1-gen ∷ xs) = just (K1-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-K1=K1-S2))
  monoidal-step (K1-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ K1-gen ∷ xs , at-head (axiom ax-K1-S0=S0-K1))
  monoidal-step (K2-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ K2-gen ∷ xs , at-head (axiom ax-K2-S0=S0-K2))
  monoidal-step (K2-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ K2-gen ∷ xs , at-head (axiom ax-K2-S1=S1-K2))
  monoidal-step (CS01-gen ∷ K2-gen ∷ xs) = just (K2-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-K2=K2-CS01))
  monoidal-step (CS12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-K0=K0-CS12))
  monoidal-step _ = nothing

  module Monoidal = Rewriting.Step (step-cong (mvI-step then monoidal-step))



  order-step : Step-Function Gen Rel
  order-step (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom ax-S0-S0-S0-S0=ε))
  order-step (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ xs) = just (xs , at-head (axiom ax-S1-S1-S1-S1=ε))
  order-step (S2-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ xs) = just (xs , at-head (axiom ax-S2-S2-S2-S2=ε))
  order-step (CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs) = just (xs , at-head (axiom ax-CS01-CS01-CS01-CS01=ε))
  order-step (CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ xs) = just (xs , at-head (axiom ax-CS12-CS12-CS12-CS12=ε))
  order-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  order-step (K0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K0-K0=iI-iI-iI))
  order-step (K1-gen ∷ K1-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K1-K1=iI-iI-iI))
  order-step (K2-gen ∷ K2-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K2-K2=iI-iI-iI))
  order-step (S0-gen ∷ K0-gen ∷ S0-gen ∷ K0-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-S0-K0-S0-K0-S0-K0=iI-iI-iI))
  order-step (S1-gen ∷ K1-gen ∷ S1-gen ∷ K1-gen ∷ S1-gen ∷ K1-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-S1-K1-S1-K1-S1-K1=iI-iI-iI))
  order-step (S2-gen ∷ K2-gen ∷ S2-gen ∷ K2-gen ∷ S2-gen ∷ K2-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-S2-K2-S2-K2-S2-K2=iI-iI-iI))
  order-step _ = nothing


  module Order = Step-With-Standardization (step-cong (order-step)) comm-canonical lemma-comm-canonical


  lemma-S0K0S0 : Rel ⊢ S0 • K0 • S0 === K0 • S0 ^ 3 • K0 • iI
  lemma-S0K0S0 =
    equational S0 • K0 • S0
      by right right Order.general-rewrite 100 auto
    equals S0 • K0 • S0 • K0 • S0 • K0 • K0 • S0 ^ 3 • K0 • iI ^ 2
      by general-assoc auto
    equals (S0 • K0 • S0 • K0 • S0 • K0) • K0 • S0 ^ 3 • K0 • iI ^ 2
      by left axiom ax-S0-K0-S0-K0-S0-K0=iI-iI-iI
    equals (iI ^ 3) • K0 • S0 ^ 3 • K0 • iI ^ 2
      by Order.general-rewrite 100 auto
    equals K0 • S0 ^ 3 • K0 • iI

  lemma-K0S0K0 : Rel ⊢ K0 • S0 • K0 === S0 ^ 3 • K0 • S0 ^ 3
  lemma-K0S0K0 =
    equational K0 • S0 • K0
      by Order.general-rewrite 100 auto
    equals S0 ^ 3 •  (S0 • K0 • S0 • K0 • S0 • K0) • K0 • iI • S0 ^ 3
      by right left axiom ax-S0-K0-S0-K0-S0-K0=iI-iI-iI
    equals S0 ^ 3 •  (iI ^ 3) • K0 • iI • S0 ^ 3
      by Order.general-rewrite 100 auto
    equals S0 ^ 3 • K0 • S0 ^ 3

  lemma-K0-S0-S0-K0-S0=S0-S0-S0-K0-S0-S0-K0-iI : Rel ⊢ K0 • S0 • S0 • K0 • S0 === S0 • S0 • S0 • K0 • S0 • S0 • K0 • iI
  lemma-K0-S0-S0-K0-S0=S0-S0-S0-K0-S0-S0-K0-iI =
    equational K0 • S0 • S0 • K0 • S0
      by right right lemma-S0K0S0
    equals K0 • S0 • K0 • S0 ^ 3 • K0 • iI
      by general-assoc auto
    equals (K0 • S0 • K0) • S0 ^ 3 • K0 • iI
      by left lemma-K0S0K0
    equals (S0 ^ 3 • K0 • S0 ^ 3) • S0 ^ 3 • K0 • iI
      by Order.general-rewrite 100 auto
    equals S0 • S0 • S0 • K0 • S0 • S0 • K0 • iI



  lemma-S1K1S1 : Rel ⊢ S1 • K1 • S1 === K1 • S1 ^ 3 • K1 • iI
  lemma-S1K1S1 =
    equational S1 • K1 • S1
      by right right Order.general-rewrite 111 auto
    equals S1 • K1 • S1 • K1 • S1 • K1 • K1 • S1 ^ 3 • K1 • iI ^ 2
      by general-assoc auto
    equals (S1 • K1 • S1 • K1 • S1 • K1) • K1 • S1 ^ 3 • K1 • iI ^ 2
      by left axiom ax-S1-K1-S1-K1-S1-K1=iI-iI-iI
    equals (iI ^ 3) • K1 • S1 ^ 3 • K1 • iI ^ 2
      by Order.general-rewrite 111 auto
    equals K1 • S1 ^ 3 • K1 • iI

  lemma-K1S1K1 : Rel ⊢ K1 • S1 • K1 === S1 ^ 3 • K1 • S1 ^ 3
  lemma-K1S1K1 =
    equational K1 • S1 • K1
      by Order.general-rewrite 111 auto
    equals S1 ^ 3 •  (S1 • K1 • S1 • K1 • S1 • K1) • K1 • iI • S1 ^ 3
      by right left axiom ax-S1-K1-S1-K1-S1-K1=iI-iI-iI
    equals S1 ^ 3 •  (iI ^ 3) • K1 • iI • S1 ^ 3
      by Order.general-rewrite 111 auto
    equals S1 ^ 3 • K1 • S1 ^ 3

  lemma-K1-S1-S1-K1-S1=S1-S1-S1-K1-S1-S1-K1-iI : Rel ⊢ K1 • S1 • S1 • K1 • S1 === S1 • S1 • S1 • K1 • S1 • S1 • K1 • iI
  lemma-K1-S1-S1-K1-S1=S1-S1-S1-K1-S1-S1-K1-iI =
    equational K1 • S1 • S1 • K1 • S1
      by right right lemma-S1K1S1
    equals K1 • S1 • K1 • S1 ^ 3 • K1 • iI
      by general-assoc auto
    equals (K1 • S1 • K1) • S1 ^ 3 • K1 • iI
      by left lemma-K1S1K1
    equals (S1 ^ 3 • K1 • S1 ^ 3) • S1 ^ 3 • K1 • iI
      by Order.general-rewrite 111 auto
    equals S1 • S1 • S1 • K1 • S1 • S1 • K1 • iI




  lemma-S2K2S2 : Rel ⊢ S2 • K2 • S2 === K2 • S2 ^ 3 • K2 • iI
  lemma-S2K2S2 =
    equational S2 • K2 • S2
      by right right Order.general-rewrite 122 auto
    equals S2 • K2 • S2 • K2 • S2 • K2 • K2 • S2 ^ 3 • K2 • iI ^ 2
      by general-assoc auto
    equals (S2 • K2 • S2 • K2 • S2 • K2) • K2 • S2 ^ 3 • K2 • iI ^ 2
      by left axiom ax-S2-K2-S2-K2-S2-K2=iI-iI-iI
    equals (iI ^ 3) • K2 • S2 ^ 3 • K2 • iI ^ 2
      by Order.general-rewrite 122 auto
    equals K2 • S2 ^ 3 • K2 • iI

  lemma-K2S2K2 : Rel ⊢ K2 • S2 • K2 === S2 ^ 3 • K2 • S2 ^ 3
  lemma-K2S2K2 =
    equational K2 • S2 • K2
      by Order.general-rewrite 122 auto
    equals S2 ^ 3 •  (S2 • K2 • S2 • K2 • S2 • K2) • K2 • iI • S2 ^ 3
      by right left axiom ax-S2-K2-S2-K2-S2-K2=iI-iI-iI
    equals S2 ^ 3 •  (iI ^ 3) • K2 • iI • S2 ^ 3
      by Order.general-rewrite 122 auto
    equals S2 ^ 3 • K2 • S2 ^ 3

  lemma-K2-S2-S2-K2-S2=S2-S2-S2-K2-S2-S2-K2-iI : Rel ⊢ K2 • S2 • S2 • K2 • S2 === S2 • S2 • S2 • K2 • S2 • S2 • K2 • iI
  lemma-K2-S2-S2-K2-S2=S2-S2-S2-K2-S2-S2-K2-iI =
    equational K2 • S2 • S2 • K2 • S2
      by right right lemma-S2K2S2
    equals K2 • S2 • K2 • S2 ^ 3 • K2 • iI
      by general-assoc auto
    equals (K2 • S2 • K2) • S2 ^ 3 • K2 • iI
      by left lemma-K2S2K2
    equals (S2 ^ 3 • K2 • S2 ^ 3) • S2 ^ 3 • K2 • iI
      by Order.general-rewrite 122 auto
    equals S2 • S2 • S2 • K2 • S2 • S2 • K2 • iI


  lemma-CS01-K0-CS01-K0-CS01-CS01-CS01=S0-K0-CS01-K0-S0-S0-S0 : Rel ⊢ CS01 • K0 • CS01 • K0 • CS01 • CS01 • CS01 === S0 • K0 • CS01 • K0 • S0 • S0 • S0
  lemma-CS01-K0-CS01-K0-CS01-CS01-CS01=S0-K0-CS01-K0-S0-S0-S0 =
    equational CS01 • K0 • CS01 • K0 • CS01 • CS01 • CS01
      by Order.general-rewrite 122 auto
    equals (CS01 • K0 • CS01 • K0 • S0) • CS01 ^ 3 • S0 ^ 3
      by left axiom ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01
    equals (S0 • K0 • CS01 • K0 • CS01) • CS01 ^ 3 • S0 ^ 3
      by Order.general-rewrite 122 auto
    equals S0 • K0 • CS01 • K0 • S0 • S0 • S0

  lemma-CS01-CS01-K0-CS01-K0-CS01-CS01=S0-S0-K0-CS01-K0-S0-S0 : Rel ⊢ CS01 • CS01 • K0 • CS01 • K0 • CS01 • CS01 === S0 • S0 • K0 • CS01 • K0 • S0 • S0
  lemma-CS01-CS01-K0-CS01-K0-CS01-CS01=S0-S0-K0-CS01-K0-S0-S0 =
    equational CS01 • CS01 • K0 • CS01 • K0 • CS01 • CS01
      by Order.general-rewrite 122 auto
    equals CS01 • (CS01 • K0 • CS01 • K0 • CS01 • CS01 • CS01) • CS01 • CS01 • CS01
      by right left lemma-CS01-K0-CS01-K0-CS01-CS01-CS01=S0-K0-CS01-K0-S0-S0-S0
    equals CS01 • (S0 • K0 • CS01 • K0 • S0 • S0 • S0) • CS01 • CS01 • CS01
      by general-comm auto
    equals S0 • (CS01 • K0 • CS01 • K0 • CS01 • CS01 • CS01) • S0 • S0 • S0
      by right left lemma-CS01-K0-CS01-K0-CS01-CS01-CS01=S0-K0-CS01-K0-S0-S0-S0
    equals S0 • (S0 • K0 • CS01 • K0 • S0 • S0 • S0) • S0 • S0 • S0
      by Order.general-rewrite 122 auto
    equals S0 • S0 • K0 • CS01 • K0 • S0 • S0

  lemma-CX10-CS01=S1-CS01-CS01-CS01-CX10 : Rel ⊢ CX10 • CS01 === S1 • CS01 • CS01 • CS01 • CX10
  lemma-CX10-CS01=S1-CS01-CS01-CS01-CX10 =
    equational CX10 • CS01
      by Order.general-rewrite 122 auto
    equals K0 • (CS01 • CS01 • K0 • CS01 • K0 • CS01 • CS01) • K0 • CX10 • iI ^ 2
      by right left lemma-CS01-CS01-K0-CS01-K0-CS01-CS01=S0-S0-K0-CS01-K0-S0-S0
    equals K0 • (S0 • S0 • K0 • CS01 • K0 • S0 • S0) • K0 • CX10 • iI ^ 2
      by Order.general-rewrite 122 auto
    equals (X0 • CS01) • X0 • CX10
      by left axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
    equals (CS01 • CS01 • CS01 • X0 • S1) • X0 • CX10
      by Order.general-rewrite 122 auto
    equals S1 • CS01 • CS01 • CS01 • CX10
    
  lemma-CS01-K1-CS01-K1-CS01-CS01-CS01=S1-K1-CS01-K1-S1-S1-S1 : Rel ⊢ CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 === S1 • K1 • CS01 • K1 • S1 • S1 • S1
  lemma-CS01-K1-CS01-K1-CS01-CS01-CS01=S1-K1-CS01-K1-S1-S1-S1 =
    equational CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01
      by Order.general-rewrite 022 auto
    equals (CS01 • K1 • CS01 • K1 • S1) • CS01 ^ 3 • S1 ^ 3
      by left axiom ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01
    equals (S1 • K1 • CS01 • K1 • CS01) • CS01 ^ 3 • S1 ^ 3
      by Order.general-rewrite 022 auto
    equals S1 • K1 • CS01 • K1 • S1 • S1 • S1

  lemma-CS01-CS01-K1-CS01-K1-CS01-CS01=S1-S1-K1-CS01-K1-S1-S1 : Rel ⊢ CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 === S1 • S1 • K1 • CS01 • K1 • S1 • S1
  lemma-CS01-CS01-K1-CS01-K1-CS01-CS01=S1-S1-K1-CS01-K1-S1-S1 =
    equational CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01
      by Order.general-rewrite 022 auto
    equals CS01 • (CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01) • CS01 • CS01 • CS01
      by right left lemma-CS01-K1-CS01-K1-CS01-CS01-CS01=S1-K1-CS01-K1-S1-S1-S1
    equals CS01 • (S1 • K1 • CS01 • K1 • S1 • S1 • S1) • CS01 • CS01 • CS01
      by general-comm auto
    equals S1 • (CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01) • S1 • S1 • S1
      by right left lemma-CS01-K1-CS01-K1-CS01-CS01-CS01=S1-K1-CS01-K1-S1-S1-S1
    equals S1 • (S1 • K1 • CS01 • K1 • S1 • S1 • S1) • S1 • S1 • S1
      by Order.general-rewrite 022 auto
    equals S1 • S1 • K1 • CS01 • K1 • S1 • S1

  lemma-CX01-CS01=S0-CS01-CS01-CS01-CX01 : Rel ⊢ CX01 • CS01 === S0 • CS01 • CS01 • CS01 • CX01
  lemma-CX01-CS01=S0-CS01-CS01-CS01-CX01 =
    equational CX01 • CS01
      by Order.general-rewrite 022 auto
    equals K1 • (CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01) • K1 • CX01 • iI ^ 2
      by right left lemma-CS01-CS01-K1-CS01-K1-CS01-CS01=S1-S1-K1-CS01-K1-S1-S1
    equals K1 • (S1 • S1 • K1 • CS01 • K1 • S1 • S1) • K1 • CX01 • iI ^ 2
      by Order.general-rewrite 022 auto
    equals (X1 • CS01) • X1 • CX01
      by left axiom ax-X1-CS01=CS01-CS01-CS01-X1-S0
    equals (CS01 • CS01 • CS01 • X1 • S0) • X1 • CX01
      by Order.general-rewrite 022 auto
    equals S0 • CS01 • CS01 • CS01 • CX01


  lemma-CS12-K1-CS12-K1-CS12-CS12-CS12=S1-K1-CS12-K1-S1-S1-S1 : Rel ⊢ CS12 • K1 • CS12 • K1 • CS12 • CS12 • CS12 === S1 • K1 • CS12 • K1 • S1 • S1 • S1
  lemma-CS12-K1-CS12-K1-CS12-CS12-CS12=S1-K1-CS12-K1-S1-S1-S1 =
    equational CS12 • K1 • CS12 • K1 • CS12 • CS12 • CS12
      by Order.general-rewrite 222 auto
    equals (CS12 • K1 • CS12 • K1 • S1) • CS12 ^ 3 • S1 ^ 3
      by left axiom ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12
    equals (S1 • K1 • CS12 • K1 • CS12) • CS12 ^ 3 • S1 ^ 3
      by Order.general-rewrite 222 auto
    equals S1 • K1 • CS12 • K1 • S1 • S1 • S1

  lemma-CS12-CS12-K1-CS12-K1-CS12-CS12=S1-S1-K1-CS12-K1-S1-S1 : Rel ⊢ CS12 • CS12 • K1 • CS12 • K1 • CS12 • CS12 === S1 • S1 • K1 • CS12 • K1 • S1 • S1
  lemma-CS12-CS12-K1-CS12-K1-CS12-CS12=S1-S1-K1-CS12-K1-S1-S1 =
    equational CS12 • CS12 • K1 • CS12 • K1 • CS12 • CS12
      by Order.general-rewrite 222 auto
    equals CS12 • (CS12 • K1 • CS12 • K1 • CS12 • CS12 • CS12) • CS12 • CS12 • CS12
      by right left lemma-CS12-K1-CS12-K1-CS12-CS12-CS12=S1-K1-CS12-K1-S1-S1-S1
    equals CS12 • (S1 • K1 • CS12 • K1 • S1 • S1 • S1) • CS12 • CS12 • CS12
      by general-comm auto
    equals S1 • (CS12 • K1 • CS12 • K1 • CS12 • CS12 • CS12) • S1 • S1 • S1
      by right left lemma-CS12-K1-CS12-K1-CS12-CS12-CS12=S1-K1-CS12-K1-S1-S1-S1
    equals S1 • (S1 • K1 • CS12 • K1 • S1 • S1 • S1) • S1 • S1 • S1
      by Order.general-rewrite 222 auto
    equals S1 • S1 • K1 • CS12 • K1 • S1 • S1

  lemma-CX21-CS12=S2-CS12-CS12-CS12-CX21 : Rel ⊢ CX21 • CS12 === S2 • CS12 • CS12 • CS12 • CX21
  lemma-CX21-CS12=S2-CS12-CS12-CS12-CX21 =
    equational CX21 • CS12
      by Order.general-rewrite 222 auto
    equals K1 • (CS12 • CS12 • K1 • CS12 • K1 • CS12 • CS12) • K1 • CX21 • iI ^ 2
      by right left lemma-CS12-CS12-K1-CS12-K1-CS12-CS12=S1-S1-K1-CS12-K1-S1-S1
    equals K1 • (S1 • S1 • K1 • CS12 • K1 • S1 • S1) • K1 • CX21 • iI ^ 2
      by Order.general-rewrite 222 auto
    equals (X1 • CS12) • X1 • CX21
      by left axiom ax-X1-CS12=CS12-CS12-CS12-X1-S2
    equals (CS12 • CS12 • CS12 • X1 • S2) • X1 • CX21
      by Order.general-rewrite 222 auto
    equals S2 • CS12 • CS12 • CS12 • CX21


  lemma-CS12-K2-CS12-K2-CS12-CS12-CS12=S2-K2-CS12-K2-S2-S2-S2 : Rel ⊢ CS12 • K2 • CS12 • K2 • CS12 • CS12 • CS12 === S2 • K2 • CS12 • K2 • S2 • S2 • S2
  lemma-CS12-K2-CS12-K2-CS12-CS12-CS12=S2-K2-CS12-K2-S2-S2-S2 =
    equational CS12 • K2 • CS12 • K2 • CS12 • CS12 • CS12
      by Order.general-rewrite 122 auto
    equals (CS12 • K2 • CS12 • K2 • S2) • CS12 ^ 3 • S2 ^ 3
      by left axiom ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12
    equals (S2 • K2 • CS12 • K2 • CS12) • CS12 ^ 3 • S2 ^ 3
      by Order.general-rewrite 122 auto
    equals S2 • K2 • CS12 • K2 • S2 • S2 • S2

  lemma-CS12-CS12-K2-CS12-K2-CS12-CS12=S2-S2-K2-CS12-K2-S2-S2 : Rel ⊢ CS12 • CS12 • K2 • CS12 • K2 • CS12 • CS12 === S2 • S2 • K2 • CS12 • K2 • S2 • S2
  lemma-CS12-CS12-K2-CS12-K2-CS12-CS12=S2-S2-K2-CS12-K2-S2-S2 =
    equational CS12 • CS12 • K2 • CS12 • K2 • CS12 • CS12
      by Order.general-rewrite 122 auto
    equals CS12 • (CS12 • K2 • CS12 • K2 • CS12 • CS12 • CS12) • CS12 • CS12 • CS12
      by right left lemma-CS12-K2-CS12-K2-CS12-CS12-CS12=S2-K2-CS12-K2-S2-S2-S2
    equals CS12 • (S2 • K2 • CS12 • K2 • S2 • S2 • S2) • CS12 • CS12 • CS12
      by general-comm auto
    equals S2 • (CS12 • K2 • CS12 • K2 • CS12 • CS12 • CS12) • S2 • S2 • S2
      by right left lemma-CS12-K2-CS12-K2-CS12-CS12-CS12=S2-K2-CS12-K2-S2-S2-S2
    equals S2 • (S2 • K2 • CS12 • K2 • S2 • S2 • S2) • S2 • S2 • S2
      by Order.general-rewrite 122 auto
    equals S2 • S2 • K2 • CS12 • K2 • S2 • S2

  lemma-CX12-CS12=S1-CS12-CS12-CS12-CX12 : Rel ⊢ CX12 • CS12 === S1 • CS12 • CS12 • CS12 • CX12
  lemma-CX12-CS12=S1-CS12-CS12-CS12-CX12 =
    equational CX12 • CS12
      by Order.general-rewrite 122 auto
    equals K2 • (CS12 • CS12 • K2 • CS12 • K2 • CS12 • CS12) • K2 • CX12 • iI ^ 2
      by right left lemma-CS12-CS12-K2-CS12-K2-CS12-CS12=S2-S2-K2-CS12-K2-S2-S2
    equals K2 • (S2 • S2 • K2 • CS12 • K2 • S2 • S2) • K2 • CX12 • iI ^ 2
      by Order.general-rewrite 122 auto
    equals (X2 • CS12) • X2 • CX12
      by left axiom ax-X2-CS12=CS12-CS12-CS12-X2-S1
    equals (CS12 • CS12 • CS12 • X2 • S1) • X2 • CX12
      by Order.general-rewrite 122 auto
    equals S1 • CS12 • CS12 • CS12 • CX12




  lemma-K0-CS01-K0-S0=S0-CS01-CS01-CS01-K0-CS01-K0-CS01 : Rel ⊢ K0 • CS01 • K0 • S0 === S0 • CS01 • CS01 • CS01 • K0 • CS01 • K0 • CS01
  lemma-K0-CS01-K0-S0=S0-CS01-CS01-CS01-K0-CS01-K0-CS01 =
    equational K0 • CS01 • K0 • S0
      by Order.general-rewrite 122 auto
    equals (CS01 • CS01 • CS01) • (CS01 • K0 • CS01 • K0 • S0)
      by right axiom ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01
    equals (CS01 • CS01 • CS01) • (S0 • K0 • CS01 • K0 • CS01)
      by Order.general-rewrite 122 auto
    equals S0 • CS01 • CS01 • CS01 • K0 • CS01 • K0 • CS01


  lemma-CX10-S0=S0-S1-CS01-CS01-CX10 : Rel ⊢ CX10 • S0 === S0 • S1 • CS01 • CS01 • CX10
  lemma-CX10-S0=S0-S1-CS01-CS01-CX10 =
    equational CX10 • S0
      by Order.general-rewrite 122 auto
    equals (K0 • CS01 • K0) • (K0 • CS01 • K0 • S0) • iI ^ 2
      by right left lemma-K0-CS01-K0-S0=S0-CS01-CS01-CS01-K0-CS01-K0-CS01
    equals (K0 • CS01 • K0) • (S0 • CS01 • CS01 • CS01 • K0 • CS01 • K0 • CS01) • iI ^ 2
      by general-assoc auto
    equals (K0 • CS01 • K0 • S0) • (CS01 • CS01 • CS01 • K0 • CS01 • K0 • CS01) • iI ^ 2
      by left lemma-K0-CS01-K0-S0=S0-CS01-CS01-CS01-K0-CS01-K0-CS01
    equals (S0 • CS01 • CS01 • CS01 • K0 • CS01 • K0 • CS01) • (CS01 • CS01 • CS01 • K0 • CS01 • K0 • CS01) • iI ^ 2
      by Order.general-rewrite 122 auto
    equals (S0 • CS01 • CS01 • CS01) • CX10 • CS01
      by right lemma-CX10-CS01=S1-CS01-CS01-CS01-CX10
    equals (S0 • CS01 • CS01 • CS01) • S1 • CS01 • CS01 • CS01 • CX10
      by Order.general-rewrite 122 auto
    equals S0 • S1 • CS01 • CS01 • CX10


  lemma-K1-CS01-K1-S1=S1-CS01-CS01-CS01-K1-CS01-K1-CS01 : Rel ⊢ K1 • CS01 • K1 • S1 === S1 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01
  lemma-K1-CS01-K1-S1=S1-CS01-CS01-CS01-K1-CS01-K1-CS01 =
    equational K1 • CS01 • K1 • S1
      by Order.general-rewrite 122 auto
    equals (CS01 • CS01 • CS01) • (CS01 • K1 • CS01 • K1 • S1)
      by right axiom ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01
    equals (CS01 • CS01 • CS01) • (S1 • K1 • CS01 • K1 • CS01)
      by Order.general-rewrite 122 auto
    equals S1 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01


  lemma-CX01-S1=S0-S1-CS01-CS01-CX01 : Rel ⊢ CX01 • S1 === S0 • S1 • CS01 • CS01 • CX01
  lemma-CX01-S1=S0-S1-CS01-CS01-CX01 =
    equational CX01 • S1
      by Order.general-rewrite 122 auto
    equals (K1 • CS01 • K1) • (K1 • CS01 • K1 • S1) • iI ^ 2
      by right left lemma-K1-CS01-K1-S1=S1-CS01-CS01-CS01-K1-CS01-K1-CS01
    equals (K1 • CS01 • K1) • (S1 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01) • iI ^ 2
      by general-assoc auto
    equals (K1 • CS01 • K1 • S1) • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01) • iI ^ 2
      by left lemma-K1-CS01-K1-S1=S1-CS01-CS01-CS01-K1-CS01-K1-CS01
    equals (S1 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01) • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01) • iI ^ 2
      by Order.general-rewrite 122 auto
    equals (S1 • CS01 • CS01 • CS01) • CX01 • CS01
      by right lemma-CX01-CS01=S0-CS01-CS01-CS01-CX01
    equals (S1 • CS01 • CS01 • CS01) • S0 • CS01 • CS01 • CS01 • CX01
      by Order.general-rewrite 122 auto
    equals S0 • S1 • CS01 • CS01 • CX01


  lemma-K1-CS12-K1-S1=S1-CS12-CS12-CS12-K1-CS12-K1-CS12 : Rel ⊢ K1 • CS12 • K1 • S1 === S1 • CS12 • CS12 • CS12 • K1 • CS12 • K1 • CS12
  lemma-K1-CS12-K1-S1=S1-CS12-CS12-CS12-K1-CS12-K1-CS12 =
    equational K1 • CS12 • K1 • S1
      by Order.general-rewrite 122 auto
    equals (CS12 • CS12 • CS12) • (CS12 • K1 • CS12 • K1 • S1)
      by right axiom ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12
    equals (CS12 • CS12 • CS12) • (S1 • K1 • CS12 • K1 • CS12)
      by Order.general-rewrite 122 auto
    equals S1 • CS12 • CS12 • CS12 • K1 • CS12 • K1 • CS12


  lemma-CX21-S1=S1-S2-CS12-CS12-CX21 : Rel ⊢ CX21 • S1 === S1 • S2 • CS12 • CS12 • CX21
  lemma-CX21-S1=S1-S2-CS12-CS12-CX21 =
    equational CX21 • S1
      by Order.general-rewrite 122 auto
    equals (K1 • CS12 • K1) • (K1 • CS12 • K1 • S1) • iI ^ 2
      by right left lemma-K1-CS12-K1-S1=S1-CS12-CS12-CS12-K1-CS12-K1-CS12
    equals (K1 • CS12 • K1) • (S1 • CS12 • CS12 • CS12 • K1 • CS12 • K1 • CS12) • iI ^ 2
      by general-assoc auto
    equals (K1 • CS12 • K1 • S1) • (CS12 • CS12 • CS12 • K1 • CS12 • K1 • CS12) • iI ^ 2
      by left lemma-K1-CS12-K1-S1=S1-CS12-CS12-CS12-K1-CS12-K1-CS12
    equals (S1 • CS12 • CS12 • CS12 • K1 • CS12 • K1 • CS12) • (CS12 • CS12 • CS12 • K1 • CS12 • K1 • CS12) • iI ^ 2
      by Order.general-rewrite 122 auto
    equals (S1 • CS12 • CS12 • CS12) • CX21 • CS12
      by right lemma-CX21-CS12=S2-CS12-CS12-CS12-CX21
    equals (S1 • CS12 • CS12 • CS12) • S2 • CS12 • CS12 • CS12 • CX21
      by Order.general-rewrite 122 auto
    equals S1 • S2 • CS12 • CS12 • CX21



  lemma-K2-CS12-K2-S2=S2-CS12-CS12-CS12-K2-CS12-K2-CS12 : Rel ⊢ K2 • CS12 • K2 • S2 === S2 • CS12 • CS12 • CS12 • K2 • CS12 • K2 • CS12
  lemma-K2-CS12-K2-S2=S2-CS12-CS12-CS12-K2-CS12-K2-CS12 =
    equational K2 • CS12 • K2 • S2
      by Order.general-rewrite 122 auto
    equals (CS12 • CS12 • CS12) • (CS12 • K2 • CS12 • K2 • S2)
      by right axiom ax-CS12-K2-CS12-K2-S2=S2-K2-CS12-K2-CS12
    equals (CS12 • CS12 • CS12) • (S2 • K2 • CS12 • K2 • CS12)
      by Order.general-rewrite 122 auto
    equals S2 • CS12 • CS12 • CS12 • K2 • CS12 • K2 • CS12


  lemma-CX12-S2=S1-S2-CS12-CS12-CX12 : Rel ⊢ CX12 • S2 === S1 • S2 • CS12 • CS12 • CX12
  lemma-CX12-S2=S1-S2-CS12-CS12-CX12 =
    equational CX12 • S2
      by Order.general-rewrite 122 auto
    equals (K2 • CS12 • K2) • (K2 • CS12 • K2 • S2) • iI ^ 2
      by right left lemma-K2-CS12-K2-S2=S2-CS12-CS12-CS12-K2-CS12-K2-CS12
    equals (K2 • CS12 • K2) • (S2 • CS12 • CS12 • CS12 • K2 • CS12 • K2 • CS12) • iI ^ 2
      by general-assoc auto
    equals (K2 • CS12 • K2 • S2) • (CS12 • CS12 • CS12 • K2 • CS12 • K2 • CS12) • iI ^ 2
      by left lemma-K2-CS12-K2-S2=S2-CS12-CS12-CS12-K2-CS12-K2-CS12
    equals (S2 • CS12 • CS12 • CS12 • K2 • CS12 • K2 • CS12) • (CS12 • CS12 • CS12 • K2 • CS12 • K2 • CS12) • iI ^ 2
      by Order.general-rewrite 122 auto
    equals (S2 • CS12 • CS12 • CS12) • CX12 • CS12
      by right lemma-CX12-CS12=S1-CS12-CS12-CS12-CX12
    equals (S2 • CS12 • CS12 • CS12) • S1 • CS12 • CS12 • CS12 • CX12
      by Order.general-rewrite 122 auto
    equals S1 • S2 • CS12 • CS12 • CX12



  lemma-K1-CS01-CS01-K1-S1=S0-S1-CS01-CS01-K1-CS01-CS01-K1 : Rel ⊢ K1 • CS01 • CS01 • K1 • S1 === S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01 • K1
  lemma-K1-CS01-CS01-K1-S1=S0-S1-CS01-CS01-K1-CS01-CS01-K1 =
    equational K1 • CS01 • CS01 • K1 • S1
      by Order.general-rewrite 100 auto
    equals (CX01 • S1) • iI ^ 3
      by left lemma-CX01-S1=S0-S1-CS01-CS01-CX01
    equals (S0 • S1 • CS01 • CS01 • CX01) • iI ^ 3
      by Order.general-rewrite 100 auto
    equals S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01 • K1
    
  lemma-K2-CS12-CS12-K2-S2=S1-S2-CS12-CS12-K2-CS12-CS12-K2 : Rel ⊢ K2 • CS12 • CS12 • K2 • S2 === S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12 • K2
  lemma-K2-CS12-CS12-K2-S2=S1-S2-CS12-CS12-K2-CS12-CS12-K2 =
    equational K2 • CS12 • CS12 • K2 • S2
      by Order.general-rewrite 100 auto
    equals (CX12 • S2) • iI ^ 3
      by left lemma-CX12-S2=S1-S2-CS12-CS12-CX12
    equals (S1 • S2 • CS12 • CS12 • CX12) • iI ^ 3
      by Order.general-rewrite 100 auto
    equals S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12 • K2
    
  lemma-K1-CS12-CS12-K1-S1=S2-S1-CS12-CS12-K1-CS12-CS12-K1 : Rel ⊢ K1 • CS12 • CS12 • K1 • S1 === S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12 • K1
  lemma-K1-CS12-CS12-K1-S1=S2-S1-CS12-CS12-K1-CS12-CS12-K1 =
    equational K1 • CS12 • CS12 • K1 • S1
      by Order.general-rewrite 100 auto
    equals (CX21 • S1) • iI ^ 3
      by left lemma-CX21-S1=S1-S2-CS12-CS12-CX21
    equals (S1 • S2 • CS12 • CS12 • CX21) • iI ^ 3
      by Order.general-rewrite 100 auto
    equals S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12 • K1
    
  lemma-K0-CS01-CS01-K0-S0=S1-S0-CS01-CS01-K0-CS01-CS01-K0 : Rel ⊢ K0 • CS01 • CS01 • K0 • S0 === S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01 • K0
  lemma-K0-CS01-CS01-K0-S0=S1-S0-CS01-CS01-K0-CS01-CS01-K0 =
    equational K0 • CS01 • CS01 • K0 • S0
      by Order.general-rewrite 100 auto
    equals (CX10 • S0) • iI ^ 3
      by left lemma-CX10-S0=S0-S1-CS01-CS01-CX10
    equals (S0 • S1 • CS01 • CS01 • CX10) • iI ^ 3
      by Order.general-rewrite 100 auto
    equals S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01 • K0

  -- mvCSL
  lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1 : Rel ⊢ K1 • CS12 • CS12 • K1 • CS12 === S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1
  lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1 =
    equational K1 • CS12 • CS12 • K1 • CS12
      by Order.general-rewrite 100 auto
    equals (CX21 • CS12) • iI ^ 3
      by left lemma-CX21-CS12=S2-CS12-CS12-CS12-CX21
    equals (S2 • CS12 • CS12 • CS12 • CX21) • iI ^ 3
      by Order.general-rewrite 100 auto
    equals S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1
    
  lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2 : Rel ⊢ K2 • CS12 • CS12 • K2 • CS12 === S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2
  lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2 =
    equational K2 • CS12 • CS12 • K2 • CS12
      by Order.general-rewrite 100 auto
    equals (CX12 • CS12) • iI ^ 3
      by left lemma-CX12-CS12=S1-CS12-CS12-CS12-CX12
    equals (S1 • CS12 • CS12 • CS12 • CX12) • iI ^ 3
      by Order.general-rewrite 100 auto
    equals S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2
    
  lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1 : Rel ⊢ K1 • CS01 • CS01 • K1 • CS01 === S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1
  lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1 =
    equational K1 • CS01 • CS01 • K1 • CS01
      by Order.general-rewrite 100 auto
    equals (CX01 • CS01) • iI ^ 3
      by left lemma-CX01-CS01=S0-CS01-CS01-CS01-CX01
    equals (S0 • CS01 • CS01 • CS01 • CX01) • iI ^ 3
      by Order.general-rewrite 100 auto
    equals S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1
    
  lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0 : Rel ⊢ K0 • CS01 • CS01 • K0 • CS01 === S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0
  lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0 =
    equational K0 • CS01 • CS01 • K0 • CS01
      by Order.general-rewrite 100 auto
    equals (CX10 • CS01) • iI ^ 3
      by left lemma-CX10-CS01=S1-CS01-CS01-CS01-CX10
    equals (S1 • CS01 • CS01 • CS01 • CX10) • iI ^ 3
      by Order.general-rewrite 100 auto
    equals S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0



  mvSL-step : Step-Function Gen Rel
  mvSL-step (K0-gen ∷ S0-gen ∷ S0-gen ∷ K0-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S0-gen ∷ S0-gen ∷ K0-gen ∷ S0-gen ∷ S0-gen ∷ K0-gen ∷ iI-gen ∷ xs , at-head (lemma-K0-S0-S0-K0-S0=S0-S0-S0-K0-S0-S0-K0-iI))
  mvSL-step (K1-gen ∷ S1-gen ∷ S1-gen ∷ K1-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ S1-gen ∷ S1-gen ∷ K1-gen ∷ S1-gen ∷ S1-gen ∷ K1-gen ∷ iI-gen ∷ xs , at-head (lemma-K1-S1-S1-K1-S1=S1-S1-S1-K1-S1-S1-K1-iI))
  mvSL-step (K2-gen ∷ S2-gen ∷ S2-gen ∷ K2-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ S2-gen ∷ S2-gen ∷ K2-gen ∷ S2-gen ∷ S2-gen ∷ K2-gen ∷ iI-gen ∷ xs , at-head (lemma-K2-S2-S2-K2-S2=S2-S2-S2-K2-S2-S2-K2-iI))
  mvSL-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ S1-gen ∷ xs) = just (S0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ xs , at-head (lemma-K1-CS01-CS01-K1-S1=S0-S1-CS01-CS01-K1-CS01-CS01-K1))
  mvSL-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ S2-gen ∷ xs) = just (S1-gen ∷ S2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ xs , at-head (lemma-K2-CS12-CS12-K2-S2=S1-S2-CS12-CS12-K2-CS12-CS12-K2))
  mvSL-step (K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ S1-gen ∷ xs) = just (S2-gen ∷ S1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ xs , at-head (lemma-K1-CS12-CS12-K1-S1=S2-S1-CS12-CS12-K1-CS12-CS12-K1))
  
  mvSL-step _ = nothing



  mvCSL-step : Step-Function Gen Rel
  mvCSL-step (K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ CS12-gen ∷ xs) = just (S2-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ CS12-gen ∷ CS12-gen ∷ K1-gen ∷ xs , at-head (lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1))
  mvCSL-step (K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ CS12-gen ∷ xs) = just (S1-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ CS12-gen ∷ CS12-gen ∷ K2-gen ∷ xs , at-head (lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2))
  mvCSL-step (K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ CS01-gen ∷ xs) = just (S0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ CS01-gen ∷ CS01-gen ∷ K1-gen ∷ xs , at-head (lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1))
  mvCSL-step (K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ CS01-gen ∷ xs) = just (S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ K0-gen ∷ xs , at-head (lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0))
  mvCSL-step _ = nothing


  module mvSL = Step-With-Standardization (step-cong (order-step then mvSL-step)) comm-canonical lemma-comm-canonical
  module mvSCSL = Step-With-Standardization (step-cong (mvI-step then order-step then mvSL-step then mvCSL-step))comm-canonical lemma-comm-canonical



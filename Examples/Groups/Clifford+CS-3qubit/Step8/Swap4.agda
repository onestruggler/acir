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
open Monoid-Lemmas

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
open import Examples.Groups.Clifford+CS-3qubit.Step8.Basis-Change

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap4 where

lemma-Swap01-X0=X1-Swap01 : Rel ⊢ Swap01 • X0 === X1 • Swap01
lemma-Swap01-X0=X1-Swap01 =
  equational Swap01 • X0
    by MvSwap01.general-rewrite 100 auto
  equals X1 • Swap01

lemma-Swap01-CX01=CX10-Swap01 : Rel ⊢ Swap01 • CX01 === CX10 • Swap01
lemma-Swap01-CX01=CX10-Swap01 =
  equational Swap01 • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • CX10
    by Order.general-rewrite 100 auto
  equals CX10 • (CX10 • CX01 • CX10)
    by right lemma-Swap-alt-def reversed
  equals CX10 • Swap01


lemma-Swap01-CX10=CX01-Swap01 : Rel ⊢ Swap01 • CX10 === CX01 • Swap01
lemma-Swap01-CX10=CX01-Swap01 = 
  equational Swap01 • CX10
    by left lemma-Swap-alt-def
  equals (CX10 • CX01 • CX10) • CX10
    by Order.general-rewrite 100 auto
  equals CX01 • Swap01



lemma-Swap12-X1=X2-Swap12 : Rel ⊢ Swap12 • X1 === X2 • Swap12
lemma-Swap12-X1=X2-Swap12 =
  equational Swap12 • X1
    by MvSwap12.general-rewrite 211 auto
  equals X2 • Swap12

lemma-Swap12-CX12=CX21-Swap12 : Rel ⊢ Swap12 • CX12 === CX21 • Swap12
lemma-Swap12-CX12=CX21-Swap12 =
  equational Swap12 • CX12
    by Order.general-rewrite 211 auto
  equals CX12 • CX21
    by Order.general-rewrite 211 auto
  equals CX21 • (CX21 • CX12 • CX21)
    by right lemma-Swap12-alt-def reversed
  equals CX21 • Swap12


lemma-Swap12-CX21=CX12-Swap12 : Rel ⊢ Swap12 • CX21 === CX12 • Swap12
lemma-Swap12-CX21=CX12-Swap12 = 
  equational Swap12 • CX21
    by left lemma-Swap12-alt-def
  equals (CX21 • CX12 • CX21) • CX21
    by Order.general-rewrite 211 auto
  equals CX12 • Swap12



lemma-CCX0-CX10=CX10-CCX0 : Rel ⊢ CCX0 • CX10 === CX10 • CCX0
lemma-CCX0-CX10=CX10-CCX0 =
  equational CCX0 • CX10
    by Order.general-rewrite 100 auto
  equals K0 • (CCZ • CS01) • CS01 • K0 • iI
    by right left lemma-CCZ-CS01=CS01-CCZ
  equals K0 • (CS01 • CCZ) • CS01 • K0 • iI
    by general-assoc auto
  equals K0 • CS01 • (CCZ • CS01) • K0 • iI
    by right right left lemma-CCZ-CS01=CS01-CCZ
  equals K0 • CS01 • (CS01 • CCZ) • K0 • iI
    by Order.general-rewrite 100 auto
  equals CX10 • CCX0


lemma-f0 : Rel ⊢ CS01 • Swap12 • CS01 • Swap12 === Swap12 • CS01 • Swap12 • CS01
lemma-f0 =
  equational CS01 • Swap12 • CS01 • Swap12
    by Order.general-rewrite 100 auto
  equals CS01 • CX12 • CX21 • CS01 • CX21 • CX12
    by general-comm auto
  equals CX12 • (CS01 • CX21 • CS01 • CX21) • CX12
    by right left lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01
  equals CX12 • (CX21 • CS01 • CX21 • CS01) • CX12
    by Order.general-rewrite 100 auto
  equals Swap12 • CS01 • Swap12 • CS01

lemma-f1 : Rel ⊢ CS01 • Swap12 • CS01 • CS01 • Swap12 === Swap12 • CS01 • CS01 • Swap12 • CS01
lemma-f1 =
  equational CS01 • Swap12 • CS01 • CS01 • Swap12
    by Order.general-rewrite 100 auto
  equals (CS01 • Swap12 • CS01 • Swap12) • Swap12 • CS01 • Swap12
    by left lemma-f0
  equals (Swap12 • CS01 • Swap12 • CS01) • Swap12 • CS01 • Swap12
    by general-assoc auto
  equals (Swap12 • CS01 • Swap12) • (CS01 • Swap12 • CS01 • Swap12)
    by right lemma-f0
  equals (Swap12 • CS01 • Swap12) • (Swap12 • CS01 • Swap12 • CS01)
    by Order.general-rewrite 100 auto
  equals Swap12 • CS01 • CS01 • Swap12 • CS01

lemma-f2 : Rel ⊢ CS01 • CS01 • Swap12 • CS01 • CS01 • Swap12 === Swap12 • CS01 • CS01 • Swap12 • CS01 • CS01
lemma-f2 =
  equational CS01 • CS01 • Swap12 • CS01 • CS01 • Swap12
    by right lemma-f1
  equals CS01 • Swap12 • CS01 • CS01 • Swap12 • CS01
    by general-assoc auto
  equals (CS01 • Swap12 • CS01 • CS01 • Swap12) • CS01
    by left lemma-f1
  equals (Swap12 • CS01 • CS01 • Swap12 • CS01) • CS01
    by general-assoc auto
  equals Swap12 • CS01 • CS01 • Swap12 • CS01 • CS01


lemma-f3 : Rel ⊢ K1 • Swap12 • CS01 • CS01 • Swap12 === Swap12 • CS01 • CS01 • Swap12 • K1
lemma-f3 =
  equational K1 • Swap12 • CS01 • CS01 • Swap12
    by general-assoc auto
  equals (K1 • Swap12) • CS01 • CS01 • Swap12
    by left lemma-Swap12-K2=K1-Swap12 reversed
  equals (Swap12 • K2) • CS01 • CS01 • Swap12
    by general-comm auto
  equals Swap12 • CS01 • CS01 • K2 • Swap12
    by right right right lemma-Swap12-K1=K2-Swap12 reversed
  equals Swap12 • CS01 • CS01 • Swap12 • K1

lemma-CX01-CX02=CX02-CX01 : Rel ⊢ CX01 • CX02 === CX02 • CX01
lemma-CX01-CX02=CX02-CX01 =
  equational CX01 • CX02
    by refl
  equals (K1 • CS01 • CS01 • K1 • iI) • (K2 • (Swap12 • CS01 • Swap12) • (Swap12 • CS01 • Swap12) • K2 • iI)
    by Order.general-rewrite 100 auto
  equals K2 • (K1 • CS01 • CS01) • (K1 • Swap12) • ((CS01 • CS01 • Swap12) • K2 • iI) • iI
    by right right left lemma-Swap12-K2=K1-Swap12 reversed
  equals K2 • (K1 • CS01 • CS01) • (Swap12 • K2) • ((CS01 • CS01 • Swap12) • K2 • iI) • iI
    by general-comm auto
  equals (K2 • K1 • CS01 • CS01 • Swap12 • CS01 • CS01) • (K2 • Swap12) • K2 • iI • iI
    by right left lemma-Swap12-K1=K2-Swap12 reversed
  equals (K2 • K1 • CS01 • CS01 • Swap12 • CS01 • CS01) • (Swap12 • K1) • K2 • iI • iI
    by general-assoc auto
  equals (K2 • K1) • (CS01 • CS01 • Swap12 • CS01 • CS01 • Swap12) • K1 • K2 • iI • iI
    by right left lemma-f2
  equals (K2 • K1) • (Swap12 • CS01 • CS01 • Swap12 • CS01 • CS01) • K1 • K2 • iI • iI
    by general-assoc auto
  equals K2 • (K1 • Swap12 • CS01 • CS01 • Swap12) • CS01 • CS01 • K1 • K2 • iI • iI
    by right left lemma-f3
  equals K2 • (Swap12 • CS01 • CS01 • Swap12 • K1) • CS01 • CS01 • K1 • K2 • iI • iI
    by Order.general-rewrite 100 auto
  equals CX02 • CX01


lemma-S0-S0-CX10 : Rel ⊢ S0 • S0 • CX10 === CX10 • S0 • S0 • S1 • S1
lemma-S0-S0-CX10 =
  equational S0 • S0 • CX10
    by Order.general-rewrite 100 auto
  equals (S1 • S0 • CS01 • CS01) • (S1 • S0 • CS01 • CS01 • CX10) • S1 • S1
    by right left symm lemma-CX10-S0
  equals (S1 • S0 • CS01 • CS01) • (CX10 • S0) • S1 • S1
    by general-assoc auto
  equals (S1 • S0 • CS01 • CS01 • CX10) • S0 • S1 • S1
    by left symm lemma-CX10-S0
  equals (CX10 • S0) • S0 • S1 • S1
    by general-assoc auto
  equals CX10 • S0 • S0 • S1 • S1

lemma-X0-CX01=CX01-X0-X1 : Rel ⊢ X0 • CX01 === CX01 • X0 • X1
lemma-X0-CX01=CX01-X0-X1 =
  equational X0 • CX01
    by refl
  equals (K0 • S0 • S0 • K0 • iI) • K1 • CS01 • CS01 • K1 • iI
    by Order.general-rewrite 100 auto
  equals (K1 • K0) • (S0 • S0 • CX10) • K0 • iI • K1 • iI
    by right left lemma-S0-S0-CX10
  equals (K1 • K0) • (CX10 • S0 • S0 • S1 • S1) • K0 • iI • K1 • iI
    by Order.general-rewrite 100 auto
  equals CX01 • X0 • X1


lemma-CX12-CX21-CS12-CS12-CS12 : Rel ⊢ CX12 • CX21 • CS12 • CS12 • CS12 === S2 • S2 • S2 • CS12 • CX12 • CX21
lemma-CX12-CX21-CS12-CS12-CS12 =
  equational CX12 • CX21 • CS12 • CS12 • CS12
    by general-assoc auto
  equals (CX12 • CX21 • CS12) • CS12 • CS12
    by left lemma-CX12-CX21-CS12
  equals (S2 • CS12 • CS12 • CS12 • CX12 • CX21) • CS12 • CS12
    by general-assoc auto
  equals (S2 • CS12 • CS12 • CS12) • (CX12 • CX21 • CS12) • CS12
    by right left lemma-CX12-CX21-CS12
  equals (S2 • CS12 • CS12 • CS12) • (S2 • CS12 • CS12 • CS12 • CX12 • CX21) • CS12
    by general-assoc auto
  equals (S2 • CS12 • CS12 • CS12) • (S2 • CS12 • CS12 • CS12) • CX12 • CX21 • CS12
    by right right lemma-CX12-CX21-CS12
  equals (S2 • CS12 • CS12 • CS12) • (S2 • CS12 • CS12 • CS12) • S2 • CS12 • CS12 • CS12 • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals S2 • S2 • S2 • CS12 • CX12 • CX21


lemma-CCZ-CS12=CS12-CCZ : Rel ⊢ CCZ • CS12 === CS12 • CCZ
lemma-CCZ-CS12=CS12-CCZ =
  equational CCZ • CS12
    by left refl
  equals (CS10 • CX12 • CX21 • CS10 • CX12 • CX21 • CS10 • CS10 • CS10 • CX12 • CX21) • CS12
    by general-assoc auto
  equals (CS10 • CX12 • CX21 • CS10 • CX12 • CX21 • CS10 • CS10 • CS10) • CX12 • CX21 • CS12
    by right lemma-CX12-CX21-CS12
  equals (CS10 • CX12 • CX21 • CS10 • CX12 • CX21 • CS10 • CS10 • CS10) • S2 • CS12 • CS12 • CS12 • CX12 • CX21
    by general-comm auto
  equals (CS10 • CX12 • CX21 • CS10) • (CX12 • CX21 • CS12 • CS12 • CS12) • (CS10 • CS10 • CS10) • S2 • CX12 • CX21
    by right left lemma-CX12-CX21-CS12-CS12-CS12
  equals (CS10 • CX12 • CX21 • CS10) • (S2 • S2 • S2 • CS12 • CX12 • CX21) • (CS10 • CS10 • CS10) • S2 • CX12 • CX21
    by general-comm auto
  equals (CS10 • CX12 • CX21 • CS10) • (S2 • S2 • S2 • CS12) • (CX12 • S2) • CX21 • (CS10 • CS10 • CS10) • CX12 • CX21
    by right right left lemma-CX12-S2
  equals (CS10 • CX12 • CX21 • CS10) • (S2 • S2 • S2 • CS12) • (S1 • S2 • CS12 • CS12 • CX12) • CX21 • (CS10 • CS10 • CS10) • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals CS10 • (CX12 • CX21 • CS12 • CS12 • CS12) • CS10 • S1 • CX12 • CX21 • (CS10 • CS10 • CS10) • CX12 • CX21
    by right left lemma-CX12-CX21-CS12-CS12-CS12
  equals CS10 • (S2 • S2 • S2 • CS12 • CX12 • CX21) • CS10 • S1 • CX12 • CX21 • (CS10 • CS10 • CS10) • CX12 • CX21
    by general-comm auto
  equals CS10 • (S2 • S2 • S2 • CS12) • (CX12 • CX21 • S1) • CS10 • CX12 • CX21 • (CS10 • CS10 • CS10) • CX12 • CX21
    by right right left lemma-CX12-CX21-S1
  equals CS10 • (S2 • S2 • S2 • CS12) • (S2 • CX12 • CX21) • CS10 • CX12 • CX21 • (CS10 • CS10 • CS10) • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals CS12 • CS10 • CX12 • CX21 • CS10 • CX12 • CX21 • CS10 • CS10 • CS10 • CX12 • CX21
    by right symm refl
  equals CS12 • CCZ


lemma-X0-CCX1=CCX1-CX21-X0 : Rel ⊢ X0 • CCX1 === CCX1 • CX21 • X0
lemma-X0-CCX1=CCX1-CX21-X0 =
  equational X0 • CCX1
    by general-comm auto
  equals K1 • (X0 • CCZ) • K1 • iI
    by right left lemma-X-CCZ
  equals K1 • (CS12 • CS12 • CCZ • X0) • K1 • iI
    by general-assoc auto
  equals K1 • CS12 • (CS12 • CCZ) • X0 • K1 • iI
    by right right left symm lemma-CCZ-CS12=CS12-CCZ
  equals K1 • CS12 • (CCZ • CS12) • X0 • K1 • iI
    by general-assoc auto
  equals K1 • (CS12 • CCZ) • CS12 • X0 • K1 • iI
    by right left symm lemma-CCZ-CS12=CS12-CCZ
  equals K1 • (CCZ • CS12) • CS12 • X0 • K1 • iI
    by Order.general-rewrite 100 auto
  equals CCX1 • CX21 • X0

lemma-g1 : Rel ⊢ Swap01 • CS12 • Swap01 === Swap12 • CS01 • Swap12
lemma-g1 =
  equational Swap01 • CS12 • Swap01
    by left lemma-Swap-alt-def
  equals (CX10 • CX01 • CX10) • CS12 • Swap01
    by right right  lemma-Swap-alt-def
  equals (CX10 • CX01 • CX10) • CS12 • CX10 • CX01 • CX10
    by Order.general-rewrite 100 auto
  equals CX10 • CX01 • CS12 • CX01 • CX10
    by axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12
  equals CX12 • CX21 • CS01 • CX21 • CX12
    by Order.general-rewrite 100 auto
  equals Swap12 • CS01 • Swap12

lemma-Swap01-CX12=CX02-Swap01 : Rel ⊢ Swap01 • CX12 === CX02 • Swap01
lemma-Swap01-CX12=CX02-Swap01 =
  equational Swap01 • CX12
    by refl
  equals Swap01 • K2 • CS12 • CS12 • K2 • iI
    by Order.general-rewrite 100 auto
  equals K2 • Swap01 • CS12 • CS12 • Swap01 • K2 • iI • Swap01
    by Order.general-rewrite 100 auto
  equals K2 • (Swap01 • CS12 • Swap01) • (Swap01 • CS12 • Swap01) • K2 • iI • Swap01
    by right left lemma-g1
  equals K2 • (Swap12 • CS01 • Swap12) • (Swap01 • CS12 • Swap01) • K2 • iI • Swap01
    by right right left lemma-g1
  equals K2 • (Swap12 • CS01 • Swap12) • (Swap12 • CS01 • Swap12) • K2 • iI • Swap01
    by general-assoc auto
  equals (K2 • (Swap12 • CS01 • Swap12) • (Swap12 • CS01 • Swap12) • K2 • iI) • Swap01
    by refl
  equals CX02 • Swap01


lemma-Swap01-CX02=CX12-Swap01 : Rel ⊢ Swap01 • CX02 === CX12 • Swap01
lemma-Swap01-CX02=CX12-Swap01 =
  equational Swap01 • CX02
    by Order.general-rewrite 100 auto
  equals Swap01 • (CX02 • Swap01) • Swap01
    by right left lemma-Swap01-CX12=CX02-Swap01 reversed
  equals Swap01 • (Swap01 • CX12) • Swap01
    by Order.general-rewrite 100 auto
  equals CX12 • Swap01


lemma-Swap01-CX21=CX20-Swap01 : Rel ⊢ Swap01 • CX21 === CX20 • Swap01
lemma-Swap01-CX21=CX20-Swap01 =
  equational Swap01 • CX21
    by refl
  equals Swap01 • K1 • CS12 • CS12 • K1 • iI
    by Order.general-rewrite 100 auto
  equals (Swap01 • K1) • (CS12 • CS12) • (K1 • Swap01) • iI • Swap01
    by left lemma-Swap01-K1=K0-Swap01
  equals (K0 • Swap01) • (CS12 • CS12) • (K1 • Swap01) • iI • Swap01
    by right right left symm lemma-Swap01-K0=K1-Swap01
  equals (K0 • Swap01) • (CS12 • CS12) • (Swap01 • K0) • iI • Swap01
    by Order.general-rewrite 100 auto
  equals K0 • (Swap01 • CS12 • Swap01) • (Swap01 • CS12 • Swap01) • K0 • iI • Swap01
    by right left lemma-g1
  equals K0 • (CS02) • (Swap01 • CS12 • Swap01) • K0 • iI • Swap01
    by right right left lemma-g1
  equals K0 • (CS02) • (CS02) • K0 • iI • Swap01
    by Order.general-rewrite 100 auto
  equals CX20 • Swap01


lemma-Swap01-CX20=CX21-Swap01 : Rel ⊢ Swap01 • CX20 === CX21 • Swap01
lemma-Swap01-CX20=CX21-Swap01 =
  equational Swap01 • CX20
    by Order.general-rewrite 100 auto
  equals Swap01 • (CX20 • Swap01) • Swap01
    by right left symm lemma-Swap01-CX21=CX20-Swap01
  equals Swap01 • (Swap01 • CX21) • Swap01
    by Order.general-rewrite 100 auto
  equals CX21 • Swap01


lemma-Swap01-CCZ=CCZ-Swap01 : Rel ⊢ Swap01 • CCZ === CCZ • Swap01
lemma-Swap01-CCZ=CCZ-Swap01 =
  equational Swap01 • CCZ
    by right lemma-CCZ-alt-def
  equals Swap01 • CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
    by left lemma-Swap-alt-def
  equals (CX10 • CX01 • CX10) • CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
    by Order.general-rewrite 100 auto
  equals CX10 • (CX01 • CS12 • CX01 • CS12) • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
    by right left symm (lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12)
  equals CX10 • (CS12 • CX01 • CS12 • CX01) • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
    by general-comm auto
  equals (CX10 • CS12 • CX01 • CS12) • (CX01 • CX10 • CX01) • CX10 • CS12 • CS12 • CS12 • CX01
    by right left lemma-Swap-alt-def
  equals (CX10 • CS12 • CX01 • CS12) • (CX10 • CX01 • CX10) • CX10 • CS12 • CS12 • CS12 • CX01
    by Order.general-rewrite 100 auto
  equals (CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01) • CX01 • CX10 • CX01
    by left symm lemma-CCZ-alt-def
  equals CCZ • Swap01


lemma-Swap12-CCZ=CCZ-Swap12 : Rel ⊢ Swap12 • CCZ === CCZ • Swap12
lemma-Swap12-CCZ=CCZ-Swap12 =
  equational Swap12 • CCZ
    by refl
  equals (CX12 • CX21 • CX12) • CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals CX12 • (CX21 • CS01 • CX21 • CS01) • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by right left symm (lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01)
  equals CX12 • (CS01 • CX21 • CS01 • CX21) • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CX12 • CX21 • CS01) • (CX21 • CX12 • CX21) • CS01 • CS01 • CS01 • CX12 • CX21
    by right left symm lemma-Swap12-alt-def
  equals (CS01 • CX12 • CX21 • CS01) • (CX12 • CX21 • CX12) • CS01 • CS01 • CS01 • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals (CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21) • CX21 • CX12 • CX21
    by cong refl (symm lemma-Swap12-alt-def)
  equals CCZ • Swap12


lemma-Swap01-CCX2=CCX2-Swap01 : Rel ⊢ Swap01 • CCX2 === CCX2 • Swap01
lemma-Swap01-CCX2=CCX2-Swap01 =
  equational Swap01 • CCX2
    by general-comm auto
  equals K2 • (Swap01 • CCZ) • K2 • iI
    by right left lemma-Swap01-CCZ=CCZ-Swap01
  equals K2 • (CCZ • Swap01) • K2 • iI
    by general-comm auto
  equals CCX2 • Swap01


lemma-Swap12-CCX0=CCX0-Swap12 : Rel ⊢ Swap12 • CCX0 === CCX0 • Swap12
lemma-Swap12-CCX0=CCX0-Swap12 =
  equational Swap12 • CCX0
    by general-comm auto
  equals K0 • (Swap12 • CCZ) • K0 • iI
    by right left lemma-Swap12-CCZ=CCZ-Swap12
  equals K0 • (CCZ • Swap12) • K0 • iI
    by general-comm auto
  equals CCX0 • Swap12


lemma-Swap01-CCX0=CCX1-Swap01 : Rel ⊢ Swap01 • CCX0 === CCX1 • Swap01
lemma-Swap01-CCX0=CCX1-Swap01 =
  equational Swap01 • CCX0
    by refl
  equals Swap01 • K0 • CCZ • K0 • iI
    by general-assoc auto
  equals (Swap01 • K0) • CCZ • K0 • iI
    by left lemma-Swap01-K0=K1-Swap01
  equals (K1 • Swap01) • CCZ • K0 • iI
    by general-assoc auto
  equals K1 • (Swap01 • CCZ) • K0 • iI
    by right left lemma-Swap01-CCZ=CCZ-Swap01
  equals K1 • (CCZ • Swap01) • K0 • iI
    by general-assoc auto
  equals (K1 • CCZ) • (Swap01 • K0) • iI
    by right left lemma-Swap01-K0=K1-Swap01
  equals (K1 • CCZ) • (K1 • Swap01) • iI
    by general-comm auto
  equals CCX1 • Swap01


lemma-Swap01-CCX1=CCX0-Swap01 : Rel ⊢ Swap01 • CCX1 === CCX0 • Swap01
lemma-Swap01-CCX1=CCX0-Swap01 =
  equational Swap01 • CCX1
    by Order.general-rewrite 100 auto
  equals Swap01 • (CCX1 • Swap01) • Swap01
    by right left symm lemma-Swap01-CCX0=CCX1-Swap01
  equals Swap01 • (Swap01 • CCX0) • Swap01
    by Order.general-rewrite 100 auto
  equals CCX0 • Swap01


lemma-CS02 : Rel ⊢ Swap12 • CS01 • Swap12 === Swap01 • CS12 • Swap01
lemma-CS02 =
  equational Swap12 • CS01 • Swap12
    by Order.general-rewrite 100 auto
  equals CX12 • CX21 • CS01 • CX21 • CX12
    by symm (axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12)
  equals CX10 • CX01 • CS12 • CX01 • CX10
    by Order.general-rewrite 100 auto
  equals (CX10 • CX01 • CX10) • CS12 • (CX10 • CX01 • CX10)
    by left lemma-Swap-alt-def reversed
  equals Swap01 • CS12 • (CX10 • CX01 • CX10)
    by right right lemma-Swap-alt-def reversed
  equals Swap01 • CS12 • Swap01

lemma-Swap01-CS02=CS12-Swap01 : Rel ⊢ Swap01 • CS02 === CS12 • Swap01
lemma-Swap01-CS02=CS12-Swap01 =
  equational Swap01 • CS02
    by right lemma-CS02
  equals Swap01 • Swap01 • CS12 • Swap01
    by Order.general-rewrite 100 auto
  equals CS12 • Swap01

lemma-Swap01-CS12=CS02-Swap01 : Rel ⊢ Swap01 • CS12 === CS02 • Swap01
lemma-Swap01-CS12=CS02-Swap01 =
  equational Swap01 • CS12
    by Order.general-rewrite 100 auto
  equals Swap01 • (CS12 • Swap01) • Swap01
    by right left symm lemma-Swap01-CS02=CS12-Swap01
  equals Swap01 • (Swap01 • CS02) • Swap01
    by Order.general-rewrite 100 auto
  equals CS02 • Swap01





lemma-Swap12-CX01=CX02-Swap12 : Rel ⊢ Swap12 • CX01 === CX02 • Swap12
lemma-Swap12-CX01=CX02-Swap12 =
  equational Swap12 • CX01
    by refl
  equals Swap12 • K1 • CS01 • CS01 • K1 • iI
    by Order.general-rewrite 100 auto
  equals (Swap12 • K1) • (CS01 • CS01) • (K1 • Swap12) • iI • Swap12
    by left lemma-Swap12-K1=K2-Swap12
  equals (K2 • Swap12) • (CS01 • CS01) • (K1 • Swap12) • iI • Swap12
    by right right left symm lemma-Swap12-K2=K1-Swap12
  equals (K2 • Swap12) • (CS01 • CS01) • (Swap12 • K2) • iI • Swap12
    by Order.general-rewrite 100 auto
  equals K2 • (Swap12 • CS01 • Swap12) • (Swap12 • CS01 • Swap12) • K2 • iI • Swap12
    by right left refl
  equals K2 • (CS02) • (Swap12 • CS01 • Swap12) • K2 • iI • Swap12
    by right right left refl
  equals K2 • (CS02) • (CS02) • K2 • iI • Swap12
    by Order.general-rewrite 100 auto
  equals CX02 • Swap12


lemma-Swap12-CX02=CX01-Swap12 : Rel ⊢ Swap12 • CX02 === CX01 • Swap12
lemma-Swap12-CX02=CX01-Swap12 =
  equational Swap12 • CX02
    by Order.general-rewrite 100 auto
  equals Swap12 • (CX02 • Swap12) • Swap12
    by right left symm lemma-Swap12-CX01=CX02-Swap12
  equals Swap12 • (Swap12 • CX01) • Swap12
    by Order.general-rewrite 100 auto
  equals CX01 • Swap12


lemma-Swap12-CCX2=CCX1-Swap12 : Rel ⊢ Swap12 • CCX2 === CCX1 • Swap12
lemma-Swap12-CCX2=CCX1-Swap12 =
  equational Swap12 • CCX2
    by refl
  equals Swap12 • K2 • CCZ • K2 • iI
    by general-assoc auto
  equals (Swap12 • K2) • CCZ • K2 • iI
    by left lemma-Swap12-K2=K1-Swap12
  equals (K1 • Swap12) • CCZ • K2 • iI
    by general-assoc auto
  equals K1 • (Swap12 • CCZ) • K2 • iI
    by right left lemma-Swap12-CCZ=CCZ-Swap12
  equals K1 • (CCZ • Swap12) • K2 • iI
    by general-assoc auto
  equals (K1 • CCZ) • (Swap12 • K2) • iI
    by right left lemma-Swap12-K2=K1-Swap12
  equals (K1 • CCZ) • (K1 • Swap12) • iI
    by general-comm auto
  equals CCX1 • Swap12


lemma-Swap12-CCX1=CCX2-Swap12 : Rel ⊢ Swap12 • CCX1 === CCX2 • Swap12
lemma-Swap12-CCX1=CCX2-Swap12 =
  equational Swap12 • CCX1
    by Order.general-rewrite 100 auto
  equals Swap12 • (CCX1 • Swap12) • Swap12
    by right left symm lemma-Swap12-CCX2=CCX1-Swap12
  equals Swap12 • (Swap12 • CCX2) • Swap12
    by Order.general-rewrite 100 auto
  equals CCX2 • Swap12


lemma-Swap12-CX10=CX20-Swap12 : Rel ⊢ Swap12 • CX10 === CX20 • Swap12
lemma-Swap12-CX10=CX20-Swap12 =
  equational Swap12 • CX10
    by Order.general-rewrite 100 auto
  equals CX20 • Swap12


lemma-Swap12-Swap01-Swap12=Swap01-Swap12-Swap01 : Rel ⊢ Swap12 • Swap01 • Swap12 === Swap01 • Swap12 • Swap01
lemma-Swap12-Swap01-Swap12=Swap01-Swap12-Swap01 =
  equational Swap12 • Swap01 • Swap12
    by refl
  equals Swap12 • (CX01 • CX10 • CX01) • Swap12
    by general-assoc auto
  equals (Swap12 • CX01) • CX10 • CX01 • Swap12
    by left lemma-Swap12-CX01=CX02-Swap12
  equals (CX02 • Swap12) • CX10 • CX01 • Swap12
    by general-assoc auto
  equals CX02 • (Swap12 • CX10) • CX01 • Swap12
    by right left lemma-Swap12-CX10=CX20-Swap12
  equals CX02 • (CX20 • Swap12) • CX01 • Swap12
    by general-assoc auto
  equals CX02 • CX20 • (Swap12 • CX01) • Swap12
    by right right left lemma-Swap12-CX01=CX02-Swap12
  equals CX02 • CX20 • (CX02 • Swap12) • Swap12
    by Order.general-rewrite 100 auto
  equals CX02 • CX20 • CX02
    by Order.general-rewrite 100 auto
  equals CX02 • CX20 • (CX02 • Swap01) • Swap01
    by right right left symm lemma-Swap01-CX12=CX02-Swap01
  equals CX02 • CX20 • (Swap01 • CX12) • Swap01
    by general-assoc auto
  equals CX02 • (CX20 • Swap01) • CX12 • Swap01
    by right left symm lemma-Swap01-CX21=CX20-Swap01
  equals CX02 • (Swap01 • CX21) • CX12 • Swap01
    by general-assoc auto
  equals (CX02 • Swap01) • CX21 • CX12 • Swap01
    by left symm lemma-Swap01-CX12=CX02-Swap01
  equals (Swap01 • CX12) • CX21 • CX12 • Swap01
    by general-assoc auto
  equals Swap01 • (CX12 • CX21 • CX12) • Swap01
    by refl
  equals Swap01 • Swap12 • Swap01


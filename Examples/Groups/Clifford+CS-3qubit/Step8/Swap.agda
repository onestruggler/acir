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

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap where

lemma-CX12-S1=S1-CX12 : Rel ⊢ CX12 • S1 === S1 • CX12
lemma-CX12-S1=S1-CX12 =
  equational CX12 • S1
    by general-comm auto
  equals S1 • CX12


lemma-CX12-S2 : Rel ⊢ CX12 • S2 === S1 • S2 • CS12 • CS12 • CX12
lemma-CX12-S2 =
  equational CX12 • S2
    by general-comm auto
  equals (K2 • CS12 • CS12 • K2 • S2) • iI
    by left lemma-K2-CS12-CS12-K2-S2=S1-S2-CS12-CS12-K2-CS12-CS12-K2
  equals (S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • iI
    by general-comm auto
  equals S1 • S2 • CS12 • CS12 • CX12

lemma-CX01-S1 : Rel ⊢ CX01 • S1 === S0 • S1 • CS01 • CS01 • CX01
lemma-CX01-S1 =
  equational CX01 • S1
    by general-comm auto
  equals (K1 • CS01 • CS01 • K1 • S1) • iI
    by left lemma-K1-CS01-CS01-K1-S1=S0-S1-CS01-CS01-K1-CS01-CS01-K1
  equals (S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • iI
    by general-comm auto
  equals S0 • S1 • CS01 • CS01 • CX01


lemma-CX21-S1 : Rel ⊢ CX21 • S1 === S2 • S1 • CS12 • CS12 • CX21
lemma-CX21-S1 =
  equational CX21 • S1
    by general-comm auto
  equals (K1 • CS12 • CS12 • K1 • S1) • iI
    by left lemma-K1-CS12-CS12-K1-S1=S2-S1-CS12-CS12-K1-CS12-CS12-K1
  equals (S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • iI
    by general-comm auto
  equals S2 • S1 • CS12 • CS12 • CX21


lemma-CX10-S0 : Rel ⊢ CX10 • S0 === S1 • S0 • CS01 • CS01 • CX10
lemma-CX10-S0 =
  equational CX10 • S0
    by general-comm auto
  equals (K0 • CS01 • CS01 • K0 • S0) • iI
    by left lemma-K0-CS01-CS01-K0-S0=S1-S0-CS01-CS01-K0-CS01-CS01-K0
  equals (S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • iI
    by general-comm auto
  equals S1 • S0 • CS01 • CS01 • CX10


lemma-CX10-S0' : Rel ⊢ CX10 • S0 === S0 • S1 • CS01 • CS01 • CX10
lemma-CX10-S0' =
  equational CX10 • S0
    by general-comm auto
  equals (K0 • CS01 • CS01 • K0 • S0) • iI
    by left lemma-K0-CS01-CS01-K0-S0=S1-S0-CS01-CS01-K0-CS01-CS01-K0
  equals (S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • iI
    by general-comm auto
  equals S0 • S1 • CS01 • CS01 • CX10


lemma-K0-CS01-CS01-K0-CS01-CS01=S1-S1-CS01-CS01-K0-CS01-CS01-K0 : Rel ⊢  K0 • CS01 • CS01 • K0 • CS01 • CS01 === S1 • S1 • CS01 • CS01 • K0 • CS01 • CS01 • K0
lemma-K0-CS01-CS01-K0-CS01-CS01=S1-S1-CS01-CS01-K0-CS01-CS01-K0 =
  equational K0 • CS01 • CS01 • K0 • CS01 • CS01
    by general-assoc auto
  equals (K0 • CS01 • CS01 • K0 • CS01) • CS01
    by left lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0
  equals (S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • CS01
    by general-assoc auto
  equals (S1 • CS01 • CS01 • CS01) • K0 • CS01 • CS01 • K0 • CS01
    by right lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0
  equals (S1 • CS01 • CS01 • CS01) • S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0
    by Order.general-rewrite 100 auto
  equals S1 • S1 • CS01 • CS01 • K0 • CS01 • CS01 • K0

lemma-K1-CS01-CS01-K1-CS01-CS01=S0-S0-CS01-CS01-K1-CS01-CS01-K1 : Rel ⊢  K1 • CS01 • CS01 • K1 • CS01 • CS01 === S0 • S0 • CS01 • CS01 • K1 • CS01 • CS01 • K1
lemma-K1-CS01-CS01-K1-CS01-CS01=S0-S0-CS01-CS01-K1-CS01-CS01-K1 =
  equational K1 • CS01 • CS01 • K1 • CS01 • CS01
    by general-assoc auto
  equals (K1 • CS01 • CS01 • K1 • CS01) • CS01
    by left lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals (S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • CS01
    by general-assoc auto
  equals (S0 • CS01 • CS01 • CS01) • K1 • CS01 • CS01 • K1 • CS01
    by right lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals (S0 • CS01 • CS01 • CS01) • S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1
    by Order.general-rewrite 100 auto
  equals S0 • S0 • CS01 • CS01 • K1 • CS01 • CS01 • K1

lemma-K1-CS12-CS12-K1-CS12-CS12=S2-S2-CS12-CS12-K1-CS12-CS12-K1 : Rel ⊢  K1 • CS12 • CS12 • K1 • CS12 • CS12 === S2 • S2 • CS12 • CS12 • K1 • CS12 • CS12 • K1
lemma-K1-CS12-CS12-K1-CS12-CS12=S2-S2-CS12-CS12-K1-CS12-CS12-K1 =
  equational K1 • CS12 • CS12 • K1 • CS12 • CS12
    by general-assoc auto
  equals (K1 • CS12 • CS12 • K1 • CS12) • CS12
    by left lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals (S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • CS12
    by general-assoc auto
  equals (S2 • CS12 • CS12 • CS12) • K1 • CS12 • CS12 • K1 • CS12
    by right lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals (S2 • CS12 • CS12 • CS12) • S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1
    by Order.general-rewrite 100 auto
  equals S2 • S2 • CS12 • CS12 • K1 • CS12 • CS12 • K1

lemma-K2-CS12-CS12-K2-CS12-CS12=S1-S1-CS12-CS12-K2-CS12-CS12-K2 : Rel ⊢  K2 • CS12 • CS12 • K2 • CS12 • CS12 === S1 • S1 • CS12 • CS12 • K2 • CS12 • CS12 • K2
lemma-K2-CS12-CS12-K2-CS12-CS12=S1-S1-CS12-CS12-K2-CS12-CS12-K2 =
  equational K2 • CS12 • CS12 • K2 • CS12 • CS12
    by general-assoc auto
  equals (K2 • CS12 • CS12 • K2 • CS12) • CS12
    by left lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals (S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • CS12
    by general-assoc auto
  equals (S1 • CS12 • CS12 • CS12) • K2 • CS12 • CS12 • K2 • CS12
    by right lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals (S1 • CS12 • CS12 • CS12) • S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2
    by Order.general-rewrite 100 auto
  equals S1 • S1 • CS12 • CS12 • K2 • CS12 • CS12 • K2


lemma-CX21-CS12 : Rel ⊢ CX21 • CS12 === S2 • CS12 ^ 3 • CX21
lemma-CX21-CS12 =
  equational CX21 • CS12
    by general-comm auto
  equals iI • K1 • CS12 • CS12 • K1 • CS12
    by right lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals iI • S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1
    by general-comm auto
  equals S2 • CS12 ^ 3 • CX21





lemma-CX21-CS12-CS12 : Rel ⊢ CX21 • CS12 • CS12 === S2 • S2 • CS12 • CS12 • CX21
lemma-CX21-CS12-CS12 =
  equational CX21 • CS12 • CS12
    by general-comm auto
  equals (K1 • CS12 • CS12 • K1 • CS12 • CS12) • iI
    by left lemma-K1-CS12-CS12-K1-CS12-CS12=S2-S2-CS12-CS12-K1-CS12-CS12-K1
  equals (S2 • S2 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • iI
    by general-comm auto
  equals S2 • S2 • CS12 • CS12 • CX21

lemma-CX21-CS12-CS12-CS12 : Rel ⊢ CX21 • CS12 • CS12 • CS12 === S2 • S2 • S2 • CS12 • CX21
lemma-CX21-CS12-CS12-CS12 =
  equational CX21 • CS12 • CS12 • CS12
    by general-assoc auto
  equals (CX21 • CS12 • CS12) • CS12
    by left lemma-CX21-CS12-CS12
  equals (S2 • S2 • CS12 • CS12 • CX21) • CS12
    by general-assoc auto
  equals (S2 • S2 • CS12 • CS12) • CX21 • CS12
    by right lemma-CX21-CS12
  equals (S2 • S2 • CS12 • CS12) • S2 • CS12 ^ 3 • CX21
    by Order.general-rewrite 100 auto
  equals S2 • S2 • S2 • CS12 • CX21


lemma-CX12-CS12-CS12 : Rel ⊢ CX12 • CS12 • CS12 === S1 • S1 • CS12 • CS12 • CX12
lemma-CX12-CS12-CS12 =
  equational CX12 • CS12 • CS12
    by general-comm auto
  equals (K2 • CS12 • CS12 • K2 • CS12 • CS12) • iI
    by left lemma-K2-CS12-CS12-K2-CS12-CS12=S1-S1-CS12-CS12-K2-CS12-CS12-K2
  equals (S1 • S1 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • iI
    by general-comm auto
  equals S1 • S1 • CS12 • CS12 • CX12


lemma-CX01-CS01 : Rel ⊢ CX01 • CS01 === S0 • CS01 • CS01 • CS01 • CX01
lemma-CX01-CS01 =
  equational CX01 • CS01
    by general-comm auto
  equals (K1 • CS01 • CS01 • K1 • CS01) • iI
    by left lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals (S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • iI
    by general-comm auto
  equals S0 • CS01 • CS01 • CS01 • CX01



lemma-CX01-CS01-CS01 : Rel ⊢ CX01 • CS01 • CS01 === S0 • S0 • CS01 • CS01 • CX01
lemma-CX01-CS01-CS01 =
  equational CX01 • CS01 • CS01
    by general-comm auto
  equals (K1 • CS01 • CS01 • K1 • CS01 • CS01) • iI
    by left lemma-K1-CS01-CS01-K1-CS01-CS01=S0-S0-CS01-CS01-K1-CS01-CS01-K1
  equals (S0 • S0 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • iI
    by general-comm auto
  equals S0 • S0 • CS01 • CS01 • CX01




lemma-CX01-CS01-CS01-CS01 : Rel ⊢ CX01 • CS01 • CS01 • CS01 === S0 • S0 • S0 • CS01 • CX01
lemma-CX01-CS01-CS01-CS01 =
  equational CX01 • CS01 • CS01 • CS01
    by general-comm auto
  equals (K1 • CS01 • CS01 • K1 • CS01) • CS01 • CS01 • iI
    by left lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals (S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • CS01 • CS01 • iI
    by general-comm auto
  equals (S0 • CS01 • CS01 • CS01) • (CX01 • CS01 • CS01)
    by right lemma-CX01-CS01-CS01
  equals (S0 • CS01 • CS01 • CS01) • S0 • S0 • CS01 • CS01 • CX01
    by Order.general-rewrite 100 auto
  equals S0 • S0 • S0 • CS01 • CX01


lemma-CX10-CS01-CS01 : Rel ⊢ CX10 • CS01 • CS01 === S1 • S1 • CS01 • CS01 • CX10
lemma-CX10-CS01-CS01 =
  equational CX10 • CS01 • CS01
    by general-comm auto
  equals (K0 • CS01 • CS01 • K0 • CS01 • CS01) • iI
    by left lemma-K0-CS01-CS01-K0-CS01-CS01=S1-S1-CS01-CS01-K0-CS01-CS01-K0
  equals (S1 • S1 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • iI
    by general-comm auto
  equals S1 • S1 • CS01 • CS01 • CX10


lemma-Swap12-S1=S2-Swap12 : Rel ⊢ (CX12 • CX21 • CX12) • S1 === S2 • CX12 • CX21 • CX12
lemma-Swap12-S1=S2-Swap12 =
  equational (CX12 • CX21 • CX12) • S1
    by general-assoc auto
  equals CX12 • CX21 • (CX12 • S1)
    by right right general-comm auto
  equals CX12 • CX21 • (S1 • CX12)
    by general-assoc auto
  equals CX12 • (CX21 • S1) • CX12
    by right left lemma-CX21-S1
  equals CX12 • (S2 • S1 • CS12 • CS12 • CX21) • CX12
    by general-assoc auto
  equals (CX12 • S2) • S1 • CS12 • CS12 • CX21 • CX12
    by left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • CX12) • S1 • CS12 • CS12 • CX21 • CX12
    by general-comm auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (CX12 • CS12 • CS12) • CX21 • CX12
    by right left lemma-CX12-CS12-CS12
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • S1 • CS12 • CS12 • CX12) • CX21 • CX12
    by Order.general-rewrite 100 auto
  equals S2 • CX12 • CX21 • CX12

lemma-Swap12-S2=S1-Swap12 : Rel ⊢ (CX12 • CX21 • CX12) • S2 === S1 • CX12 • CX21 • CX12
lemma-Swap12-S2=S1-Swap12 =
  equational (CX12 • CX21 • CX12) • S2
    by general-assoc auto
  equals (CX12 • CX21) • (CX12 • S2)
    by right lemma-CX12-S2
  equals (CX12 • CX21) • (S1 • S2 • CS12 • CS12 • CX12)
    by general-assoc auto
  equals CX12 • (CX21 • S1) • (S2 • CS12 • CS12 • CX12)
    by right left lemma-CX21-S1
  equals CX12 • (S2 • S1 • CS12 • CS12 • CX21) • (S2 • CS12 • CS12 • CX12)
    by general-comm auto
  equals (CX12 • S2) • (S1 • CS12 • CS12 • S2) • (CX21 • CS12 • CS12) • CX12
    by cong lemma-CX12-S2 (right left lemma-CX21-CS12-CS12)
  equals (S1 • S2 • CS12 • CS12 • CX12) • (S1 • CS12 • CS12 • S2) • (S2 • S2 • CS12 • CS12 • CX21) • CX12
    by general-comm auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (CX12 • CS12 • CS12) • (S2 • S2 • S2 • CS12 • CS12 • CX21 • CX12)
    by right left lemma-CX12-CS12-CS12
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • S1 • CS12 • CS12 • CX12) • (S2 • S2 • S2 • CS12 • CS12 • CX21 • CX12)
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12 • S1 • S1 • S1 • CS12 • CS12) • (CX12 • S2) • S2 • S2 • CS12 • CS12 • CX21 • CX12
    by right left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • S1 • S1 • S1 • CS12 • CS12) • (S1 • S2 • CS12 • CS12 • CX12) • S2 • S2 • CS12 • CS12 • CX21 • CX12
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12 • S1 • S1 • S1 • CS12 • CS12 • S1 • S2 • CS12 • CS12) • (CX12 • S2) • S2 • CS12 • CS12 • CX21 • CX12
    by right left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • S1 • S1 • S1 • CS12 • CS12 • S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12 • CX12) • S2 • CS12 • CS12 • CX21 • CX12
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12 • S1 • S1 • S1 • CS12 • CS12 • S1 • S2 • CS12 • CS12 • S1 • S2 • CS12 • CS12) • (CX12 • S2) • CS12 • CS12 • CX21 • CX12
    by right left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • S1 • S1 • S1 • CS12 • CS12 • S1 • S2 • CS12 • CS12 • S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12 • CX12) • CS12 • CS12 • CX21 • CX12
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12 • S1 • S1 • S1 • CS12 • CS12 • S1 • S2 • CS12 • CS12 • S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • (CX12 • CS12 • CS12) • CX21 • CX12
    by right right left lemma-CX12-CS12-CS12
  equals (S1 • S2 • CS12 • CS12 • S1 • S1 • S1 • CS12 • CS12 • S1 • S2 • CS12 • CS12 • S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • (S1 • S1 • CS12 • CS12 • CX12) • CX21 • CX12
    by Order.general-rewrite 200 auto
  equals S1 • CX12 • CX21 • CX12


lemma-Swap01-S0=S1-Swap01 : Rel ⊢ (CX01 • CX10 • CX01) • S0 === S1 • CX01 • CX10 • CX01
lemma-Swap01-S0=S1-Swap01 =
  equational (CX01 • CX10 • CX01) • S0
    by general-assoc auto
  equals CX01 • CX10 • (CX01 • S0)
    by right right general-comm auto
  equals CX01 • CX10 • (S0 • CX01)
    by general-assoc auto
  equals CX01 • (CX10 • S0) • CX01
    by right left lemma-CX10-S0
  equals CX01 • (S1 • S0 • CS01 • CS01 • CX10) • CX01
    by general-assoc auto
  equals (CX01 • S1) • S0 • CS01 • CS01 • CX10 • CX01
    by left lemma-CX01-S1
  equals (S0 • S1 • CS01 • CS01 • CX01) • S0 • CS01 • CS01 • CX10 • CX01
    by general-comm auto
  equals (S0 • S1 • CS01 • CS01 • S0) • (CX01 • CS01 • CS01) • CX10 • CX01
    by right left lemma-CX01-CS01-CS01
  equals (S0 • S1 • CS01 • CS01 • S0) • (S0 • S0 • CS01 • CS01 • CX01) • CX10 • CX01
    by Order.general-rewrite 100 auto
  equals S1 • CX01 • CX10 • CX01

lemma-Swap01-S1=S0-Swap01 : Rel ⊢ (CX01 • CX10 • CX01) • S1 === S0 • CX01 • CX10 • CX01
lemma-Swap01-S1=S0-Swap01 =
  equational (CX01 • CX10 • CX01) • S1
    by general-assoc auto
  equals (CX01 • CX10) • (CX01 • S1)
    by right lemma-CX01-S1
  equals (CX01 • CX10) • (S0 • S1 • CS01 • CS01 • CX01)
    by general-assoc auto
  equals CX01 • (CX10 • S0) • (S1 • CS01 • CS01 • CX01)
    by right left lemma-CX10-S0
  equals CX01 • (S1 • S0 • CS01 • CS01 • CX10) • (S1 • CS01 • CS01 • CX01)
    by general-comm auto
  equals (CX01 • S1) • (S0 • CS01 • CS01 • S1) • (CX10 • CS01 • CS01) • CX01
    by cong lemma-CX01-S1 (right left lemma-CX10-CS01-CS01)
  equals (S0 • S1 • CS01 • CS01 • CX01) • (S0 • CS01 • CS01 • S1) • (S1 • S1 • CS01 • CS01 • CX10) • CX01
    by general-comm auto
  equals (S0 • S1 • CS01 • CS01 • S0) • (CX01 • CS01 • CS01) • (S1 • S1 • S1 • CS01 • CS01 • CX10 • CX01)
    by right left lemma-CX01-CS01-CS01
  equals (S0 • S1 • CS01 • CS01 • S0) • (S0 • S0 • CS01 • CS01 • CX01) • (S1 • S1 • S1 • CS01 • CS01 • CX10 • CX01)
    by general-assoc auto
  equals (S0 • S1 • CS01 • CS01 • S0 • S0 • S0 • CS01 • CS01) • (CX01 • S1) • S1 • S1 • CS01 • CS01 • CX10 • CX01
    by right left lemma-CX01-S1
  equals (S0 • S1 • CS01 • CS01 • S0 • S0 • S0 • CS01 • CS01) • (S0 • S1 • CS01 • CS01 • CX01) • S1 • S1 • CS01 • CS01 • CX10 • CX01
    by general-assoc auto
  equals (S0 • S1 • CS01 • CS01 • S0 • S0 • S0 • CS01 • CS01 • S0 • S1 • CS01 • CS01) • (CX01 • S1) • S1 • CS01 • CS01 • CX10 • CX01
    by right left lemma-CX01-S1
  equals (S0 • S1 • CS01 • CS01 • S0 • S0 • S0 • CS01 • CS01 • S0 • S1 • CS01 • CS01) • (S0 • S1 • CS01 • CS01 • CX01) • S1 • CS01 • CS01 • CX10 • CX01
    by general-assoc auto
  equals (S0 • S1 • CS01 • CS01 • S0 • S0 • S0 • CS01 • CS01 • S0 • S1 • CS01 • CS01 • S0 • S1 • CS01 • CS01) • (CX01 • S1) • CS01 • CS01 • CX10 • CX01
    by right left lemma-CX01-S1
  equals (S0 • S1 • CS01 • CS01 • S0 • S0 • S0 • CS01 • CS01 • S0 • S1 • CS01 • CS01 • S0 • S1 • CS01 • CS01) • (S0 • S1 • CS01 • CS01 • CX01) • CS01 • CS01 • CX10 • CX01
    by general-assoc auto
  equals (S0 • S1 • CS01 • CS01 • S0 • S0 • S0 • CS01 • CS01 • S0 • S1 • CS01 • CS01 • S0 • S1 • CS01 • CS01) • (S0 • S1 • CS01 • CS01) • (CX01 • CS01 • CS01) • CX10 • CX01
    by right right left lemma-CX01-CS01-CS01
  equals (S0 • S1 • CS01 • CS01 • S0 • S0 • S0 • CS01 • CS01 • S0 • S1 • CS01 • CS01 • S0 • S1 • CS01 • CS01) • (S0 • S1 • CS01 • CS01) • (S0 • S0 • CS01 • CS01 • CX01) • CX10 • CX01
    by Order.general-rewrite 100 auto
  equals S0 • CX01 • CX10 • CX01


lemma-Swap12-CS12=CS12-Swap12 : Rel ⊢ Swap12 • CS12 === CS12 • Swap12
lemma-Swap12-CS12=CS12-Swap12 =
  equational Swap12 • CS12
    by general-comm auto
  equals CX12 • CX21 • (K2 • CS12 • CS12 • K2 • CS12) • iI
    by right right left lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals CX12 • CX21 • (S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • iI
    by general-assoc auto
  equals CX12 • (CX21 • S1) • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2 • iI
    by right left lemma-CX21-S1
  equals CX12 • (S2 • S1 • CS12 • CS12 • CX21) • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2 • iI
    by general-assoc auto
  equals (CX12 • S2) • (S1 • CS12 • CS12) • (CX21 • CS12 • CS12) • CS12 • K2 • CS12 • CS12 • K2 • iI
    by cong lemma-CX12-S2 (right left lemma-CX21-CS12-CS12)
  equals (S1 • S2 • CS12 • CS12 • CX12) • (S1 • CS12 • CS12) • (S2 • S2 • CS12 • CS12 • CX21) • CS12 • K2 • CS12 • CS12 • K2 • iI
    by Order.general-rewrite 100 auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (CX12 • S2) • S2 • (K1 • CS12 • CS12 • K1 • CS12) • K2 • CS12 • CS12 • K2 • iI ^ 2
    by right cong lemma-CX12-S2 (right left lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1)
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • S2 • CS12 • CS12 • CX12) • S2 • (S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • K2 • CS12 • CS12 • K2 • iI ^ 2
    by Order.general-rewrite 100 auto
  equals (S1 • S2 • S1 • S1 • S2) • (CX12 • S2) • S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • iI ^ 2
    by right left lemma-CX12-S2
  equals (S1 • S2 • S1 • S1 • S2) • (S1 • S2 • CS12 • CS12 • CX12) • S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • iI ^ 2
    by general-assoc auto
  equals (S1 • S2 • S1 • S1 • S2) • (S1 • S2 • CS12 • CS12) • (CX12 • S2) • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • iI ^ 2
    by right right (left lemma-CX12-S2)
  equals (S1 • S2 • S1 • S1 • S2) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12 • CX12) • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • iI ^ 2
    by Order.general-rewrite 100 auto
  equals S1 • (CX12 • CS12 • CS12) • CS12 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • iI ^ 2
    by right left lemma-CX12-CS12-CS12
  equals S1 • (S1 • S1 • CS12 • CS12 • CX12) • CS12 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • iI ^ 2
    by general-comm auto
  equals (S1 • S1 • S1 • CS12 • CS12) • (K2 • CS12 • CS12 • K2 • CS12) • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • iI ^ 3
    by right left lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals (S1 • S1 • S1 • CS12 • CS12) • (S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • iI ^ 3
    by Order.general-rewrite 100 auto
  equals CS12 • Swap12



lemma-Swap01-CS01=CS01-Swap01 : Rel ⊢ Swap01 • CS01 === CS01 • Swap01
lemma-Swap01-CS01=CS01-Swap01 =
  equational Swap01 • CS01
    by general-comm auto
  equals CX01 • CX10 • (K1 • CS01 • CS01 • K1 • CS01) • iI
    by right right left lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals CX01 • CX10 • (S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • iI
    by general-assoc auto
  equals CX01 • (CX10 • S0) • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1 • iI
    by right left lemma-CX10-S0
  equals CX01 • (S1 • S0 • CS01 • CS01 • CX10) • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1 • iI
    by general-assoc auto
  equals (CX01 • S1) • (S0 • CS01 • CS01) • (CX10 • CS01 • CS01) • CS01 • K1 • CS01 • CS01 • K1 • iI
    by cong lemma-CX01-S1 (right left lemma-CX10-CS01-CS01)
  equals (S0 • S1 • CS01 • CS01 • CX01) • (S0 • CS01 • CS01) • (S1 • S1 • CS01 • CS01 • CX10) • CS01 • K1 • CS01 • CS01 • K1 • iI
    by Order.general-rewrite 100 auto
  equals (S0 • S1 • CS01 • CS01 • S0) • (CX01 • S1) • S1 • (K0 • CS01 • CS01 • K0 • CS01) • K1 • CS01 • CS01 • K1 • iI ^ 2
    by right cong lemma-CX01-S1 (right left lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0)
  equals (S0 • S1 • CS01 • CS01 • S0) • (S0 • S1 • CS01 • CS01 • CX01) • S1 • (S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • K1 • CS01 • CS01 • K1 • iI ^ 2
    by Order.general-rewrite 100 auto
  equals (S0 • S1 • S0 • S0 • S1) • (CX01 • S1) • S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • iI ^ 2
    by right left lemma-CX01-S1
  equals (S0 • S1 • S0 • S0 • S1) • (S0 • S1 • CS01 • CS01 • CX01) • S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • iI ^ 2
    by general-assoc auto
  equals (S0 • S1 • S0 • S0 • S1) • (S0 • S1 • CS01 • CS01) • (CX01 • S1) • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • iI ^ 2
    by right right (left lemma-CX01-S1)
  equals (S0 • S1 • S0 • S0 • S1) • (S0 • S1 • CS01 • CS01) • (S0 • S1 • CS01 • CS01 • CX01) • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • iI ^ 2
    by Order.general-rewrite 100 auto
  equals S0 • (CX01 • CS01 • CS01) • CS01 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • iI ^ 2
    by right left lemma-CX01-CS01-CS01
  equals S0 • (S0 • S0 • CS01 • CS01 • CX01) • CS01 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • iI ^ 2
    by general-comm auto
  equals (S0 • S0 • S0 • CS01 • CS01) • (K1 • CS01 • CS01 • K1 • CS01) • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • iI ^ 3
    by right left lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals (S0 • S0 • S0 • CS01 • CS01) • (S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • iI ^ 3
    by Order.general-rewrite 100 auto
  equals CS01 • Swap01

lemma-14 : Rel ⊢ S0 • S0 • K0 • CS01 • CS01 === K0 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • iI
lemma-14 =
  equational S0 • S0 • K0 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals K0 • (X0 • CS01) • CS01
    by right left axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
  equals K0 • (CS01 • CS01 • CS01 • X0 • S1) • CS01
    by general-comm auto
  equals K0 • (CS01 • CS01 • CS01 • S1) • X0 • CS01
    by right right axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
  equals K0 • (CS01 • CS01 • CS01 • S1) • CS01 • CS01 • CS01 • X0 • S1
    by Order.general-rewrite 100 auto
  equals K0 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • iI



lemma-14c : Rel ⊢ S1 • S1 • K1 • CS12 • CS12 === K1 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • iI
lemma-14c =
  equational S1 • S1 • K1 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals K1 • (X1 • CS12) • CS12
    by right left axiom ax-X1-CS12=CS12-CS12-CS12-X1-S2
  equals K1 • (CS12 • CS12 • CS12 • X1 • S2) • CS12
    by general-comm auto
  equals K1 • (CS12 • CS12 • CS12 • S2) • X1 • CS12
    by right right axiom ax-X1-CS12=CS12-CS12-CS12-X1-S2
  equals K1 • (CS12 • CS12 • CS12 • S2) • CS12 • CS12 • CS12 • X1 • S2
    by Order.general-rewrite 211 auto
  equals K1 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • iI


lemma-14d : Rel ⊢ S2 • S2 • K2 • CS12 • CS12 === K2 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • iI
lemma-14d =
  equational S2 • S2 • K2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals K2 • (X2 • CS12) • CS12
    by right left axiom ax-X2-CS12=CS12-CS12-CS12-X2-S1
  equals K2 • (CS12 • CS12 • CS12 • X2 • S1) • CS12
    by general-comm auto
  equals K2 • (CS12 • CS12 • CS12 • S1) • X2 • CS12
    by right right axiom ax-X2-CS12=CS12-CS12-CS12-X2-S1
  equals K2 • (CS12 • CS12 • CS12 • S1) • CS12 • CS12 • CS12 • X2 • S1
    by Order.general-rewrite 211 auto
  equals K2 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • iI





lemma-C8 : Rel ⊢ K0 • S0 • S0 • K0 • CS01 • CS01 === CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1
lemma-C8 =
  equational K0 • S0 • S0 • K0 • CS01 • CS01
    by right lemma-14
  equals K0 • K0 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • iI
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1



lemma-C8b : Rel ⊢ K1 • S1 • S1 • K1 • CS12 • CS12 === CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2
lemma-C8b =
  equational K1 • S1 • S1 • K1 • CS12 • CS12
    by right lemma-14c
  equals K1 • K1 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • iI
    by Order.general-rewrite 211 auto
  equals CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2


lemma-14b : Rel ⊢ S1 • S1 • K1 • CS01 • CS01 === K1 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • iI
lemma-14b =
  equational S1 • S1 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals K1 • (X1 • CS01) • CS01
    by right left axiom ax-X1-CS01=CS01-CS01-CS01-X1-S0
  equals K1 • (CS01 • CS01 • CS01 • X1 • S0) • CS01
    by general-comm auto
  equals K1 • (CS01 • CS01 • CS01 • S0) • X1 • CS01
    by right right axiom ax-X1-CS01=CS01-CS01-CS01-X1-S0
  equals K1 • (CS01 • CS01 • CS01 • S0) • CS01 • CS01 • CS01 • X1 • S0
    by Order.general-rewrite 100 auto
  equals K1 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • iI




lemma-10 : Rel ⊢ K0 • S0 • K0 === S0 ^ 3 • K0 • S0 ^ 3
lemma-10 =
  equational K0 • S0 • K0
    by Order.general-rewrite 100 auto
  equals S0 ^ 3 •  (S0 • K0 • S0 • K0 • S0 • K0) • K0 • iI • S0 ^ 3
    by right left axiom ax-S0-K0-S0-K0-S0-K0=iI-iI-iI
  equals S0 ^ 3 •  (iI ^ 3) • K0 • iI • S0 ^ 3
    by Order.general-rewrite 100 auto
  equals S0 ^ 3 • K0 • S0 ^ 3


lemma-K1-S1-K1=S1^3-K1-S1^3 : Rel ⊢ K1 • S1 • K1 === S1 ^ 3 • K1 • S1 ^ 3
lemma-K1-S1-K1=S1^3-K1-S1^3 =
  equational K1 • S1 • K1
    by Order.general-rewrite 111 auto
  equals S1 ^ 3 •  (S1 • K1 • S1 • K1 • S1 • K1) • K1 • iI • S1 ^ 3
    by right left axiom ax-S1-K1-S1-K1-S1-K1=iI-iI-iI
  equals S1 ^ 3 •  (iI ^ 3) • K1 • iI • S1 ^ 3
    by Order.general-rewrite 111 auto
  equals S1 ^ 3 • K1 • S1 ^ 3

lemma-10c : Rel ⊢ K2 • S2 • K2 === S2 ^ 3 • K2 • S2 ^ 3
lemma-10c =
  equational K2 • S2 • K2
    by Order.general-rewrite 222 auto
  equals S2 ^ 3 •  (S2 • K2 • S2 • K2 • S2 • K2) • K2 • iI • S2 ^ 3
    by right left axiom ax-S2-K2-S2-K2-S2-K2=iI-iI-iI
  equals S2 ^ 3 •  (iI ^ 3) • K2 • iI • S2 ^ 3
    by Order.general-rewrite 222 auto
  equals S2 ^ 3 • K2 • S2 ^ 3



lemma-5 : Rel ⊢ K0 • S0 • K0 • S0 === S0 ^ 3 • K0
lemma-5 =
  equational K0 • S0 • K0 • S0
    by general-assoc auto
  equals (K0 • S0 • K0) • S0
    by left lemma-10
  equals (S0 ^ 3 • K0 • S0 ^ 3) • S0
    by Order.general-rewrite 100 auto
  equals S0 ^ 3 • K0




lemma-5' : Rel ⊢ S0 • K0 • S0 • K0 === K0 • S0 ^ 3
lemma-5' =
  equational S0 • K0 • S0 • K0
    by general-assoc auto
  equals S0 • (K0 • S0 • K0)
    by right lemma-10
  equals S0 • (S0 ^ 3 • K0 • S0 ^ 3)
    by Order.general-rewrite 100 auto
  equals K0 • S0 ^ 3

lemma-4 = lemma-5'

lemma-SKS : Rel ⊢ S0 • K0 • S0 === K0 • S0 ^ 3 • K0 • iI
lemma-SKS =
  equational S0 • K0 • S0
    by Order.general-rewrite 100 auto
  equals (S0 • K0 • S0 • K0) • K0 • iI
    by left lemma-5'
  equals (K0 • S0 ^ 3) • K0 • iI
    by general-assoc auto
  equals K0 • S0 ^ 3 • K0 • iI




lemma-11b : Rel ⊢ K1 • S1 • K1 === S1 ^ 3 • K1 • S1 ^ 3
lemma-11b =
  equational K1 • S1 • K1
    by Order.general-rewrite 111 auto
  equals S1 ^ 3 •  (S1 • K1 • S1 • K1 • S1 • K1) • K1 • iI • S1 ^ 3
    by right left axiom ax-S1-K1-S1-K1-S1-K1=iI-iI-iI
  equals S1 ^ 3 •  (iI ^ 3) • K1 • iI • S1 ^ 3
    by Order.general-rewrite 111 auto
  equals S1 ^ 3 • K1 • S1 ^ 3


lemma-11c : Rel ⊢ K2 • S2 • K2 === S2 ^ 3 • K2 • S2 ^ 3
lemma-11c =
  equational K2 • S2 • K2
    by Order.general-rewrite 222 auto
  equals S2 ^ 3 •  (S2 • K2 • S2 • K2 • S2 • K2) • K2 • iI • S2 ^ 3
    by right left axiom ax-S2-K2-S2-K2-S2-K2=iI-iI-iI
  equals S2 ^ 3 •  (iI ^ 3) • K2 • iI • S2 ^ 3
    by Order.general-rewrite 222 auto
  equals S2 ^ 3 • K2 • S2 ^ 3


lemma-5b : Rel ⊢ K1 • S1 • K1 • S1 === S1 ^ 3 • K1
lemma-5b =
  equational K1 • S1 • K1 • S1
    by general-assoc auto
  equals (K1 • S1 • K1) • S1
    by left lemma-11b
  equals (S1 ^ 3 • K1 • S1 ^ 3) • S1
    by Order.general-rewrite 111 auto
  equals S1 ^ 3 • K1


lemma-5c : Rel ⊢ K2 • S2 • K2 • S2 === S2 ^ 3 • K2
lemma-5c =
  equational K2 • S2 • K2 • S2
    by general-assoc auto
  equals (K2 • S2 • K2) • S2
    by left lemma-11c
  equals (S2 ^ 3 • K2 • S2 ^ 3) • S2
    by Order.general-rewrite 222 auto
  equals S2 ^ 3 • K2

lemma-5'b : Rel ⊢ S1 • K1 • S1 • K1 === K1 • S1 ^ 3
lemma-5'b =
  equational S1 • K1 • S1 • K1
    by general-assoc auto
  equals S1 • (K1 • S1 • K1)
    by right lemma-11b
  equals S1 • (S1 ^ 3 • K1 • S1 ^ 3)
    by Order.general-rewrite 111 auto
  equals K1 • S1 ^ 3

lemma-4b = lemma-5'b

lemma-5'c : Rel ⊢ S2 • K2 • S2 • K2 === K2 • S2 ^ 3
lemma-5'c =
  equational S2 • K2 • S2 • K2
    by general-assoc auto
  equals S2 • (K2 • S2 • K2)
    by right lemma-11c
  equals S2 • (S2 ^ 3 • K2 • S2 ^ 3)
    by Order.general-rewrite 222 auto
  equals K2 • S2 ^ 3

lemma-4c = lemma-5'c


lemma-SKSb : Rel ⊢ S1 • K1 • S1 === K1 • S1 ^ 3 • K1 • iI
lemma-SKSb =
  equational S1 • K1 • S1
    by Order.general-rewrite 111 auto
  equals (S1 • K1 • S1 • K1) • K1 • iI
    by left lemma-5'b
  equals (K1 • S1 ^ 3) • K1 • iI
    by general-assoc auto
  equals K1 • S1 ^ 3 • K1 • iI


lemma-SKSc : Rel ⊢ S2 • K2 • S2 === K2 • S2 ^ 3 • K2 • iI
lemma-SKSc =
  equational S2 • K2 • S2
    by Order.general-rewrite 222 auto
  equals (S2 • K2 • S2 • K2) • K2 • iI
    by left lemma-5'c
  equals (K2 • S2 ^ 3) • K2 • iI
    by general-assoc auto
  equals K2 • S2 ^ 3 • K2 • iI



lemma-15 : Rel ⊢ K0 • S0 • K0 • CS01 • CS01 === S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S0 • K0 • S1 • S1
lemma-15 =
  equational K0 • S0 • K0  • CS01 • CS01
    by general-assoc auto
  equals (K0 • S0 • K0) • CS01 • CS01
    by left lemma-10
  equals (S0 ^ 3 • K0 • S0 ^ 3) • CS01 • CS01
    by general-comm auto
  equals S0 • (S0 • S0 • K0 • CS01 • CS01) • S0 ^ 3
    by right left lemma-14
  equals S0 • (K0 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • iI) • S0 ^ 3
    by Order.general-rewrite 100 auto
  equals (S0 • K0 • CS01 • CS01 • K0 • S0 • S0) • (K0 • S0 ^ 3) • S1 • S1 • iI
    by right left symm lemma-5'
  equals (S0 • K0 • CS01 • CS01 • K0 • S0 • S0) • (S0 • K0 • S0 • K0) • S1 • S1 • iI
    by general-assoc auto
  equals (S0 • K0 • CS01 • CS01 • K0) • (S0 ^ 3 • K0) • S0 • K0 • S1 • S1 • iI
    by right left symm lemma-5
  equals (S0 • K0 • CS01 • CS01 • K0) • (K0 • S0 • K0 • S0) • S0 • K0 • S1 • S1 • iI
    by Order.general-rewrite 100 auto
  equals S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S0 • K0 • S1 • S1



lemma-15b : Rel ⊢ K1 • S1 • K1 • CS12 • CS12 === S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S1 • K1 • S2 • S2
lemma-15b =
  equational K1 • S1 • K1  • CS12 • CS12
    by general-assoc auto
  equals (K1 • S1 • K1) • CS12 • CS12
    by left lemma-K1-S1-K1=S1^3-K1-S1^3
  equals (S1 ^ 3 • K1 • S1 ^ 3) • CS12 • CS12
    by general-comm auto
  equals S1 • (S1 • S1 • K1 • CS12 • CS12) • S1 ^ 3
    by right left lemma-14c
  equals S1 • (K1 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • iI) • S1 ^ 3
    by Order.general-rewrite 211 auto
  equals (S1 • K1 • CS12 • CS12 • K1 • S1 • S1) • (K1 • S1 ^ 3) • S2 • S2 • iI
    by right left symm lemma-5'b
  equals (S1 • K1 • CS12 • CS12 • K1 • S1 • S1) • (S1 • K1 • S1 • K1) • S2 • S2 • iI
    by general-assoc auto
  equals (S1 • K1 • CS12 • CS12 • K1) • (S1 ^ 3 • K1) • S1 • K1 • S2 • S2 • iI
    by right left symm lemma-5b
  equals (S1 • K1 • CS12 • CS12 • K1) • (K1 • S1 • K1 • S1) • S1 • K1 • S2 • S2 • iI
    by Order.general-rewrite 211 auto
  equals S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S1 • K1 • S2 • S2



lemma-13a : Rel ⊢ K0 • CS01 • CS01 • K0 • CS01 • CS01 === CS01 • CS01 • S1 • S1 • K0 • CS01 • CS01 • K0
lemma-13a =
  equational K0 • CS01 • CS01 • K0 • CS01 • CS01
    by general-assoc auto
  equals (K0 • CS01 • CS01 • K0 • CS01) • CS01
    by left lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0
  equals (S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • CS01
    by general-assoc auto
  equals S1 • CS01 • CS01 • CS01 • (K0 • CS01 • CS01 • K0 • CS01)
    by right right right right lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0
  equals S1 • CS01 • CS01 • CS01 • (S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0)
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • S1 • S1 • K0 • CS01 • CS01 • K0


lemma-23ac : Rel ⊢ K1 • CS12 • CS12 • K1 • CS12 • CS12 === CS12 • CS12 • S2 • S2 • K1 • CS12 • CS12 • K1
lemma-23ac =
  equational K1 • CS12 • CS12 • K1 • CS12 • CS12
    by general-assoc auto
  equals (K1 • CS12 • CS12 • K1 • CS12) • CS12
    by left lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals (S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • CS12
    by general-assoc auto
  equals S2 • CS12 • CS12 • CS12 • (K1 • CS12 • CS12 • K1 • CS12)
    by right right right right lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals S2 • CS12 • CS12 • CS12 • (S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1)
    by Order.general-rewrite 211 auto
  equals CS12 • CS12 • S2 • S2 • K1 • CS12 • CS12 • K1


lemma-13b : Rel ⊢ CS01 • CS01 • K0 • CS01 • CS01 • K0 === K0 • CS01 • CS01 • K0 • CS01 • CS01 • S1 • S1 
lemma-13b =
  equational CS01 • CS01 • K0 • CS01 • CS01 • K0
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • S1 • S1 • K0 • CS01 • CS01 • K0) • S1 • S1
    by left lemma-13a reversed
  equals (K0 • CS01 • CS01 • K0 • CS01 • CS01) • S1 • S1
    by general-assoc auto
  equals K0 • CS01 • CS01 • K0 • CS01 • CS01 • S1 • S1 



lemma-13c : Rel ⊢ CS12 • CS12 • K1 • CS12 • CS12 • K1 === K1 • CS12 • CS12 • K1 • CS12 • CS12 • S2 • S2 
lemma-13c =
  equational CS12 • CS12 • K1 • CS12 • CS12 • K1
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • S2 • S2 • K1 • CS12 • CS12 • K1) • S2 • S2
    by left symm lemma-23ac
  equals (K1 • CS12 • CS12 • K1 • CS12 • CS12) • S2 • S2
    by general-assoc auto
  equals K1 • CS12 • CS12 • K1 • CS12 • CS12 • S2 • S2 


lemma-13-K1-a : Rel ⊢ K1 • CS01 • CS01 • K1 • CS01 • CS01 === CS01 • CS01 • S0 • S0 • K1 • CS01 • CS01 • K1
lemma-13-K1-a =
  equational K1 • CS01 • CS01 • K1 • CS01 • CS01
    by general-assoc auto
  equals (K1 • CS01 • CS01 • K1 • CS01) • CS01
    by left lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals (S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • CS01
    by general-assoc auto
  equals S0 • CS01 • CS01 • CS01 • (K1 • CS01 • CS01 • K1 • CS01)
    by right right right right lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals S0 • CS01 • CS01 • CS01 • (S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1)
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • S0 • S0 • K1 • CS01 • CS01 • K1

lemma-13-K2-a : Rel ⊢ K2 • CS12 • CS12 • K2 • CS12 • CS12 === CS12 • CS12 • S1 • S1 • K2 • CS12 • CS12 • K2
lemma-13-K2-a =
  equational K2 • CS12 • CS12 • K2 • CS12 • CS12
    by general-assoc auto
  equals (K2 • CS12 • CS12 • K2 • CS12) • CS12
    by left lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals (S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • CS12
    by general-assoc auto
  equals S1 • CS12 • CS12 • CS12 • (K2 • CS12 • CS12 • K2 • CS12)
    by right right right right lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals S1 • CS12 • CS12 • CS12 • (S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2)
    by Order.general-rewrite 101 auto
  equals CS12 • CS12 • S1 • S1 • K2 • CS12 • CS12 • K2


lemma-13-K1-b : Rel ⊢ CS01 • CS01 • K1 • CS01 • CS01 • K1 === K1 • CS01 • CS01 • K1 • CS01 • CS01 • S0 • S0 
lemma-13-K1-b =
  equational CS01 • CS01 • K1 • CS01 • CS01 • K1
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • S0 • S0 • K1 • CS01 • CS01 • K1) • S0 • S0
    by left lemma-13-K1-a reversed
  equals (K1 • CS01 • CS01 • K1 • CS01 • CS01) • S0 • S0
    by general-assoc auto
  equals K1 • CS01 • CS01 • K1 • CS01 • CS01 • S0 • S0 


lemma-13-K2-b : Rel ⊢ CS12 • CS12 • K2 • CS12 • CS12 • K2 === K2 • CS12 • CS12 • K2 • CS12 • CS12 • S1 • S1 
lemma-13-K2-b =
  equational CS12 • CS12 • K2 • CS12 • CS12 • K2
    by Order.general-rewrite 101 auto
  equals (CS12 • CS12 • S1 • S1 • K2 • CS12 • CS12 • K2) • S1 • S1
    by left lemma-13-K2-a reversed
  equals (K2 • CS12 • CS12 • K2 • CS12 • CS12) • S1 • S1
    by general-assoc auto
  equals K2 • CS12 • CS12 • K2 • CS12 • CS12 • S1 • S1 


lemma-S0-CX10 : Rel ⊢ S0 • K0 • CS01 • CS01 • K0 === K0 • CS01 • CS01 • K0 • S0 • S1 • CS01 • CS01
lemma-S0-CX10 =
  equational S0 • K0 • CS01 • CS01 • K0
    by Order.general-rewrite 100 auto
  equals (S0 • S1) • (K0 • CS01 • CS01 • K0 • CS01 • CS01 • S1 • S1) • S1 • CS01 • CS01
    by right left lemma-13b reversed
  equals (S0 • S1) • (CS01 • CS01 • K0 • CS01 • CS01 • K0) • S1 • CS01 • CS01
    by general-comm auto
  equals (S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • S1 • CS01 • CS01
    by left symm (lemma-K0-CS01-CS01-K0-S0=S1-S0-CS01-CS01-K0-CS01-CS01-K0)
  equals (K0 • CS01 • CS01 • K0 • S0) • S1 • CS01 • CS01
    by general-comm auto
  equals K0 • CS01 • CS01 • K0 • S0 • S1 • CS01 • CS01






lemma-S1-CX21 : Rel ⊢ S1 • K1 • CS12 • CS12 • K1 === K1 • CS12 • CS12 • K1 • S1 • S2 • CS12 • CS12
lemma-S1-CX21 =
  equational S1 • K1 • CS12 • CS12 • K1
    by Order.general-rewrite 211 auto
  equals (S1 • S2) • (K1 • CS12 • CS12 • K1 • CS12 • CS12 • S2 • S2) • S2 • CS12 • CS12
    by right left lemma-13c reversed
  equals (S1 • S2) • (CS12 • CS12 • K1 • CS12 • CS12 • K1) • S2 • CS12 • CS12
    by general-comm auto
  equals (S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • S2 • CS12 • CS12
    by left symm (lemma-K1-CS12-CS12-K1-S1=S2-S1-CS12-CS12-K1-CS12-CS12-K1)
  equals (K1 • CS12 • CS12 • K1 • S1) • S2 • CS12 • CS12
    by general-comm auto
  equals K1 • CS12 • CS12 • K1 • S1 • S2 • CS12 • CS12

lemma-S1-CX21' : Rel ⊢ S1 • CX21 === CX21 • S1 • S2 • CS12 • CS12
lemma-S1-CX21' =
  equational S1 • CX21
    by Order.general-rewrite 211 auto
  equals (S1 • K1 • CS12 • CS12 • K1) • iI
    by left lemma-S1-CX21
  equals (K1 • CS12 • CS12 • K1 • S1 • S2 • CS12 • CS12) • iI
    by Order.general-rewrite 211 auto
  equals CX21 • S1 • S2 • CS12 • CS12


lemma-S1-S1-CX21 : Rel ⊢ S1 • S1 • CX21 === CX21 • S1 • S1 • S2 • S2
lemma-S1-S1-CX21 =
  equational S1 • S1 • CX21
    by right lemma-S1-CX21'
  equals S1 • CX21 • S1 • S2 • CS12 • CS12
    by general-assoc auto
  equals (S1 • CX21) • S1 • S2 • CS12 • CS12
    by left lemma-S1-CX21'
  equals (CX21 • S1 • S2 • CS12 • CS12) • S1 • S2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals CX21 • S1 • S1 • S2 • S2



lemma-S1-CX01 : Rel ⊢ S1 • K1 • CS01 • CS01 • K1 === K1 • CS01 • CS01 • K1 • S0 • S1 • CS01 • CS01
lemma-S1-CX01 =
  equational S1 • K1 • CS01 • CS01 • K1
    by Order.general-rewrite 100 auto
  equals (S0 • S1) • (K1 • CS01 • CS01 • K1 • CS01 • CS01 • S0 • S0) • S0 • CS01 • CS01
    by right left lemma-13-K1-b reversed
  equals (S0 • S1) • (CS01 • CS01 • K1 • CS01 • CS01 • K1) • S0 • CS01 • CS01
    by general-assoc auto
  equals (S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • S0 • CS01 • CS01
    by left symm (lemma-K1-CS01-CS01-K1-S1=S0-S1-CS01-CS01-K1-CS01-CS01-K1)
  equals (K1 • CS01 • CS01 • K1 • S1) • S0 • CS01 • CS01
    by general-comm auto
  equals K1 • CS01 • CS01 • K1 • S0 • S1 • CS01 • CS01


 
lemma-S2-CX12 : Rel ⊢ S2 • K2 • CS12 • CS12 • K2 === K2 • CS12 • CS12 • K2 • S1 • S2 • CS12 • CS12
lemma-S2-CX12 =
  equational S2 • K2 • CS12 • CS12 • K2
    by Order.general-rewrite 101 auto
  equals (S1 • S2) • (K2 • CS12 • CS12 • K2 • CS12 • CS12 • S1 • S1 ) • S1 • CS12 • CS12
    by right left lemma-13-K2-b reversed
  equals (S1 • S2) • (CS12 • CS12 • K2 • CS12 • CS12 • K2) • S1 • CS12 • CS12
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • S1 • CS12 • CS12
    by left symm (lemma-K2-CS12-CS12-K2-S2=S1-S2-CS12-CS12-K2-CS12-CS12-K2)
  equals (K2 • CS12 • CS12 • K2 • S2) • S1 • CS12 • CS12
    by general-comm auto
  equals K2 • CS12 • CS12 • K2 • S1 • S2 • CS12 • CS12


lemma-S2-CX12' : Rel ⊢ S2 • CX12 === CX12 • S2 • S1 • CS12 • CS12
lemma-S2-CX12' =
  equational S2 • CX12
    by Order.general-rewrite 211 auto
  equals (S2 • K2 • CS12 • CS12 • K2) • iI
    by left lemma-S2-CX12
  equals (K2 • CS12 • CS12 • K2 • S1 • S2 • CS12 • CS12) • iI
    by Order.general-rewrite 211 auto
  equals CX12 • S2 • S1 • CS12 • CS12





lemma-13 : Rel ⊢ CS01 • CS01 • K0 • CS01 • CS01 === S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S1
lemma-13 =
  equational CS01 • CS01 • K0 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K0 • CS01 • CS01 • K0) • K0 • iI
    by left lemma-13b
  equals (K0 • CS01 • CS01 • K0 • CS01 • CS01 • S1 • S1) • K0 • iI
    by Order.general-rewrite 100 auto
  equals (K0 • CS01 • CS01 • K0 • S0 • S1 • CS01 • CS01) • S0 ^ 3 • K0 • iI • S1
    by left symm lemma-S0-CX10
  equals (S0 • K0 • CS01 • CS01 • K0) • S0 ^ 3 • K0 • iI • S1
    by general-assoc auto
  equals (S0 • K0 • CS01 • CS01) • (K0 • S0 ^ 3 • K0 • iI) • S1
    by right left symm lemma-SKS
  equals (S0 • K0 • CS01 • CS01) • (S0 • K0 • S0) • S1
    by general-assoc auto
  equals S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S1

lemma-13-K1 : Rel ⊢ CS01 • CS01 • K1 • CS01 • CS01 === S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S0
lemma-13-K1 =
  equational CS01 • CS01 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K1 • CS01 • CS01 • K1) • K1 • iI
    by left lemma-13-K1-b
  equals (K1 • CS01 • CS01 • K1 • CS01 • CS01 • S0 • S0) • K1 • iI
    by Order.general-rewrite 100 auto
  equals (K1 • CS01 • CS01 • K1 • S0 • S1 • CS01 • CS01) • S1 ^ 3 • K1 • iI • S0
    by left lemma-S1-CX01 reversed
  equals (S1 • K1 • CS01 • CS01 • K1) • S1 ^ 3 • K1 • iI • S0
    by general-assoc auto
  equals (S1 • K1 • CS01 • CS01) • (K1 • S1 ^ 3 • K1 • iI) • S0
    by right left symm lemma-SKSb
  equals (S1 • K1 • CS01 • CS01) • (S1 • K1 • S1) • S0
    by general-assoc auto
  equals S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S0


lemma-13-K2 : Rel ⊢ CS12 • CS12 • K2 • CS12 • CS12 === S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S1
lemma-13-K2 =
  equational CS12 • CS12 • K2 • CS12 • CS12
    by Order.general-rewrite 101 auto
  equals (CS12 • CS12 • K2 • CS12 • CS12 • K2) • K2 • iI
    by left lemma-13-K2-b
  equals (K2 • CS12 • CS12 • K2 • CS12 • CS12 • S1 • S1) • K2 • iI
    by Order.general-rewrite 101 auto
  equals (K2 • CS12 • CS12 • K2 • S1 • S2 • CS12 • CS12) • S2 ^ 3 • K2 • iI • S1
    by left lemma-S2-CX12 reversed
  equals (S2 • K2 • CS12 • CS12 • K2) • S2 ^ 3 • K2 • iI • S1
    by general-assoc auto
  equals (S2 • K2 • CS12 • CS12) • (K2 • S2 ^ 3 • K2 • iI) • S1
    by right left symm lemma-SKSc
  equals (S2 • K2 • CS12 • CS12) • (S2 • K2 • S2) • S1
    by general-assoc auto
  equals S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S1


lemma-13-K1-c : Rel ⊢ CS12 • CS12 • K1 • CS12 • CS12 === S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2
lemma-13-K1-c =
  equational CS12 • CS12 • K1 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • K1 • CS12 • CS12 • K1) • K1 • iI
    by left lemma-13c
  equals (K1 • CS12 • CS12 • K1 • CS12 • CS12 • S2 • S2) • K1 • iI
    by Order.general-rewrite 211 auto
  equals (K1 • CS12 • CS12 • K1 • S1 • S2 • CS12 • CS12) • S1 ^ 3 • K1 • iI • S2
    by left symm lemma-S1-CX21
  equals (S1 • K1 • CS12 • CS12 • K1) • S1 ^ 3 • K1 • iI • S2
    by general-assoc auto
  equals (S1 • K1 • CS12 • CS12) • (K1 • S1 ^ 3 • K1 • iI) • S2
    by right left symm lemma-SKSb
  equals (S1 • K1 • CS12 • CS12) • (S1 • K1 • S1) • S2
    by general-assoc auto
  equals S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2




lemma-16 : Rel ⊢ S0 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 === K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • S1 • K1 • iI
lemma-16 =
  equational S0 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals S0 • K0 • (CS01 • CS01 • K0 • CS01 • CS01) • CS01 • CS01 • K1 • CS01 • CS01
    by right right left lemma-13
  equals S0 • K0 • (S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S1) • CS01 • CS01 • K1 • CS01 • CS01
    by general-assoc auto
  equals (S0 • K0 • S0 • K0) • CS01 • CS01 • S0 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by left lemma-5'
  equals (K0 • S0 ^ 3) • CS01 • CS01 • S0 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (K0 • CS01 • CS01 • K0 • S0 • S1) • CS01 • CS01 • K1 • CS01 • CS01
    by right lemma-13-K1
  equals (K0 • CS01 • CS01 • K0 • S0 • S1) • S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S0
    by general-assoc auto
  equals (K0 • CS01 • CS01 • K0 • S0) • (S1 • S1 • K1 • CS01 • CS01) • S1 • K1 • S1 • S0
    by right left lemma-14b
  equals (K0 • CS01 • CS01 • K0 • S0) • (K1 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • iI) • S1 • K1 • S1 • S0
    by Order.general-rewrite 100 auto
  equals (K0 • CS01 • CS01 • K0) • (K1 • CS01 • CS01 • K1 • S1 • S1) • (K1 • S1 • K1 • S1) • iI
    by right right left lemma-5b
  equals (K0 • CS01 • CS01 • K0) • (K1 • CS01 • CS01 • K1 • S1 • S1) • (S1 ^ 3 • K1) • iI
    by Order.general-rewrite 100 auto
  equals K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • S1 • K1 • iI




lemma-16b : Rel ⊢ S1 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 === K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • S2 • K2 • iI
lemma-16b =
  equational S1 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals S1 • K1 • (CS12 • CS12 • K1 • CS12 • CS12) • CS12 • CS12 • K2 • CS12 • CS12
    by right right left lemma-13-K1-c
  equals S1 • K1 • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2) • CS12 • CS12 • K2 • CS12 • CS12
    by general-assoc auto
  equals (S1 • K1 • S1 • K1) • CS12 • CS12 • S1 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by left lemma-5'b
  equals (K1 • S1 ^ 3) • CS12 • CS12 • S1 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (K1 • CS12 • CS12 • K1 • S1 • S2) • CS12 • CS12 • K2 • CS12 • CS12
    by right lemma-13-K2
  equals (K1 • CS12 • CS12 • K1 • S1 • S2) • S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S1
    by general-assoc auto
  equals (K1 • CS12 • CS12 • K1 • S1) • (S2 • S2 • K2 • CS12 • CS12) • S2 • K2 • S2 • S1
    by right left lemma-14d
  equals (K1 • CS12 • CS12 • K1 • S1) • (K2 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • iI) • S2 • K2 • S2 • S1
    by Order.general-rewrite 211 auto
  equals (K1 • CS12 • CS12 • K1) • (K2 • CS12 • CS12 • K2 • S2 • S2) • (K2 • S2 • K2 • S2) • iI
    by right right left lemma-5c
  equals (K1 • CS12 • CS12 • K1) • (K2 • CS12 • CS12 • K2 • S2 • S2) • (S2 ^ 3 • K2) • iI
    by Order.general-rewrite 211 auto
  equals K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • S2 • K2 • iI



lemma-17 : Rel ⊢ K0 • CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01 === CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • S1 • K1 • S1 • iI
lemma-17 =
  equational K0 • CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals K0 • S0 • (CS01 • CS01 • K0 • CS01 • CS01) • CS01 • CS01 • K1 • CS01 • CS01
    by right right left lemma-13
  equals K0 • S0 • (S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S1) • CS01 • CS01 • K1 • CS01 • CS01
    by general-assoc auto
  equals (K0 • S0 • S0 • K0 • CS01 • CS01) • S0 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by left lemma-C8
  equals (CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1) • S0 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by general-comm auto
  equals (CS01 • CS01 • K0 • S0) • (S0 • K0 • S0 • K0) • S0 • S1 • S1 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by right left lemma-4
  equals (CS01 • CS01 • K0 • S0) • (K0 • S0 ^ 3) • S0 • S1 • S1 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K0 • S0 • K0 • S1 • S1 • S1) • CS01 • CS01 • K1 • CS01 • CS01
    by right lemma-13-K1
  equals (CS01 • CS01 • K0 • S0 • K0 • S1 • S1 • S1) • S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S0
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K0 • S0 • K0 • K1) • CS01 • CS01 • S1 • K1 • S1 • S0
    by general-comm auto
  equals (CS01 • CS01 • K1) • (K0 • S0 • K0 • CS01 • CS01) • S1 • K1 • S1 • S0
    by right left lemma-15
  equals (CS01 • CS01 • K1) • (S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S0 • K0 • S1 • S1) • S1 • K1 • S1 • S0
    by general-comm auto
  equals (CS01 • CS01 • K1 • S0 • K0 • CS01 • CS01) • S0 • (K0 • S0 • S0 • K0 • S0) • S1 • S1 • S1 • K1 • S1
    by right right left lemma-K0-S0-S0-K0-S0=S0-S0-S0-K0-S0-S0-K0-iI
  equals (CS01 • CS01 • K1 • S0 • K0 • CS01 • CS01) • S0 • (S0 • S0 • S0 • K0 • S0 • S0 • K0 • iI) • S1 • S1 • S1 • K1 • S1
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K1 • S0 • K0 • CS01 • CS01) • (K0 • S0 • S0 • K0 • iI) • S1 • S1 • S1 • K1 • S1
    by general-comm auto
  equals CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • S1 • K1 • S1 • iI





lemma-17b : Rel ⊢ K1 • CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12 === CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • S2 • K2 • S2 • iI
lemma-17b =
  equational K1 • CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals K1 • S1 • (CS12 • CS12 • K1 • CS12 • CS12) • CS12 • CS12 • K2 • CS12 • CS12
    by right right left lemma-13-K1-c
  equals K1 • S1 • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2) • CS12 • CS12 • K2 • CS12 • CS12
    by general-assoc auto
  equals (K1 • S1 • S1 • K1 • CS12 • CS12) • S1 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by left lemma-C8b
  equals (CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2) • S1 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by general-comm auto
  equals (CS12 • CS12 • K1 • S1) • (S1 • K1 • S1 • K1) • S1 • S2 • S2 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by right left lemma-4b
  equals (CS12 • CS12 • K1 • S1) • (K1 • S1 ^ 3) • S1 • S2 • S2 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • K1 • S1 • K1 • S2 • S2 • S2) • CS12 • CS12 • K2 • CS12 • CS12
    by right lemma-13-K2
  equals (CS12 • CS12 • K1 • S1 • K1 • S2 • S2 • S2) • S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S1
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • K1 • S1 • K1 • K2) • CS12 • CS12 • S2 • K2 • S2 • S1
    by general-comm auto
  equals (CS12 • CS12 • K2) • (K1 • S1 • K1 • CS12 • CS12) • S2 • K2 • S2 • S1
    by right left lemma-15b
  equals (CS12 • CS12 • K2) • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S1 • K1 • S2 • S2) • S2 • K2 • S2 • S1
    by general-comm auto
  equals (CS12 • CS12 • K2 • S1 • K1 • CS12 • CS12) • S1 • (K1 • S1 • S1 • K1 • S1) • S2 • S2 • S2 • K2 • S2
    by right right left lemma-K1-S1-S1-K1-S1=S1-S1-S1-K1-S1-S1-K1-iI
  equals (CS12 • CS12 • K2 • S1 • K1 • CS12 • CS12) • S1 • (S1 • S1 • S1 • K1 • S1 • S1 • K1 • iI) • S2 • S2 • S2 • K2 • S2
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • K2 • S1 • K1 • CS12 • CS12) • (K1 • S1 • S1 • K1 • iI) • S2 • S2 • S2 • K2 • S2
    by general-comm auto
  equals CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • S2 • K2 • S2 • iI



lemma-7 : Rel ⊢ S0 • K0 • S0 • S0 • K0 • S0 === K0 • S0 • S0 • K0 • iI
lemma-7 =
  equational S0 • K0 • S0 • S0 • K0 • S0
    by right lemma-K0-S0-S0-K0-S0=S0-S0-S0-K0-S0-S0-K0-iI
  equals S0 • S0 • S0 • S0 • K0 • S0 • S0 • K0 • iI
    by Order.general-rewrite 100 auto
  equals K0 • S0 • S0 • K0 • iI


lemma-7b : Rel ⊢ S1 • K1 • S1 • S1 • K1 • S1 === K1 • S1 • S1 • K1 • iI
lemma-7b =
  equational S1 • K1 • S1 • S1 • K1 • S1
    by right lemma-K1-S1-S1-K1-S1=S1-S1-S1-K1-S1-S1-K1-iI
  equals S1 • S1 • S1 • S1 • K1 • S1 • S1 • K1 • iI
    by Order.general-rewrite 111 auto
  equals K1 • S1 • S1 • K1 • iI

lemma-Swap01-K1=K0-Swap01' : Rel ⊢ CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 === K0 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01
lemma-Swap01-K1=K0-Swap01' = symm (
  equational  K0 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (K0 • CS01 • CS01 • K1 • K0) • (CS01 • CS01 • K0 • CS01 • CS01) • CS01 • CS01 • K1 • CS01 • CS01
    by right left lemma-13
  equals (K0 • CS01 • CS01 • K1 • K0) • (S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S1) • CS01 • CS01 • K1 • CS01 • CS01
    by general-assoc auto
  equals (K0 • CS01 • CS01 • K1) • (K0 • S0 • K0 • CS01 • CS01) • S0 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by right left lemma-15
  equals (K0 • CS01 • CS01 • K1) • (S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S0 • K0 • S1 • S1) • S0 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by general-comm auto
  equals (K0 • CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01) • S0 • K0 • S0 • S0 • K0 • S1 • S1 • S0 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by left lemma-17
  equals (CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • S1 • K1 • S1 • iI) • S0 • K0 • S0 • S0 • K0 • S1 • S1 • S0 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by general-comm auto
  equals (CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • S1 • K1 • S1 • iI) • (S0 • K0 • S0 • S0 • K0 • S0) • S1 • S1 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by right left lemma-7
  equals (CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • S1 • K1 • S1 • iI) • (K0 • S0 • S0 • K0 • iI) • S1 • S1 • K0 • S0 • S1 • CS01 • CS01 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • S0 • K0 • K1 • CS01 • CS01 • K0 • S1 • S1 • S1 • K1) • S0 • CS01 • CS01 • K1 • CS01 • CS01
    by general-comm auto
  equals (CS01 • CS01 • K1 • S1 • S1 • S1) • (S0 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01) • S0 • K1 • CS01 • CS01
    by right left lemma-16
  equals (CS01 • CS01 • K1 • S1 • S1 • S1) • (K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • S1 • K1 • iI) • S0 • K1 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K1 • S1 • S1 • S1 • K0 • CS01 • CS01 • K0 • K1) • (CS01 • CS01 • K1 • CS01 • CS01) • S1 • S0 
    by right left lemma-13-K1
  equals (CS01 • CS01 • K1 • S1 • S1 • S1 • K0 • CS01 • CS01 • K0 • K1) • (S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S0) • S1 • S0 
    by general-comm auto
  equals (CS01 • CS01 • K1 • S1 • S1 • S1 • K0 • CS01 • CS01 • K0) • (K1 • S1 • K1 • S1) • CS01 • CS01 • K1 • S1 • S0 • S1 • S0 
    by right left lemma-5b
  equals (CS01 • CS01 • K1 • S1 • S1 • S1 • K0 • CS01 • CS01 • K0) • (S1 ^ 3 • K1) • CS01 • CS01 • K1 • S1 • S0 • S1 • S0 
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0) • (S1 • S1 • K1 • CS01 • CS01) • K1 • S1 • S0 • S1 • S0 
    by right left lemma-14b
  equals (CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0) • (K1 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • iI) • K1 • S1 • S0 • S1 • S0 
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1)




lemma-Swap12-K2=K1-Swap12' : Rel ⊢ CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 === K1 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12
lemma-Swap12-K2=K1-Swap12' = symm (
  equational  K1 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (K1 • CS12 • CS12 • K2 • K1) • (CS12 • CS12 • K1 • CS12 • CS12) • CS12 • CS12 • K2 • CS12 • CS12
    by right left lemma-13-K1-c
  equals (K1 • CS12 • CS12 • K2 • K1) • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2) • CS12 • CS12 • K2 • CS12 • CS12
    by general-assoc auto
  equals (K1 • CS12 • CS12 • K2) • (K1 • S1 • K1 • CS12 • CS12) • S1 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by right left lemma-15b
  equals (K1 • CS12 • CS12 • K2) • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S1 • K1 • S2 • S2) • S1 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by general-comm auto
  equals (K1 • CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12) • S1 • K1 • S1 • S1 • K1 • S2 • S2 • S1 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by left lemma-17b
  equals (CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • S2 • K2 • S2 • iI) • S1 • K1 • S1 • S1 • K1 • S2 • S2 • S1 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by general-comm auto
  equals (CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • S2 • K2 • S2 • iI) • (S1 • K1 • S1 • S1 • K1 • S1) • S2 • S2 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by right left lemma-7b
  equals (CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • S2 • K2 • S2 • iI) • (K1 • S1 • S1 • K1 • iI) • S2 • S2 • K1 • S1 • S2 • CS12 • CS12 • K2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • S1 • K1 • K2 • CS12 • CS12 • K1 • S2 • S2 • S2 • K2) • S1 • CS12 • CS12 • K2 • CS12 • CS12
    by general-comm auto
  equals (CS12 • CS12 • K2 • S2 • S2 • S2) • (S1 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12) • S1 • K2 • CS12 • CS12
    by right left lemma-16b
  equals (CS12 • CS12 • K2 • S2 • S2 • S2) • (K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • S2 • K2 • iI) • S1 • K2 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • K2 • S2 • S2 • S2 • K1 • CS12 • CS12 • K1 • K2) • (CS12 • CS12 • K2 • CS12 • CS12) • S2 • S1 
    by right left lemma-13-K2
  equals (CS12 • CS12 • K2 • S2 • S2 • S2 • K1 • CS12 • CS12 • K1 • K2) • (S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S1) • S2 • S1 
    by general-comm auto
  equals (CS12 • CS12 • K2 • S2 • S2 • S2 • K1 • CS12 • CS12 • K1) • (K2 • S2 • K2 • S2) • CS12 • CS12 • K2 • S2 • S1 • S2 • S1 
    by right left lemma-5c
  equals (CS12 • CS12 • K2 • S2 • S2 • S2 • K1 • CS12 • CS12 • K1) • (S2 ^ 3 • K2) • CS12 • CS12 • K2 • S2 • S1 • S2 • S1 
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1) • (S2 • S2 • K2 • CS12 • CS12) • K2 • S2 • S1 • S2 • S1 
    by right left lemma-14d
  equals (CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1) • (K2 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • iI) • K2 • S2 • S1 • S2 • S1 
    by Order.general-rewrite 211 auto
  equals CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2)






lemma-Swap01-K1=K0-Swap01 : Rel ⊢ Swap01 • K1 === K0 • Swap01
lemma-Swap01-K1=K0-Swap01 =
  equational Swap01 • K1
    by general-comm auto
  equals K1 • (CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1) • K1 • iI ^ 3
    by right left lemma-Swap01-K1=K0-Swap01'
  equals K1 • (K0 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01) • K1 • iI ^ 3
    by general-comm auto
  equals K0 • Swap01

hypB1 : Rel ⊢ K1 === Swap01 • K0 • Swap01
hypB1 =
  equational K1
    by Order.general-rewrite 100 auto
  equals Swap01 • Swap01 • K1
    by right lemma-Swap01-K1=K0-Swap01
  equals Swap01 • K0 • Swap01


lemma-Swap12-K2=K1-Swap12 : Rel ⊢ Swap12 • K2 === K1 • Swap12
lemma-Swap12-K2=K1-Swap12 =
  equational Swap12 • K2
    by general-comm auto
  equals K2 • (CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2) • K2 • iI ^ 3
    by right left lemma-Swap12-K2=K1-Swap12'
  equals K2 • (K1 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12) • K2 • iI ^ 3
    by general-comm auto
  equals K1 • Swap12



hypB2 : Rel ⊢ K2 === Swap12 • Swap01 • K0 • Swap01 • Swap12
hypB2 =
  equational K2
    by Order.general-rewrite 100 auto
  equals Swap12 • Swap12 • K2
    by right lemma-Swap12-K2=K1-Swap12
  equals Swap12 • (K1) • Swap12
    by right left hypB1
  equals Swap12 • (Swap01 • K0 • Swap01) • Swap12
    by general-assoc auto
  equals Swap12 • Swap01 • K0 • Swap01 • Swap12


hypB3 : Rel ⊢ Swap01 • K0 • Swap01 • K0 === K0 • Swap01 • K0 • Swap01
hypB3 =
  equational Swap01 • K0 • Swap01 • K0
    by general-assoc auto
  equals (Swap01 • K0 • Swap01) • K0
    by left hypB1 reversed
  equals K1 • K0
    by axiom ax-K1-K0=K0-K1
  equals K0 • K1
    by right hypB1
  equals K0 • Swap01 • K0 • Swap01


lemma-X0-CS01=S1-CS01-CS01-CS01-X0 : Rel ⊢ X0 • CS01 === S1 • CS01 • CS01 • CS01 • X0
lemma-X0-CS01=S1-CS01-CS01-CS01-X0 =
  equational X0 • CS01
    by axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
  equals CS01 • CS01 • CS01 • X0 • S1
    by general-comm auto
  equals S1 • CS01 • CS01 • CS01 • X0


lemma-CX21-CZ12 : Rel ⊢ CX21 • CS12 • CS12 === CS12 • CS12 • S2 • S2 • CX21
lemma-CX21-CZ12 =
  equational CX21 • CS12 • CS12
    by general-comm auto
  equals ((K1 • CS12 • CS12 • K1 • CS12) • CS12) • iI
    by left left lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals ((S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • CS12) • iI
    by general-assoc auto
  equals (S2 • CS12 • CS12 • CS12) • (K1 • CS12 • CS12 • K1 • CS12) • iI
    by right left lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals (S2 • CS12 • CS12 • CS12) • (S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • iI
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • S2 • S2 • CX21


lemma-CX12-CZ12 : Rel ⊢ CX12 • CS12 • CS12 === CS12 • CS12 • S1 • S1 • CX12
lemma-CX12-CZ12 =
  equational CX12 • CS12 • CS12
    by general-comm auto
  equals ((K2 • CS12 • CS12 • K2 • CS12) • CS12) • iI
    by left left lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals ((S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • CS12) • iI
    by general-assoc auto
  equals (S1 • CS12 • CS12 • CS12) • (K2 • CS12 • CS12 • K2 • CS12) • iI
    by right left lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals (S1 • CS12 • CS12 • CS12) • (S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2) • iI
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • S1 • S1 • CX12


lemma-CX12-CX21-CZ12 : Rel ⊢ CX12 • CX21 • CS12 • CS12 === CS12 • CS12 • CX12 • CX21 • S1 • S1
lemma-CX12-CX21-CZ12 =
  equational CX12 • CX21 • CS12 • CS12
    by right lemma-CX21-CZ12
  equals CX12 • CS12 • CS12 • S2 • S2 • CX21
    by general-assoc auto
  equals (CX12 • CS12 • CS12) • S2 • S2 • CX21
    by left lemma-CX12-CZ12
  equals (CS12 • CS12 • S1 • S1 • CX12) • S2 • S2 • CX21
    by general-comm auto
  equals (CS12 • CS12 • CX12) • S1 • (S1 • K1 • CS12 • CS12 • K1) • iI • S2 • S2
    by right right left lemma-S1-CX21
   equals (CS12 • CS12 • CX12) • S1 • (K1 • CS12 • CS12 • K1 • S1 • S2 • CS12 • CS12) • iI • S2 • S2
    by general-assoc auto
   equals (CS12 • CS12 • CX12) • (S1 • K1 • CS12 • CS12 • K1) • (S1 • S2 • CS12 • CS12) • iI • S2 • S2
    by right left lemma-S1-CX21
   equals (CS12 • CS12 • CX12) • (K1 • CS12 • CS12 • K1 • S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • iI • S2 • S2
    by Order.general-rewrite 100 auto
   equals (CS12 • CS12 • CX12) • (CX21 • S1 • S1 )
    by general-assoc auto
  equals CS12 • CS12 • CX12 • CX21 • S1 • S1

lemma-15u : Rel ⊢ K1 • S1 • K1 • CS01 • CS01 === S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S1 • K1 • S0 • S0
lemma-15u =
  equational K1 • S1 • K1  • CS01 • CS01
    by general-assoc auto
  equals (K1 • S1 • K1) • CS01 • CS01
    by left lemma-K1-S1-K1=S1^3-K1-S1^3
  equals (S1 ^ 3 • K1 • S1 ^ 3) • CS01 • CS01
    by general-comm auto
  equals S1 • (S1 • S1 • K1 • CS01 • CS01) • S1 ^ 3
    by right left lemma-14b
  equals S1 • (K1 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • iI) • S1 ^ 3
    by Order.general-rewrite 011 auto
  equals (S1 • K1 • CS01 • CS01 • K1 • S1 • S1) • (K1 • S1 ^ 3) • S0 • S0 • iI
    by right left symm lemma-5'b
  equals (S1 • K1 • CS01 • CS01 • K1 • S1 • S1) • (S1 • K1 • S1 • K1) • S0 • S0 • iI
    by general-assoc auto
  equals (S1 • K1 • CS01 • CS01 • K1) • (S1 ^ 3 • K1) • S1 • K1 • S0 • S0 • iI
    by right left symm lemma-5b
  equals (S1 • K1 • CS01 • CS01 • K1) • (K1 • S1 • K1 • S1) • S1 • K1 • S0 • S0 • iI
    by Order.general-rewrite 101 auto
  equals S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S1 • K1 • S0 • S0



lemma-C8u : Rel ⊢ K1 • S1 • S1 • K1 • CS01 • CS01 === CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0
lemma-C8u =
  equational K1 • S1 • S1 • K1 • CS01 • CS01
    by right lemma-14b
  equals K1 • K1 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • iI
    by Order.general-rewrite 011 auto
  equals CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0




lemma-17u : Rel ⊢ K1 • CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01 === CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • S0 • K0 • S0 • iI
lemma-17u =
  equational K1 • CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01
    by Order.general-rewrite 011 auto
  equals K1 • S1 • (CS01 • CS01 • K1 • CS01 • CS01) • CS01 • CS01 • K0 • CS01 • CS01
    by right right left lemma-13-K1
  equals K1 • S1 • (S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S0) • CS01 • CS01 • K0 • CS01 • CS01
    by general-assoc auto
  equals (K1 • S1 • S1 • K1 • CS01 • CS01) • S1 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by left lemma-C8u
  equals (CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0) • S1 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by general-comm auto
  equals (CS01 • CS01 • K1 • S1) • (S1 • K1 • S1 • K1) • S1 • S0 • S0 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by right left lemma-4b
  equals (CS01 • CS01 • K1 • S1) • (K1 • S1 ^ 3) • S1 • S0 • S0 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by Order.general-rewrite 011 auto
  equals (CS01 • CS01 • K1 • S1 • K1 • S0 • S0 • S0) • CS01 • CS01 • K0 • CS01 • CS01
    by right lemma-13
  equals (CS01 • CS01 • K1 • S1 • K1 • S0 • S0 • S0) • S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S1
    by Order.general-rewrite 011 auto
  equals (CS01 • CS01 • K1 • S1 • K1 • K0) • CS01 • CS01 • S0 • K0 • S0 • S1
    by general-comm auto
  equals (CS01 • CS01 • K0) • (K1 • S1 • K1 • CS01 • CS01) • S0 • K0 • S0 • S1
    by right left lemma-15u
  equals (CS01 • CS01 • K0) • (S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S1 • K1 • S0 • S0) • S0 • K0 • S0 • S1
    by general-comm auto
  equals (CS01 • CS01 • K0 • S1 • K1 • CS01 • CS01) • S1 • (K1 • S1 • S1 • K1 • S1) • S0 • S0 • S0 • K0 • S0
    by right right left lemma-K1-S1-S1-K1-S1=S1-S1-S1-K1-S1-S1-K1-iI
  equals (CS01 • CS01 • K0 • S1 • K1 • CS01 • CS01) • S1 • (S1 • S1 • S1 • K1 • S1 • S1 • K1 • iI) • S0 • S0 • S0 • K0 • S0
    by Order.general-rewrite 011 auto
  equals (CS01 • CS01 • K0 • S1 • K1 • CS01 • CS01) • (K1 • S1 • S1 • K1 • iI) • S0 • S0 • S0 • K0 • S0
    by general-comm auto
  equals CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • S0 • K0 • S0 • iI



lemma-16u : Rel ⊢ S1 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 === K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • S0 • K0 • iI
lemma-16u =
  equational S1 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01
    by Order.general-rewrite 011 auto
  equals S1 • K1 • (CS01 • CS01 • K1 • CS01 • CS01) • CS01 • CS01 • K0 • CS01 • CS01
    by right right left lemma-13-K1
  equals S1 • K1 • (S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S0) • CS01 • CS01 • K0 • CS01 • CS01
    by general-assoc auto
  equals (S1 • K1 • S1 • K1) • CS01 • CS01 • S1 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by left lemma-5'b
  equals (K1 • S1 ^ 3) • CS01 • CS01 • S1 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by Order.general-rewrite 011 auto
  equals (K1 • CS01 • CS01 • K1 • S1 • S0) • CS01 • CS01 • K0 • CS01 • CS01
    by right lemma-13
  equals (K1 • CS01 • CS01 • K1 • S1 • S0) • S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S1
    by general-assoc auto
  equals (K1 • CS01 • CS01 • K1 • S1) • (S0 • S0 • K0 • CS01 • CS01) • S0 • K0 • S0 • S1
    by right left lemma-14
  equals (K1 • CS01 • CS01 • K1 • S1) • (K0 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • iI) • S0 • K0 • S0 • S1
    by Order.general-rewrite 011 auto
  equals (K1 • CS01 • CS01 • K1) • (K0 • CS01 • CS01 • K0 • S0 • S0) • (K0 • S0 • K0 • S0) • iI
    by right right left lemma-5
  equals (K1 • CS01 • CS01 • K1) • (K0 • CS01 • CS01 • K0 • S0 • S0) • (S0 ^ 3 • K0) • iI
    by Order.general-rewrite 011 auto
  equals K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • S0 • K0 • iI



lemma-16ut : Rel ⊢ S2 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12 === K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • S1 • K1 • iI
lemma-16ut =
  equational S2 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12
    by Order.general-rewrite 122 auto
  equals S2 • K2 • (CS12 • CS12 • K2 • CS12 • CS12) • CS12 • CS12 • K1 • CS12 • CS12
    by right right left lemma-13-K2
  equals S2 • K2 • (S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S1) • CS12 • CS12 • K1 • CS12 • CS12
    by general-assoc auto
  equals (S2 • K2 • S2 • K2) • CS12 • CS12 • S2 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by left lemma-5'c
  equals (K2 • S2 ^ 3) • CS12 • CS12 • S2 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by Order.general-rewrite 122 auto
  equals (K2 • CS12 • CS12 • K2 • S2 • S1) • CS12 • CS12 • K1 • CS12 • CS12
    by right lemma-13-K1-c
  equals (K2 • CS12 • CS12 • K2 • S2 • S1) • S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2
    by general-assoc auto
  equals (K2 • CS12 • CS12 • K2 • S2) • (S1 • S1 • K1 • CS12 • CS12) • S1 • K1 • S1 • S2
    by right left lemma-14c
  equals (K2 • CS12 • CS12 • K2 • S2) • (K1 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • iI) • S1 • K1 • S1 • S2
    by Order.general-rewrite 122 auto
  equals (K2 • CS12 • CS12 • K2) • (K1 • CS12 • CS12 • K1 • S1 • S1) • (K1 • S1 • K1 • S1) • iI
    by right right left lemma-5b
  equals (K2 • CS12 • CS12 • K2) • (K1 • CS12 • CS12 • K1 • S1 • S1) • (S1 ^ 3 • K1) • iI
    by Order.general-rewrite 122 auto
  equals K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • S1 • K1 • iI



lemma-Swap01-K0=K1-Swap01'-u : Rel ⊢ CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 === K1 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01
lemma-Swap01-K0=K1-Swap01'-u = symm (
  equational  K1 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (K1 • CS01 • CS01 • K0 • K1) • (CS01 • CS01 • K1 • CS01 • CS01) • CS01 • CS01 • K0 • CS01 • CS01
    by right left lemma-13-K1
  equals (K1 • CS01 • CS01 • K0 • K1) • (S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S0) • CS01 • CS01 • K0 • CS01 • CS01
    by general-assoc auto
  equals (K1 • CS01 • CS01 • K0) • (K1 • S1 • K1 • CS01 • CS01) • S1 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by right left lemma-15u
  equals (K1 • CS01 • CS01 • K0) • (S1 • K1 • CS01 • CS01 • S1 • K1 • S1 • S1 • K1 • S0 • S0) • S1 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by general-comm auto
  equals (K1 • CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01) • S1 • K1 • S1 • S1 • K1 • S0 • S0 • S1 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by left lemma-17u
  equals (CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • S0 • K0 • S0 • iI) • S1 • K1 • S1 • S1 • K1 • S0 • S0 • S1 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by general-comm auto
  equals (CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • S0 • K0 • S0 • iI) • (S1 • K1 • S1 • S1 • K1 • S1) • S0 • S0 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by right left lemma-7b
  equals (CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01 • K1 • S1 • S1 • K1 • S0 • S0 • S0 • K0 • S0 • iI) • (K1 • S1 • S1 • K1 • iI) • S0 • S0 • K1 • S1 • S0 • CS01 • CS01 • K0 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • S1 • K1 • K0 • CS01 • CS01 • K1 • S0 • S0 • S0 • K0) • S1 • CS01 • CS01 • K0 • CS01 • CS01
    by general-comm auto
  equals (CS01 • CS01 • K0 • S0 • S0 • S0) • (S1 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01) • S1 • K0 • CS01 • CS01
    by right left lemma-16u
  equals (CS01 • CS01 • K0 • S0 • S0 • S0) • (K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • S0 • K0 • iI) • S1 • K0 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K0 • S0 • S0 • S0 • K1 • CS01 • CS01 • K1 • K0) • (CS01 • CS01 • K0 • CS01 • CS01) • S0 • S1 
    by right left lemma-13
  equals (CS01 • CS01 • K0 • S0 • S0 • S0 • K1 • CS01 • CS01 • K1 • K0) • (S0 • K0 • CS01 • CS01 • S0 • K0 • S0 • S1) • S0 • S1 
    by general-comm auto
  equals (CS01 • CS01 • K0 • S0 • S0 • S0 • K1 • CS01 • CS01 • K1) • (K0 • S0 • K0 • S0) • CS01 • CS01 • K0 • S0 • S1 • S0 • S1 
    by right left lemma-5
  equals (CS01 • CS01 • K0 • S0 • S0 • S0 • K1 • CS01 • CS01 • K1) • (S0 ^ 3 • K0) • CS01 • CS01 • K0 • S0 • S1 • S0 • S1 
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1) • (S0 • S0 • K0 • CS01 • CS01) • K0 • S0 • S1 • S0 • S1 
    by right left lemma-14
  equals (CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1) • (K0 • CS01 • CS01 • K0 • S0 • S0 • K0 • S1 • S1 • iI) • K0 • S0 • S1 • S0 • S1 
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0)


lemma-Swap-alt-def : Rel ⊢ CX01 • CX10 • CX01 === CX10 • CX01 • CX10
lemma-Swap-alt-def =
  equational CX01 • CX10 • CX01
    by Order.general-rewrite 100 auto
  equals K1 • (CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1) • iI ^ 3
    by right left lemma-Swap01-K1=K0-Swap01'
  equals K1 • (K0 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01) • iI ^ 3
    by general-comm auto
  equals K0 • (K1 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01) • iI ^ 3
    by right left symm lemma-Swap01-K0=K1-Swap01'-u
  equals K0 • (CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0) • iI ^ 3
    by Order.general-rewrite 100 auto
  equals CX10 • CX01 • CX10



lemma-7t : Rel ⊢ S2 • K2 • S2 • S2 • K2 • S2 === K2 • S2 • S2 • K2 • iI
lemma-7t =
  equational S2 • K2 • S2 • S2 • K2 • S2
    by right lemma-K2-S2-S2-K2-S2=S2-S2-S2-K2-S2-S2-K2-iI
  equals S2 • S2 • S2 • S2 • K2 • S2 • S2 • K2 • iI
    by Order.general-rewrite 222 auto
  equals K2 • S2 • S2 • K2 • iI


lemma-15bu : Rel ⊢ K2 • S2 • K2 • CS12 • CS12 === S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S2 • K2 • S1 • S1
lemma-15bu =
  equational K2 • S2 • K2  • CS12 • CS12
    by general-assoc auto
  equals (K2 • S2 • K2) • CS12 • CS12
    by left lemma-10c
  equals (S2 ^ 3 • K2 • S2 ^ 3) • CS12 • CS12
    by general-comm auto
  equals S2 • (S2 • S2 • K2 • CS12 • CS12) • S2 ^ 3
    by right left lemma-14d
  equals S2 • (K2 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • iI) • S2 ^ 3
    by Order.general-rewrite 122 auto
  equals (S2 • K2 • CS12 • CS12 • K2 • S2 • S2) • (K2 • S2 ^ 3) • S1 • S1 • iI
    by right left symm lemma-5'c
  equals (S2 • K2 • CS12 • CS12 • K2 • S2 • S2) • (S2 • K2 • S2 • K2) • S1 • S1 • iI
    by general-assoc auto
  equals (S2 • K2 • CS12 • CS12 • K2) • (S2 ^ 3 • K2) • S2 • K2 • S1 • S1 • iI
    by right left symm lemma-5c
  equals (S2 • K2 • CS12 • CS12 • K2) • (K2 • S2 • K2 • S2) • S2 • K2 • S1 • S1 • iI
    by Order.general-rewrite 122 auto
  equals S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S2 • K2 • S1 • S1

lemma-C8bu : Rel ⊢ K2 • S2 • S2 • K2 • CS12 • CS12 === CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1
lemma-C8bu =
  equational K2 • S2 • S2 • K2 • CS12 • CS12
    by right lemma-14d
  equals K2 • K2 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • iI
    by Order.general-rewrite 122 auto
  equals CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1


lemma-17bu : Rel ⊢ K2 • CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12 === CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • S1 • K1 • S1 • iI
lemma-17bu =
  equational K2 • CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12
    by Order.general-rewrite 122 auto
  equals K2 • S2 • (CS12 • CS12 • K2 • CS12 • CS12) • CS12 • CS12 • K1 • CS12 • CS12
    by right right left lemma-13-K2
  equals K2 • S2 • (S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S1) • CS12 • CS12 • K1 • CS12 • CS12
    by general-assoc auto
  equals (K2 • S2 • S2 • K2 • CS12 • CS12) • S2 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by left lemma-C8bu
  equals (CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1) • S2 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by general-comm auto
  equals (CS12 • CS12 • K2 • S2) • (S2 • K2 • S2 • K2) • S2 • S1 • S1 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by right left lemma-4c
  equals (CS12 • CS12 • K2 • S2) • (K2 • S2 ^ 3) • S2 • S1 • S1 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by Order.general-rewrite 122 auto
  equals (CS12 • CS12 • K2 • S2 • K2 • S1 • S1 • S1) • CS12 • CS12 • K1 • CS12 • CS12
    by right lemma-13-K1-c
  equals (CS12 • CS12 • K2 • S2 • K2 • S1 • S1 • S1) • S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2
    by Order.general-rewrite 122 auto
  equals (CS12 • CS12 • K2 • S2 • K2 • K1) • CS12 • CS12 • S1 • K1 • S1 • S2
    by general-comm auto
  equals (CS12 • CS12 • K1) • (K2 • S2 • K2 • CS12 • CS12) • S1 • K1 • S1 • S2
    by right left lemma-15bu
  equals (CS12 • CS12 • K1) • (S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S2 • K2 • S1 • S1) • S1 • K1 • S1 • S2
    by general-comm auto
  equals (CS12 • CS12 • K1 • S2 • K2 • CS12 • CS12) • S2 • (K2 • S2 • S2 • K2 • S2) • S1 • S1 • S1 • K1 • S1
    by right right left lemma-K2-S2-S2-K2-S2=S2-S2-S2-K2-S2-S2-K2-iI
  equals (CS12 • CS12 • K1 • S2 • K2 • CS12 • CS12) • S2 • (S2 • S2 • S2 • K2 • S2 • S2 • K2 • iI) • S1 • S1 • S1 • K1 • S1
    by Order.general-rewrite 122 auto
  equals (CS12 • CS12 • K1 • S2 • K2 • CS12 • CS12) • (K2 • S2 • S2 • K2 • iI) • S1 • S1 • S1 • K1 • S1
    by general-comm auto
  equals CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • S1 • K1 • S1 • iI

lemma-Swap12-K1=K2-Swap12' : Rel ⊢ CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 === K2 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12
lemma-Swap12-K1=K2-Swap12' = symm (
  equational  K2 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (K2 • CS12 • CS12 • K1 • K2) • (CS12 • CS12 • K2 • CS12 • CS12) • CS12 • CS12 • K1 • CS12 • CS12
    by right left lemma-13-K2
  equals (K2 • CS12 • CS12 • K1 • K2) • (S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S1) • CS12 • CS12 • K1 • CS12 • CS12
    by general-assoc auto
  equals (K2 • CS12 • CS12 • K1) • (K2 • S2 • K2 • CS12 • CS12) • S2 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by right left lemma-15bu
  equals (K2 • CS12 • CS12 • K1) • (S2 • K2 • CS12 • CS12 • S2 • K2 • S2 • S2 • K2 • S1 • S1) • S2 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by general-comm auto
  equals (K2 • CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12) • S2 • K2 • S2 • S2 • K2 • S1 • S1 • S2 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by left lemma-17bu
  equals (CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • S1 • K1 • S1 • iI) • S2 • K2 • S2 • S2 • K2 • S1 • S1 • S2 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by general-comm auto
  equals (CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • S1 • K1 • S1 • iI) • (S2 • K2 • S2 • S2 • K2 • S2) • S1 • S1 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by right left lemma-7t
  equals (CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12 • K2 • S2 • S2 • K2 • S1 • S1 • S1 • K1 • S1 • iI) • (K2 • S2 • S2 • K2 • iI) • S1 • S1 • K2 • S2 • S1 • CS12 • CS12 • K1 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • S2 • K2 • K1 • CS12 • CS12 • K2 • S1 • S1 • S1 • K1) • S2 • CS12 • CS12 • K1 • CS12 • CS12
    by general-comm auto
  equals (CS12 • CS12 • K1 • S1 • S1 • S1) • (S2 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12) • S2 • K1 • CS12 • CS12
    by right left lemma-16ut
  equals (CS12 • CS12 • K1 • S1 • S1 • S1) • (K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • S1 • K1 • iI) • S2 • K1 • CS12 • CS12
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • K1 • S1 • S1 • S1 • K2 • CS12 • CS12 • K2 • K1) • (CS12 • CS12 • K1 • CS12 • CS12) • S1 • S2 
    by right left lemma-13-K1-c
  equals (CS12 • CS12 • K1 • S1 • S1 • S1 • K2 • CS12 • CS12 • K2 • K1) • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2) • S1 • S2 
    by general-comm auto
  equals (CS12 • CS12 • K1 • S1 • S1 • S1 • K2 • CS12 • CS12 • K2) • (K1 • S1 • K1 • S1) • CS12 • CS12 • K1 • S1 • S2 • S1 • S2 
    by right left lemma-5b
  equals (CS12 • CS12 • K1 • S1 • S1 • S1 • K2 • CS12 • CS12 • K2) • (S1 ^ 3 • K1) • CS12 • CS12 • K1 • S1 • S2 • S1 • S2 
    by Order.general-rewrite 211 auto
  equals (CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2) • (S1 • S1 • K1 • CS12 • CS12) • K1 • S1 • S2 • S1 • S2 
    by right left lemma-14c
  equals (CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2) • (K1 • CS12 • CS12 • K1 • S1 • S1 • K1 • S2 • S2 • iI) • K1 • S1 • S2 • S1 • S2 
    by Order.general-rewrite 211 auto
  equals CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1)

lemma-Swap12-alt-def : Rel ⊢ CX12 • CX21 • CX12 === CX21 • CX12 • CX21
lemma-Swap12-alt-def =
  equational CX12 • CX21 • CX12
    by Order.general-rewrite 211 auto
  equals K2 • (CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2) • iI ^ 3
    by right left lemma-Swap12-K2=K1-Swap12'
  equals K2 • (K1 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1 • K2 • CS12 • CS12) • iI ^ 3
    by general-comm auto
  equals K1 • (K2 • CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12) • iI ^ 3
    by right left symm lemma-Swap12-K1=K2-Swap12'
  equals K1 • (CS12 • CS12 • K1 • K2 • CS12 • CS12 • K2 • K1 • CS12 • CS12 • K1) • iI ^ 3
    by Order.general-rewrite 211 auto
  equals CX21 • CX12 • CX21


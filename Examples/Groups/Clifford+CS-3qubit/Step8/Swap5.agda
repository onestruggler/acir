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
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap4

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap5 where


lemma-CS12-CX10-CX01-CS12-CX01-CX10=CX10-CX01-CS12-CX01-CX10-CS12 : Rel ⊢ CS12 • CX10 • CX01 • CS12 • CX01 • CX10 === CX10 • CX01 • CS12 • CX01 • CX10 • CS12
lemma-CS12-CX10-CX01-CS12-CX01-CX10=CX10-CX01-CS12-CX01-CX10-CS12 =
  equational CS12 • CX10 • CX01 • CS12 • CX01 • CX10
    by general-comm auto
  equals CX10 • (CS12 • CX01 • CS12 • CX01) • CX10
    by right left lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12
  equals CX10 • (CX01 • CS12 • CX01 • CS12) • CX10
    by general-comm auto
  equals CX10 • CX01 • CS12 • CX01 • CX10 • CS12


lemma-CX10-CX21=CX21-CX20-CX10 : Rel ⊢ CX10 • CX21 === CX21 • CX20 • CX10
lemma-CX10-CX21=CX21-CX20-CX10 =
  equational CX10 • CX21
    by Order.general-rewrite 100 auto
  equals (CX10 • CX21 • CX10) • CX10
    by left Order.general-rewrite 100 auto
  equals (CX21 • K0 • CX21 • CS01 • CS01 • CX21 • CS01 • CS01 • K0 • iI) • CX10
    by general-assoc auto
  equals (CX21 • K0) • (CX21 • CS01 • CS01 • CX21 • CS01) • CS01 • K0 • iI • CX10
    by right left symm lemma-e1
  equals (CX21 • K0) • (CS01 • CX21 • CS01 • CS01 • CX21) • CS01 • K0 • iI • CX10
    by general-assoc auto
  equals CX21 • K0 • (CS01 • CX21 • CS01 • CS01 • CX21 • CS01) • K0 • iI • CX10
    by right right left lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12
  equals CX21 • K0 • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • K0 • iI • CX10
    by Order.general-rewrite 100 auto
  equals CX21 • (K0 • (Swap12 • CS01 • Swap12) • (Swap12 • CS01 • Swap12) • K0 • iI) • CX10
    by refl
  equals CX21 • CX20 • CX10

lemma-e1e : Rel ⊢ CX12 • CX21 • CS01 • CS01 • CX21 • CX12 === CX21 • CS01 • CS01 • CX21 • CS01 • CS01
lemma-e1e =
  equational CX12 • CX21 • CS01 • CS01 • CX21 • CX12
    by symm (lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12)
  equals CS01 • CX21 • CS01 • CS01 • CX21 • CS01
    by general-assoc auto
  equals (CS01 • CX21 • CS01 • CS01 • CX21) • CS01
    by left lemma-e1
  equals (CX21 • CS01 • CS01 • CX21 • CS01) • CS01
    by general-assoc auto
  equals CX21 • CS01 • CS01 • CX21 • CS01 • CS01

lemma-e1e2 : Rel ⊢ CX12 • CX21 • CS01 • CS01 • CX21 • CX12 === CS01 • CS01 • CX21 • CS01 • CS01 • CX21
lemma-e1e2 =
  equational CX12 • CX21 • CS01 • CS01 • CX21 • CX12
    by symm (lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12)
  equals CS01 • CX21 • CS01 • CS01 • CX21 • CS01
    by general-assoc auto
  equals CS01 • (CX21 • CS01 • CS01 • CX21 • CS01)
    by right symm lemma-e1
  equals CS01 • (CS01 • CX21 • CS01 • CS01 • CX21)
    by general-assoc auto
  equals CS01 • CS01 • CX21 • CS01 • CS01 • CX21

lemma-ee0 : Rel ⊢ Swap01 • CS01 • CS01 === CS01 • CS01 • Swap01
lemma-ee0 =
  equational Swap01 • CS01 • CS01
    by general-assoc auto
  equals (Swap01 • CS01) • CS01
    by left lemma-Swap01-CS01=CS01-Swap01
  equals (CS01 • Swap01) • CS01
    by assoc
  equals CS01 • Swap01 • CS01
    by right lemma-Swap01-CS01=CS01-Swap01
  equals CS01 • CS01 • Swap01

lemma-ee1 : Rel ⊢ CX20 • CS01 • CS01 • CX20 === CS01 • CS01 • CS12 • CS12
lemma-ee1 =
  equational CX20 • CS01 • CS01 • CX20
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CX20) • CS01 • CS01 • CX20
    by right left lemma-Swap01-CX20=CX21-Swap01
  equals Swap01 • (CX21 • Swap01) • CS01 • CS01 • CX20
    by general-assoc auto
  equals (Swap01 • CX21) • (Swap01 • CS01) • CS01 • CX20
    by right left lemma-Swap01-CS01=CS01-Swap01
  equals (Swap01 • CX21) • (CS01 • Swap01) • CS01 • CX20
    by general-assoc auto
  equals (Swap01 • CX21) • CS01 • (Swap01 • CS01) • CX20
    by right right left lemma-Swap01-CS01=CS01-Swap01
  equals (Swap01 • CX21) • CS01 • (CS01 • Swap01) • CX20
    by general-assoc auto
  equals (Swap01 • CX21 • CS01 • CS01) • Swap01 • CX20
    by right lemma-Swap01-CX20=CX21-Swap01
  equals (Swap01 • CX21 • CS01 • CS01) • CX21 • Swap01
    by general-assoc auto
  equals Swap01 • (CX21 • CS01 • CS01 • CX21) • Swap01
    by Order.general-rewrite 100 auto
  equals Swap01 • CX12 • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • CX12 • Swap01
    by right right left lemma-e1e2
  equals Swap01 • CX12 • (CS01 • CS01 • CX21 • CS01 • CS01 • CX21) • CX12 • Swap01
    by general-comm auto
  equals (Swap01 • CS01 • CS01) • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • Swap01
    by left lemma-ee0
  equals (CS01 • CS01 • Swap01) • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • Swap01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01) • (Swap01 • CS02) • CS02 • Swap01
    by right right symm lemma-Swap01-CS12=CS02-Swap01
  equals (CS01 • CS01) • (Swap01 • CS02) • Swap01 • CS12
    by general-assoc auto
  equals (CS01 • CS01) • Swap01 • (CS02 • Swap01) • CS12
    by right right left lemma-Swap01-CS12=CS02-Swap01 reversed
  equals (CS01 • CS01) • Swap01 • (Swap01 • CS12) • CS12
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • CS12 • CS12


lemma-CX20-S1 : Rel ⊢ CX20 • S1 === S1 • CX20
lemma-CX20-S1 =
  equational CX20 • S1
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CX20) • S1
    by right left lemma-Swap01-CX20=CX21-Swap01
  equals Swap01 • (CX21 • Swap01) • S1
    by right assoc
  equals Swap01 • CX21 • (Swap01 • S1)
    by right right lemma-Swap01-S1=S0-Swap01
  equals Swap01 • CX21 • (S0 • Swap01)
    by general-comm auto
  equals (Swap01 • S0) • CX21 • Swap01
    by left lemma-Swap01-S0=S1-Swap01
  equals (S1 • Swap01) • CX21 • Swap01
    by right symm lemma-Swap01-CX20=CX21-Swap01
  equals (S1 • Swap01) • Swap01 • CX20
    by Order.general-rewrite 100 auto
  equals S1 • CX20


lemma-CX20-S1-S1 : Rel ⊢ CX20 • S1 • S1 === S1 • S1 • CX20
lemma-CX20-S1-S1 =
  equational CX20 • S1 • S1
    by symm assoc
  equals (CX20 • S1) • S1
    by left lemma-CX20-S1
  equals (S1 • CX20) • S1
    by assoc
  equals S1 • CX20 • S1
    by right lemma-CX20-S1
  equals S1 • S1 • CX20


lemma-CX20-S2 : Rel ⊢ CX20 • S2 === S2 • CX20
lemma-CX20-S2 =
  equational CX20 • S2
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CX20) • S2
    by right left lemma-Swap01-CX20=CX21-Swap01
  equals Swap01 • (CX21 • Swap01) • S2
    by right assoc
  equals Swap01 • CX21 • (Swap01 • S2)
    by right right lemma-Swap01-S2=S2-Swap01
  equals Swap01 • CX21 • (S2 • Swap01)
    by general-comm auto
  equals (Swap01 • S2) • CX21 • Swap01
    by left lemma-Swap01-S2=S2-Swap01
  equals (S2 • Swap01) • CX21 • Swap01
    by right symm lemma-Swap01-CX20=CX21-Swap01
  equals (S2 • Swap01) • Swap01 • CX20
    by Order.general-rewrite 100 auto
  equals S2 • CX20


lemma-CX20-S2-S2 : Rel ⊢ CX20 • S2 • S2 === S2 • S2 • CX20
lemma-CX20-S2-S2 =
  equational CX20 • S2 • S2
    by symm assoc
  equals (CX20 • S2) • S2
    by left lemma-CX20-S2
  equals (S2 • CX20) • S2
    by assoc
  equals S2 • CX20 • S2
    by right lemma-CX20-S2
  equals S2 • S2 • CX20

lemma-Swap12-CX20=CX10-Swap12 : Rel ⊢ Swap12 • CX20 === CX10 • Swap12
lemma-Swap12-CX20=CX10-Swap12 = Order.general-rewrite 100 auto


lemma-CX20-CX21 : Rel ⊢ CX20 • CX21 === CX21 • CX20
lemma-CX20-CX21 =
  equational CX20 • CX21
    by Order.general-rewrite 100 auto
  equals Swap12 • (Swap12 • CX20) • CX21
    by right left lemma-Swap12-CX20=CX10-Swap12
  equals Swap12 • (CX10 • Swap12) • CX21
    by right assoc
  equals Swap12 • CX10 • (Swap12 • CX21)
    by right right lemma-Swap12-CX21=CX12-Swap12
  equals Swap12 • CX10 • (CX12 • Swap12)
    by general-comm auto
  equals (Swap12 • CX12) • CX10 • Swap12
    by left lemma-Swap12-CX12=CX21-Swap12
  equals (CX21 • Swap12) • CX10 • Swap12
    by right symm lemma-Swap12-CX20=CX10-Swap12
  equals (CX21 • Swap12) • Swap12 • CX20
    by Order.general-rewrite 100 auto
  equals CX21 • CX20

lemma-CX20 : Rel ⊢ CX20 === CX12 • CX21 • CX10 • CX21 • CX12
lemma-CX20 = Order.general-rewrite 100 auto


lemma-eaux1 : Rel ⊢ CX12 • CX21 • CS01 • CS01 • CX12 • CX21 === CS01 • CS01 • CX21 • CX12 • CS01 • CS01
lemma-eaux1 =
  equational CX12 • CX21 • CS01 • CS01 • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals (CX12 • CX21) • (CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21) • CX21 • CX12 • CS01 • CS01 • CX21 • CX12 • CS01 • CS01
    by right left lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε
  equals (CX12 • CX21) • (ε) • CX21 • CX12 • CS01 • CS01 • CX21 • CX12 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • CX21 • CX12 • CS01 • CS01


lemma-eaux2 : Rel ⊢ CX21 • CX12 • CS01 • CS01 • CX21 • CX12 === CS01 • CS01 • CX12 • CX21 • CS01 • CS01
lemma-eaux2 =
  equational CX21 • CX12 • CS01 • CS01 • CX21 • CX12
    by Order.general-rewrite 100 auto
  equals ε • CX21 • CX12 • CS01 • CS01 • CX21 • CX12
    by left symm (lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε)
  equals (CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21) • CX21 • CX12 • CS01 • CS01 • CX21 • CX12
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • CX12 • CX21 • CS01 • CS01


lemma-eee0 : Rel ⊢ CX21 • CX20 • CS01 • CS01 • CX21 • CX20 === CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10
lemma-eee0 =
  equational CX21 • CX20 • CS01 • CS01 • CX21 • CX20
    by right right right right symm lemma-CX20-CX21
  equals CX21 • CX20 • CS01 • CS01 • CX20 • CX21
    by right left lemma-CX20
  equals CX21 • (CX12 • CX21 • CX10 • CX21 • CX12) • CS01 • CS01 • CX20 • CX21
    by right right right right left lemma-CX20
  equals CX21 • (CX12 • CX21 • CX10 • CX21 • CX12) • CS01 • CS01 • (CX12 • CX21 • CX10 • CX21 • CX12) • CX21
    by Order.general-rewrite 100 auto
  equals (CX21 • CX12 • CX21) • (CX10 • CX21 • CS01 • CS01 • CX21 • CX10) • (CX21 • CX12 • CX21)
    by left symm lemma-Swap12-alt-def
  equals (CX12 • CX21 • CX12) • (CX10 • CX21 • CS01 • CS01 • CX21 • CX10) • (CX21 • CX12 • CX21)
    by right right symm lemma-Swap12-alt-def
  equals (CX12 • CX21 • CX12) • (CX10 • CX21 • CS01 • CS01 • CX21 • CX10) • (CX12 • CX21 • CX12)
    by Order.general-rewrite 100 auto
  equals K0 • (CX12 • CX21 • CS01 • CS01 • CX12 • CX21) • K0 • iI • CS01 • CS01 • K0 • (CX21 • CX12 • CS01 • CS01 • CX21 • CX12) • K0 • iI
    by right left lemma-eaux1
  equals K0 • (CS01 • CS01 • CX21 • CX12 • CS01 • CS01) • K0 • iI • CS01 • CS01 • K0 • (CX21 • CX12 • CS01 • CS01 • CX21 • CX12) • K0 • iI
    by general-assoc auto
  equals (K0 • (CS01 • CS01 • CX21 • CX12 • CS01 • CS01) • K0 • iI • CS01 • CS01 • K0) • (CX21 • CX12 • CS01 • CS01 • CX21 • CX12) • K0 • iI
    by right left lemma-eaux2
  equals (K0 • (CS01 • CS01 • CX21 • CX12 • CS01 • CS01) • K0 • iI • CS01 • CS01 • K0) • (CS01 • CS01 • CX12 • CX21 • CS01 • CS01) • K0 • iI
    by Order.general-rewrite 100 auto
  equals (K0 • (CS01 • CS01 • CX21 • CS01 • CS01) • K0 • iI • CS01 • CS01 • K0) • (CS01 • CS01 • CX21 • CS01 • CS01) • K0 • iI
    by Order.general-rewrite 100 auto
  equals CX10 • CX21 • (CX10 • CS01 • CS01) • CX10 • CX21 • CX10
    by right right left lemma-CX10-CS01-CS01
  equals CX10 • CX21 • (S1 • S1 • CS01 • CS01 • CX10) • CX10 • CX21 • CX10
    by Order.general-rewrite 100 auto
  equals CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10

 
lemma-d0e : Rel ⊢ CS01 • CS01 • CS01 • CX21 • CS01 • CS01 • CX21 === CX21 • CS01 • CS01 • CX21 • CS01 • CS01 • CS01
lemma-d0e =
  equational CS01 • CS01 • CS01 • CX21 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CX21 • CS01 • CX21
    by left lemma-d0
  equals (CX21 • CS01 • CX21 • CS01 • CS01 • CS01) • CX21 • CS01 • CX21
    by general-assoc auto
  equals (CX21 • CS01 • CX21) • CS01 • CS01 • CS01 • CX21 • CS01 • CX21
    by right lemma-d0
  equals (CX21 • CS01 • CX21) • CX21 • CS01 • CX21 • CS01 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals CX21 • CS01 • CS01 • CX21 • CS01 • CS01 • CS01


lemma-d01 : Rel ⊢ CX21 • CS01 • CX21 • S1 === S1 • CX21 • CS01 • CX21
lemma-d01 =
  equational CX21 • CS01 • CX21 • S1
    by right right lemma-CX21-S1
  equals CX21 • CS01 • S2 • S1 • CS12 • CS12 • CX21
    by general-comm auto
  equals S2 • (CX21 • S1) • CS01 • CS12 • CS12 • CX21
    by right left lemma-CX21-S1
  equals S2 • (S2 • S1 • CS12 • CS12 • CX21) • CS01 • CS12 • CS12 • CX21
    by general-comm auto
  equals S2 • (S2 • S1 • CS12 • CS12) • (CX21 • CS12 • CS12) • CS01 • CX21
    by right right left lemma-CX21-CS12-CS12
  equals S2 • (S2 • S1 • CS12 • CS12) • (S2 • S2 • CS12 • CS12 • CX21) • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals S1 • CX21 • CS01 • CX21


lemma-d02 : Rel ⊢ CX21 • CS01 • CS01 • CX21 • S1 === S1 • CX21 • CS01 • CS01 • CX21
lemma-d02 =
  equational CX21 • CS01 • CS01 • CX21 • S1
    by right right right lemma-CX21-S1
  equals CX21 • CS01 • CS01 • S2 • S1 • CS12 • CS12 • CX21
    by general-comm auto
  equals S2 • (CX21 • S1) • CS01 • CS01 • CS12 • CS12 • CX21
    by right left lemma-CX21-S1
  equals S2 • (S2 • S1 • CS12 • CS12 • CX21) • CS01 • CS01 • CS12 • CS12 • CX21
    by general-comm auto
  equals S2 • (S2 • S1 • CS12 • CS12) • (CX21 • CS12 • CS12) • CS01 • CS01 • CX21
    by right right left lemma-CX21-CS12-CS12
  equals S2 • (S2 • S1 • CS12 • CS12) • (S2 • S2 • CS12 • CS12 • CX21) • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals S1 • CX21 • CS01 • CS01 • CX21


lemma-d03 : Rel ⊢ CX21 • CS01 • CS01 • CX21 • S1 • S1 • S1 === S1 • S1 • S1 • CX21 • CS01 • CS01 • CX21
lemma-d03 =
  equational CX21 • CS01 • CS01 • CX21 • S1 • S1 • S1
    by general-assoc auto
  equals (CX21 • CS01 • CS01 • CX21 • S1) • S1 • S1
    by left lemma-d02
  equals (S1 • CX21 • CS01 • CS01 • CX21) • S1 • S1
    by general-assoc auto
  equals S1 • (CX21 • CS01 • CS01 • CX21 • S1) • S1
    by right left lemma-d02
  equals S1 • (S1 • CX21 • CS01 • CS01 • CX21) • S1
    by general-assoc auto
  equals S1 • S1 • CX21 • CS01 • CS01 • CX21 • S1
    by right right lemma-d02
  equals S1 • S1 • S1 • CX21 • CS01 • CS01 • CX21



lemma-eee1 : Rel ⊢ CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10 • CS01 === CS01 • CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10
lemma-eee1 =
  equational CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10 • CS01
    by general-assoc auto
  equals (CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21) • CX10 • CS01
    by right lemma-CX10-CS01
  equals (CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21) • S1 • CS01 ^ 3 • CX10
    by general-assoc auto
  equals (CX10 • CX21 • CS01 • CS01) • (S1 • S1 • CX21) • S1 • CS01 ^ 3 • CX10
    by right left lemma-S1-S1-CX21
  equals (CX10 • CX21 • CS01 • CS01) • (CX21 • S1 • S1 • S2 • S2) • S1 • CS01 ^ 3 • CX10
    by general-comm auto
  equals CX10 • (CX21 • CS01 • CS01 • CX21 • CS01 • CS01 • CS01) • (S1 • S1 • S2 • S2) • S1 • CX10
    by right left symm lemma-d0e
  equals CX10 • (CS01 • CS01 • CS01 • CX21 • CS01 • CS01 • CX21) • (S1 • S1 • S2 • S2) • S1 • CX10
    by general-assoc auto
  equals (CX10 • CS01 • CS01 • CS01) • (CX21 • CS01 • CS01 • CX21) • (S1 • S1 • S2 • S2) • S1 • CX10
    by left lemma-CX10-CS01-CS01-CS01 
  equals (S1 • S1 • S1 • CS01 • CX10) • (CX21 • CS01 • CS01 • CX21) • (S1 • S1 • S2 • S2) • S1 • CX10
    by general-comm auto
  equals (S1 • S1 • S1 • CS01 • CX10) • (CX21 • CS01 • CS01 • CX21 • S1 • S1 • S1) • S2 • S2 • CX10
    by right left lemma-d03
  equals (S1 • S1 • S1 • CS01 • CX10) • (S1 • S1 • S1 • CX21 • CS01 • CS01 • CX21) • S2 • S2 • CX10
    by Order.general-rewrite 1000 auto
  equals (CS01 • CX10) • (S1 • S1 • CX21) • (CS01 • CS01 • CX21) • S2 • S2 • CX10
    by right left lemma-S1-S1-CX21
  equals (CS01 • CX10) • (CX21 • S1 • S1 • S2 • S2) • (CS01 • CS01 • CX21) • S2 • S2 • CX10
    by Order.general-rewrite 1000 auto
  equals CS01 • CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10

lemma-ee3 : Rel ⊢ CX21 • CX20 • CS01 • CS01 • CX21 • CX20 • CS01 === CS01 • CX21 • CX20 • CS01 • CS01 • CX21 • CX20
lemma-ee3 =
  equational CX21 • CX20 • CS01 • CS01 • CX21 • CX20 • CS01
    by general-assoc auto
  equals (CX21 • CX20 • CS01 • CS01 • CX21 • CX20) • CS01
    by left lemma-eee0
  equals (CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10) • CS01
    by general-assoc auto
  equals CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10 • CS01
    by lemma-eee1
  equals CS01 • CX10 • CX21 • CS01 • CS01 • S1 • S1 • CX21 • CX10
    by right symm lemma-eee0
  equals CS01 • CX21 • CX20 • CS01 • CS01 • CX21 • CX20

lemma-ee4 : Rel ⊢ CX21 • CX20 • CS01 • CS01 • CX21 • CX20 • CS01 • CS01 === CS01 • CS01 • CX21 • CX20 • CS01 • CS01 • CX21 • CX20
lemma-ee4 =
  equational CX21 • CX20 • CS01 • CS01 • CX21 • CX20 • CS01 • CS01
    by general-assoc auto
  equals (CX21 • CX20 • CS01 • CS01 • CX21 • CX20 • CS01) • CS01
    by left lemma-ee3
  equals (CS01 • CX21 • CX20 • CS01 • CS01 • CX21 • CX20) • CS01
    by general-assoc auto
  equals CS01 • CX21 • CX20 • CS01 • CS01 • CX21 • CX20 • CS01
    by right lemma-ee3
  equals CS01 • CS01 • CX21 • CX20 • CS01 • CS01 • CX21 • CX20



lemma-CX10-CX02=CX02-CX12-CX10 : Rel ⊢ CX10 • CX02 === CX02 • CX12 • CX10
lemma-CX10-CX02=CX02-CX12-CX10 =
  equational CX10 • CX02
    by Order.general-rewrite 100 auto
  equals CX10 • K2 • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • K2 • iI
    by right right left symm (lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12)
  equals CX10 • K2 • (CS01 • CX21 • CS01 • CS01 • CX21 • CS01) • K2 • iI
    by general-assoc auto
  equals CX10 • K2 • (CS01 • CX21 • CS01 • CS01 • CX21) • CS01 • K2 • iI
    by right right left lemma-e1
  equals CX10 • K2 • (CX21 • CS01 • CS01 • CX21 • CS01) • CS01 • K2 • iI
    by general-comm auto
  equals K2 • (CX10 • CX21) • (CS01 • CS01 • CX21 • CS01) • CS01 • K2 • iI
    by right left lemma-CX10-CX21=CX21-CX20-CX10
  equals K2 • (CX21 • CX20 • CX10) • (CS01 • CS01 • CX21 • CS01) • CS01 • K2 • iI
    by general-assoc auto
  equals K2 • (CX21 • CX20) • (CX10 • CS01 • CS01) • (CX21 • CS01) • CS01 • K2 • iI
    by right right left lemma-CX10-CS01-CS01
  equals K2 • (CX21 • CX20) • (S1 • S1 • CS01 • CS01 • CX10) • (CX21 • CS01) • CS01 • K2 • iI
    by general-assoc auto
  equals (K2 • CX21 • CX20 • S1 • S1 • CS01 • CS01) • (CX10 • CX21) • CS01 • CS01 • K2 • iI
    by right left lemma-CX10-CX21=CX21-CX20-CX10
  equals (K2 • CX21 • CX20 • S1 • S1 • CS01 • CS01) • (CX21 • CX20 • CX10) • CS01 • CS01 • K2 • iI
    by general-assoc auto
  equals (K2 • CX21 • CX20 • S1 • S1 • CS01 • CS01) • (CX21 • CX20) • (CX10 • CS01 • CS01) • K2 • iI
    by right right left lemma-CX10-CS01-CS01
  equals (K2 • CX21 • CX20 • S1 • S1 • CS01 • CS01) • (CX21 • CX20) • (S1 • S1 • CS01 • CS01 • CX10) • K2 • iI
    by general-comm auto
  equals (K2 • CX21 • CX20 • S1 • S1 • CS01 • CS01) • CX21 • (CX20 • S1 • S1) • CS01 • CS01 • CX10 • K2 • iI
    by right right left lemma-CX20-S1-S1
  equals (K2 • CX21 • CX20 • S1 • S1 • CS01 • CS01) • CX21 • (S1 • S1 • CX20) • CS01 • CS01 • CX10 • K2 • iI
    by general-comm auto
  equals (K2 • CX21 • CX20 • S1 • S1 • CS01 • CS01) • (CX21 • S1 • S1) • (CX20 • CS01 • CS01 • CX10) • K2 • iI
    by general-comm auto
  equals (K2 • CX21 • CX20 • CS01 • CS01) • (S1 • S1 • CX21) • (S1 • S1) • (CX20 • CS01 • CS01 • CX10) • K2 • iI
    by right left lemma-S1-S1-CX21
  equals (K2 • CX21 • CX20 • CS01 • CS01) • (CX21 • S1 • S1 • S2 • S2) • (S1 • S1) • (CX20 • CS01 • CS01 • CX10) • K2 • iI
    by Order.general-rewrite 100 auto
  equals (K2 • CX21 • CX20 • CS01 • CS01) • (CX21 • S2 • S2) • (CX20 • CS01 • CS01 • CX10) • K2 • iI
    by general-comm auto
  equals (K2 • CX21 • CX20 • CS01 • CS01) • CX21 • (S2 • S2 • CX20) • CS01 • CS01 • CX10 • K2 • iI
    by right right left symm lemma-CX20-S2-S2
  equals (K2 • CX21 • CX20 • CS01 • CS01) • CX21 • (CX20 • S2 • S2) • CS01 • CS01 • CX10 • K2 • iI
    by general-comm auto
  equals K2 • (CX21 • CX20 • CS01 • CS01 • CX21 • CX20 • CS01 • CS01) • S2 • S2 • CX10 • K2 • iI
    by right left lemma-ee4
  equals K2 • (CS01 • CS01 • CX21 • CX20 • CS01 • CS01 • CX21 • CX20) • S2 • S2 • CX10 • K2 • iI
    by general-comm auto
  equals (K2 • CS01 • CS01 • CX21) • (CX20 • CS01 • CS01) • (CX21 • CX20) • S2 • S2 • CX10 • K2 • iI
    by right right left symm lemma-CX20-CX21
  equals (K2 • CS01 • CS01 • CX21) • (CX20 • CS01 • CS01) • (CX20 • CX21) • S2 • S2 • CX10 • K2 • iI
    by general-comm auto
  equals (K2 • CS01 • CS01 • CX21) • (CX20 • CS01 • CS01 • CX20) • CX21 • S2 • S2 • CX10 • K2 • iI
    by right left lemma-ee1
  equals (K2 • CS01 • CS01 • CX21) • (CS01 • CS01 • CS12 • CS12) • CX21 • S2 • S2 • CX10 • K2 • iI
    by general-comm auto
  equals (K2 • CS01 • CS01 • CX21) • (CS01 • CS01) • (CS12 • CS12 • S2 • S2 • CX21) • CX10 • K2 • iI
    by right right left symm lemma-CX21-CZ12
  equals (K2 • CS01 • CS01 • CX21) • (CS01 • CS01) • (CX21 • CS12 • CS12) • CX10 • K2 • iI
    by Order.general-rewrite 100 auto
  equals (K2 • CS01 • CS01 • CX21) • CS01 • CS01 • CX21 • K2 • iI • CX12 • CX10
    by general-comm auto
  equals (K2 • (CS01 • CS01 • CX21 • CS01 • CS01 • CX21) • K2 • iI) • CX12 • CX10
    by left right left symm lemma-e1e2
  equals (K2 • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • K2 • iI) • CX12 • CX10
    by Order.general-rewrite 100 auto
  equals CX02 • CX12 • CX10

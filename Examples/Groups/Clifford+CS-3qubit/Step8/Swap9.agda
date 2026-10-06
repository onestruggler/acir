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
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap5
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap6
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap7
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap8
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap9a

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap9 where

lemma-X2-CCZ : Rel ⊢ X2 • CCZ === CS01 • CS01 • CCZ • X2
lemma-X2-CCZ =
  equational X2 • CCZ
    by Order.general-rewrite 100 auto
  equals (Swap12 • Swap01 • Swap01) • (Swap12 • X2) • CCZ
    by right left MvSwap12.general-rewrite 100 auto
  equals (Swap12 • Swap01 • Swap01) • (X1 • Swap12) • CCZ
    by general-assoc auto
  equals (Swap12 • Swap01) • (Swap01 • X1) • Swap12 • CCZ
    by right left MvSwap01.general-rewrite 100 auto
  equals (Swap12 • Swap01) • (X0 • Swap01) • Swap12 • CCZ
    by right right lemma-Swap12-CCZ=CCZ-Swap12
  equals (Swap12 • Swap01) • (X0 • Swap01) • CCZ • Swap12
    by general-assoc auto
  equals (Swap12 • Swap01) • X0 • (Swap01 • CCZ) • Swap12
    by right right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (Swap12 • Swap01) • X0 • (CCZ • Swap01) • Swap12
    by general-assoc auto
  equals (Swap12 • Swap01) • (X0 • CCZ) • Swap01 • Swap12
    by right left lemma-X-CCZ
  equals (Swap12 • Swap01) • (CS12 • CS12 • CCZ • X0) • Swap01 • Swap12
    by general-assoc auto
  equals (Swap12) • (Swap01 • CS12) • (CS12 • CCZ • X0) • Swap01 • Swap12
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals (Swap12) • (CS02 • Swap01) • (CS12 • CCZ • X0) • Swap01 • Swap12
    by general-assoc auto
  equals (Swap12 • CS02) • (Swap01 • CS12) • (CCZ • X0) • Swap01 • Swap12
    by left lemma-Swap12-CS02=CS01-Swap12
  equals (CS01 • Swap12) • (Swap01 • CS12) • (CCZ • X0) • Swap01 • Swap12
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals (CS01 • Swap12) • (CS02 • Swap01) • (CCZ • X0) • Swap01 • Swap12
    by general-assoc auto
  equals (CS01) • (Swap12 • CS02) • (Swap01 • CCZ) • (X0) • Swap01 • Swap12
    by right (left lemma-Swap12-CS02=CS01-Swap12)
  equals (CS01) • (CS01 • Swap12) • (Swap01 • CCZ) • (X0) • Swap01 • Swap12
    by right right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (CS01) • (CS01 • Swap12) • (CCZ • Swap01) • (X0) • Swap01 • Swap12
    by general-assoc auto
  equals (CS01 • CS01) • (Swap12 • CCZ) • (Swap01 • X0) • Swap01 • Swap12
    by right left lemma-Swap12-CCZ=CCZ-Swap12
  equals (CS01 • CS01) • (CCZ • Swap12) • (Swap01 • X0) • Swap01 • Swap12
    by right right left MvSwap01.general-rewrite 100 auto
  equals (CS01 • CS01) • (CCZ • Swap12) • (X1 • Swap01) • Swap01 • Swap12
    by general-assoc auto
  equals (CS01 • CS01) • CCZ • (Swap12 • X1) • (Swap01) • Swap01 • Swap12
    by right right left MvSwap12.general-rewrite 100 auto
  equals (CS01 • CS01) • CCZ • (X2 • Swap12) • (Swap01) • Swap01 • Swap12
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • CCZ • X2


lemma-X2-CCZ-X2 : Rel ⊢ X2 • CCZ • X2 === CS01 • CS01 • CCZ
lemma-X2-CCZ-X2 =
  equational X2 • CCZ • X2
    by symm assoc
  equals (X2 • CCZ) • X2
    by left lemma-X2-CCZ
  equals (CS01 • CS01 • CCZ • X2) • X2
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • CCZ



lemma-CX10-CCX0-CCX1=CCX1-CX10-CCX0 : Rel ⊢ CX10 • CCX0 • CCX1 === CCX1 • CX10 • CCX0
lemma-CX10-CCX0-CCX1=CCX1-CX10-CCX0 =
  equational CX10 • CCX0 • CCX1
    by Order.general-rewrite 100 auto
  equals (K0 • CS01 • CS01 • CCZ • K0) • CCX1 • iI
    by right left lemma-CK21-CCZ-CK21-S2=CCX1 reversed
  equals (K0 • CS01 • CS01 • CCZ • K0) • (CK21 • CCZ • CK21 • S2) • iI
    by general-comm auto
  equals K0 • (CS01 • CS01 • CCZ • CK21) • (K0 • CCZ • CK21 • S2) • iI
    by right left lemma-CS01-CS01-CCZ-CK21=CK21-CS01-CS01-CCZ
  equals K0 • (CK21 • CS01 • CS01 • CCZ) • (K0 • CCZ • CK21 • S2) • iI
    by general-comm auto
  equals CK21 • K0 • (CS01 • CS01 • CCZ) • (K0 • CCZ • CK21 • S2) • iI
    by right right left lemma-X2-CCZ-X2 reversed
  equals CK21 • K0 • (X2 • CCZ • X2) • (K0 • CCZ • CK21 • S2) • iI
    by general-comm auto
  equals (CK21 • K0 • X2 • CCZ • K0) • (X2 • CCZ) • CK21 • S2 • iI
    by right left lemma-X2-CCZ
  equals (CK21 • K0 • X2 • CCZ • K0) • (CS01 • CS01 • CCZ • X2) • CK21 • S2 • iI
    by Order.general-rewrite 100 auto
  equals (CK21 • X2) • (CCX0 • CS01) • (CS01 • CCZ • X2) • CK21 • S2
    by right left lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0
  equals (CK21 • X2) • (CS01 • CS12 • CCZ • CCX0) • (CS01 • CCZ • X2) • CK21 • S2
    by general-assoc auto
  equals (CK21 • X2) • (CS01 • CS12 • CCZ) • (CCX0 • CS01) • CCZ • X2 • CK21 • S2
    by right right left lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0
  equals (CK21 • X2) • (CS01 • CS12 • CCZ) • (CS01 • CS12 • CCZ • CCX0) • CCZ • X2 • CK21 • S2
    by general-assoc auto
  equals (CK21 • X2) • (CS01 • CS12 • CCZ) • (CS01 • CS12 • CCZ) • (CCX0 • CCZ) • X2 • CK21 • S2
    by right right right left lemma-CCX0-CCZ=CS12-CS12-CCZ-CCX0
  equals (CK21 • X2) • (CS01 • CS12 • CCZ) • (CS01 • CS12 • CCZ) • (CS12 • CS12 • CCZ • CCX0) • X2 • CK21 • S2
    by general-assoc auto
  equals (CK21 • X2 • CS01 • CS12 • CCZ • CS01 • CS12 • CCZ) • CS12 • (CS12 • CCZ) • CCX0 • X2 • CK21 • S2
    by right right left lemma-CCZ-CS12=CS12-CCZ reversed
  equals (CK21 • X2 • CS01 • CS12 • CCZ • CS01 • CS12 • CCZ) • CS12 • (CCZ • CS12) • CCX0 • X2 • CK21 • S2
    by general-assoc auto
  equals (CK21 • X2 • CS01 • CS12 • CCZ • CS01 • CS12 • CCZ) • (CS12 • CCZ) • CS12 • CCX0 • X2 • CK21 • S2
    by right left lemma-CCZ-CS12=CS12-CCZ reversed
  equals (CK21 • X2 • CS01 • CS12 • CCZ • CS01 • CS12 • CCZ) • (CCZ • CS12) • CS12 • CCX0 • X2 • CK21 • S2
    by general-assoc auto
  equals (CK21 • X2 • CS01 • CS12 • CCZ • CS01 • CS12) • (CCZ • CCZ) • CS12 • CS12 • CCX0 • X2 • CK21 • S2
    by right left lemma-CCZ-CCZ=ε
  equals (CK21 • X2 • CS01 • CS12 • CCZ • CS01 • CS12) • (ε) • CS12 • CS12 • CCX0 • X2 • CK21 • S2
    by general-assoc auto
  equals (CK21 • X2 • CS01) • (CS12 • CCZ) • (CS01 • CS12) • (ε) • CS12 • CS12 • CCX0 • X2 • CK21 • S2
    by right left lemma-CCZ-CS12=CS12-CCZ reversed
  equals (CK21 • X2 • CS01) • (CCZ • CS12) • (CS01 • CS12) • (ε) • CS12 • CS12 • CCX0 • X2 • CK21 • S2
    by Order.general-rewrite 100 auto
  equals (CK21 • CS01) • X2 • (CCZ • CS01) • CCX0 • X2 • CK21 • S2
    by right right left lemma-CCZ-CS01=CS01-CCZ
  equals (CK21 • CS01) • X2 • (CS01 • CCZ) • CCX0 • X2 • CK21 • S2
    by general-comm auto
  equals (CK21 • CS01) • CS01 • (X2 • CCZ) • CCX0 • X2 • CK21 • S2
    by right right left lemma-X2-CCZ
  equals (CK21 • CS01) • CS01 • (CS01 • CS01 • CCZ • X2) • CCX0 • X2 • CK21 • S2
    by Order.general-rewrite 100 auto
  equals (CK21 • CCZ) • K0 • (X2 • CCZ • X2) • K0 • iI • CK21 • S2
    by right right left lemma-X2-CCZ-X2
  equals (CK21 • CCZ) • K0 • (CS01 • CS01 • CCZ) • K0 • iI • CK21 • S2
    by general-comm auto
  equals (CK21 • CCZ) • K0 • (CS01 • CS01 • CCZ • CK21) • S2 • K0 • iI
    by right right left lemma-CS01-CS01-CCZ-CK21=CK21-CS01-CS01-CCZ
  equals (CK21 • CCZ) • K0 • (CK21 • CS01 • CS01 • CCZ) • S2 • K0 • iI
    by general-assoc auto
  equals (CK21 • CCZ) • K0 • (CK21 • CS01 • CS01) • (CCZ • S2) • K0 • iI
    by right right right left lemma-CCZ-S2=S2-CCZ
  equals (CK21 • CCZ) • K0 • (CK21 • CS01 • CS01) • (S2 • CCZ) • K0 • iI
    by general-comm auto
  equals (CK21 • CCZ • CK21 • S2) • K0 • CS01 • CS01 • CCZ • K0 • iI
    by left lemma-CK21-CCZ-CK21-S2=CCX1
  equals (CCX1) • K0 • CS01 • CS01 • CCZ • K0 • iI
    by Order.general-rewrite 100 auto
  equals CCX1 • CX10 • CCX0


lemma-CX01-CCX1-CCX0=CCX0-CX01-CCX1 : Rel ⊢ CX01 • CCX1 • CCX0 === CCX0 • CX01 • CCX1
lemma-CX01-CCX1-CCX0=CCX0-CX01-CCX1 =
  equational CX01 • CCX1 • CCX0
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CX01) • CCX1 • CCX0
    by right left lemma-Swap01-CX01=CX10-Swap01
  equals Swap01 • (CX10 • Swap01) • CCX1 • CCX0
    by general-assoc auto
  equals Swap01 • CX10 • (Swap01 • CCX1) • CCX0
    by right right left lemma-Swap01-CCX1=CCX0-Swap01
  equals Swap01 • CX10 • (CCX0 • Swap01) • CCX0
    by general-assoc auto
  equals (Swap01 • CX10 • CCX0) • Swap01 • CCX0
    by right lemma-Swap01-CCX0=CCX1-Swap01
  equals (Swap01 • CX10 • CCX0) • CCX1 • Swap01
    by general-assoc auto
  equals (Swap01) • (CX10 • CCX0 • CCX1) • Swap01
    by right left lemma-CX10-CCX0-CCX1=CCX1-CX10-CCX0
  equals (Swap01) • (CCX1 • CX10 • CCX0) • Swap01
    by general-assoc auto
  equals (Swap01 • CCX1) • (CX10 • CCX0) • Swap01
    by left lemma-Swap01-CCX1=CCX0-Swap01
  equals (CCX0 • Swap01) • (CX10 • CCX0) • Swap01
    by general-assoc auto
  equals (CCX0) • (Swap01 • CX10) • (CCX0) • Swap01
    by right left lemma-Swap01-CX10=CX01-Swap01
  equals (CCX0) • (CX01 • Swap01) • (CCX0) • Swap01
    by general-assoc auto
  equals (CCX0) • (CX01) • (Swap01 • CCX0) • Swap01
    by right right left lemma-Swap01-CCX0=CCX1-Swap01
  equals (CCX0) • (CX01) • (CCX1 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals CCX0 • CX01 • CCX1



lemma-CCX0-K1-CS01-CS01-CCZ-K1=K1-CS01-CS01-CCZ-K1-CCX0 : Rel ⊢ CCX0 • K1 • CS01 • CS01 • CCZ • K1 === K1 • CS01 • CS01 • CCZ • K1 • CCX0
lemma-CCX0-K1-CS01-CS01-CCZ-K1=K1-CS01-CS01-CCZ-K1-CCX0 =
  equational CCX0 • K1 • CS01 • CS01 • CCZ • K1
    by Order.general-rewrite 100 auto
  equals (CCX0 • CX01 • CCX1) • iI ^ 3
    by left lemma-CX01-CCX1-CCX0=CCX0-CX01-CCX1 reversed
  equals (CX01 • CCX1 • CCX0) • iI ^ 3
    by Order.general-rewrite 100 auto
  equals K1 • CS01 • CS01 • CCZ • K1 • CCX0

lemma-K1-CCX0-K1-CS01-CS01-CCZ=CS01-CS01-CCZ-K1-CCX0-K1 : Rel ⊢ K1 • CCX0 • K1 • CS01 • CS01 • CCZ === CS01 • CS01 • CCZ • K1 • CCX0 • K1
lemma-K1-CCX0-K1-CS01-CS01-CCZ=CS01-CS01-CCZ-K1-CCX0-K1 =
  equational K1 • CCX0 • K1 • CS01 • CS01 • CCZ
    by Order.general-rewrite 100 auto
  equals K1 • (CCX0 • K1 • CS01 • CS01 • CCZ • K1) • K1 • iI
    by right left lemma-CCX0-K1-CS01-CS01-CCZ-K1=K1-CS01-CS01-CCZ-K1-CCX0
  equals K1 • (K1 • CS01 • CS01 • CCZ • K1 • CCX0) • K1 • iI
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • CCZ • K1 • CCX0 • K1


lemma-CX01-CCX0-CX01=CCX1-CCX0-CCX1 : Rel ⊢ CX01 • CCX0 • CX01 === CCX1 • CCX0 • CCX1
lemma-CX01-CCX0-CX01=CCX1-CCX0-CCX1 =
  equational CX01 • CCX0 • CX01
    by Order.general-rewrite 100 auto
  equals K1 • CS01 • CS01 • (K1 • CCX0 • K1 • CS01 • CS01) • K1 • iI ^ 2
    by general-assoc auto
  equals (K1 • CS01 • CS01 • K1 • CCX0 • K1 • CS01 • CS01) • ε • K1 • iI ^ 2
    by right left lemma-CCZ-CCZ=ε reversed
  equals (K1 • CS01 • CS01 • K1 • CCX0 • K1 • CS01 • CS01) • (CCZ • CCZ) • K1 • iI ^ 2
    by general-assoc auto
  equals K1 • CS01 • CS01 • (K1 • CCX0 • K1 • CS01 • CS01 • CCZ) • CCZ • K1 • iI ^ 2
    by right right right left lemma-K1-CCX0-K1-CS01-CS01-CCZ=CS01-CS01-CCZ-K1-CCX0-K1
  equals K1 • CS01 • CS01 • (CS01 • CS01 • CCZ • K1 • CCX0 • K1) • CCZ • K1 • iI ^ 2
    by Order.general-rewrite 100 auto
  equals CCX1 • CCX0 • CCX1


lemma-CX10-CCX1-CX10=CCX0-CCX1-CCX0 : Rel ⊢ CX10 • CCX1 • CX10 === CCX0 • CCX1 • CCX0
lemma-CX10-CCX1-CX10=CCX0-CCX1-CCX0 =
  equational CX10 • CCX1 • CX10
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CX10) • CCX1 • CX10
    by right left lemma-Swap01-CX10=CX01-Swap01
  equals Swap01 • (CX01 • Swap01) • CCX1 • CX10
    by general-assoc auto
  equals Swap01 • CX01 • (Swap01 • CCX1) • CX10
    by right right left lemma-Swap01-CCX1=CCX0-Swap01
  equals Swap01 • CX01 • (CCX0 • Swap01) • CX10
    by general-assoc auto
  equals Swap01 • CX01 • CCX0 • (Swap01 • CX10)
    by right right right lemma-Swap01-CX10=CX01-Swap01
  equals Swap01 • CX01 • CCX0 • (CX01 • Swap01)
    by general-assoc auto
  equals Swap01 • (CX01 • CCX0 • CX01) • Swap01
    by right left lemma-CX01-CCX0-CX01=CCX1-CCX0-CCX1
  equals Swap01 • (CCX1 • CCX0 • CCX1) • Swap01
    by general-assoc auto
  equals (Swap01 • CCX1) • CCX0 • CCX1 • Swap01
    by left lemma-Swap01-CCX1=CCX0-Swap01
  equals (CCX0 • Swap01) • CCX0 • CCX1 • Swap01
    by general-assoc auto
  equals CCX0 • (Swap01 • CCX0) • CCX1 • Swap01
    by right left lemma-Swap01-CCX0=CCX1-Swap01
  equals CCX0 • (CCX1 • Swap01) • CCX1 • Swap01
    by general-assoc auto
  equals CCX0 • CCX1 • (Swap01 • CCX1) • Swap01
    by right right left lemma-Swap01-CCX1=CCX0-Swap01
  equals CCX0 • CCX1 • (CCX0 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals CCX0 • CCX1 • CCX0


lemma-CCX1-CX01=CX01-CCX1 : Rel ⊢ CCX1 • CX01 === CX01 • CCX1
lemma-CCX1-CX01=CX01-CCX1 =
  equational CCX1 • CX01
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CCX1) • CX01
    by right left lemma-Swap01-CCX1=CCX0-Swap01
  equals Swap01 • (CCX0 • Swap01) • CX01
    by general-assoc auto
  equals Swap01 • CCX0 • (Swap01 • CX01)
    by right right lemma-Swap01-CX01=CX10-Swap01
  equals Swap01 • CCX0 • (CX10 • Swap01)
    by general-assoc auto
  equals Swap01 • (CCX0 • CX10) • Swap01
    by right left lemma-CCX0-CX10=CX10-CCX0
  equals Swap01 • (CX10 • CCX0) • Swap01
    by general-assoc auto
  equals (Swap01 • CX10) • CCX0 • Swap01
    by left lemma-Swap01-CX10=CX01-Swap01
  equals (CX01 • Swap01) • CCX0 • Swap01
    by general-assoc auto
  equals CX01 • (Swap01 • CCX0) • Swap01
    by right left lemma-Swap01-CCX0=CCX1-Swap01
  equals CX01 • (CCX1 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals CX01 • CCX1


lemma-CCX0-CCX1-CCX0=CCX1-CCX0-CCX1 : Rel ⊢ CCX0 • CCX1 • CCX0 === CCX1 • CCX0 • CCX1
lemma-CCX0-CCX1-CCX0=CCX1-CCX0-CCX1 =
  equational CCX0 • CCX1 • CCX0
    by symm lemma-CX10-CCX1-CX10=CCX0-CCX1-CCX0
  equals CX10 • CCX1 • CX10
    by Order.general-rewrite 100 auto
  equals CX01 • (CX01 • CX10 • CX01) • CX01 • (CCX1 • CX01) • (CX01 • CX10 • CX01) • CX01
    by right right right left lemma-CCX1-CX01=CX01-CCX1
  equals CX01 • (Swap01) • CX01 • (CX01 • CCX1) • (Swap01) • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • (Swap01 • CCX1) • (Swap01) • CX01
    by right left lemma-Swap01-CCX1=CCX0-Swap01
  equals CX01 • (CCX0 • Swap01) • (Swap01) • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • CCX0 • CX01
    by lemma-CX01-CCX0-CX01=CCX1-CCX0-CCX1
  equals CCX1 • CCX0 • CCX1


lemma-CX21-CCX2-CX21=CCX1-CCX2-CCX1 : Rel ⊢ CX21 • CCX2 • CX21 === CCX1 • CCX2 • CCX1
lemma-CX21-CCX2-CX21=CCX1-CCX2-CCX1 =
  equational CX21 • CCX2 • CX21
    by Order.general-rewrite 100 auto
  equals (Swap01 • Swap12 • Swap12) • (Swap01 • CX21) • CCX2 • CX21
    by right left lemma-Swap01-CX21=CX20-Swap01
  equals (Swap01 • Swap12 • Swap12) • (CX20 • Swap01) • CCX2 • CX21
    by general-assoc auto
  equals (Swap01 • Swap12 • Swap12 • CX20) • (Swap01 • CCX2) • CX21
    by right left lemma-Swap01-CCX2=CCX2-Swap01
  equals (Swap01 • Swap12 • Swap12 • CX20) • (CCX2 • Swap01) • CX21
    by general-assoc auto
  equals (Swap01 • Swap12 • Swap12 • CX20 • CCX2) • Swap01 • CX21
    by right lemma-Swap01-CX21=CX20-Swap01
  equals (Swap01 • Swap12 • Swap12 • CX20 • CCX2) • CX20 • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12) • (Swap12 • CX20) • CCX2 • CX20 • Swap01
    by right left lemma-Swap12-CX20=CX10-Swap12
  equals (Swap01 • Swap12) • (CX10 • Swap12) • CCX2 • CX20 • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12 • CX10) • (Swap12 • CCX2) • CX20 • Swap01
    by right left lemma-Swap12-CCX2=CCX1-Swap12
  equals (Swap01 • Swap12 • CX10) • (CCX1 • Swap12) • CX20 • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12 • CX10 • CCX1) • (Swap12 • CX20) • Swap01
    by right left lemma-Swap12-CX20=CX10-Swap12
  equals (Swap01 • Swap12 • CX10 • CCX1) • (CX10 • Swap12) • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12) • (CX10 • CCX1 • CX10) • Swap12 • Swap01
    by right left lemma-CX10-CCX1-CX10=CCX0-CCX1-CCX0
  equals (Swap01 • Swap12) • (CCX0 • CCX1 • CCX0) • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01) • (Swap12 • CCX0) • CCX1 • CCX0 • Swap12 • Swap01
    by right left lemma-Swap12-CCX0=CCX0-Swap12
  equals (Swap01) • (CCX0 • Swap12) • CCX1 • CCX0 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CCX0) • (Swap12 • CCX1) • CCX0 • Swap12 • Swap01
    by right left lemma-Swap12-CCX1=CCX2-Swap12
  equals (Swap01 • CCX0) • (CCX2 • Swap12) • CCX0 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CCX0 • CCX2) • (Swap12 • CCX0) • Swap12 • Swap01
    by right left lemma-Swap12-CCX0=CCX0-Swap12
  equals (Swap01 • CCX0 • CCX2) • (CCX0 • Swap12) • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CCX0) • CCX2 • CCX0 • Swap12 • Swap12 • Swap01
    by left lemma-Swap01-CCX0=CCX1-Swap01
  equals (CCX1 • Swap01) • CCX2 • CCX0 • Swap12 • Swap12 • Swap01
    by general-assoc auto
  equals CCX1 • (Swap01 • CCX2) • CCX0 • Swap12 • Swap12 • Swap01
    by right left lemma-Swap01-CCX2=CCX2-Swap01
  equals CCX1 • (CCX2 • Swap01) • CCX0 • Swap12 • Swap12 • Swap01
    by general-assoc auto
  equals (CCX1 • CCX2) • (Swap01 • CCX0) • Swap12 • Swap12 • Swap01
    by right left lemma-Swap01-CCX0=CCX1-Swap01
  equals (CCX1 • CCX2) • (CCX1 • Swap01) • Swap12 • Swap12 • Swap01
    by Order.general-rewrite 100 auto
  equals CCX1 • CCX2 • CCX1



lemma-CX12-CCX1-CX12=CCX2-CCX1-CCX2 : Rel ⊢ CX12 • CCX1 • CX12 === CCX2 • CCX1 • CCX2
lemma-CX12-CCX1-CX12=CCX2-CCX1-CCX2 =
  equational CX12 • CCX1 • CX12
    by Order.general-rewrite 100 auto
  equals Swap12 • (Swap12 • CX12) • CCX1 • CX12
    by right left lemma-Swap12-CX12=CX21-Swap12
  equals Swap12 • (CX21 • Swap12) • CCX1 • CX12
    by general-assoc auto
  equals (Swap12 • CX21) • (Swap12 • CCX1) • CX12
    by right left lemma-Swap12-CCX1=CCX2-Swap12
  equals (Swap12 • CX21) • (CCX2 • Swap12) • CX12
    by general-assoc auto
  equals (Swap12 • CX21 • CCX2) • Swap12 • CX12
    by right lemma-Swap12-CX12=CX21-Swap12
  equals (Swap12 • CX21 • CCX2) • CX21 • Swap12
    by general-assoc auto
  equals (Swap12) • (CX21 • CCX2 • CX21) • Swap12
    by right left lemma-CX21-CCX2-CX21=CCX1-CCX2-CCX1
  equals (Swap12) • (CCX1 • CCX2 • CCX1) • Swap12
    by general-assoc auto
  equals (Swap12 • CCX1) • CCX2 • CCX1 • Swap12
    by left lemma-Swap12-CCX1=CCX2-Swap12
  equals (CCX2 • Swap12) • CCX2 • CCX1 • Swap12
    by general-assoc auto
  equals (CCX2) • (Swap12 • CCX2) • CCX1 • Swap12
    by right (left lemma-Swap12-CCX2=CCX1-Swap12)
  equals (CCX2) • (CCX1 • Swap12) • CCX1 • Swap12
    by general-assoc auto
  equals (CCX2 • CCX1) • (Swap12 • CCX1) • Swap12
    by right left lemma-Swap12-CCX1=CCX2-Swap12
  equals (CCX2 • CCX1) • (CCX2 • Swap12) • Swap12
    by Order.general-rewrite 100 auto
  equals CCX2 • CCX1 • CCX2




lemma-CCX0-CX12=CX12-CX10-CCX0 : Rel ⊢ CCX0 • CX12 === CX12 • CX10 • CCX0
lemma-CCX0-CX12=CX12-CX10-CCX0 =
  equational CCX0 • CX12
    by Order.general-rewrite 211 auto
  equals (Swap01 • Swap12 • Swap12) • (Swap01 • CCX0) • CX12
    by right left lemma-Swap01-CCX0=CCX1-Swap01
  equals (Swap01 • Swap12 • Swap12) • (CCX1 • Swap01) • CX12
    by general-assoc auto
  equals (Swap01 • Swap12 • Swap12 • CCX1) • Swap01 • CX12
    by right lemma-Swap01-CX12=CX02-Swap01
  equals (Swap01 • Swap12 • Swap12 • CCX1) • CX02 • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12) • (Swap12 • CCX1) • CX02 • Swap01
    by right left lemma-Swap12-CCX1=CCX2-Swap12
  equals (Swap01 • Swap12) • (CCX2 • Swap12) • CX02 • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12 • CCX2) • (Swap12 • CX02) • Swap01
    by right left lemma-Swap12-CX02=CX01-Swap12
  equals (Swap01 • Swap12 • CCX2) • (CX01 • Swap12) • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12) • (CCX2 • CX01) • Swap12 • Swap01
    by right left lemma-CCX2-CX01=CX01-CX02-CCX2
  equals (Swap01 • Swap12) • (CX01 • CX02 • CCX2) • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01) • (Swap12 • CX01) • CX02 • CCX2 • Swap12 • Swap01
    by right left lemma-Swap12-CX01=CX02-Swap12
  equals (Swap01) • (CX02 • Swap12) • CX02 • CCX2 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CX02) • (Swap12 • CX02) • CCX2 • Swap12 • Swap01
    by right left lemma-Swap12-CX02=CX01-Swap12
  equals (Swap01 • CX02) • (CX01 • Swap12) • CCX2 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CX02 • CX01) • (Swap12 • CCX2) • Swap12 • Swap01
    by right left lemma-Swap12-CCX2=CCX1-Swap12
  equals (Swap01 • CX02 • CX01) • (CCX1 • Swap12) • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CX02) • (CX01) • (CCX1 • Swap12) • Swap12 • Swap01
    by left lemma-Swap01-CX02=CX12-Swap01
  equals (CX12 •  Swap01) • (CX01) • (CCX1 • Swap12) • Swap12 • Swap01
    by general-assoc auto
  equals (CX12) •  (Swap01 • CX01) • (CCX1 • Swap12) • Swap12 • Swap01
    by right left lemma-Swap01-CX01=CX10-Swap01
  equals (CX12) •  (CX10 • Swap01) • (CCX1 • Swap12) • Swap12 • Swap01
    by general-assoc auto
  equals (CX12 •  CX10) • (Swap01 • CCX1) • Swap12 • Swap12 • Swap01
    by right left lemma-Swap01-CCX1=CCX0-Swap01
  equals (CX12 •  CX10) • (CCX0 • Swap01) • Swap12 • Swap12 • Swap01
    by Order.general-rewrite 211 auto
  equals CX12 • CX10 • CCX0



lemma-CCX0-CCX2-CCX1-CCX2=CCX2-CCX1-CCX2-CCX0 : Rel ⊢ CCX0 • CCX2 • CCX1 • CCX2 === CCX2 • CCX1 • CCX2 • CCX0
lemma-CCX0-CCX2-CCX1-CCX2=CCX2-CCX1-CCX2-CCX0 =
  equational CCX0 • CCX2 • CCX1 • CCX2
    by right symm lemma-CX12-CCX1-CX12=CCX2-CCX1-CCX2
  equals CCX0 • CX12 • CCX1 • CX12
    by Order.general-rewrite 100 auto
  equals CX12 • CX12 • (CCX0 • CX12) • CCX1 • CX12
    by right right left lemma-CCX0-CX12=CX12-CX10-CCX0
  equals CX12 • CX12 • (CX12 • CX10 • CCX0) • CCX1 • CX12
    by Order.general-rewrite 100 auto
  equals CX12 • (CX10 • CCX0 • CCX1) • CX12
    by right left lemma-CX10-CCX0-CCX1=CCX1-CX10-CCX0
  equals CX12 • (CCX1 • CX10 • CCX0) • CX12
    by Order.general-rewrite 100 auto
  equals CX12 • CCX1 • CX12 • (CX12 • CX10 • CCX0) • CX12
    by right right right left lemma-CCX0-CX12=CX12-CX10-CCX0 reversed
  equals CX12 • CCX1 • CX12 • (CCX0 • CX12) • CX12
    by Order.general-rewrite 100 auto
  equals (CX12 • CCX1 • CX12) • CCX0
    by left lemma-CX12-CCX1-CX12=CCX2-CCX1-CCX2
  equals (CCX2 • CCX1 • CCX2) • CCX0
    by general-assoc auto
  equals CCX2 • CCX1 • CCX2 • CCX0


lemma-CCX0-CX01=CX01-CCX1-CCX0-CCX1 : Rel ⊢ CCX0 • CX01 === CX01 • CCX1 • CCX0 • CCX1
lemma-CCX0-CX01=CX01-CCX1-CCX0-CCX1 =
  equational CCX0 • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • CX01 • CCX0 • CX01
    by right lemma-CX01-CCX0-CX01=CCX1-CCX0-CCX1
  equals CX01 • CCX1 • CCX0 • CCX1


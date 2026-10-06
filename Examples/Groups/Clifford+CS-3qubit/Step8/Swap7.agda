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

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap7 where

lemma-h1 : Rel ⊢ Swap01 • CS12 • Swap01 === CS02
lemma-h1 =
  equational Swap01 • CS12 • Swap01
    by left lemma-Swap-alt-def
  equals (CX10 • CX01 • CX10) • CS12 • Swap01
    by right right lemma-Swap-alt-def
  equals (CX10 • CX01 • CX10) • CS12 • (CX10 • CX01 • CX10)
    by Order.general-rewrite 100 auto
  equals CX10 • CX01 • CS12 • CX01 • CX10
    by axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12
  equals CX12 • CX21 • CS01 • CX21 • CX12
    by Order.general-rewrite 100 auto
  equals CS02


lemma-h2 : Rel ⊢ Swap01 • CS12 • CS12 • Swap01 === CS02 • CS02
lemma-h2 =
  equational Swap01 • CS12 • CS12 • Swap01
    by Order.general-rewrite 100 auto
  equals (Swap01 • CS12 • Swap01) • (Swap01 • CS12 • Swap01)
    by cong lemma-h1 lemma-h1
  equals CS02 • CS02



lemma-CX01-CCZ=CS02-CS02-CCZ-CX01 : Rel ⊢ CX01 • CCZ === CS02 • CS02 • CCZ • CX01
lemma-CX01-CCZ=CS02-CS02-CCZ-CX01 =
  equational CX01 • CCZ
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CX01) • CCZ
    by right left lemma-Swap01-CX01=CX10-Swap01
  equals Swap01 • (CX10 • Swap01) • CCZ
    by right assoc
  equals Swap01 • CX10 • Swap01 • CCZ
    by right right lemma-Swap01-CCZ=CCZ-Swap01
  equals Swap01 • CX10 • CCZ • Swap01
    by general-assoc auto
  equals Swap01 • (CX10 • CCZ) • Swap01
    by right left lemma-CX10-CCZ=CS12-CS12-CCZ-CX10
  equals Swap01 • (CS12 • CS12 • CCZ • CX10) • Swap01
    by Order.general-rewrite 100 auto
  equals (Swap01 • CS12 • CS12 • Swap01) • Swap01 • CCZ • CX10 • Swap01
    by left lemma-h2
  equals (CS02 • CS02) • Swap01 • CCZ • CX10 • Swap01
    by general-assoc auto
  equals (CS02 • CS02) • (Swap01 • CCZ) • CX10 • Swap01
    by right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (CS02 • CS02) • (CCZ • Swap01) • CX10 • Swap01
    by general-assoc auto
  equals (CS02 • CS02) • CCZ • (Swap01 • CX10) • Swap01
    by right right left lemma-Swap01-CX10=CX01-Swap01
  equals (CS02 • CS02) • CCZ • (CX01 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals CS02 • CS02 • CCZ • CX01


lemma-h3 : Rel ⊢ CS02 • CX01 === CX01 • CS02
lemma-h3 =
  equational CS02 • CX01
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CS02) • CX01
    by right left lemma-Swap01-CS02=CS12-Swap01
  equals Swap01 • (CS12 • Swap01) • CX01
    by right assoc
  equals Swap01 • CS12 • Swap01 • CX01
    by right right lemma-Swap01-CX01=CX10-Swap01
  equals Swap01 • CS12 • CX10 • Swap01
    by general-comm auto
  equals Swap01 • CX10 • CS12 • Swap01
    by general-assoc auto
  equals (Swap01 • CX10) • CS12 • Swap01
    by left lemma-Swap01-CX10=CX01-Swap01
  equals (CX01 • Swap01) • CS12 • Swap01
    by general-assoc auto
  equals CX01 • (Swap01 • CS12) • Swap01
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals CX01 • (CS02 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals CX01 • CS02


lemma-h4 : Rel ⊢ CS02 • CS02 • CX01 === CX01 • CS02 • CS02
lemma-h4 =
  equational CS02 • CS02 • CX01
    by right lemma-h3
  equals CS02 • CX01 • CS02
    by general-assoc auto
  equals (CS02 • CX01) • CS02
    by left lemma-h3
  equals (CX01 • CS02) • CS02
    by general-assoc auto
  equals CX01 • CS02 • CS02

lemma-CCX2-CX01=CX01-CX02-CCX2 : Rel ⊢ CCX2 • CX01 === CX01 • CX02 • CCX2
lemma-CCX2-CX01=CX01-CX02-CCX2 =
  equational CCX2 • CX01
    by Order.general-rewrite 100 auto
  equals K2 • CS02 • CS02 • (CS02 • CS02 • CCZ • CX01) • K2 • iI
    by right right right left lemma-CX01-CCZ=CS02-CS02-CCZ-CX01 reversed
  equals K2 • CS02 • CS02 • (CX01 • CCZ) • K2 • iI
    by general-assoc auto
  equals K2 • (CS02 • CS02 • CX01) • CCZ • K2 • iI
    by right left lemma-h4
  equals K2 • (CX01 • CS02 • CS02) • CCZ • K2 • iI
    by Order.general-rewrite 100 auto
  equals CX01 • CX02 • CCX2












lemma-Swap02-CCX0 : Rel ⊢ Swap01 • Swap12 • Swap01 • CCX0 === CCX2 • Swap01 • Swap12 • Swap01
lemma-Swap02-CCX0 =
  equational Swap01 • Swap12 • Swap01 • CCX0
    by right right lemma-Swap01-CCX0=CCX1-Swap01
  equals Swap01 • Swap12 • CCX1 • Swap01
    by general-assoc auto
  equals Swap01 • (Swap12 • CCX1) • Swap01
    by right left lemma-Swap12-CCX1=CCX2-Swap12
  equals Swap01 • (CCX2 • Swap12) • Swap01
    by general-assoc auto
  equals (Swap01 • CCX2) • Swap12 • Swap01
    by left lemma-Swap01-CCX2=CCX2-Swap01
  equals (CCX2 • Swap01) • Swap12 • Swap01
    by general-assoc auto
  equals CCX2 • Swap01 • Swap12 • Swap01


lemma-Swap02-CX21 : Rel ⊢ Swap01 • Swap12 • Swap01 • CX21 === CX01 • Swap01 • Swap12 • Swap01
lemma-Swap02-CX21 =
  equational Swap01 • Swap12 • Swap01 • CX21
    by right right lemma-Swap01-CX21=CX20-Swap01
  equals Swap01 • Swap12 • CX20 • Swap01
    by general-assoc auto
  equals Swap01 • (Swap12 • CX20) • Swap01
    by right left lemma-Swap12-CX20=CX10-Swap12
  equals Swap01 • (CX10 • Swap12) • Swap01
    by general-assoc auto
  equals (Swap01 • CX10) • Swap12 • Swap01
    by left lemma-Swap01-CX10=CX01-Swap01
  equals (CX01 • Swap01) • Swap12 • Swap01
    by general-assoc auto
  equals CX01 • Swap01 • Swap12 • Swap01


lemma-Swap02-CCX2 : Rel ⊢ Swap01 • Swap12 • Swap01 • CCX2 === CCX0 • Swap01 • Swap12 • Swap01
lemma-Swap02-CCX2 =
  equational Swap01 • Swap12 • Swap01 • CCX2
    by right right lemma-Swap01-CCX2=CCX2-Swap01
  equals Swap01 • Swap12 • CCX2 • Swap01
    by general-assoc auto
  equals Swap01 • (Swap12 • CCX2) • Swap01
    by right left lemma-Swap12-CCX2=CCX1-Swap12
  equals Swap01 • (CCX1 • Swap12) • Swap01
    by general-assoc auto
  equals (Swap01 • CCX1) • Swap12 • Swap01
    by left lemma-Swap01-CCX1=CCX0-Swap01
  equals (CCX0 • Swap01) • Swap12 • Swap01
    by general-assoc auto
  equals CCX0 • Swap01 • Swap12 • Swap01



lemma-Swap02-CX01 : Rel ⊢ Swap01 • Swap12 • Swap01 • CX01 === CX21 • Swap01 • Swap12 • Swap01
lemma-Swap02-CX01 =
  equational Swap01 • Swap12 • Swap01 • CX01
    by right right lemma-Swap01-CX01=CX10-Swap01
  equals Swap01 • Swap12 • CX10 • Swap01
    by general-assoc auto
  equals Swap01 • (Swap12 • CX10) • Swap01
    by right left lemma-Swap12-CX10=CX20-Swap12
  equals Swap01 • (CX20 • Swap12) • Swap01
    by general-assoc auto
  equals (Swap01 • CX20) • Swap12 • Swap01
    by left lemma-Swap01-CX20=CX21-Swap01
  equals (CX21 • Swap01) • Swap12 • Swap01
    by general-assoc auto
  equals CX21 • Swap01 • Swap12 • Swap01



lemma-Swap02-CX02 : Rel ⊢ Swap01 • Swap12 • Swap01 • CX02 === CX20 • Swap01 • Swap12 • Swap01
lemma-Swap02-CX02 =
  equational Swap01 • Swap12 • Swap01 • CX02
    by right right lemma-Swap01-CX02=CX12-Swap01
  equals Swap01 • Swap12 • CX12 • Swap01
    by general-assoc auto
  equals Swap01 • (Swap12 • CX12) • Swap01
    by right left lemma-Swap12-CX12=CX21-Swap12
  equals Swap01 • (CX21 • Swap12) • Swap01
    by general-assoc auto
  equals (Swap01 • CX21) • Swap12 • Swap01
    by left lemma-Swap01-CX21=CX20-Swap01
  equals (CX20 • Swap01) • Swap12 • Swap01
    by general-assoc auto
  equals CX20 • Swap01 • Swap12 • Swap01



lemma-CCX0-CX21 : Rel ⊢ CCX0 • CX21 === CX21 • CX20 • CCX0
lemma-CCX0-CX21 =
  equational CCX0 • CX21
    by Order.general-rewrite 100 auto
  equals Swap01 • Swap12 • Swap01 • (Swap01 • Swap12 • Swap01 • CCX0) • CX21
    by right right right left lemma-Swap02-CCX0
  equals Swap01 • Swap12 • Swap01 • (CCX2 • Swap01 • Swap12 • Swap01) • CX21
    by general-assoc auto
  equals (Swap01 • Swap12 • Swap01 • CCX2) • Swap01 • Swap12 • Swap01 • CX21
    by right lemma-Swap02-CX21
  equals (Swap01 • Swap12 • Swap01 • CCX2) • CX01 • Swap01 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12 • Swap01) • (CCX2 • CX01) • Swap01 • Swap12 • Swap01
    by right left lemma-CCX2-CX01=CX01-CX02-CCX2
  equals (Swap01 • Swap12 • Swap01) • (CX01 • CX02 • CCX2) • Swap01 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12 • Swap01 • CX01) • (CX02 • CCX2) • Swap01 • Swap12 • Swap01
    by left lemma-Swap02-CX01
  equals (CX21 • Swap01 • Swap12 • Swap01) • (CX02 • CCX2) • Swap01 • Swap12 • Swap01
    by general-assoc auto
  equals CX21 • (Swap01 • Swap12 • Swap01 • CX02) • (CCX2) • Swap01 • Swap12 • Swap01
    by right left lemma-Swap02-CX02
  equals CX21 • (CX20 • Swap01 • Swap12 • Swap01) • (CCX2) • Swap01 • Swap12 • Swap01
    by general-assoc auto
  equals (CX21 • CX20) • (Swap01 • Swap12 • Swap01 • CCX2) • Swap01 • Swap12 • Swap01
    by right left lemma-Swap02-CCX2
  equals (CX21 • CX20) • (CCX0 • Swap01 • Swap12 • Swap01) • Swap01 • Swap12 • Swap01
    by Order.general-rewrite 100 auto
  equals CX21 • CX20 • CCX0



  




lemma-hh0 : Rel ⊢ CCX0 • CX21 • CS01 • CX21 === CX21 • CS01 • CX21 • CCX0
lemma-hh0 =
  equational CCX0 • CX21 • CS01 • CX21
    by general-assoc auto
  equals (CCX0 • CX21) • CS01 • CX21
    by left lemma-CCX0-CX21
  equals (CX21 • CX20 • CCX0) • CS01 • CX21
    by general-assoc auto
  equals (CX21 • CX20) • (CCX0 • CS01) • CX21
    by right left lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0
  equals (CX21 • CX20) • (CS01 • CS12 • CCZ • CCX0) • CX21
    by general-assoc auto
  equals (CX21 • CX20) • (CS01 • CS12 • CCZ) • CCX0 • CX21
    by right right lemma-CCX0-CX21
  equals (CX21 • CX20) • (CS01 • CS12 • CCZ) • CX21 • CX20 • CCX0
    by general-assoc auto
  equals (CX21 • CX20 • CS01 • CS12 • CCZ) • (CX21 • CX20) • CCX0
    by right left symm lemma-CX20-CX21
  equals (CX21 • CX20 • CS01 • CS12 • CCZ) • (CX20 • CX21) • CCX0
    by general-assoc auto
  equals CX21 • (CX20 • CS01 • CS12 • CCZ • CX20) • CX21 • CCX0
    by right left lemma-gg1
  equals CX21 • CS01 • CX21 • CCX0

lemma-hh1 : Rel ⊢ CCX0 • CX21 • CS01 • CS01 • CS01 • CX21 === CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
lemma-hh1 =
  equational CCX0 • CX21 • CS01 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (CCX0 • CX21 • CS01 • CX21) • (CX21 • CS01 • CX21) • (CX21 • CS01 • CX21)
    by left lemma-hh0
  equals (CX21 • CS01 • CX21 • CCX0) • (CX21 • CS01 • CX21) • (CX21 • CS01 • CX21)
    by general-assoc auto
  equals (CX21 • CS01 • CX21) • (CCX0 • CX21 • CS01 • CX21) • (CX21 • CS01 • CX21)
    by right left lemma-hh0
  equals (CX21 • CS01 • CX21) • (CX21 • CS01 • CX21 • CCX0) • (CX21 • CS01 • CX21)
    by general-assoc auto
  equals (CX21 • CS01 • CX21) • (CX21 • CS01 • CX21) • (CCX0 • CX21 • CS01 • CX21)
    by right right lemma-hh0
  equals (CX21 • CS01 • CX21) • (CX21 • CS01 • CX21) • (CX21 • CS01 • CX21 • CCX0)
    by Order.general-rewrite 100 auto
  equals CX21 • CS01 • CS01 • CS01 • CX21 • CCX0


lemma-CS02-CS12=CS12-CS01 : Rel ⊢ CS02 • CS12 === CS12 • CS02
lemma-CS02-CS12=CS12-CS01 =
  equational CS02 • CS12
    by Order.general-rewrite 100 auto
  equals Swap12 • (Swap12 • CS02) • CS12
    by right left Order.general-rewrite 100 auto
  equals Swap12 • (CS01 • Swap12) • CS12
    by right assoc
  equals Swap12 • CS01 • Swap12 • CS12
    by right right lemma-Swap12-CS12=CS12-Swap12
  equals Swap12 • CS01 • CS12 • Swap12
    by general-comm auto
  equals Swap12 • CS12 • CS01 • Swap12
    by general-assoc auto
  equals (Swap12 • CS12) • CS01 • Swap12
    by left lemma-Swap12-CS12=CS12-Swap12
  equals (CS12 • Swap12) • CS01 • Swap12
    by general-assoc auto
  equals CS12 • (Swap12 • CS01) • Swap12
    by right left Order.general-rewrite 100 auto
  equals CS12 • (CS02 • Swap12) • Swap12
    by Order.general-rewrite 100 auto
  equals CS12 • CS02



lemma-gg4 : Rel ⊢ CS12 • CCZ === CCZ • CS12
lemma-gg4 =
  equational CS12 • CCZ
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CS12) • CCZ
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals Swap01 • (CS02 • Swap01) • CCZ
    by right assoc
  equals Swap01 • CS02 • Swap01 • CCZ
    by right right lemma-Swap01-CCZ=CCZ-Swap01
  equals Swap01 • CS02 • CCZ • Swap01
    by general-assoc auto
  equals Swap01 • (CS02 • CCZ) • Swap01
    by right left lemma-CS02-CCZ=CCZ-CS02
  equals Swap01 • (CCZ • CS02) • Swap01
    by general-assoc auto
  equals (Swap01 • CCZ) • CS02 • Swap01
    by left lemma-Swap01-CCZ=CCZ-Swap01
  equals (CCZ • Swap01) • CS02 • Swap01
    by general-assoc auto
  equals CCZ • (Swap01 • CS02) • Swap01
    by right left lemma-Swap01-CS02=CS12-Swap01
  equals CCZ • (CS12 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals CCZ • CS12



lemma-CCX0-CCZ=CS12-CS12-CCZ-CCX0 : Rel ⊢ CCX0 • CCZ === CS12 • CS12 • CCZ • CCX0
lemma-CCX0-CCZ=CS12-CS12-CCZ-CCX0 =
  equational CCX0 • CCZ
    by right lemma-CCZ-b
  equals CCX0 • CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CCX0 • CS01) • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by left lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0
  equals (CS01 • CS12 • CCZ • CCX0) • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CS01 • CS12 • CCZ) • (CCX0 • Swap12) • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by right left symm lemma-Swap12-CCX0=CCX0-Swap12
  equals (CS01 • CS12 • CCZ) • (Swap12 • CCX0) • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CS01 • CS12 • CCZ • Swap12) • (CCX0 • CS01) • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by right left lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0
  equals (CS01 • CS12 • CCZ • Swap12) • (CS01 • CS12 • CCZ • CCX0) • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CS01 • CS12 • CCZ • Swap12 • CS01 • CS12 • CCZ) • (CCX0 • Swap12) • CX21 • CS01 • CS01 • CS01 • CX21
    by right left symm lemma-Swap12-CCX0=CCX0-Swap12
  equals (CS01 • CS12 • CCZ • Swap12 • CS01 • CS12 • CCZ) • (Swap12 • CCX0) • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CS01 • CS12 • CCZ • Swap12 • CS01 • CS12 • CCZ • Swap12) • CCX0 • CX21 • CS01 • CS01 • CS01 • CX21
    by right lemma-hh1
  equals (CS01 • CS12 • CCZ • Swap12 • CS01 • CS12 • CCZ • Swap12) • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by general-assoc auto
  equals (CS01 • CS12 • CCZ) • (Swap12 • CS01) • CS12 • CCZ • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by right left Order.general-rewrite 100 auto
  equals (CS01 • CS12 • CCZ) • (CS02 • Swap12) • CS12 • CCZ • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by general-assoc auto
  equals (CS01 • CS12 • CCZ • CS02) • (Swap12 • CS12) • CCZ • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by right left lemma-Swap12-CS12=CS12-Swap12
  equals (CS01 • CS12 • CCZ • CS02) • (CS12 • Swap12) • CCZ • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by general-assoc auto
  equals (CS01 • CS12 • CCZ • CS02 • CS12) • (Swap12 • CCZ) • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by right left lemma-Swap12-CCZ=CCZ-Swap12
  equals (CS01 • CS12 • CCZ • CS02 • CS12) • (CCZ • Swap12) • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by Order.general-rewrite 100 auto
  equals (CS01 • CS12 • CCZ) • (CS02 • CS12) • CCZ • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by right left lemma-CS02-CS12=CS12-CS01
  equals (CS01 • CS12 • CCZ) • (CS12 • CS02) • CCZ • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by general-assoc auto
  equals (CS01 • CS12 • CCZ) • CS12 • (CS02 • CCZ) • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by right right left lemma-CS02-CCZ=CCZ-CS02
  equals (CS01 • CS12 • CCZ) • CS12 • (CCZ • CS02) • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by general-assoc auto
  equals (CS01 • CS12) • (CCZ • CS12) • (CCZ • CS02) • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by right left symm lemma-gg4
  equals (CS01 • CS12) • (CS12 • CCZ) • (CCZ • CS02) • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by general-assoc auto
  equals (CS01 • CS12) • CS12 • (CCZ • CCZ) • CS02 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by right right left lemma-CCZ-CCZ=ε
  equals (CS01 • CS12) • CS12 • (ε) • CS02 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • CS01 • CS02 • CX21 • CS01 • CS01 • CS01 • CX21 • CCX0
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • (CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21) • CCX0
    by right right left symm lemma-CCZ-b
  equals CS12 • CS12 • CCZ • CCX0


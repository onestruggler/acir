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

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap9a where

lemma-CCX1-CS12=CS12-CS02-CCZ-CCX1 : Rel ⊢ CCX1 • CS12 === CS12 • CS02 • CCZ • CCX1
lemma-CCX1-CS12=CS12-CS02-CCZ-CCX1 =
  equational CCX1 • CS12
    by Order.general-rewrite 200 auto
  equals (Swap01 • Swap12 • Swap12) • (Swap01 • CCX1) • CS12
    by right left lemma-Swap01-CCX1=CCX0-Swap01
  equals (Swap01 • Swap12 • Swap12) • (CCX0 • Swap01) • CS12
    by general-assoc auto
  equals (Swap01 • Swap12 • Swap12) • CCX0 • (Swap01 • CS12)
    by right right lemma-Swap01-CS12=CS02-Swap01
  equals (Swap01 • Swap12 • Swap12) • CCX0 • (CS02 • Swap01)
    by general-assoc auto
  equals (Swap01 • Swap12) • (Swap12 • CCX0) • (CS02 • Swap01)
    by right left lemma-Swap12-CCX0=CCX0-Swap12
  equals (Swap01 • Swap12) • (CCX0 • Swap12) • (CS02 • Swap01)
    by general-assoc auto
  equals (Swap01 • Swap12) • CCX0 • (Swap12 • CS02) • Swap01
    by right right left lemma-Swap12-CS02=CS01-Swap12
  equals (Swap01 • Swap12) • CCX0 • (CS01 • Swap12) • Swap01
    by general-assoc auto
  equals (Swap01 • Swap12) • (CCX0 • CS01) • Swap12 • Swap01
    by right left lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0
  equals (Swap01 • Swap12) • (CS01 • CS12 • CCZ • CCX0) • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01) • (Swap12 • CS01) • CS12 • CCZ • CCX0 • Swap12 • Swap01
    by right left Order.general-rewrite 200 auto
  equals (Swap01) • (CS02 • Swap12) • CS12 • CCZ • CCX0 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CS02) • (Swap12 • CS12) • CCZ • CCX0 • Swap12 • Swap01
    by right left lemma-Swap12-CS12=CS12-Swap12
  equals (Swap01 • CS02) • (CS12 • Swap12) • CCZ • CCX0 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CS02) • CS12 • (Swap12 • CCZ) • CCX0 • Swap12 • Swap01
    by right right left lemma-Swap12-CCZ=CCZ-Swap12
  equals (Swap01 • CS02) • CS12 • (CCZ • Swap12) • CCX0 • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CS02 • CS12 • CCZ) • (Swap12 • CCX0) • Swap12 • Swap01
    by right left lemma-Swap12-CCX0=CCX0-Swap12
  equals (Swap01 • CS02 • CS12 • CCZ) • (CCX0 • Swap12) • Swap12 • Swap01
    by general-assoc auto
  equals (Swap01 • CS02) • (CS12 • CCZ) • (CCX0 • Swap12) • Swap12 • Swap01
    by left lemma-Swap01-CS02=CS12-Swap01
  equals (CS12 • Swap01) • (CS12 • CCZ) • (CCX0 • Swap12) • Swap12 • Swap01
    by general-assoc auto
  equals (CS12) • (Swap01 • CS12) • (CCZ) • (CCX0 • Swap12) • Swap12 • Swap01
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals (CS12) • (CS02 • Swap01) • (CCZ) • (CCX0 • Swap12) • Swap12 • Swap01
    by general-assoc auto
  equals (CS12 • CS02) • (Swap01 • CCZ) • (CCX0 • Swap12) • Swap12 • Swap01
    by right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (CS12 • CS02) • (CCZ • Swap01) • (CCX0 • Swap12) • Swap12 • Swap01
    by general-assoc auto
  equals (CS12 • CS02) • CCZ • (Swap01 • CCX0) • (Swap12) • Swap12 • Swap01
    by right right left lemma-Swap01-CCX0=CCX1-Swap01
  equals (CS12 • CS02) • CCZ • (CCX1 • Swap01) • (Swap12) • Swap12 • Swap01
    by Order.general-rewrite 200 auto
  equals CS12 • CS02 • CCZ • CCX1


lemma-CCX1-CCX1=ε : Rel ⊢ CCX1 • CCX1 === ε
lemma-CCX1-CCX1=ε =
  equational CCX1 • CCX1
    by Order.general-rewrite 200 auto
  equals Swap01 • (Swap01 • CCX1) • CCX1
    by right left lemma-Swap01-CCX1=CCX0-Swap01
  equals Swap01 • (CCX0 • Swap01) • CCX1
    by general-assoc auto
  equals Swap01 • CCX0 • Swap01 • CCX1
    by right right lemma-Swap01-CCX1=CCX0-Swap01
  equals Swap01 • CCX0 • CCX0 • Swap01
    by general-assoc auto
  equals Swap01 • (CCX0 • CCX0) • Swap01
    by right left lemma-CCX0-CCX0=ε
  equals Swap01 • (ε) • Swap01
    by Order.general-rewrite 200 auto
  equals ε

lemma-CK21-CCZ-CK21-S2=CCX1 : Rel ⊢ CK21 • CCZ • CK21 • S2 === CCX1
lemma-CK21-CCZ-CK21-S2=CCX1 =
  equational CK21 • CCZ • CK21 • S2
    by Order.general-rewrite 200 auto
  equals (S2 ^ 3 • CS12 • K1 • CS12 • K1) • CS12 • (CCZ • CS12) • K1 • CS12 • K1 • CS12 • iI ^ 2
    by right right left lemma-CCZ-CS12=CS12-CCZ
  equals (S2 ^ 3 • CS12 • K1 • CS12 • K1) • CS12 • (CS12 • CCZ) • K1 • CS12 • K1 • CS12 • iI ^ 2
    by Order.general-rewrite 200 auto
  equals (S2 ^ 3 • CS12 • K1 • CS12 • K1) • (CS12 • CS12 • CCZ • X0) • X0 • K1 • CS12 • K1 • CS12 • iI ^ 2
    by right left symm lemma-X-CCZ
  equals (S2 ^ 3 • CS12 • K1 • CS12 • K1) • (X0 • CCZ) • X0 • K1 • CS12 • K1 • CS12 • iI ^ 2
    by Order.general-rewrite 200 auto
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12) • (CCX1 • CS12) • K1 • CS12 • iI • X0
    by right left lemma-CCX1-CS12=CS12-CS02-CCZ-CCX1
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12) • (CS12 • CS02 • CCZ • CCX1) • K1 • CS12 • iI • X0
    by Order.general-rewrite 200 auto
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12) • (CS02 • CCZ) • K1 • CCZ • CS12 • iI • X0
    by right left lemma-CS02-CCZ=CCZ-CS02
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12) • (CCZ • CS02) • K1 • CCZ • CS12 • iI • X0
    by general-assoc auto
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ) • (CS02 • K1) • CCZ • CS12 • iI • X0
    by right left lemma-CS02-K1=K1-CS02
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ) • (K1 • CS02) • CCZ • CS12 • iI • X0
    by general-assoc auto
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ • K1) • CS02 • (CCZ • CS12) • iI • X0
    by right right left lemma-CCZ-CS12=CS12-CCZ
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ • K1) • CS02 • (CS12 • CCZ) • iI • X0
    by general-assoc auto
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ • K1) • (CS02 • CS12) • CCZ • iI • X0
    by right left lemma-CS02-CS12=CS12-CS01
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ • K1) • (CS12 • CS02) • CCZ • iI • X0
    by Order.general-rewrite 200 auto
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ • K1) • (CS12 • CS02 • CCZ) • ε • iI • X0
    by right right left lemma-CCX1-CCX1=ε reversed
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ • K1) • (CS12 • CS02 • CCZ) • (CCX1 • CCX1) • iI • X0
    by general-assoc auto
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ • K1) • (CS12 • CS02 • CCZ • CCX1) • CCX1 • iI • X0
    by right left lemma-CCX1-CS12=CS12-CS02-CCZ-CCX1 reversed
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12 • CCZ • K1) • (CCX1 • CS12) • CCX1 • iI • X0
    by Order.general-rewrite 200 auto
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12) • (CCZ • CCZ) • K1 • CS12 • CCX1 • iI • X0
    by right left lemma-CCZ-CCZ=ε
  equals (S2 ^ 3 • X0 • CS12 • K1 • CS12 • CS12) • (ε) • K1 • CS12 • CCX1 • iI • X0
    by Order.general-rewrite 200 auto
  equals (S2 ^ 3 • X0 • CS12) • (CX21 • CS12) • CCX1 • X0
    by right left lemma-scomm1t
  equals (S2 ^ 3 • X0 • CS12) • (S2 • CS12 ^ 3 • CX21) • CCX1 • X0
    by Order.general-rewrite 200 auto
  equals X0 • CX21 • CCX1 • X0
    by Order.general-rewrite 200 auto
  equals CX21 • K1 • (X0 • CCZ) • X0 • K1 • iI
    by right right left lemma-X-CCZ
  equals CX21 • K1 • (CS12 • CS12 • CCZ • X0) • X0 • K1 • iI
    by Order.general-rewrite 200 auto
  equals CCX1

lemma-aux-a1 : Rel ⊢ CS12 • CS02 • CCZ • CCX1 • K1 • CS12 === CS12 • CCZ • K1 • CCX1 • CS12 • CCX1
lemma-aux-a1 =
  equational CS12 • CS02 • CCZ • CCX1 • K1 • CS12
    by Order.general-rewrite 200 auto
  equals CS12 • (CS02 • CCZ) • K1 • CCZ • CS12
    by right left lemma-CS02-CCZ=CCZ-CS02
  equals CS12 • (CCZ • CS02) • K1 • CCZ • CS12
    by general-assoc auto
  equals CS12 • CCZ • (CS02 • K1) • CCZ • CS12
    by right right left lemma-CS02-K1=K1-CS02
  equals CS12 • CCZ • (K1 • CS02) • CCZ • CS12
    by general-assoc auto
  equals CS12 • CCZ • K1 • CS02 • (CCZ • CS12)
    by right right right right lemma-CCZ-CS12=CS12-CCZ
  equals CS12 • CCZ • K1 • CS02 • (CS12 • CCZ)
    by general-assoc auto
  equals CS12 • CCZ • K1 • (CS02 • CS12) • CCZ
    by right right right left lemma-CS02-CS12=CS12-CS01
  equals CS12 • CCZ • K1 • (CS12 • CS02) • CCZ
    by Order.general-rewrite 200 auto
  equals CS12 • CCZ • K1 • (CS12 • CS02 • CCZ) • ε
    by right right right right lemma-CCX1-CCX1=ε reversed
  equals CS12 • CCZ • K1 • (CS12 • CS02 • CCZ) • (CCX1 • CCX1)
    by general-assoc auto
  equals CS12 • CCZ • K1 • (CS12 • CS02 • CCZ • CCX1) • CCX1
    by right right right left lemma-CCX1-CS12=CS12-CS02-CCZ-CCX1 reversed
  equals CS12 • CCZ • K1 • (CCX1 • CS12) • CCX1
    by general-assoc auto
  equals CS12 • CCZ • K1 • CCX1 • CS12 • CCX1


lemma-CX01-CS12=CS12-CS02-CCZ-CX01 : Rel ⊢ CX01 • CS12 === CS12 • CS02 • CCZ • CX01
lemma-CX01-CS12=CS12-CS02-CCZ-CX01 =
  equational CX01 • CS12
    by Order.general-rewrite 200 auto
  equals Swap01 • (Swap01 • CX01) • CS12
    by right left lemma-Swap01-CX01=CX10-Swap01
  equals Swap01 • (CX10 • Swap01) • CS12
    by general-assoc auto
  equals Swap01 • CX10 • Swap01 • CS12
    by right right lemma-Swap01-CS12=CS02-Swap01
  equals Swap01 • CX10 • CS02 • Swap01
    by general-assoc auto
  equals Swap01 • (CX10 • CS02) • Swap01
    by right left lemma-CX10-CS02=CS02-CS12-CCZ-CX10
  equals Swap01 • (CS02 • CS12 • CCZ • CX10) • Swap01
    by general-assoc auto
  equals (Swap01 • CS02) • (CS12 • CCZ • CX10) • Swap01
    by left lemma-Swap01-CS02=CS12-Swap01
  equals (CS12 • Swap01) • (CS12 • CCZ • CX10) • Swap01
    by general-assoc auto
  equals (CS12) • (Swap01 • CS12) • (CCZ • CX10) • Swap01
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals (CS12) • (CS02 • Swap01) • (CCZ • CX10) • Swap01
    by general-assoc auto
  equals (CS12 • CS02) • (Swap01 • CCZ) • (CX10) • Swap01
    by right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (CS12 • CS02) • (CCZ • Swap01) • (CX10) • Swap01
    by general-assoc auto
  equals (CS12 • CS02 • CCZ) • (Swap01 • CX10) • Swap01
    by right left lemma-Swap01-CX10=CX01-Swap01
  equals (CS12 • CS02 • CCZ) • (CX01 • Swap01) • Swap01
    by Order.general-rewrite 200 auto
  equals CS12 • CS02 • CCZ • CX01



lemma-CCX1-CS01=CS01-CS02-CCZ-CCX1 : Rel ⊢ CCX1 • CS01 === CS01 • CS02 • CCZ • CCX1
lemma-CCX1-CS01=CS01-CS02-CCZ-CCX1 =
  equational CCX1 • CS01
    by Order.general-rewrite 200 auto
  equals Swap01 • (Swap01 • CCX1) • CS01
    by right left lemma-Swap01-CCX1=CCX0-Swap01
  equals Swap01 • (CCX0 • Swap01) • CS01
    by general-assoc auto
  equals Swap01 • CCX0 • Swap01 • CS01
    by right right lemma-Swap01-CS01=CS01-Swap01
  equals Swap01 • CCX0 • CS01 • Swap01
    by general-assoc auto
  equals Swap01 • (CCX0 • CS01) • Swap01
    by right left lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0
  equals Swap01 • (CS01 • CS12 • CCZ • CCX0) • Swap01
    by general-assoc auto
  equals (Swap01 • CS01) • (CS12 • CCZ • CCX0) • Swap01
    by left lemma-Swap01-CS01=CS01-Swap01
  equals (CS01 • Swap01) • (CS12 • CCZ • CCX0) • Swap01
    by general-assoc auto
  equals (CS01) • (Swap01 • CS12) • (CCZ • CCX0) • Swap01
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals (CS01) • (CS02 • Swap01) • (CCZ • CCX0) • Swap01
    by general-assoc auto
  equals (CS01 • CS02) • (Swap01 • CCZ) • (CCX0) • Swap01
    by right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (CS01 • CS02) • (CCZ • Swap01) • (CCX0) • Swap01
    by general-assoc auto
  equals (CS01 • CS02 • CCZ) • (Swap01 • CCX0) • Swap01
    by right left lemma-Swap01-CCX0=CCX1-Swap01
  equals (CS01 • CS02 • CCZ) • (CCX1 • Swap01) • Swap01
    by Order.general-rewrite 200 auto
  equals CS01 • CS02 • CCZ • CCX1


lemma-CCX1-CS01-CS01=CS01-CS01-CS02-CS02-CCX1 : Rel ⊢ CCX1 • CS01 • CS01 === CS01 • CS01 • CS02 • CS02 • CCX1
lemma-CCX1-CS01-CS01=CS01-CS01-CS02-CS02-CCX1 =
  equational CCX1 • CS01 • CS01
    by symm assoc
  equals (CCX1 • CS01) • CS01
    by left lemma-CCX1-CS01=CS01-CS02-CCZ-CCX1
  equals (CS01 • CS02 • CCZ • CCX1) • CS01
    by general-assoc auto
  equals (CS01 • CS02 • CCZ) • CCX1 • CS01
    by right lemma-CCX1-CS01=CS01-CS02-CCZ-CCX1
  equals (CS01 • CS02 • CCZ) • CS01 • CS02 • CCZ • CCX1
    by general-assoc auto
  equals (CS01 • CS02) • (CCZ • CS01) • CS02 • CCZ • CCX1
    by right left lemma-CCZ-CS01=CS01-CCZ
  equals (CS01 • CS02) • (CS01 • CCZ) • CS02 • CCZ • CCX1
    by general-assoc auto
  equals (CS01 • CS02) • CS01 • (CCZ • CS02) • CCZ • CCX1
    by right right left lemma-CS02-CCZ=CCZ-CS02 reversed
  equals (CS01 • CS02) • CS01 • (CS02 • CCZ) • CCZ • CCX1
    by general-assoc auto
  equals (CS01 • CS02 • CS01 • CS02) • (CCZ • CCZ) • CCX1
    by right left lemma-CCZ-CCZ=ε
  equals (CS01 • CS02 • CS01 • CS02) • (ε) • CCX1
    by general-assoc auto
  equals CS01 • (CS02 • CS01) • CS02 • CCX1
    by right left lemma-CS02-CS01=CS01-CS02
  equals CS01 • (CS01 • CS02) • CS02 • CCX1
    by general-assoc auto
  equals CS01 • CS01 • CS02 • CS02 • CCX1
 

lemma-CS02-CCX1=CCX1-CS02 : Rel ⊢ CS02 • CCX1 === CCX1 • CS02
lemma-CS02-CCX1=CCX1-CS02 =
  equational CS02 • CCX1
    by general-comm auto
  equals (CS02 • K1) • CCZ • K1 • iI
    by left lemma-CS02-K1=K1-CS02
  equals (K1 • CS02) • CCZ • K1 • iI
    by general-assoc auto
  equals (K1) • (CS02 • CCZ) • K1 • iI
    by right left lemma-CS02-CCZ=CCZ-CS02
  equals (K1) • (CCZ • CS02) • K1 • iI
    by general-assoc auto
  equals (K1) • (CCZ) • (CS02 • K1) • iI
    by right right left lemma-CS02-K1=K1-CS02
  equals (K1) • (CCZ) • (K1 • CS02) • iI
    by general-comm auto
  equals CCX1 • CS02


lemma-CCZ-S2=S2-CCZ : Rel ⊢ CCZ • S2 === S2 • CCZ
lemma-CCZ-S2=S2-CCZ =
  equational CCZ • S2
    by Order.general-rewrite 200 auto
  equals (Swap12 • Swap01 • Swap01) • (Swap12 • CCZ) • S2
    by right left lemma-Swap12-CCZ=CCZ-Swap12
  equals (Swap12 • Swap01 • Swap01) • (CCZ • Swap12) • S2
    by general-assoc auto
  equals (Swap12 • Swap01 • Swap01) • (CCZ) • Swap12 • S2
    by right right lemma-Swap12-S2=S1-Swap12
  equals (Swap12 • Swap01 • Swap01) • (CCZ) • S1 • Swap12
    by general-assoc auto
  equals (Swap12 • Swap01) • (Swap01 • CCZ) • S1 • Swap12
    by right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (Swap12 • Swap01) • (CCZ • Swap01) • S1 • Swap12
    by general-assoc auto
  equals (Swap12 • Swap01) • CCZ • (Swap01 • S1) • Swap12
    by right right left lemma-Swap01-S1=S0-Swap01
  equals (Swap12 • Swap01) • CCZ • (S0 • Swap01) • Swap12
    by general-assoc auto
  equals (Swap12 • Swap01) • (CCZ • S0) • Swap01 • Swap12
    by right left Order.general-rewrite 100 auto
  equals (Swap12 • Swap01) • (S0 • CCZ) • Swap01 • Swap12
    by general-assoc auto
  equals (Swap12) • (Swap01 • S0) • CCZ • Swap01 • Swap12
    by right left lemma-Swap01-S0=S1-Swap01
  equals (Swap12) • (S1 • Swap01) • CCZ • Swap01 • Swap12
    by general-assoc auto
  equals (Swap12) • S1 • (Swap01 • CCZ) • Swap01 • Swap12
    by right right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (Swap12) • S1 • (CCZ • Swap01) • Swap01 • Swap12
    by general-assoc auto
  equals (Swap12 • S1) • (CCZ • Swap01) • Swap01 • Swap12
    by left lemma-Swap12-S1=S2-Swap12
  equals (S2 • Swap12) • (CCZ • Swap01) • Swap01 • Swap12
    by general-assoc auto
  equals S2 • (Swap12 • CCZ) • Swap01 • Swap01 • Swap12
    by right left lemma-Swap12-CCZ=CCZ-Swap12
  equals S2 • (CCZ • Swap12) • Swap01 • Swap01 • Swap12
    by Order.general-rewrite 200 auto
  equals S2 • CCZ

lemma-CS01-CS01-CCZ-CK21=CK21-CS01-CS01-CCZ : Rel ⊢ CS01 • CS01 • CCZ • CK21 === CK21 • CS01 • CS01 • CCZ
lemma-CS01-CS01-CCZ-CK21=CK21-CS01-CS01-CCZ =
  equational CS01 • CS01 • CCZ • CK21
    by general-comm auto
  equals (CS01 • CS01) • (CCZ • CS12) • K1 • CS12 • K1 • CS12 • S2 ^ 3 • iI
    by right left lemma-CCZ-CS12=CS12-CCZ
  equals (CS01 • CS01) • (CS12 • CCZ) • K1 • CS12 • K1 • CS12 • S2 ^ 3 • iI
    by Order.general-rewrite 200 auto
  equals (CS01 • CS01 • CS12 • K1) • (CCX1 • CS12) • K1 • CS12 • S2 ^ 3 • iI
    by right left lemma-CCX1-CS12=CS12-CS02-CCZ-CCX1
  equals (CS01 • CS01 • CS12 • K1) • (CS12 • CS02 • CCZ • CCX1) • K1 • CS12 • S2 ^ 3 • iI
    by Order.general-rewrite 200 auto
  equals CS12 • K1 • (CX01 • CS12) • CS02 • CCZ • CCX1 • K1 • CS12 • S2 ^ 3 • iI
    by right right left lemma-CX01-CS12=CS12-CS02-CCZ-CX01
  equals CS12 • K1 • (CS12 • CS02 • CCZ • CX01) • CS02 • CCZ • CCX1 • K1 • CS12 • S2 ^ 3 • iI
    by Order.general-rewrite 200 auto
  equals (CS12 • K1 • CS12 • CS02 • CCZ • K1 • CS01 • CS01) • (K1 • CS02) • CCZ • CCX1 • K1 • CS12 • S2 ^ 3 • iI ^ 2
    by right left symm lemma-CS02-K1=K1-CS02
  equals (CS12 • K1 • CS12 • CS02 • CCZ • K1 • CS01 • CS01) • (CS02 • K1) • CCZ • CCX1 • K1 • CS12 • S2 ^ 3 • iI ^ 2
    by Order.general-rewrite 200 auto
  equals (CS12 • K1 • CS12) • (CS02 • K1) • (CCX1 • CS01 • CS01) • CS02 • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by right left lemma-CS02-K1=K1-CS02
  equals (CS12 • K1 • CS12) • (K1 • CS02) • (CCX1 • CS01 • CS01) • CS02 • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by right right left lemma-CCX1-CS01-CS01=CS01-CS01-CS02-CS02-CCX1
  equals (CS12 • K1 • CS12) • (K1 • CS02) • (CS01 • CS01 • CS02 • CS02 • CCX1) • CS02 • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by general-comm auto
  equals (CS12 • K1 • CS12 • K1 • CS02 • CS01 • CS01 • CS02 • CS02) • (CCX1 • CS02) • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by right left lemma-CS02-CCX1=CCX1-CS02 reversed
  equals (CS12 • K1 • CS12 • K1 • CS02 • CS01 • CS01 • CS02 • CS02) • (CS02 • CCX1) • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by general-assoc auto
  equals (CS12 • K1 • CS12 • K1) • (CS02 • CS01) • CS01 • CS02 • CS02 • (CS02 • CCX1) • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by right left lemma-CS02-CS01=CS01-CS02
  equals (CS12 • K1 • CS12 • K1) • (CS01 • CS02) • CS01 • CS02 • CS02 • (CS02 • CCX1) • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by general-assoc auto
  equals (CS12 • K1 • CS12 • K1) • CS01 • (CS02 • CS01) • CS02 • CS02 • (CS02 • CCX1) • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by right right left lemma-CS02-CS01=CS01-CS02
  equals (CS12 • K1 • CS12 • K1) • CS01 • (CS01 • CS02) • CS02 • CS02 • (CS02 • CCX1) • CCX1 • CCZ • CS12 • S2 ^ 3 • iI
    by general-assoc auto
  equals (CS12 • K1 • CS12 • K1 • CS01 • CS01) • (CS02 • CS02 • CS02 • CS02) • (CCX1 • CCX1) • CCZ • CS12 • S2 ^ 3 • iI
    by right left lemma-order-CS02
  equals (CS12 • K1 • CS12 • K1 • CS01 • CS01) • (ε) • (CCX1 • CCX1) • CCZ • CS12 • S2 ^ 3 • iI
    by right right left lemma-CCX1-CCX1=ε
  equals (CS12 • K1 • CS12 • K1 • CS01 • CS01) • (ε) • (ε) • CCZ • CS12 • S2 ^ 3 • iI
    by general-assoc auto
  equals (CS12 • K1 • CS12 • K1 • CS01 • CS01) • (CCZ • CS12) • S2 ^ 3 • iI
    by right left lemma-CCZ-CS12=CS12-CCZ
  equals (CS12 • K1 • CS12 • K1 • CS01 • CS01) • (CS12 • CCZ) • S2 ^ 3 • iI
    by general-comm auto
  equals (CS12 • K1 • CS12 • K1 • CS12 • CS01 • CS01) • (CCZ • S2 ^ 3) • iI
    by right left lemma-comm-powers 1 3 lemma-CCZ-S2=S2-CCZ
  equals (CS12 • K1 • CS12 • K1 • CS12 • CS01 • CS01) • (S2 ^ 3 • CCZ) • iI
    by general-assoc auto
  equals (CS12 • K1 • CS12 • K1) • (CS12 • CS01 ^ 2) • (S2 ^ 3 • CCZ) • iI
    by general-comm auto
  equals (CS12 • K1 • CS12 • K1 • CS12 • S2 • S2 • S2 • iI) • (CS01 ^ 2) • CCZ
    by general-assoc auto
  equals CK21 • CS01 • CS01 • CCZ

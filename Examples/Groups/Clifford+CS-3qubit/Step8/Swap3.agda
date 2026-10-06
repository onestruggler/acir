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

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap3 where

group-like : Grouplike Rel
group-like S0-gen = S0 ^ 3 , Order.general-rewrite 100 auto
group-like S1-gen = S1 ^ 3 , Order.general-rewrite 100 auto
group-like S2-gen = S2 ^ 3 , Order.general-rewrite 100 auto
group-like CS01-gen = CS01 ^ 3 , Order.general-rewrite 100 auto
group-like CS12-gen = CS12 ^ 3 , Order.general-rewrite 100 auto
group-like iI-gen = iI ^ 3 , Order.general-rewrite 100 auto
group-like K0-gen = K0 ^ 7 , Order.general-rewrite 100 auto
group-like K1-gen = K1 ^ 7 , Order.general-rewrite 100 auto
group-like K2-gen = K2 ^ 7 , Order.general-rewrite 100 auto


open Group-Lemmas Gen Rel group-like

lemma-CZ01-CX12-CX21-cubed-alt : Rel ⊢ CX21 • CX12 • CS01 • CS01 • CX21 • CX12 • CS01 • CS01 • CX21 • CX12 • CS01 • CS01 === ε
lemma-CZ01-CX12-CX21-cubed-alt =
  equational CX21 • CX12 • CS01 • CS01 • CX21 • CX12 • CS01 • CS01 • CX21 • CX12 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21) ⁻¹
    by lemma-cong-inv (lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε)
  equals (ε) ⁻¹
    by refl
  equals  ε


lemma-aux0 : Rel ⊢ CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12 === ε
lemma-aux0 =
  equational CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12
    by Order.general-rewrite 100 auto
  equals CX10 • CX01 • (CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01) • CX01 • CX10
    by right right left lemma-CS12-CS12-CX10-CX01-CS12-CS12-CX10-CX01-CS12-CS12-CX10-CX01=ε
  equals CX10 • CX01 • ε • CX01 • CX10
    by Order.general-rewrite 100 auto
  equals ε

lemma-aux1 : Rel ⊢ CX01 • CX10 • CX01 • CS12 • CS12 • CX01 === CS12 • CS12 • CX01 • CX10 • CS12 • CS12
lemma-aux1 =
  equational CX01 • CX10 • CX01 • CS12 • CS12 • CX01
    by general-assoc auto
  equals (CX01 • CX10 • CX01) • CS12 • CS12 • CX01
    by left lemma-Swap-alt-def
  equals (CX10 • CX01 • CX10) • CS12 • CS12 • CX01
    by general-comm auto
  equals CX10 • CX01 • CS12 • CS12 • CX10 • CX01
    by Order.general-rewrite 100 auto
  equals (CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12) • CS12 • CS12 • CX01 • CX10 • CS12 • CS12
    by left lemma-aux0
  equals ε • CS12 • CS12 • CX01 • CX10 • CS12 • CS12
    by general-assoc auto
  equals CS12 • CS12 • CX01 • CX10 • CS12 • CS12

lemma-aux2 : Rel ⊢ CS12 • CX01 • CS12 • CS12 • CX01 === CX01 • CS12 • CS12 • CX01 • CS12
lemma-aux2 =
  equational CS12 • CX01 • CS12 • CS12 • CX01
    by Order.general-rewrite 100 auto
  equals (CS12 • CX01 • CS12 • CX01) • CX01 • CS12 • CX01
    by left lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12
  equals (CX01 • CS12 • CX01 • CS12) • CX01 • CS12 • CX01
    by general-assoc auto
  equals (CX01 • CS12 • CX01) • CS12 • CX01 • CS12 • CX01
    by right lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12
  equals (CX01 • CS12 • CX01) • CX01 • CS12 • CX01 • CS12
    by Order.general-rewrite 100 auto
  equals CX01 • CS12 • CS12 • CX01 • CS12

lemma-aux3 : Rel ⊢ CS12 • CX01 • CS12 • CS12 • CS12 • CX01 === CX01 • CS12 • CS12 • CS12 • CX01 • CS12
lemma-aux3 =
  equational CS12 • CX01 • CS12 • CS12 • CS12 • CX01
    by Order.general-rewrite 100 auto
  equals (CS12 • CX01 • CS12 • CS12 • CX01) • CX01 • CS12 • CX01
    by left lemma-aux2
  equals (CX01 • CS12 • CS12 • CX01 • CS12) • CX01 • CS12 • CX01
    by general-assoc auto
  equals (CX01 • CS12 • CS12 • CX01) • CS12 • CX01 • CS12 • CX01
    by right lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12
  equals (CX01 • CS12 • CS12 • CX01) • CX01 • CS12 • CX01 • CS12
    by Order.general-rewrite 100 auto
  equals CX01 • CS12 • CS12 • CS12 • CX01 • CS12



lemma-CX10-CCZ=CS12-CS12-CCZ-CX10 : Rel ⊢ CX10 • CCZ === CS12 • CS12 • CCZ • CX10
lemma-CX10-CCZ=CS12-CS12-CCZ-CX10 =
  equational CX10 • CCZ
    by right lemma-CCZ-alt-def
  equals CX10 • CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
    by Order.general-rewrite 100 auto
  equals (CX10 • CX10 • CS12 • CX01 • CX10) • (CS12 • CX01 • CS12 • CS12 • CX01) • CX01 • CS12 • CX10 • CX01
    by right left lemma-aux2
  equals (CX10 • CX10 • CS12 • CX01 • CX10) • (CX01 • CS12 • CS12 • CX01 • CS12) • CX01 • CS12 • CX10 • CX01
    by general-assoc auto
  equals CX10 • CX10 • CS12 • (CX01 • CX10 • CX01 • CS12 • CS12 • CX01) • CS12 • CX01 • CS12 • CX10 • CX01
    by right right right left lemma-aux1
  equals CX10 • CX10 • CS12 • (CS12 • CS12 • CX01 • CX10 • CS12 • CS12) • CS12 • CX01 • CS12 • CX10 • CX01
    by general-comm auto
  equals (CX10 • CS12 • CS12 • CS12) • (CX10 • CX01 • CX10) • CS12 • CS12 • CS12 • CX01 • CS12 • CX10 • CX01
    by right left symm lemma-Swap-alt-def
  equals (CX10 • CS12 • CS12 • CS12) • (CX01 • CX10 • CX01) • CS12 • CS12 • CS12 • CX01 • CS12 • CX10 • CX01
    by general-assoc auto
  equals (CX10 • CS12 • CS12 • CS12 • CX01 • CX10) • (CX01 • CS12 • CS12 • CS12 • CX01 • CS12) • CX10 • CX01
    by right left symm lemma-aux3
  equals (CX10 • CS12 • CS12 • CS12 • CX01 • CX10) • (CS12 • CX01 • CS12 • CS12 • CS12 • CX01) • CX10 • CX01
    by general-comm auto
  equals (CS12 • CS12 • CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12) • CX01 • CX10 • CX01
    by right lemma-Swap-alt-def
  equals (CS12 • CS12 • CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12) • CX10 • CX01 • CX10
    by general-assoc auto
  equals CS12 • CS12 • (CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01) • CX10
    by right right left lemma-CCZ-alt-def reversed
  equals CS12 • CS12 • CCZ • CX10


lemma-CCX0-CCX0=ε : Rel ⊢ CCX0 • CCX0 === ε
lemma-CCX0-CCX0=ε =
  equational CCX0 • CCX0
    by Order.general-rewrite 100 auto
  equals K0 • (CCZ • CCZ) • K0 • iI 
    by right left lemma-CCZ-CCZ=ε
  equals K0 • ε • K0 • iI 
    by Order.general-rewrite 100 auto
  equals ε

lemma-CX12-CX21-S1 : Rel ⊢ CX12 • CX21 • S1 === S2 • CX12 • CX21
lemma-CX12-CX21-S1 =
  equational CX12 • CX21 • S1
    by right lemma-CX21-S1
  equals CX12 • S2 • S1 • CS12 • CS12 • CX21
    by general-assoc auto
  equals (CX12 • S2) • S1 • CS12 • CS12 • CX21
    by left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • CX12) • S1 • CS12 • CS12 • CX21
    by general-comm auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (CX12 • CS12 • CS12) • CX21
    by right left lemma-CX12-CZ12
  equals (S1 • S2 • CS12 • CS12 • S1) • (CS12 • CS12 • S1 • S1 • CX12) • CX21
    by Order.general-rewrite 100 auto
  equals S2 • CX12 • CX21


lemma-CCX0-S1=S1-CCX0 : Rel ⊢ CCX0 • S1 === S1 • CCX0
lemma-CCX0-S1=S1-CCX0 =
  equational CCX0 • S1
    by general-comm auto
  equals (K0 • CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • S1) • K0 • iI
    by right left lemma-CX12-CX21-S1
  equals (K0 • CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01) • (S2 • CX12 • CX21) • K0 • iI
    by general-comm auto
  equals (K0 • CS01 • CX12 • CX21 • CS01) • (CX12 • S2) • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right left lemma-CX12-S2
  equals (K0 • CS01 • CX12 • CX21 • CS01) • (S1 • S2 • CS12 • CS12 • CX12) • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals K0 • CS01 • (CX12 • CX21 • S1) • S2 • CS01 • (CS12 • CS12 • CX12) • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right left lemma-CX12-CX21-S1
  equals K0 • CS01 • (S2 • CX12 • CX21) • S2 • CS01 • (CS12 • CS12 • CX12) • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals (K0 • CS01 • S2) • (CX12 • S2) • CX21 • CS01 • (CS12 • CS12 • CX12) • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right left lemma-CX12-S2
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12 • CX12) • CX21 • CS01 • (CS12 • CS12 • CX12) • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12 • CX12) • (CX21 • CS12 • CS12) • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right left lemma-CX21-CS12-CS12
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12 • CX12) • (S2 • S2 • CS12 • CS12 • CX21) • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12) • (CX12 • S2) • S2 • CS12 • CS12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right left lemma-CX12-S2
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12 • CX12) • S2 • CS12 • CS12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-assoc auto
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • (CX12 • S2) • CS12 • CS12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right right left lemma-CX12-S2
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12 • CX12) • CS12 • CS12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • (CX12 • CS12 • CS12) • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right right right left lemma-CX12-CZ12
  equals (K0 • CS01 • S2) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • (CS12 • CS12 • S1 • S1 • CX12) • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by Order.general-rewrite 100 auto
  equals S1 • CCX0




lemma-CX12-CS12-CS12-CS12 : Rel ⊢ CX12 • CS12 • CS12 • CS12 === S1 • S1 • S1 • CS12 • CX12
lemma-CX12-CS12-CS12-CS12 =
  equational CX12 • CS12 • CS12 • CS12
    by general-assoc auto
  equals (CX12 • CS12 • CS12) • CS12
    by left lemma-CX12-CS12-CS12
  equals (S1 • S1 • CS12 • CS12 • CX12) • CS12
    by general-assoc auto
  equals (S1 • S1 • CS12 • CS12) • CX12 • CS12
    by right lemma-CX12-CS12
  equals (S1 • S1 • CS12 • CS12) • S1 • CS12 ^ 3 • CX12
    by Order.general-rewrite 100 auto
  equals S1 • S1 • S1 • CS12 • CX12





lemma-CX12-CX21-CS12 : Rel ⊢ CX12 • CX21 • CS12 === S2 • CS12 • CS12 • CS12 • CX12 • CX21
lemma-CX12-CX21-CS12 =
  equational CX12 • CX21 • CS12
    by general-comm auto
  equals CX12 • (K1 • CS12 • CS12 • K1 • CS12) • iI
    by right left lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals CX12 • (S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1) • iI
    by general-comm auto
  equals (CX12 • S2) • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1 • iI
    by left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • CX12) • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1 • iI
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12) • (CX12 • CS12 • CS12 • CS12) • K1 • CS12 • CS12 • K1 • iI
    by right left lemma-CX12-CS12-CS12-CS12
  equals (S1 • S2 • CS12 • CS12) • (S1 • S1 • S1 • CS12 • CX12) • K1 • CS12 • CS12 • K1 • iI
    by Order.general-rewrite 100 auto
  equals S2 • CS12 • CS12 • CS12 • CX12 • CX21


lemma-CCX0-CS12=CS12-CCX0 : Rel ⊢ CCX0 • CS12 === CS12 • CCX0
lemma-CCX0-CS12=CS12-CCX0 =
  equational CCX0 • CS12
    by general-comm auto
  equals (K0 • CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • CS12) • K0 • iI
    by right left lemma-CX12-CX21-CS12
  equals (K0 • CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01) • (S2 • CS12 • CS12 • CS12 • CX12 • CX21) • K0 • iI
    by general-comm auto
  equals (K0 • CS01 • CX12 • CX21 • CS01) • (CX12 • S2) • (CX21 • CS12 • CS12 • CS12) • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right left lemma-CX21-CS12-CS12-CS12
  equals (K0 • CS01 • CX12 • CX21 • CS01) • (CX12 • S2) • (S2 • S2 • S2 • CS12 • CX21) • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by Order.general-rewrite 100 auto
  equals (K0 • CS01 • CX12 • CX21 • CS01) • (CX12 • CS12) • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right left lemma-CX12-CS12
  equals (K0 • CS01 • CX12 • CX21 • CS01) • (S1 • CS12 ^ 3 • CX12) • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals (K0 • CS01 • CX12) • (CX21 • CS12 ^ 3)  • CS01 • S1 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right left lemma-CX21-CS12^3
  equals (K0 • CS01 • CX12) • (S2 ^ 3 • CS12 • CX21)  • CS01 • S1 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals (K0 • CS01) • (CX12 • S2 ^ 3) • CS12 • (CX21 • S1) • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right left lemma-CX12-S2^3
  equals (K0 • CS01) • ( S1 ^ 3 • S2 ^ 3 • CS12 ^ 2 • CX12) • CS12 • (CX21 • S1) • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right right left lemma-CX21-S1
  equals (K0 • CS01) • ( S1 ^ 3 • S2 ^ 3 • CS12 ^ 2 • CX12) • CS12 • (S2 • S1 • CS12 • CS12 • CX21) • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals (K0 • CS01) • ( S1 ^ 3 • S2 ^ 3 • CS12 ^ 2) • (CX12 • S2) • CS12 • S1 • CS12 • CS12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right left lemma-CX12-S2
  equals (K0 • CS01) • ( S1 ^ 3 • S2 ^ 3 • CS12 ^ 2) • (S1 • S2 • CS12 • CS12 • CX12) • CS12 • S1 • CS12 • CS12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by general-comm auto
  equals (K0 • CS01) • ( S1 ^ 3 • S2 ^ 3 • CS12 ^ 2) • (S1 • S2 • CS12 • CS12 • S1) • (CX12 • CS12 • CS12 • CS12) • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by right right right left lemma-CX12-CS12-CS12-CS12
  equals (K0 • CS01) • ( S1 ^ 3 • S2 ^ 3 • CS12 ^ 2) • (S1 • S2 • CS12 • CS12 • S1) • (S1 • S1 • S1 • CS12 • CX12) • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • K0 • iI
    by Order.general-rewrite 100 auto
  equals CS12 • CCX0


lemma-CX10-CS01-b : Rel ⊢ CX10 • CS01 === S1 • CS01 ^ 3 • CX10
lemma-CX10-CS01-b =
  equational CX10 • CS01
    by general-comm auto
  equals iI • K0 • CS01 • CS01 • K0 • CS01
    by right lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0
  equals iI • S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0
    by general-comm auto
  equals S1 • CS01 ^ 3 • CX10


lemma-CX10-CS01-CS01-CS01 : Rel ⊢ CX10 • CS01 • CS01 • CS01 === S1 • S1 • S1 • CS01 • CX10
lemma-CX10-CS01-CS01-CS01 =
  equational CX10 • CS01 • CS01 • CS01
    by general-assoc auto
  equals (CX10 • CS01 • CS01) • CS01
    by left lemma-CX10-CS01-CS01
  equals (S1 • S1 • CS01 • CS01 • CX10) • CS01
    by general-assoc auto
  equals (S1 • S1 • CS01 • CS01) • CX10 • CS01
    by right lemma-CX10-CS01
  equals (S1 • S1 • CS01 • CS01) • S1 • CS01 ^ 3 • CX10
    by Order.general-rewrite 122 auto
  equals S1 • S1 • S1 • CS01 • CX10


lemma-CX10-CX01-CS01 : Rel ⊢ CX10 • CX01 • CS01 === S0 • CS01 • CS01 • CS01 • CX10 • CX01
lemma-CX10-CX01-CS01 =
  equational CX10 • CX01 • CS01
    by general-comm auto
  equals CX10 • (K1 • CS01 • CS01 • K1 • CS01) • iI
    by right left lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals CX10 • (S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1) • iI
    by general-comm auto
  equals (CX10 • S0) • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1 • iI
    by left lemma-CX10-S0
  equals (S1 • S0 • CS01 • CS01 • CX10) • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1 • iI
    by general-assoc auto
  equals (S1 • S0 • CS01 • CS01) • (CX10 • CS01 • CS01 • CS01) • K1 • CS01 • CS01 • K1 • iI
    by right left lemma-CX10-CS01-CS01-CS01
  equals (S1 • S0 • CS01 • CS01) • (S1 • S1 • S1 • CS01 • CX10) • K1 • CS01 • CS01 • K1 • iI
    by Order.general-rewrite 122 auto
  equals S0 • CS01 • CS01 • CS01 • CX10 • CX01

lemma-CX10-CX01-CS01-CS01-CS01 : Rel ⊢ CX10 • CX01 • CS01 • CS01 • CS01 === S0 • S0 • S0 • CS01 • CX10 • CX01
lemma-CX10-CX01-CS01-CS01-CS01 =
  equational CX10 • CX01 • CS01 • CS01 • CS01
    by general-assoc auto
  equals (CX10 • CX01 • CS01) • CS01 • CS01
    by left lemma-CX10-CX01-CS01
  equals (S0 • CS01 • CS01 • CS01 • CX10 • CX01) • CS01 • CS01
    by general-assoc auto
  equals (S0 • CS01 • CS01 • CS01) • (CX10 • CX01 • CS01) • CS01
    by right left lemma-CX10-CX01-CS01
  equals (S0 • CS01 • CS01 • CS01) • (S0 • CS01 • CS01 • CS01 • CX10 • CX01) • CS01
    by general-assoc auto
  equals (S0 • CS01 • CS01 • CS01) • (S0 • CS01 • CS01 • CS01) • CX10 • CX01 • CS01
    by right right lemma-CX10-CX01-CS01
  equals (S0 • CS01 • CS01 • CS01) • (S0 • CS01 • CS01 • CS01) • S0 • CS01 • CS01 • CS01 • CX10 • CX01
    by Order.general-rewrite 122 auto
  equals S0 • S0 • S0 • CS01 • CX10 • CX01



lemma-CX10-CZ10 : Rel ⊢ CX10 • CS01 • CS01 === CS01 • CS01 • S1 • S1 • CX10
lemma-CX10-CZ10 =
  equational CX10 • CS01 • CS01
    by general-comm auto
  equals ((K0 • CS01 • CS01 • K0 • CS01) • CS01) • iI
    by left left lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0
  equals ((S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • CS01) • iI
    by general-assoc auto
  equals (S1 • CS01 • CS01 • CS01) • (K0 • CS01 • CS01 • K0 • CS01) • iI
    by right left lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0
  equals (S1 • CS01 • CS01 • CS01) • (S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0) • iI
    by Order.general-rewrite 122 auto
  equals CS01 • CS01 • S1 • S1 • CX10


lemma-CX10-CX01-S1 : Rel ⊢ CX10 • CX01 • S1 === S0 • CX10 • CX01
lemma-CX10-CX01-S1 =
  equational CX10 • CX01 • S1
    by right lemma-CX01-S1
  equals CX10 • S0 • S1 • CS01 • CS01 • CX01
    by general-assoc auto
  equals (CX10 • S0) • S1 • CS01 • CS01 • CX01
    by left lemma-CX10-S0
  equals (S1 • S0 • CS01 • CS01 • CX10) • S1 • CS01 • CS01 • CX01
    by general-comm auto
  equals (S1 • S0 • CS01 • CS01 • S1) • (CX10 • CS01 • CS01) • CX01
    by right left lemma-CX10-CZ10
  equals (S1 • S0 • CS01 • CS01 • S1) • (CS01 • CS01 • S1 • S1 • CX10) • CX01
    by Order.general-rewrite 122 auto
  equals S0 • CX10 • CX01


lemma-CCZ-CS01=CS01-CCZ : Rel ⊢ CCZ • CS01 === CS01 • CCZ
lemma-CCZ-CS01=CS01-CCZ =
  equational CCZ • CS01
    by left lemma-CCZ-alt-def
  equals (CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01) • CS01
    by general-assoc auto
  equals (CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12) • CX10 • CX01 • CS01
    by right lemma-CX10-CX01-CS01
  equals (CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12) • S0 • CS01 • CS01 • CS01 • CX10 • CX01
    by general-comm auto
  equals (CS12 • CX10 • CX01 • CS12) • (CX10 • CX01 • CS01 • CS01 • CS01) • (CS12 • CS12 • CS12) • S0 • CX10 • CX01
    by right left lemma-CX10-CX01-CS01-CS01-CS01
  equals (CS12 • CX10 • CX01 • CS12) • (S0 • S0 • S0 • CS01 • CX10 • CX01) • (CS12 • CS12 • CS12) • S0 • CX10 • CX01
    by general-comm auto
  equals (CS12 • CX10 • CX01 • CS12) • (S0 • S0 • S0 • CS01) • (CX10 • S0) • CX01 • (CS12 • CS12 • CS12) • CX10 • CX01
    by right right left lemma-CX10-S0
  equals (CS12 • CX10 • CX01 • CS12) • (S0 • S0 • S0 • CS01) • (S1 • S0 • CS01 • CS01 • CX10) • CX01 • (CS12 • CS12 • CS12) • CX10 • CX01
    by Order.general-rewrite 122 auto
  equals CS12 • (CX10 • CX01 • CS01 • CS01 • CS01) • CS12 • S1 • CX10 • CX01 • (CS12 • CS12 • CS12) • CX10 • CX01
    by right left lemma-CX10-CX01-CS01-CS01-CS01
  equals CS12 • (S0 • S0 • S0 • CS01 • CX10 • CX01) • CS12 • S1 • CX10 • CX01 • (CS12 • CS12 • CS12) • CX10 • CX01
    by general-comm auto
  equals CS12 • (S0 • S0 • S0 • CS01) • (CX10 • CX01 • S1) • CS12 • CX10 • CX01 • (CS12 • CS12 • CS12) • CX10 • CX01
    by right right left lemma-CX10-CX01-S1
  equals CS12 • (S0 • S0 • S0 • CS01) • (S0 • CX10 • CX01) • CS12 • CX10 • CX01 • (CS12 • CS12 • CS12) • CX10 • CX01
    by Order.general-rewrite 122 auto
  equals CS01 • CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
    by right symm lemma-CCZ-alt-def
  equals CS01 • CCZ



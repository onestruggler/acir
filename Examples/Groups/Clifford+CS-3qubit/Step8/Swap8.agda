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

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap8 where

lemma-hs0 : Rel ⊢ CS02 • CX21 === CX21 • CS02
lemma-hs0 =
  equational CS02 • CX21
    by Order.general-rewrite 100 auto
  equals Swap12 • (Swap12 • CS02) • CX21
    by right left Order.general-rewrite 100 auto
  equals Swap12 • (CS01 • Swap12) • CX21
    by right assoc
  equals Swap12 • CS01 • Swap12 • CX21
    by right right lemma-Swap12-CX21=CX12-Swap12
  equals Swap12 • CS01 • CX12 • Swap12
    by general-assoc auto
  equals Swap12 • (CS01 • CX12) • Swap12
    by right left (general-comm auto)
  equals Swap12 • (CX12 • CS01) • Swap12
    by general-assoc auto
  equals (Swap12 • CX12) • CS01 • Swap12
    by left lemma-Swap12-CX12=CX21-Swap12
  equals (CX21 • Swap12) • CS01 • Swap12
    by general-assoc auto
  equals CX21 • (Swap12 • CS01) • Swap12
    by right left Order.general-rewrite 100 auto
  equals CX21 • (CS02 • Swap12) • Swap12
    by Order.general-rewrite 100 auto
  equals CX21 • CS02



lemma-CS02-CS01^3=CS01^3-CS02 : Rel ⊢ CS02 • CS01 • CS01 • CS01 === CS01 • CS01 • CS01 • CS02
lemma-CS02-CS01^3=CS01^3-CS02 =
  equational CS02 • CS01 • CS01 • CS01
    by lemma-comm-powers 1 3 lemma-CS02-CS01=CS01-CS02
  equals (CS01 • CS01 • CS01) • CS02
    by general-assoc auto
  equals CS01 • CS01 • CS01 • CS02


lemma-hs1 : Rel ⊢ CS02 • CX21 • CS01 • CS01 • CS01 • CX21 === CX21 • CS01 • CS01 • CS01 • CX21 • CS02
lemma-hs1 =
  equational CS02 • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CS02 • CX21) • CS01 • CS01 • CS01 • CX21
    by left lemma-hs0
  equals (CX21 • CS02) • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals CX21 • (CS02 • CS01 • CS01 • CS01) • CX21
    by right left lemma-CS02-CS01^3=CS01^3-CS02
  equals CX21 • (CS01 • CS01 • CS01 • CS02) • CX21
    by general-assoc auto
  equals (CX21 • CS01 • CS01 • CS01) • CS02 • CX21
    by right lemma-hs0
  equals (CX21 • CS01 • CS01 • CS01) • CX21 • CS02
    by general-assoc auto
  equals CX21 • CS01 • CS01 • CS01 • CX21 • CS02

lemma-hs2 : Rel ⊢ CX21 • CS01 • CS01 • CS01 • CX21 • CS01 === CS01 • CX21 • CS01 • CS01 • CS01 • CX21
lemma-hs2 =
  equational CX21 • CS01 • CS01 • CS01 • CX21 • CS01
    by Order.general-rewrite 100 auto
  equals CX21 • (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CX21
    by right left lemma-d0
  equals CX21 • (CX21 • CS01 • CX21 • CS01 • CS01 • CS01) • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • CX21 • CS01 • CS01 • CS01 • CX21


lemma-CCZ-c : Rel ⊢ CCZ === CX21 • CS01 • CS01 • CS01 • CX21 • CS01 • CS02
lemma-CCZ-c =
  equational CCZ
    by lemma-CCZ-b
  equals CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals CS01 • (CS02 • CX21 • CS01 • CS01 • CS01 • CX21)
    by right lemma-hs1
  equals CS01 • (CX21 • CS01 • CS01 • CS01 • CX21 • CS02)
    by general-assoc auto
  equals (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CS02
    by left symm lemma-hs2
  equals (CX21 • CS01 • CS01 • CS01 • CX21 • CS01) • CS02
    by general-assoc auto
  equals CX21 • CS01 • CS01 • CS01 • CX21 • CS01 • CS02


lemma-hs3 : Rel ⊢ S1 • K1 • CS01 • CS01 • CS01 • K1 === CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1
lemma-hs3 =
  equational S1 • K1 • CS01 • CS01 • CS01 • K1
    by Order.general-rewrite 100 auto
  equals S1 • K1 • CS01 • CS01 • CS01 • K1
    by Order.general-rewrite 100 auto
  equals (S1 • K1 • CS01 • K1 • CS01 • S0 • CS01 • CS01) • S0 ^ 3 • CS01 • CX01
    by right symm lemma-CX10-CS01^3
  equals (S1 • K1 • CS01 • K1 • CS01 • S0 • CS01 • CS01) • CX01 • CS01 • CS01 • CS01
    by general-assoc auto
  equals (S1 • K1 • CS01 • K1 • CS01) • (S0 • CS01 • CS01 • CX01) • CS01 • CS01 • CS01
    by left symm (axiom ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01)
  equals (CS01 • K1 • CS01 • K1 • S1) • (S0 • CS01 • CS01 • CX01) • CS01 • CS01 • CS01
    by general-comm auto
  equals (CS01 • K1 • CS01 • K1) • (S0 • S1 • CS01 • CS01 • CX01) • CS01 • CS01 • CS01
    by right left symm lemma-CX01-S1
  equals (CS01 • K1 • CS01 • K1) • (CX01 • S1) • CS01 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals CS01 • K1 • CS01 • CS01 • CS01 • K1 • S1 • CS01 • CS01 • CS01
    by general-comm auto
  equals CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1


lemma-CS02-K1=K1-CS02 : Rel ⊢ CS02 • K1 === K1 • CS02
lemma-CS02-K1=K1-CS02 =
  equational CS02 • K1
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CS02) • K1
    by right left lemma-Swap01-CS02=CS12-Swap01
  equals Swap01 • (CS12 • Swap01) • K1
    by general-assoc auto
  equals Swap01 • CS12 • Swap01 • K1
    by right right lemma-Swap01-K1=K0-Swap01
  equals Swap01 • CS12 • K0 • Swap01
    by right symm assoc
  equals Swap01 • (CS12 • K0) • Swap01
    by right left axiom ax-CS12-K0=K0-CS12
  equals Swap01 • (K0 • CS12) • Swap01
    by general-assoc auto
  equals (Swap01 • K0) • CS12 • Swap01
    by left lemma-Swap01-K0=K1-Swap01 
  equals (K1 • Swap01) • CS12 • Swap01
    by general-assoc auto
  equals K1 • (Swap01 • CS12) • Swap01
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals K1 • (CS02 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals K1 • CS02


lemma-CS02-S1=S1-CS02 : Rel ⊢ CS02 • S1 === S1 • CS02
lemma-CS02-S1=S1-CS02 =
  equational CS02 • S1
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CS02) • S1
    by right left lemma-Swap01-CS02=CS12-Swap01
  equals Swap01 • (CS12 • Swap01) • S1
    by general-assoc auto
  equals Swap01 • CS12 • Swap01 • S1
    by right right lemma-Swap01-S1=S0-Swap01
  equals Swap01 • CS12 • S0 • Swap01
    by right symm assoc
  equals Swap01 • (CS12 • S0) • Swap01
    by right left axiom ax-CS12-S0=S0-CS12
  equals Swap01 • (S0 • CS12) • Swap01
    by general-assoc auto
  equals (Swap01 • S0) • CS12 • Swap01
    by left lemma-Swap01-S0=S1-Swap01 
  equals (S1 • Swap01) • CS12 • Swap01
    by general-assoc auto
  equals S1 • (Swap01 • CS12) • Swap01
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals S1 • (CS02 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals S1 • CS02


lemma-Swap12-CS02=CS01-Swap12 : Rel ⊢ Swap12 • CS02 === CS01 • Swap12
lemma-Swap12-CS02=CS01-Swap12 = Order.general-rewrite 100 auto

lemma-order-CS02 : Rel ⊢ CS02 • CS02 ^ 3 === ε
lemma-order-CS02 =
  equational CS02 • CS02 ^ 3
    by Order.general-rewrite 100 auto
  equals Swap12 • Swap12 • CS02 ^ 4
    by right lemma-comm-power 4 lemma-Swap12-CS02=CS01-Swap12
  equals Swap12 • CS01 ^ 4 • Swap12
    by Order.general-rewrite 100 auto
  equals ε


lemma-S1-K1-CS01-K1 : Rel ⊢ S1 • K1 • CS01 • K1 === CS01 • K1 • CS01 • K1 • CS01 ^ 3 • S1
lemma-S1-K1-CS01-K1 =
  equational S1 • K1 • CS01 • K1
    by Order.general-rewrite 100 auto
  equals (S1 • K1 • CS01 • K1 • CS01) • CS01 ^ 3
    by left symm (axiom ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01)
  equals (CS01 • K1 • CS01 • K1 • S1) • CS01 ^ 3
    by general-comm auto
  equals CS01 • K1 • CS01 • K1 • CS01 ^ 3 • S1

lemma-CS01-CS01 : Rel ⊢ CS01 • CX01 === CX01 • S0 • CS01 ^ 3
lemma-CS01-CS01 =
  equational CS01 • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • (CX01 • CS01) • CX01
    by right left lemma-CX01-CS01-f
  equals CX01 • (S0 • CS01 ^ 3 • CX01) • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • S0 • CS01 ^ 3




lemma-hs-main9 : Rel ⊢ K1 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 === CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI ^ 3
lemma-hs-main9 =
  equational K1 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1
    by general-assoc auto
  equals (K1 • CS01 • CS01) • (CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01) • K1
    by right left lemma-CS01-K1-CS01-K1-CS01-CS01-CS01=S1-K1-CS01-K1-S1-S1-S1
  equals (K1 • CS01 • CS01) • (S1 • K1 • CS01 • K1 • S1 • S1 • S1) • K1
    by Order.general-rewrite 100 auto
  equals CX01 • (K1 • S1 • K1) • CS01 • (K1 • S1 ^ 3 • K1 • iI) • iI ^ 3
    by right right right left symm lemma-SKSb
  equals CX01 • (K1 • S1 • K1) • CS01 • (S1 • K1 • S1) • iI ^ 3
    by right left lemma-11b
  equals CX01 • (S1 ^ 3 • K1 • S1 ^ 3) • CS01 • (S1 • K1 • S1) • iI ^ 3
    by Order.general-rewrite 100 auto
  equals (CX01 • S1 ^ 3 • CS01 ^ 3) • (CS01 • K1 • CS01 • K1 • S1) • iI ^ 3
    by right left axiom ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01
  equals (CX01 • S1 ^ 3 • CS01 ^ 3) • (S1 • K1 • CS01 • K1 • CS01) • iI ^ 3
    by Order.general-rewrite 100 auto
  equals (CX01 • CS01 ^ 3) • (K1 • CS01 • K1 • CS01) • iI ^ 3
    by left lemma-CX10-CS01^3
  equals (S0 ^ 3 • CS01 • CX01) • (K1 • CS01 • K1 • CS01) • iI ^ 3
    by Order.general-rewrite 100 auto
  equals CS01 • K1 • (S0 • CS01 ^ 3 • K1 • CS01) • S0 • S0 • iI ^ 3
    by Order.general-rewrite 100 auto
  equals CS01 • K1 • (S0 • CS01 ^ 3 • CX01) • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI ^ 3
    by right right left symm lemma-CX01-CS01-f
  equals CS01 • K1 • (CX01 • CS01) • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI ^ 3
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI ^ 3


lemma-hs-7 : Rel ⊢ X1 • CS12 • CS12 === CS12 • CS12 • S2 • S2 • X1
lemma-hs-7 =
  equational X1 • CS12 • CS12
    by symm assoc
  equals (X1 • CS12) • CS12
    by left axiom ax-X1-CS12=CS12-CS12-CS12-X1-S2
  equals (CS12 • CS12 • CS12 • X1 • S2) • CS12
    by general-comm auto
  equals (CS12 • CS12 • CS12 • S2) • X1 • CS12
    by right axiom ax-X1-CS12=CS12-CS12-CS12-X1-S2
  equals (CS12 • CS12 • CS12 • S2) • CS12 • CS12 • CS12 • X1 • S2
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • S2 • S2 • X1


lemma-e1' : Rel ⊢ CS01 • CX21 • CS01 • CS01 • CX21 === (CX21 • CS01 • CS01 • CX21) • CS01
lemma-e1' =
  equational CS01 • CX21 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (CS01 • CX21 • CS01 • CX21) • CX21  • CS01 • CX21
    by left lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01
  equals (CX21 • CS01 • CX21 • CS01) • CX21  • CS01 • CX21
    by general-assoc auto
  equals (CX21 • CS01 • CX21) • CS01 • CX21  • CS01 • CX21
    by right lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01
  equals (CX21 • CS01 • CX21) • CX21  • CS01 • CX21 • CS01
    by Order.general-rewrite 100 auto
  equals (CX21 • CS01 • CS01 • CX21) • CS01


lemma-hs-6 : Rel ⊢ CS02 • CS02 • CX21 • CS01 • CS01 • CX21 === CS01 • CS01
lemma-hs-6 =
  equational CS02 • CS02 • CX21 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (CX12 • CX21 • CS01 • CS01) • (CX21 • CX12 • CX21) • CS01 • CS01 • CX21
    by right left lemma-Swap12-alt-def reversed
  equals (CX12 • CX21 • CS01 • CS01) • (CX12 • CX21 • CX12) • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21
    by right right lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε
  equals CS01 • CS01 • ε
    by cong refl right-unit
  equals CS01 • CS01

lemma-hs-main6 : Rel ⊢ S0 • K1 • CS01 • CS01 • CS01 • K1 • CX21 • CS01 • CS01 • CX21 === CS01 • CS01 • K1 • CS01 • K1 • CS02 • CS02
lemma-hs-main6 =
  equational S0 • K1 • CS01 • CS01 • CS01 • K1 • CX21 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (S0 • K1 • CS01 • CS01 • CS01 • K1) • CX21 • CS01 • CS01 • CX21
    by general-comm auto
  equals K1 • S0 • CS01 ^ 3 • K1 • CX21 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals K1 • (S0 • CS01 ^ 3 • CX01) • CX01 • K1 • CX21 • CS01 • CS01 • CX21
    by right left symm lemma-CX01-CS01-f
  equals K1 • (CX01 • CS01) • CX01 • K1 • CX21 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • K1 • CS01 • K1) • (CS01 • CS01) • CX21 • CS01 • CS01 • CX21
    by right left lemma-hs-6 reversed
  equals (CS01 • CS01 • K1 • CS01 • K1) • (CS02 • CS02 • CX21 • CS01 • CS01 • CX21) • CX21 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • K1 • CS01 • K1 • CS02 • CS02


lemma-hs-main7 : Rel ⊢ K1 • CS12 • CS12 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI • CS12 • CS12 • K1 === CS01 ^ 3 • CS12 • CS12 • K1 • CS01 • CS02 • CS02 • K1 • CS12 • CS12 • CS01 ^ 3
lemma-hs-main7 =
  equational K1 • CS12 • CS12 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI • CS12 • CS12 • K1
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • (CS12 • CS12 • K1 • CS12 • CS12 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI • CS12 • CS12 • K1 • CS12 • CS12) • CS12 • CS12 
    by general-assoc auto
  equals CS12 • CS12 • ((CS12 • CS12 • K1 • CS12 • CS12) • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI) • (CS12 • CS12 • K1 • CS12 • CS12)) • CS12 • CS12 
    by right right left (left lemma-13-K1-c)
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2) • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI) • (CS12 • CS12 • K1 • CS12 • CS12)) • CS12 • CS12 
    by right right left (right right lemma-13-K1-c)
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2) • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI) • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2)) • CS12 • CS12 
    by general-assoc auto
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12) • (S1 • K1 • S1) • S2 • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI) • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2)) • CS12 • CS12 
    by right right left right left lemma-SKSb
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12) • (K1 • S1 ^ 3 • K1 • iI) • S2 • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI) • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2)) • CS12 • CS12 
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12) • (K1 • S1 ^ 3 • iI) • S2 • (K1 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1) • K1 • S0 • S0 • iI ^ 2 • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2)) • CS12 • CS12 
    by right right left right right right left lemma-hs-main9
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12) • (K1 • S1 ^ 3 • iI) • S2 • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI ^ 3) • K1 • S0 • S0 • iI ^ 2 • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2)) • CS12 • CS12 
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12 • K1 • S1 ^ 2 • CS01 • CS01 • CS01) • (S1 • K1 • CS01 • K1 • CS01) • CS01 • CS01 • K1 • iI ^ 2 • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2 ^ 2)) • CS12 • CS12 
    by right right left right left symm (axiom ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01)
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12 • K1 • S1 ^ 2 • CS01 • CS01 • CS01) • (CS01 • K1 • CS01 • K1 • S1) • CS01 • CS01 • K1 • iI ^ 2 • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2 ^ 2)) • CS12 • CS12 
    by Order.general-rewrite 200 auto
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12) • (X1 • CS01) • K1 • S1 • CS01 • CS01 • K1 • iI • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2 ^ 2)) • CS12 • CS12 
    by right right left right left axiom ax-X1-CS01=CS01-CS01-CS01-X1-S0
  equals CS12 • CS12 • ((S1 • K1 • CS12 • CS12) • (CS01 • CS01 • CS01 • X1 • S0) • K1 • S1 • CS01 • CS01 • K1 • iI • (S1 • K1 • CS12 • CS12 • S1 • K1 • S1 • S2 ^ 2)) • CS12 • CS12 
    by Order.general-rewrite 200 auto
  equals CS12 • CS12 • (((S1 • K1 • CS12 • CS12) • (CS01 • CS01 • CS01 • S0) • K1 • CS01 • CS01 • S1 ^ 3) • (K1 • S1 • K1) • (iI • CS12 • CS12 • S1 • K1 • S1 • S2 ^ 2)) • CS12 • CS12 
    by right right left right left lemma-K1-S1-K1=S1^3-K1-S1^3
  equals CS12 • CS12 • (((S1 • K1 • CS12 • CS12) • (CS01 • CS01 • CS01 • S0) • K1 • CS01 • CS01 • S1 ^ 3) • (S1 ^ 3 • K1 • S1 ^ 3) • (iI • CS12 • CS12 • S1 • K1 • S1 • S2 ^ 2)) • CS12 • CS12 
    by Order.general-rewrite 200 auto
  equals CS12 • CS12 • (((S1 • K1 • CS12 • CS12) • (CS01 • CS01 • CS01 • S0) • K1 • CS01 • CS01 • K1 • iI) • (X1 • CS12 • CS12) • (K1 • S1 • S2 ^ 2)) • CS12 • CS12 
    by right right left right left lemma-hs-7
  equals CS12 • CS12 • (((S1 • K1 • CS12 • CS12) • (CS01 • CS01 • CS01 • S0) • K1 • CS01 • CS01 • K1 • iI) • (CS12 • CS12 • S2 • S2 • X1) • (K1 • S1 • S2 ^ 2)) • CS12 • CS12 
    by Order.general-rewrite 200 auto
  equals CS12 • CS12 • (S0 • (S1 • K1 • CS01 • CS01 • CS01 • K1) • CX21 • CS01 • CS01 • K1 • iI • CS12 • CS12 • K1 • S1 ^ 3) • CS12 • CS12 
    by right right left right left lemma-hs3
  equals CS12 • CS12 • (S0 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1) • CX21 • CS01 • CS01 • K1 • iI • CS12 • CS12 • K1 • S1 ^ 3) • CS12 • CS12 
    by Order.general-rewrite 200 auto
  equals CS12 • CS12 • (S0 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01) • (S1 • CX21 • CS01 • CS01 • CX21) • S1 ^ 3) • CS12 • CS12 
    by right right left right right left symm lemma-d02
  equals CS12 • CS12 • (S0 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01) • (CX21 • CS01 • CS01 • CX21 • S1) • S1 ^ 3) • CS12 • CS12 
    by Order.general-rewrite 200 auto
  equals CS12 • CS12 • (S0 • (CS01 • K1 • CS01 • CS01 • CS01 • K1) • (CS01 ^ 3 • (CX21 • CS01 • CS01 • CX21))) • CS12 • CS12 
    by right right left right right lemma-comm-powers 3 1 lemma-e1'
  equals CS12 • CS12 • (S0 • (CS01 • K1 • CS01 • CS01 • CS01 • K1) • ((CX21 • CS01 • CS01 • CX21) • CS01 ^ 3)) • CS12 • CS12 
    by general-comm auto
  equals CS12 • CS12 • CS01 • (S0 • K1 • CS01 • CS01 • CS01 • K1 • CX21 • CS01 • CS01 • CX21) • CS01 ^ 3 • CS12 • CS12 
    by right right right left lemma-hs-main6
  equals CS12 • CS12 • CS01 • (CS01 • CS01 • K1 • CS01 • K1 • CS02 • CS02) • CS01 ^ 3 • CS12 • CS12
    by general-assoc auto
  equals (CS12 • CS12 • CS01 ^ 3 • K1 • CS01) • (K1 • (CS02 • CS02)) • CS01 ^ 3 • CS12 • CS12
    by right left lemma-comm-power 2 (symm lemma-CS02-K1=K1-CS02)
  equals (CS12 • CS12 • CS01 ^ 3 • K1 • CS01) • ((CS02 • CS02) • K1) • CS01 ^ 3 • CS12 • CS12
    by general-comm auto
  equals CS01 ^ 3 • CS12 • CS12 • K1 • CS01 • CS02 • CS02 • K1 • CS12 • CS12 • CS01 ^ 3

lemma-hs-main8 : Rel ⊢ CS01 • K1 • CS12 • CS12 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI • CS12 • CS12 • K1 • CS01 === CS12 • CS12 • K1 • CS01 • CS02 • CS02 • K1 • CS12 • CS12
lemma-hs-main8 =
  equational CS01 • K1 • CS12 • CS12 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI • CS12 • CS12 • K1 • CS01
    by general-assoc auto
  equals CS01 • (K1 • CS12 • CS12 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI • CS12 • CS12 • K1) • CS01
    by right left lemma-hs-main7
  equals CS01 • (CS01 ^ 3 • CS12 • CS12 • K1 • CS01 • CS02 • CS02 • K1 • CS12 • CS12 • CS01 ^ 3) • CS01
    by Order.general-rewrite 100 auto
  equals CS12 • CS12 • K1 • CS01 • CS02 • CS02 • K1 • CS12 • CS12

lemma-hs-main10 : Rel ⊢ K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • CS12 • CS01 • K1 • CS01 • K1 • iI ^ 3 === CX21 • CS01 • CX21 • CS02 • CS02
lemma-hs-main10 =
  equational K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • CS12 • CS01 • K1 • CS01 • K1 • iI ^ 3
    by Order.general-rewrite 100 auto
  equals (K1 • CS01 • K1 • CS12 • CS12) • (K1 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1) • CS01 • CS01 • CS01 • CS12 • CS12 • CS01 • K1 • CS01 • K1
    by right left lemma-hs-main9
  equals (K1 • CS01 • K1 • CS12 • CS12) • (CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI ^ 3) • CS01 • CS01 • CS01 • CS12 • CS12 • CS01 • K1 • CS01 • K1
    by Order.general-rewrite 100 auto
  equals K1 • (CS01 • K1 • CS12 • CS12 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • S0 • S0 • iI • CS12 • CS12 • K1 • CS01) • iI ^ 2 • K1
    by right left lemma-hs-main8
  equals K1 • (CS12 • CS12 • K1 • CS01 • CS02 • CS02 • K1 • CS12 • CS12) • iI ^ 2 • K1
    by Order.general-rewrite 100 auto
  equals K1 • (CS12 • CS12 • K1 • CS01 • iI) • (CS02 • CS02) • CX21
    by right right lemma-comm-power 2 (symm lemma-hs0) reversed
  equals K1 • (CS12 • CS12 • K1 • CS01 • iI) • CX21 • CS02 • CS02
    by Order.general-rewrite 100 auto
  equals CX21 • CS01 • CX21 • CS02 • CS02

lemma-hs-main : Rel ⊢ K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1 • CS12 • CS12 • K1 • CS01 • K1 • iI ^ 3 === S1 • CS01 ^ 3 • CX21 • CS01 • CX21 • CS02 • CS02
lemma-hs-main =
  equational K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1 • CS12 • CS12 • K1 • CS01 • K1 • iI ^ 3
    by general-comm auto
  equals (K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • CS12) • (S1 • K1 • CS01 • K1) • iI ^ 3
    by right left lemma-S1-K1-CS01-K1
  equals (K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • CS12) • (CS01 • K1 • CS01 • K1 • CS01 ^ 3 • S1) • iI ^ 3
    by general-comm auto
  equals (K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • CS12 • CS01 • K1 • CS01 • K1 • iI ^ 3) • (S1 • CS01 ^ 3)
    by left lemma-hs-main10
  equals (CX21 • CS01 • CX21 • CS02 • CS02) • (S1 • CS01 • CS01 • CS01)
    by general-assoc auto
  equals (CX21 • CS01 • CX21) • ((CS02 • CS02) • S1) • (CS01 • CS01 • CS01)
    by right left lemma-comm-power 2 (symm lemma-CS02-S1=S1-CS02) reversed
  equals (CX21 • CS01 • CX21) • (S1 • CS02 • CS02) • (CS01 • CS01 • CS01)
    by general-assoc auto
  equals (CX21 • CS01 • CX21 • S1) • CS02 • CS02 • (CS01 • CS01 • CS01)
    by left lemma-d01
  equals (S1 • CX21 • CS01 • CX21) • CS02 • CS02 • (CS01 • CS01 • CS01)
    by general-assoc auto
  equals S1 • (CX21 • CS01 • CX21) • CS02 • (CS02 • (CS01 • CS01 • CS01))
    by right right right lemma-comm-power 3 lemma-CS02-CS01=CS01-CS02
  equals S1 • (CX21 • CS01 • CX21) • CS02 • ((CS01 • CS01 • CS01) • CS02)
    by general-assoc auto
  equals S1 • (CX21 • CS01 • CX21) • (CS02 • (CS01 • CS01 • CS01)) • CS02
    by right right left lemma-comm-power 3 lemma-CS02-CS01=CS01-CS02
  equals S1 • (CX21 • CS01 • CX21) • ((CS01 • CS01 • CS01) • CS02) • CS02
    by general-assoc auto
  equals S1 • (CX21 • CS01 • CX21 • CS01 • CS01 • CS01) • CS02 • CS02
    by right left symm lemma-d0
  equals S1 • (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CS02 • CS02
    by general-assoc auto
  equals S1 • CS01 ^ 3 • CX21 • CS01 • CX21 • CS02 • CS02

lemma-CCX1-S1-CCX1=S1-CS02-CCZ : Rel ⊢ CCX1 • S1 • CCX1 === S1 • CS02 • CCZ
lemma-CCX1-S1-CCX1=S1-CS02-CCZ =
  equational CCX1 • S1 • CCX1
    by Order.general-rewrite 100 auto
  equals K1 • CCZ • (K1 • S1 • K1) • CCZ • K1 • iI ^ 2
    by right right right left lemma-CCZ-c
  equals K1 • CCZ • (K1 • S1 • K1) • (CX21 • CS01 • CS01 • CS01 • CX21 • CS01 • CS02) • K1 • iI ^ 2
    by right left lemma-CCZ-b
  equals K1 • (CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21) • (K1 • S1 • K1) • (CX21 • CS01 • CS01 • CS01 • CX21 • CS01 • CS02) • K1 • iI ^ 2
    by Order.general-rewrite 200 auto
  equals (K1 • CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • K1) • (S1 • K1 • CS01 • CS01 • CS01 • K1) • CS12 • CS12 • K1 • CS01 • CS02 • K1 • iI ^ 3
    by right left lemma-hs3
  equals (K1 • CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • K1) • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1) • CS12 • CS12 • K1 • CS01 • CS02 • K1 • iI ^ 3
    by general-assoc auto
  equals K1 • (CS01 • CS02) • CX21 • CS01 • CS01 • CS01 • K1 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1) • CS12 • CS12 • K1 • CS01 • CS02 • K1 • iI ^ 3
    by right left symm lemma-CS02-CS01=CS01-CS02
  equals K1 • (CS02 • CS01) • CX21 • CS01 • CS01 • CS01 • K1 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1) • CS12 • CS12 • K1 • CS01 • CS02 • K1 • iI ^ 3
    by general-assoc auto
  equals (K1 • CS02) • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1) • CS12 • CS12 • K1 • CS01 • CS02 • K1 • iI ^ 3
    by left symm lemma-CS02-K1=K1-CS02
  equals (CS02 • K1) • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1) • CS12 • CS12 • K1 • CS01 • CS02 • K1 • iI ^ 3
    by general-comm auto
  equals (CS02 • K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1) • CS12 • CS12 • K1 • CS01 • iI ^ 3) • CS02 • K1
    by right lemma-CS02-K1=K1-CS02
  equals (CS02 • K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1) • CS12 • CS12 • K1 • CS01 • iI ^ 3) • K1 • CS02
    by general-comm auto
  equals CS02 • (K1 • CS01 • CX21 • CS01 • CS01 • CS01 • K1 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • CS01 • S1 • CS12 • CS12 • K1 • CS01 • K1 • iI ^ 3) • CS02
    by right left lemma-hs-main
  equals CS02 • (S1 • CS01 ^ 3 • CX21 • CS01 • CX21 • CS02 • CS02) • CS02
    by general-assoc auto
  equals ((CS02 • S1) • (CS01 ^ 3 • CX21 • CS01 • CX21) • CS02 • CS02) • CS02
    by left right left symm lemma-CS02-CCZ
  equals ((CS02 • S1) • (CS02 • CCZ) • CS02 • CS02) • CS02
    by left right left lemma-CS02-CCZ=CCZ-CS02
  equals ((CS02 • S1) • (CCZ • CS02) • CS02 • CS02) • CS02
    by general-assoc auto
  equals (CS02 • S1 • CCZ) • CS02 ^ 4
    by right lemma-order-CS02
  equals (CS02 • S1 • CCZ) • ε
    by general-assoc auto
  equals (CS02 • S1) • CCZ
    by left lemma-CS02-S1=S1-CS02
  equals (S1 • CS02) • CCZ
    by assoc
  equals S1 • CS02 • CCZ


lemma-CCX0-S0-CCX0=S0-CS12-CCZ : Rel ⊢ CCX0 • S0 • CCX0 === S0 • CS12 • CCZ
lemma-CCX0-S0-CCX0=S0-CS12-CCZ =
  equational CCX0 • S0 • CCX0
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CCX0) • S0 • CCX0
    by right left lemma-Swap01-CCX0=CCX1-Swap01
  equals Swap01 • (CCX1 • Swap01) • S0 • CCX0
    by general-assoc auto
  equals Swap01 • CCX1 • (Swap01 • S0) • CCX0
    by right right left lemma-Swap01-S0=S1-Swap01
  equals Swap01 • CCX1 • (S1 • Swap01) • CCX0
    by general-assoc auto
  equals Swap01 • CCX1 • S1 • Swap01 • CCX0
    by right right right lemma-Swap01-CCX0=CCX1-Swap01
  equals Swap01 • CCX1 • S1 • CCX1 • Swap01
    by general-assoc auto
  equals Swap01 • (CCX1 • S1 • CCX1) • Swap01
    by right left lemma-CCX1-S1-CCX1=S1-CS02-CCZ
  equals Swap01 • (S1 • CS02 • CCZ) • Swap01
    by general-assoc auto
  equals Swap01 • S1 • CS02 • CCZ • Swap01
    by right right right symm lemma-Swap01-CCZ=CCZ-Swap01
  equals Swap01 • S1 • CS02 • Swap01 • CCZ
    by general-assoc auto
  equals Swap01 • S1 • (CS02 • Swap01) • CCZ
    by right right left symm lemma-Swap01-CS12=CS02-Swap01
  equals Swap01 • S1 • (Swap01 • CS12) • CCZ
    by general-assoc auto
  equals Swap01 • (S1 • Swap01) • CS12 • CCZ
    by right left symm lemma-Swap01-S0=S1-Swap01
  equals Swap01 • (Swap01 • S0) • CS12 • CCZ
    by Order.general-rewrite 100 auto
  equals S0 • CS12 • CCZ

lemma-CCX0-S0=S0-CS12-CCZ-CCX0 : Rel ⊢ CCX0 • S0 === S0 • CS12 • CCZ • CCX0
lemma-CCX0-S0=S0-CS12-CCZ-CCX0 =
  equational CCX0 • S0
    by right symm right-unit
  equals CCX0 • S0 • ε
    by right right symm lemma-CCX0-CCX0=ε
  equals CCX0 • S0 • CCX0 • CCX0
    by general-assoc auto
  equals (CCX0 • S0 • CCX0) • CCX0
    by left lemma-CCX0-S0-CCX0=S0-CS12-CCZ
  equals (S0 • CS12 • CCZ) • CCX0
    by general-assoc auto
  equals S0 • CS12 • CCZ • CCX0


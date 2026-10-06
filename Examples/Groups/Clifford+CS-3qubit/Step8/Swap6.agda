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

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap6 where


lemma-CS02-CS01=CS01-CS02 : Rel ⊢ CS02 • CS01 === CS01 • CS02
lemma-CS02-CS01=CS01-CS02 =
  equational CS02 • CS01
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CS02) • CS01
    by right left lemma-Swap01-CS02=CS12-Swap01
  equals Swap01 • (CS12 • Swap01) • CS01
    by general-assoc auto
  equals Swap01 • CS12 • Swap01 • CS01
    by right right lemma-Swap01-CS01=CS01-Swap01
  equals Swap01 • CS12 • CS01 • Swap01
    by right symm assoc
  equals Swap01 • (CS12 • CS01) • Swap01
    by right left axiom ax-CS12-CS01=CS01-CS12
  equals Swap01 • (CS01 • CS12) • Swap01
    by general-assoc auto
  equals (Swap01 • CS01) • CS12 • Swap01
    by left lemma-Swap01-CS01=CS01-Swap01 
  equals (CS01 • Swap01) • CS12 • Swap01
    by general-assoc auto
  equals CS01 • (Swap01 • CS12) • Swap01
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals CS01 • (CS02 • Swap01) • Swap01
    by Order.general-rewrite 100 auto
  equals CS01 • CS02


lemma-h10 : Rel ⊢ Swap01 • CS01 • CS02 === CS01 • CS12 • Swap01
lemma-h10 =
  equational Swap01 • CS01 • CS02
    by symm assoc
  equals (Swap01 • CS01) • CS02
    by left lemma-Swap01-CS01=CS01-Swap01
  equals (CS01 • Swap01) • CS02
    by assoc
  equals CS01 • Swap01 • CS02
    by right lemma-Swap01-CS02=CS12-Swap01
  equals CS01 • CS12 • Swap01

  

lemma-CCZ-b : Rel ⊢ CCZ === CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
lemma-CCZ-b =
  equational CCZ
    by refl
  equals CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CX12 • CX21 • CS01) • (CX12 • CX21 • CX12) • CS01 • CS01 • CS01 • CX21
    by right left lemma-Swap12-alt-def
  equals (CS01 • CX12 • CX21 • CS01) • (CX21 • CX12 • CX21) • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals CS01 • (CX12 • CX21 • CS01 • CX21 • CX12) • CX21 • CS01 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21


lemma-CS02-CCZ : Rel ⊢ CS02 • CCZ === CS01 ^ 3 • CX21 • CS01 • CX21
lemma-CS02-CCZ =
  equational CS02 • CCZ
    by right lemma-CCZ-b
  equals CS02 • CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CS02 • CS01) • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by left lemma-CS02-CS01=CS01-CS02
  equals (CS01 • CS02) • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • (CX12 • CX21 • CS01 • CS01) • (CX21 • CX12 • CX21) • CS01 • CS01 • CS01 • CX21
    by right right left symm lemma-Swap12-alt-def
  equals CS01 • (CX12 • CX21 • CS01 • CS01) • (CX12 • CX21 • CX12) • CS01 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • CS01) • (CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21) • CX21 • CS01 • CX21
    by right left lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε
  equals (CS01 • CS01 • CS01) • ε • CX21 • CS01 • CX21
    by general-assoc auto
  equals CS01 ^ 3 • CX21 • CS01 • CX21

lemma-h13 : Rel ⊢ S1 • CX21 • CS01 • CX21 === CX21 • CS01 • CX21 • S1
lemma-h13 =
  equational S1 • CX21 • CS01 • CX21
    by general-assoc auto
  equals (S1 • CX21) • CS01 • CX21
    by left lemma-S1-CX21'
  equals (CX21 • S1 • S2 • CS12 • CS12) • CS01 • CX21
    by general-comm auto
  equals (CX21 • CS01) • S2 • S1 • CS12 • CS12 • CX21
    by right symm lemma-CX21-S1
  equals (CX21 • CS01) • CX21 • S1
    by general-assoc auto
  equals CX21 • CS01 • CX21 • S1


lemma-CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS12-CS12-CS12=CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS01-CS01-CS01 : Rel ⊢ CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 === CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS01 • CS01 • CS01
lemma-CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS12-CS12-CS12=CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS01-CS01-CS01 =
  equational CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12
    by Order.general-rewrite 100 auto
  equals (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS01) • CS01 • CS01 • CS01 • CS12 • CS12 • CS12
    by left symm (axiom ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1)
  equals (CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12) • CS01 • CS01 • CS01 • CS12 • CS12 • CS12
    by Order.general-rewrite 100 auto
  equals CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS01 • CS01 • CS01



lemma-aux-c1 : Rel ⊢ CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • iI ^ 3 === ε
lemma-aux-c1 =
  equational CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • iI ^ 3
    by Order.general-rewrite 100 auto
  equals (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12) • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • iI ^ 3
    by left lemma-CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS12-CS12-CS12=CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS01-CS01-CS01
  equals (CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS01 • CS01 • CS01) • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • iI ^ 3
    by Order.general-rewrite 100 auto
  equals ε

lemma-CS12-K1-CS12-CS12-CS12-CS01-K1-CS01-CS01-CS01-K1=K1-CS01-K1-CS01-CS01-CS01-CS12-K1-CS12-CS12-CS12 : Rel ⊢ CS12 • K1 • CS12 • CS12 • CS12 • CS01 • K1 • CS01 • CS01 • CS01 • K1 === K1 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • K1 • CS12 • CS12 • CS12
lemma-CS12-K1-CS12-CS12-CS12-CS01-K1-CS01-CS01-CS01-K1=K1-CS01-K1-CS01-CS01-CS01-CS12-K1-CS12-CS12-CS12 =
  equational CS12 • K1 • CS12 • CS12 • CS12 • CS01 • K1 • CS01 • CS01 • CS01 • K1
    by Order.general-rewrite 100 auto
  equals K1 • CS01 • K1 • CS01 • CS01 • CS01 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • CS01 • K1 • CS01 • CS01 • CS01 • K1) • iI ^ 2
    by Order.general-rewrite 100 auto
  equals (K1 • CS01 • K1 • CS01 • CS01 • CS01) • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS12 • CS12 • CS12 • iI ^ 3) • CS12 • K1 • CS12 • CS12 • CS12
    by right left lemma-aux-c1
  equals (K1 • CS01 • K1 • CS01 • CS01 • CS01) • ε • CS12 • K1 • CS12 • CS12 • CS12
    by general-assoc auto
  equals K1 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • K1 • CS12 • CS12 • CS12



lemma-CS12-K1-CS01 : Rel ⊢ CS12 • K1 • CS01 === K1 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • iI • iI • CS12
lemma-CS12-K1-CS01 =
  equational CS12 • K1 • CS01
    by Order.general-rewrite 100 auto
  equals (CS12 • K1 • CS12 • CS12 • CS12 • CS01 • K1 • CS01 • CS01 • CS01 • K1) • K1 • iI • CS01 • K1 • iI • CS12
    by left lemma-CS12-K1-CS12-CS12-CS12-CS01-K1-CS01-CS01-CS01-K1=K1-CS01-K1-CS01-CS01-CS01-CS12-K1-CS12-CS12-CS12
  equals (K1 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • K1 • CS12 • CS12 • CS12) • K1 • iI • CS01 • K1 • iI • CS12
    by Order.general-rewrite 100 auto
  equals K1 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • iI • iI • CS12

lemma-CS01-CS12-K1-CS01-CS12-K1-S1=S1-K1-CS01-CS12-K1-CS01-CS12-CS02-CCZ : Rel ⊢ CS01 • CS12 • K1 • CS01 • CS12 • K1 • S1 === S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12 • CS02 • CCZ
lemma-CS01-CS12-K1-CS01-CS12-K1-S1=S1-K1-CS01-CS12-K1-CS01-CS12-CS02-CCZ =
  equational CS01 • CS12 • K1 • CS01 • CS12 • K1 • S1
    by general-assoc auto
  equals CS01 • (CS12 • K1 • CS01) • CS12 • K1 • S1
    by right left lemma-CS12-K1-CS01
  equals CS01 • (K1 • CS01 • K1 • CS01 • CS01 • CS01 • CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • iI • iI • CS12) • CS12 • K1 • S1
    by Order.general-rewrite 100 auto
  equals (CS01 • K1 • CS01 • K1 • CS01 ^ 3 • iI) • (CS12 • K1 • CS12 • K1) • CX21 • CS01 • CX21 • S1
    by right right symm lemma-h13
  equals (CS01 • K1 • CS01 • K1 • CS01 ^ 3 • iI) • (CS12 • K1 • CS12 • K1) • S1 • CX21 • CS01 • CX21
    by general-assoc auto
  equals (CS01 • K1 • CS01 • K1 • CS01 ^ 3 • iI) • (CS12 • K1 • CS12 • K1 • S1) • CX21 • CS01 • CX21
    by right left axiom ax-CS12-K1-CS12-K1-S1=S1-K1-CS12-K1-CS12
  equals (CS01 • K1 • CS01 • K1 • CS01 ^ 3 • iI) • (S1 • K1 • CS12 • K1 • CS12) • CX21 • CS01 • CX21
    by general-comm auto
  equals (CS01 • K1 • CS01 • K1 • S1) • (CS01 ^ 3 • K1 • iI • CS12 • K1 • CS12) • CX21 • CS01 • CX21
    by left axiom ax-CS01-K1-CS01-K1-S1=S1-K1-CS01-K1-CS01
  equals (S1 • K1 • CS01 • K1 • CS01) • (CS01 ^ 3 • K1 • iI • CS12 • K1 • CS12) • CX21 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12) • CS01 ^ 3 • CX21 • CS01 • CX21
    by right symm lemma-CS02-CCZ
  equals (S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12) • CS02 • CCZ
    by general-assoc auto
  equals S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12 • CS02 • CCZ




lemma-h11 : Rel ⊢ Swap01 • K0 • CS01 • CS02 === K1 • CS10 • CS12 • Swap01
lemma-h11 =
  equational Swap01 • K0 • CS01 • CS02
    by general-assoc auto
  equals (Swap01 • K0) • CS01 • CS02
    by left lemma-Swap01-K0=K1-Swap01
  equals (K1 • Swap01) • CS01 • CS02
    by general-assoc auto
  equals K1 • Swap01 • CS01 • CS02
    by right lemma-h10
  equals K1 • CS10 • CS12 • Swap01

lemma-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ : Rel ⊢ CS01 • CS02 • K0 • CS01 • CS02 • K0 • S0 === S0 • K0 • CS01 • CS02 • K0 • CS01 • CS02 • CS12 • CCZ
lemma-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ =
  equational CS01 • CS02 • K0 • CS01 • CS02 • K0 • S0
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CS01) • CS02 • K0 • CS01 • CS02 • K0 • S0
    by right left lemma-Swap01-CS01=CS01-Swap01
  equals Swap01 • (CS01 • Swap01) • CS02 • K0 • CS01 • CS02 • K0 • S0
    by general-assoc auto
  equals (Swap01 • CS01) • (Swap01 • CS02) • K0 • CS01 • CS02 • K0 • S0
    by right left lemma-Swap01-CS02=CS12-Swap01
  equals (Swap01 • CS01) • (CS12 • Swap01) • K0 • CS01 • CS02 • K0 • S0
    by general-assoc auto
  equals (Swap01 • CS01 • CS12) • (Swap01 • K0) • CS01 • CS02 • K0 • S0
    by right left lemma-Swap01-K0=K1-Swap01
  equals (Swap01 • CS01 • CS12) • (K1 • Swap01) • CS01 • CS02 • K0 • S0
    by general-assoc auto
  equals (Swap01 • CS01 • CS12 • K1) • (Swap01 • CS01 • CS02) • K0 • S0
    by right left lemma-h10
  equals (Swap01 • CS01 • CS12 • K1) • (CS01 • CS12 • Swap01) • K0 • S0
    by general-assoc auto
  equals (Swap01 • CS01 • CS12 • K1 • CS01 • CS12) • (Swap01 • K0) • S0
    by right left lemma-Swap01-K0=K1-Swap01
  equals (Swap01 • CS01 • CS12 • K1 • CS01 • CS12) • (K1 • Swap01) • S0
    by general-assoc auto
  equals (Swap01 • CS01 • CS12 • K1 • CS01 • CS12 • K1) • Swap01 • S0
    by right lemma-Swap01-S0=S1-Swap01
  equals (Swap01 • CS01 • CS12 • K1 • CS01 • CS12 • K1) • S1 • Swap01
    by general-assoc auto
  equals Swap01 • (CS01 • CS12 • K1 • CS01 • CS12 • K1 • S1) • Swap01
    by right left lemma-CS01-CS12-K1-CS01-CS12-K1-S1=S1-K1-CS01-CS12-K1-CS01-CS12-CS02-CCZ
  equals Swap01 • (S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12 • CS02 • CCZ) • Swap01
    by general-assoc auto
  equals (Swap01 • S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12 • CS02) • (CCZ • Swap01)
    by right symm lemma-Swap01-CCZ=CCZ-Swap01
  equals (Swap01 • S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12 • CS02) • (Swap01 • CCZ)
    by general-assoc auto
  equals (Swap01 • S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12) • (CS02 • Swap01) • CCZ
    by right left lemma-Swap01-CS12=CS02-Swap01 reversed
  equals (Swap01 • S1 • K1 • CS01 • CS12 • K1 • CS01 • CS12) • (Swap01 • CS12) • CCZ
    by general-assoc auto
  equals (Swap01 • S1 • K1 • CS01 • CS12) • (K1 • CS01 • CS12 • Swap01) • CS12 • CCZ
    by right left lemma-h11 reversed
  equals (Swap01 • S1 • K1 • CS01 • CS12) • (Swap01 • K0 • CS01 • CS02) • CS12 • CCZ
    by general-assoc auto
  equals (Swap01 • S1) • (K1 • CS01 • CS12 • Swap01) • (K0 • CS01 • CS02) • CS12 • CCZ
    by right left symm lemma-h11
  equals (Swap01 • S1) • (Swap01 • K0 • CS01 • CS02) • (K0 • CS01 • CS02) • CS12 • CCZ
    by left lemma-Swap01-S1=S0-Swap01
  equals (S0 • Swap01) • (Swap01 • K0 • CS01 • CS02) • (K0 • CS01 • CS02) • CS12 • CCZ
    by Order.general-rewrite 100 auto
  equals S0 • K0 • CS01 • CS02 • K0 • CS01 • CS02 • CS12 • CCZ






lemma-gg0 : Rel ⊢ CX21 • CS01 • CS02 • CCZ • CX21 === CS01
lemma-gg0 =
  equational CX21 • CS01 • CS02 • CCZ • CX21
    by general-assoc auto
  equals (CX21 • CS01 • CS02) • CCZ • CX21
    by right left lemma-CCZ-b
  equals (CX21 • CS01 • CS02) • (CS01 • Swap12 • CS01 • Swap12 • CX21 • CS01 • CS01 • CS01 • CX21) • CX21
    by Order.general-rewrite 100 auto
  equals (CX21 • CS01 • CS02 • CS01 • CS02 • CX21 • CS01 • CS01) • CS01
    by general-assoc auto
  equals (CX21 • CS01) • (CS02 • CS01) • (CS02 • CX21 • CS01 • CS01) • CS01
    by right left lemma-CS02-CS01=CS01-CS02
  equals (CX21 • CS01) • (CS01 • CS02) • (CS02 • CX21 • CS01 • CS01) • CS01
    by Order.general-rewrite 100 auto
  equals ((CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01) • (CX21 • CX12 • CX21) • CS01 • CS01) • CS01
    by left right left lemma-Swap12-alt-def reversed
  equals ((CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01) • (CX12 • CX21 • CX12) • CS01 • CS01) • CS01
    by general-comm auto
  equals (CX21 • CX12 • CS01 • CS01 • CX21 • CX12 • CS01 • CS01 • CX21 • CX12 • CS01 • CS01) • CS01
    by left lemma-CZ01-CX12-CX21-cubed-alt
  equals ε • CS01
    by left-unit
  equals CS01


lemma-gg1 : Rel ⊢ CX20 • CS01 • CS12 • CCZ • CX20 === CS01
lemma-gg1 =
  equational CX20 • CS01 • CS12 • CCZ • CX20
    by Order.general-rewrite 100 auto
  equals Swap01 • (Swap01 • CX20) • CS01 • CS12 • CCZ • CX20
    by right left lemma-Swap01-CX20=CX21-Swap01
  equals Swap01 • (CX21 • Swap01) • CS01 • CS12 • CCZ • CX20
    by general-assoc auto
  equals (Swap01 • CX21) • (Swap01 • CS01) • CS12 • CCZ • CX20
    by right left lemma-Swap01-CS01=CS01-Swap01
  equals (Swap01 • CX21) • (CS01 • Swap01) • CS12 • CCZ • CX20
    by general-assoc auto
  equals (Swap01 • CX21 • CS01) • (Swap01 • CS12) • CCZ • CX20
    by right left lemma-Swap01-CS12=CS02-Swap01
  equals (Swap01 • CX21 • CS01) • (CS02 • Swap01) • CCZ • CX20
    by general-assoc auto
  equals (Swap01 • CX21 • CS01 • CS02) • (Swap01 • CCZ) • CX20
    by right left lemma-Swap01-CCZ=CCZ-Swap01
  equals (Swap01 • CX21 • CS01 • CS02) • (CCZ • Swap01) • CX20
    by general-assoc auto
  equals (Swap01 • CX21 • CS01 • CS02 • CCZ) • Swap01 • CX20
    by right lemma-Swap01-CX20=CX21-Swap01
  equals (Swap01 • CX21 • CS01 • CS02 • CCZ) • CX21 • Swap01
    by general-assoc auto
  equals Swap01 • (CX21 • CS01 • CS02 • CCZ • CX21) • Swap01
    by right left lemma-gg0
  equals Swap01 • (CS01) • Swap01
    by right symm lemma-Swap01-CS01=CS01-Swap01
  equals Swap01 • Swap01 • CS01
    by Order.general-rewrite 100 auto
  equals CS01

lemma-CS02-CCZ=CCZ-CS02 : Rel ⊢ CS02 • CCZ === CCZ • CS02
lemma-CS02-CCZ=CCZ-CS02 =
  equational CS02 • CCZ
    by Order.general-rewrite 100 auto
  equals Swap12 • (Swap12 • CS02) • CCZ
    by right left Order.general-rewrite 100 auto
  equals Swap12 • (CS01 • Swap12) • CCZ
    by right assoc
  equals Swap12 • CS01 • Swap12 • CCZ
    by right right lemma-Swap12-CCZ=CCZ-Swap12
  equals Swap12 • CS01 • CCZ • Swap12
    by general-assoc auto
  equals Swap12 • (CS01 • CCZ) • Swap12
    by right left symm lemma-CCZ-CS01=CS01-CCZ
  equals Swap12 • (CCZ • CS01) • Swap12
    by general-assoc auto
  equals (Swap12 • CCZ) • CS01 • Swap12
    by left lemma-Swap12-CCZ=CCZ-Swap12
  equals (CCZ • Swap12) • CS01 • Swap12
    by general-assoc auto
  equals CCZ • (Swap12 • CS01) • Swap12
    by right left Order.general-rewrite 100 auto
  equals CCZ • (CS02 • Swap12) • Swap12
    by Order.general-rewrite 100 auto
  equals CCZ • CS02


lemma-g6 : Rel ⊢ CS12 • CCZ === CS01 ^ 3 • CX20 • CS01 • CX20
lemma-g6 =
  equational CS12 • CCZ
    by Order.general-rewrite 200 auto
  equals CS01 ^ 3 • CX20 • (CX20 • CS01 • CS12 • CCZ • CX20) • CX20
    by right right left lemma-gg1
  equals CS01 ^ 3 • CX20 • (CS01) • CX20

lemma-g5 : Rel ⊢ CX20 • CCX0 === K0 • (CS01 ^ 3 • CX21 • CS01 • CX21) • CS02 • K0 • iI
lemma-g5 =
  equational CX20 • CCX0
    by Order.general-rewrite 200 auto
  equals K0 • (CS02 • (CS02 • CCZ))• K0 • iI
    by right left right lemma-CS02-CCZ=CCZ-CS02
  equals K0 • (CS02 • (CCZ • CS02))• K0 • iI
    by general-assoc auto
  equals K0 • (CS02 • CCZ) • CS02 • K0 • iI
    by right left lemma-CS02-CCZ
  equals K0 • (CS01 ^ 3 • CX21 • CS01 • CX21) • CS02 • K0 • iI


lemma-g10 : Rel ⊢ CS01 • CS01 • CS01 • CX21 • CS01 • CX21 === CS12 • CS12 • CS12 • CX01 • CS12 • CX01
lemma-g10 =
  equational CS01 • CS01 • CS01 • CX21 • CS01 • CX21
    by lemma-d0
  equals CX21 • CS01 • CX21 • CS01 • CS01 • CS01
    by Order.general-rewrite 200 auto
  equals CX21 • (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CX21
    by right left symm (axiom ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21)
  equals CX21 • (CS12 • CX01 • CS12 • CS12 • CS12 • CX01) • CX21
    by general-assoc auto
  equals CX21 • (CS12 • CX01 • CS12 • CS12 • CS12) • CX01 • CX21
    by Order.general-rewrite 200 auto
  equals (CX21 • CS12) • CX01 • (CS12 • CS12 • CS12 • CX21) • CX01
    by left lemma-CX21-CS12
  equals (S2 • CS12 ^ 3 • CX21) • CX01 • (CS12 • CS12 • CS12 • CX21) • CX01
    by Order.general-rewrite 200 auto
  equals (S2 • CS12 ^ 3 • CX01) • (CX21 • CS12 • CS12 • CS12) • CX21 • CX01
    by right left lemma-CX21-CS12-CS12-CS12
  equals (S2 • CS12 ^ 3 • CX01) • (S2 • S2 • S2 • CS12 • CX21) • CX21 • CX01
    by Order.general-rewrite 200 auto
  equals CS12 • CS12 • CS12 • CX01 • CS12 • CX01


lemma-g13 : Rel ⊢ (CX01 • CS12 • CX01) • CS02 === (CX01 • CS12 • CX01) • CX10 • CX01 • CS12 • CX01 • CX10
lemma-g13 =
  equational (CX01 • CS12 • CX01) • CS02
    by right lemma-CS02
  equals (CX01 • CS12 • CX01) • (Swap01 • CS12 • Swap01)
    by right left lemma-Swap-alt-def
  equals (CX01 • CS12 • CX01) • ((CX10 • CX01 • CX10) • CS12 • Swap01)
    by right right right lemma-Swap-alt-def
  equals (CX01 • CS12 • CX01) • ((CX10 • CX01 • CX10) • CS12 • (CX10 • CX01 • CX10))
    by Order.general-rewrite 200 auto
  equals (CX01 • CS12 • CX01) • CX10 • CX01 • CS12 • CX01 • CX10


lemma-Swap01a : Rel ⊢ Swap01 === K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • iI ^ 3
lemma-Swap01a =
  equational Swap01
    by Order.general-rewrite 100 auto
  equals K1 • (CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1) • iI ^ 3 
    by right left lemma-Swap01-K1=K0-Swap01'
  equals K1 • (K0 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01) • iI ^ 3 
    by general-comm auto
  equals K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • iI ^ 3


lemma-Swap01b : Rel ⊢ Swap01 === CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K1 • K0 • iI ^ 3
lemma-Swap01b =
  equational Swap01
    by lemma-Swap-alt-def
  equals CX10 • CX01 • CX10
    by Order.general-rewrite 100 auto
  equals (K0 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01) • K0 • iI ^ 3
    by left symm lemma-Swap01-K1=K0-Swap01'
  equals (CS01 • CS01 • K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1) • K0 • iI ^ 3
    by general-comm auto
  equals CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K1 • K0 • iI ^ 3

lemma-K1-CS01-CS01-K0-K1-CS01-K0-K1-CS01-CS01-K1=K0-CS01-CS01-K0-K1-CS01-K0-K1-CS01-CS01-K0 : Rel ⊢ K1 • CS01 • CS01 • K0 • K1 • CS01 • K0 • K1 • CS01 • CS01 • K1 === K0 • CS01 • CS01 • K0 • K1 • CS01 • K0 • K1 • CS01 • CS01 • K0
lemma-K1-CS01-CS01-K0-K1-CS01-K0-K1-CS01-CS01-K1=K0-CS01-CS01-K0-K1-CS01-K0-K1-CS01-CS01-K0 =
  equational K1 • CS01 • CS01 • K0 • K1 • CS01 • K0 • K1 • CS01 • CS01 • K1
    by Order.general-rewrite 200 auto
  equals (K0 • CS01 • CS01 • K0 • K1) • ((K1 • K0 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • K0 • K1 • CS01 • CS01 • iI ^ 3) • CS01 • (CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K1 • K0 • iI ^ 3)) • K0 • K1 • CS01 • CS01 • K0
    by right left left symm lemma-Swap01a
  equals (K0 • CS01 • CS01 • K0 • K1) • (Swap01 • CS01 • (CS01 • CS01 • K0 • K1 • CS01 • CS01 • K1 • K0 • CS01 • CS01 • K1 • K0 • iI ^ 3)) • K0 • K1 • CS01 • CS01 • K0
    by right left right right symm lemma-Swap01b
  equals (K0 • CS01 • CS01 • K0 • K1) • (Swap01 • CS01 • Swap01) • K0 • K1 • CS01 • CS01 • K0
    by right left right lemma-Swap01-CS01=CS01-Swap01 reversed
  equals (K0 • CS01 • CS01 • K0 • K1) • (Swap01 • Swap01 • CS01) • K0 • K1 • CS01 • CS01 • K0
    by right left Order.general-rewrite 200 auto
  equals (K0 • CS01 • CS01 • K0 • K1) • CS01 • (K0 • K1 • CS01 • CS01 • K0)
    by general-assoc auto
  equals K0 • CS01 • CS01 • K0 • K1 • CS01 • K0 • K1 • CS01 • CS01 • K0


lemma-g14 : Rel ⊢ CX10 • K1 • CS01 • K1 • CX10 === CX01 • K0 • CS01 • K0 • CX01
lemma-g14 =
  equational CX10 • K1 • CS01 • K1 • CX10
    by general-comm auto
  equals (K0 • CS01 • CS01 • K0 • K1 • CS01 • K0 • K1 • CS01 • CS01 • K0) • iI ^ 2
    by left symm (lemma-K1-CS01-CS01-K0-K1-CS01-K0-K1-CS01-CS01-K1=K0-CS01-CS01-K0-K1-CS01-K0-K1-CS01-CS01-K0)
  equals (K1 • CS01 • CS01 • K0 • K1 • CS01 • K0 • K1 • CS01 • CS01 • K1) • iI ^ 2
    by general-comm auto
  equals CX01 • K0 • CS01 • K0 • CX01

lemma-CS01-CX01 : Rel ⊢ CS01 • CX01 === CX01 • S0 • CS01 ^ 3
lemma-CS01-CX01 =
  equational CS01 • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • (CX01 • CS01) • CX01
    by right left lemma-CX01-CS01-f
  equals CX01 • (S0 • CS01 ^ 3 • CX01) • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • S0 • CS01 ^ 3


lemma-ag2 : Rel ⊢ K1 • CS12 • K1 • CS01 • K1 • CS12 • CS12 • CS12 === CS01 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12 • K1 • CS01 ^ 3
lemma-ag2 =
  equational K1 • CS12 • K1 • CS01 • K1 • CS12 • CS12 • CS12
    by Order.general-rewrite 100 auto
  equals (CS12 • CS12 • CS12) • (CS12 • K1 • CS12 • K1 • CS01 • K1 • CS01) • CS12 • CS12 • CS12 • CS01 ^ 3
    by right left axiom ax-CS12-K1-CS12-K1-CS01-K1-CS01=CS01-K1-CS01-K1-CS12-K1-CS12
  equals (CS12 • CS12 • CS12) • (CS01 • K1 • CS01 • K1 • CS12 • K1 • CS12) • CS12 • CS12 • CS12 • CS01 ^ 3
    by Order.general-rewrite 100 auto
  equals CS01 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12 • K1 • CS01 ^ 3

lemma-ag1 : Rel ⊢ CS01 • K1 • CS12 • K1 • CS01 • K1 • CS12 • CS12 • CS12 • K1 === CS12 • CS12 • CS12 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS01 • K1 • CS01 • CS01
lemma-ag1 =
  equational CS01 • K1 • CS12 • K1 • CS01 • K1 • CS12 • CS12 • CS12 • K1
    by general-assoc auto
  equals CS01 • (K1 • CS12 • K1 • CS01 • K1 • CS12 • CS12 • CS12) • K1
    by right left lemma-ag2
  equals CS01 • (CS01 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12 • K1 • CS01 ^ 3) • K1
    by Order.general-rewrite 100 auto
  equals (CS12 • CS12 • CS12 • K1) • (CX01 • CS01) • K1 • CS12 • K1 • CS01 ^ 3 • K1
    by right left lemma-CX01-CS01=S0-CS01-CS01-CS01-CX01
  equals (CS12 • CS12 • CS12 • K1) • (S0 • CS01 • CS01 • CS01 • CX01) • K1 • CS12 • K1 • CS01 ^ 3 • K1
    by Order.general-rewrite 200 auto
  equals (CS12 • CS12 • CS12 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1) • (CX01 • S0 • CS01 ^ 3) • K1
    by right left lemma-CS01-CX01 reversed
  equals (CS12 • CS12 • CS12 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1) • (CS01 • CX01) • K1
    by Order.general-rewrite 200 auto
  equals CS12 • CS12 • CS12 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS01 • K1 • CS01 • CS01

lemma-CS01-CS01-K1-CS12-K1-CS01-K1-CS12-CS12-CS12-K1=K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1-CS01-CS01 : Rel ⊢ CS01 • CS01 • K1 • CS12 • K1 • CS01 • K1 • CS12 • CS12 • CS12 • K1 === K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12 • K1 • CS01 • CS01
lemma-CS01-CS01-K1-CS12-K1-CS01-K1-CS12-CS12-CS12-K1=K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1-CS01-CS01 =
  equational CS01 • CS01 • K1 • CS12 • K1 • CS01 • K1 • CS12 • CS12 • CS12 • K1
    by right lemma-ag1
  equals CS01 • CS12 • CS12 • CS12 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS01 • K1 • CS01 • CS01
    by general-comm auto
  equals CS12 • CS12 • CS12 • (CS01 • K1 • CS01 • CS01 • CS01 • K1 • CS12 • K1 • CS01) • K1 • CS01 • CS01
    by right right right left symm (axiom ax-CS12-K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1=CS01-K1-CS01-CS01-CS01-K1-CS12-K1-CS01-K1)
  equals CS12 • CS12 • CS12 • (CS12 • K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12) • K1 • CS01 • CS01
    by Order.general-rewrite 200 auto
  equals K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12 • K1 • CS01 • CS01


lemma-K1-CS12-K1-CS01-CS01-K1-CS12-K1-CS01=CS01-K1-CS12-K1-CS01-CS01-K1-CS12-K1 : Rel ⊢ K1 • CS12 • K1 • CS01 • CS01 • K1 • CS12 • K1 • CS01 === CS01 • K1 • CS12 • K1 • CS01 • CS01 • K1 • CS12 • K1
lemma-K1-CS12-K1-CS01-CS01-K1-CS12-K1-CS01=CS01-K1-CS12-K1-CS01-CS01-K1-CS12-K1 =
  equational K1 • CS12 • K1 • CS01 • CS01 • K1 • CS12 • K1 • CS01
    by Order.general-rewrite 200 auto
  equals (K1 • CS12 • K1) • (CS01 • CS01 • K1 • CS12 • K1 • CS01 • K1 • CS12 • CS12 • CS12 • K1) • K1 • CS12 • K1 • iI ^ 2
    by right left lemma-CS01-CS01-K1-CS12-K1-CS01-K1-CS12-CS12-CS12-K1=K1-CS12-CS12-CS12-K1-CS01-K1-CS12-K1-CS01-CS01
  equals (K1 • CS12 • K1) • (K1 • CS12 • CS12 • CS12 • K1 • CS01 • K1 • CS12 • K1 • CS01 • CS01) • K1 • CS12 • K1 • iI ^ 2
    by Order.general-rewrite 200 auto
  equals CS01 • K1 • CS12 • K1 • CS01 • CS01 • K1 • CS12 • K1


lemma-g81 : Rel ⊢ CS12 • CX01 • CS12 • K1 • CS01 • K1 === K1 • CS01 • K1 • CS12 • CX01 • CS12
lemma-g81 =
  equational CS12 • CX01 • CS12 • K1 • CS01 • K1
    by Order.general-rewrite 200 auto
  equals K1 • (K1 • CS12 • K1 • CS01 • CS01 • K1 • CS12 • K1 • CS01) • K1 • iI ^ 2
    by right left lemma-K1-CS12-K1-CS01-CS01-K1-CS12-K1-CS01=CS01-K1-CS12-K1-CS01-CS01-K1-CS12-K1
  equals K1 • (CS01 • K1 • CS12 • K1 • CS01 • CS01 • K1 • CS12 • K1) • K1 • iI ^ 2
    by Order.general-rewrite 200 auto
  equals K1 • CS01 • K1 • CS12 • CX01 • CS12

lemma-g91 : Rel ⊢ CS12 • Swap01 • CS12 • CX10 • K1 • CS01 • K1 • CX10 === CX10 • K1 • CS01 • K1 • CX10 • CS12 • Swap01 • CS12
lemma-g91 =
  equational CS12 • Swap01 • CS12 • CX10 • K1 • CS01 • K1 • CX10
    by Order.general-rewrite 200 auto
  equals CX10 • (CX10 • CS12 • Swap01 • CS12 • CX10 • K1 • CS01 • K1) • CX10
    by right left right right left lemma-Swap-alt-def
  equals CX10 • (CX10 • CS12 • (CX10 • CX01 • CX10) • CS12 • CX10 • K1 • CS01 • K1) • CX10
    by Order.general-rewrite 200 auto
  equals CX10 • (CS12 • CX01 • CS12 • K1 • CS01 • K1) • CX10
    by right left lemma-g81
  equals CX10 • (K1 • CS01 • K1 • CS12 • CX01 • CS12) • CX10
    by Order.general-rewrite 200 auto
  equals CX10 • (K1 • CS01 • K1 • CX10 • CS12) • (CX10 • CX01 • CX10) • (CS12 • CX10) • CX10
    by right right left symm lemma-Swap-alt-def
  equals CX10 • (K1 • CS01 • K1 • CX10 • CS12) • Swap01 • (CS12 • CX10) • CX10
    by Order.general-rewrite 200 auto
  equals CX10 • K1 • CS01 • K1 • CX10 • CS12 • Swap01 • CS12

lemma-g9 : Rel ⊢ (CX01 • CS12 • CX01) • CS02 • K0 • CS01 • K0 === K0 • CS01 • K0 • (CX01 • CS12 • CX01) • CS02
lemma-g9 =
  equational (CX01 • CS12 • CX01) • CS02 • K0 • CS01 • K0
    by general-assoc auto
  equals ((CX01 • CS12 • CX01) • CS02) • K0 • CS01 • K0
    by left lemma-g13
  equals ((CX01 • CS12 • CX01) • CX10 • CX01 • CS12 • CX01 • CX10) • K0 • CS01 • K0
    by Order.general-rewrite 200 auto
  equals (CX01 • CS12 • CX01 • CX10 • CX01 • CS12) • (CX01 • K0 • CS01 • K0 • CX01) • CX01 • CX10
    by right left symm lemma-g14
  equals (CX01 • CS12 • CX01 • CX10 • CX01 • CS12) • (CX10 • K1 • CS01 • K1 • CX10) • CX01 • CX10
    by general-assoc auto
  equals CX01 • (CS12 • Swap01 • CS12 • CX10 • K1 • CS01 • K1 • CX10) • CX01 • CX10
    by right (left lemma-g91)
  equals CX01 • (CX10 • K1 • CS01 • K1 • CX10 • CS12 • Swap01 • CS12) • CX01 • CX10
    by general-assoc auto
  equals CX01 • (CX10 • K1 • CS01 • K1 • CX10) • (CS12 • Swap01 • CS12) • CX01 • CX10
    by right (left lemma-g14)
  equals CX01 • (CX01 • K0 • CS01 • K0 • CX01) • (CS12 • Swap01 • CS12) • CX01 • CX10
    by general-assoc auto
  equals CX01 • (CX01 • K0 • CS01 • K0 • CX01) • (CS12 • CX01 • CX10 • CX01 • CS12) • CX01 • CX10
    by Order.general-rewrite 200 auto
  equals K0 • CS01 • K0 • (CX01 • CS12 • CX01) • CX10 • CX01 • CS12 • CX01 • CX10
    by right right right symm lemma-g13
  equals K0 • CS01 • K0 • (CX01 • CS12 • CX01) • CS02


lemma-g7 : Rel ⊢ CX20 • CCX0 • CS01 === CS01 • CX20 • CCX0
lemma-g7 =
  equational CX20 • CCX0 • CS01
    by general-assoc auto
  equals (CX20 • CCX0) • CS01
    by left lemma-g5
  equals (K0 • (CS01 ^ 3 • CX21 • CS01 • CX21) • CS02 • K0 • iI) • CS01
    by Order.general-rewrite 200 auto
  equals K0 • ((CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CS02 • K0 • CS01 • K0) • K0 • iI ^ 2
    by right left left lemma-g10
  equals K0 • ((CS12 • CS12 • CS12 • CX01 • CS12 • CX01) • CS02 • K0 • CS01 • K0) • K0 • iI ^ 2
    by general-assoc auto
  equals K0 • CS12 • CS12 • CS12 • ((CX01 • CS12 • CX01) • CS02 • K0 • CS01 • K0) • K0 • iI ^ 2
    by right right right right left lemma-g9
  equals K0 • CS12 • CS12 • CS12 • (K0 • CS01 • K0 • (CX01 • CS12 • CX01) • CS02) • K0 • iI ^ 2
    by general-comm auto
  equals K0 • (K0 • CS01 • K0 • (CS12 • CS12 • CS12 • CX01 • CS12 • CX01) • CS02) • K0 • iI ^ 2
    by right left right right right left symm lemma-g10
  equals K0 • (K0 • CS01 • K0 • (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CS02) • K0 • iI ^ 2
    by Order.general-rewrite 200 auto
  equals CS01 • K0 • (CS01 ^ 3 • CX21 • CS01 • CX21) • CS02 • K0 • iI
    by right lemma-g5 reversed
  equals CS01 • CX20 • CCX0


lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0 : Rel ⊢ CCX0 • CS01 === CS01 • CS12 • CCZ • CCX0
lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0 =
  equational CCX0 • CS01
    by Order.general-rewrite 100 auto
  equals CX20 • CX20 • CCX0 • CS01
    by right lemma-g7
  equals CX20 • CS01 • CX20 • CCX0
    by Order.general-rewrite 100 auto
  equals CS01 • (CS01 ^ 3 • CX20 • CS01 • CX20) • CCX0
    by right left lemma-g6 reversed
  equals CS01 • (CS12 • CCZ) • CCX0
    by general-assoc auto
  equals CS01 • CS12 • CCZ • CCX0


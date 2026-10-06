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

module Examples.Groups.Clifford+CS-3qubit.Step8.Swap2 where

lemma-CS12-CS12-CS12-CX01-CS12-CX01=CX21-CS01-CX21-CS01-CS01-CS01 : Rel ⊢ CS12 • CS12 • CS12 • CX01 • CS12 • CX01 === CX21 • CS01 • CX21 • CS01 • CS01 • CS01
lemma-CS12-CS12-CS12-CX01-CS12-CX01=CX21-CS01-CX21-CS01-CS01-CS01 =
  equational CS12 • CS12 • CS12 • CX01 • CS12 • CX01
    by Order.general-rewrite 100 auto
  equals CX21 • (CX21 • CS12 • CS12 • CS12) • CX01 • CS12 • CX01
    by right left lemma-CX21-CS12-CS12-CS12
  equals CX21 • (S2 • S2 • S2 • CS12 • CX21) • CX01 • CS12 • CX01
    by Order.general-rewrite 100 auto
  equals CX21 • (S2 • S2 • S2 • CS12 • CX01) • (CX21 • CS12) • CX01
    by right right left lemma-CX21-CS12
  equals CX21 • (S2 • S2 • S2 • CS12 • CX01) • (S2 • CS12 ^ 3 • CX21) • CX01
    by Order.general-rewrite 100 auto
  equals CX21 • (CS12 • CX01 • CS12 • CS12 • CS12 • CX01) • CX21
    by right left axiom ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21
  equals CX21 • (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CX21
    by Order.general-rewrite 100 auto
  equals CX21 • CS01 • CX21 • CS01 • CS01 • CS01


lemma-CX21-CS01-CS01-CS01-CX21-CS01=CX01-CS12-CS12-CS12-CX01-CS12 : Rel ⊢ CX21 • CS01 • CS01 • CS01 • CX21 • CS01 === CX01 • CS12 • CS12 • CS12 • CX01 • CS12
lemma-CX21-CS01-CS01-CS01-CX21-CS01=CX01-CS12-CS12-CS12-CX01-CS12 =
  equational CX21 • CS01 • CS01 • CS01 • CX21 • CS01
    by Order.general-rewrite 100 auto
  equals CX01 • CX21 • (CX01 • CS01 • CS01 • CS01) • CX21 • CS01
    by right right left lemma-CX01-CS01-CS01-CS01
  equals CX01 • CX21 • (S0 • S0 • S0 • CS01 • CX01) • CX21 • CS01
    by Order.general-rewrite 100 auto
  equals (CX01 • CX21 • S0 • S0 • S0 • CS01 • CX21) • CX01 • CS01
    by right lemma-CX01-CS01
  equals (CX01 • CX21 • S0 • S0 • S0 • CS01 • CX21) • S0 • CS01 • CS01 • CS01 • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • (CX21 • CS01 • CX21 • CS01 • CS01 • CS01) • CX01
    by right left symm lemma-CS12-CS12-CS12-CX01-CS12-CX01=CX21-CS01-CX21-CS01-CS01-CS01
  equals CX01 • (CS12 • CS12 • CS12 • CX01 • CS12 • CX01) • CX01
    by Order.general-rewrite 100 auto
  equals CX01 • CS12 • CS12 • CS12 • CX01 • CS12

lemma-aux-b1 : Rel ⊢ (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CS01 • CX21 • CS01 • CS01 • CS01 • CX21 === ε
lemma-aux-b1 =
  equational (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CS01 • CX21 • CS01 • CS01 • CS01 • CX21
    by right symm (axiom ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21)
  equals (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CS12 • CX01 • CS12 • CS12 • CS12 • CX01
    by general-assoc auto
  equals (CS01 • CS01 • CS01 • CX21 • CS01) • (CX21 • CS12) • CX01 • CS12 • CS12 • CS12 • CX01
    by right left lemma-CX21-CS12
  equals (CS01 • CS01 • CS01 • CX21 • CS01) • (S2 • CS12 ^ 3 • CX21) • CX01 • CS12 • CS12 • CS12 • CX01
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • CS01 • CX21 • CS01) • (S2 • CS12 ^ 3 • CX01) • (CX21 • CS12 • CS12 • CS12) • CX01
    by right right left lemma-CX21-CS12-CS12-CS12
  equals (CS01 • CS01 • CS01 • CX21 • CS01) • (S2 • CS12 ^ 3 • CX01) • (S2 • S2 • S2 • CS12 • CX21) • CX01
    by Order.general-rewrite 100 auto
  equals CX21 • (CX21 • CS01 • CS01 • CS01 • CX21 • CS01) • (S2 • CS12 ^ 3 • CX01) • (S2 • S2 • S2 • CS12) • CX01 • CX21
    by right left lemma-CX21-CS01-CS01-CS01-CX21-CS01=CX01-CS12-CS12-CS12-CX01-CS12
  equals CX21 • (CX01 • CS12 • CS12 • CS12 • CX01 • CS12) • (S2 • CS12 ^ 3 • CX01) • (S2 • S2 • S2 • CS12) • CX01 • CX21
    by Order.general-rewrite 100 auto
  equals ε

lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01 : Rel ⊢ CS01 • CX21 • CS01 • CX21 === CX21 • CS01 • CX21 • CS01
lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01 =
  equational CS01 • CX21 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (CX21 • CS01) • ((CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CX21 • CS01
    by right left lemma-aux-b1
  equals (CX21 • CS01) • ε • CX21 • CS01
    by general-assoc auto
  equals CX21 • CS01 • CX21 • CS01


lemma-CS01-CS01-CS01-CX21-CS01-CX21=CX01-CS12-CX01-CS12-CS12-CS12 : Rel ⊢ CS01 • CS01 • CS01 • CX21 • CS01 • CX21 === CX01 • CS12 • CX01 • CS12 • CS12 • CS12
lemma-CS01-CS01-CS01-CX21-CS01-CX21=CX01-CS12-CX01-CS12-CS12-CS12 =
  equational CS01 • CS01 • CS01 • CX21 • CS01 • CX21
    by Order.general-rewrite 122 auto
  equals CX01 • (CX01 • CS01 • CS01 • CS01) • CX21 • CS01 • CX21
    by right left lemma-CX01-CS01-CS01-CS01
  equals CX01 • (S0 • S0 • S0 • CS01 • CX01) • CX21 • CS01 • CX21
    by Order.general-rewrite 122 auto
  equals CX01 • (S0 • S0 • S0 • CS01 • CX21) • (CX01 • CS01) • CX21
    by right right left lemma-CX01-CS01
  equals CX01 • (S0 • S0 • S0 • CS01 • CX21) • (S0 • CS01 • CS01 • CS01 • CX01) • CX21
    by Order.general-rewrite 122 auto
  equals CX01 • (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CX01
    by right left symm (axiom ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21)
  equals CX01 • (CS12 • CX01 • CS12 • CS12 • CS12 • CX01) • CX01
    by Order.general-rewrite 122 auto
  equals CX01 • CS12 • CX01 • CS12 • CS12 • CS12


lemma-CX01-CS12-CS12-CS12-CX01-CS12=CX21-CS01-CS01-CS01-CX21-CS01 : Rel ⊢ CX01 • CS12 • CS12 • CS12 • CX01 • CS12 === CX21 • CS01 • CS01 • CS01 • CX21 • CS01
lemma-CX01-CS12-CS12-CS12-CX01-CS12=CX21-CS01-CS01-CS01-CX21-CS01 =
  equational CX01 • CS12 • CS12 • CS12 • CX01 • CS12
    by Order.general-rewrite 122 auto
  equals CX21 • CX01 • (CX21 • CS12 • CS12 • CS12) • CX01 • CS12
    by right right left lemma-CX21-CS12-CS12-CS12
  equals CX21 • CX01 • (S2 • S2 • S2 • CS12 • CX21) • CX01 • CS12
    by Order.general-rewrite 122 auto
  equals (CX21 • CX01 • S2 • S2 • S2 • CS12 • CX01) • CX21 • CS12
    by right lemma-CX21-CS12
  equals (CX21 • CX01 • S2 • S2 • S2 • CS12 • CX01) • S2 • CS12 ^ 3 • CX21
    by Order.general-rewrite 122 auto
  equals CX21 • (CX01 • CS12 • CX01 • CS12 • CS12 • CS12) • CX21
    by right left symm lemma-CS01-CS01-CS01-CX21-CS01-CX21=CX01-CS12-CX01-CS12-CS12-CS12
  equals CX21 • (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CX21
    by Order.general-rewrite 122 auto
  equals CX21 • CS01 • CS01 • CS01 • CX21 • CS01

lemma-aux-b2 : Rel ⊢ (CS12 • CS12 • CS12 • CX01 • CS12 • CX01) • CS12 • CX01 • CS12 • CS12 • CS12 • CX01 === ε
lemma-aux-b2 =
  equational (CS12 • CS12 • CS12 • CX01 • CS12 • CX01) • CS12 • CX01 • CS12 • CS12 • CS12 • CX01
    by right symm (symm (axiom ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21))
  equals (CS12 • CS12 • CS12 • CX01 • CS12 • CX01) • CS01 • CX21 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CS12 • CS12 • CS12 • CX01 • CS12) • (CX01 • CS01) • CX21 • CS01 • CS01 • CS01 • CX21
    by right left lemma-CX01-CS01
  equals (CS12 • CS12 • CS12 • CX01 • CS12) • (S0 • CS01 • CS01 • CS01 • CX01) • CX21 • CS01 • CS01 • CS01 • CX21
    by Order.general-rewrite 122 auto
  equals (CS12 • CS12 • CS12 • CX01 • CS12) • (S0 • CS01 ^ 3 • CX21) • (CX01 • CS01 • CS01 • CS01) • CX21
    by right right left lemma-CX01-CS01-CS01-CS01
  equals (CS12 • CS12 • CS12 • CX01 • CS12) • (S0 • CS01 ^ 3 • CX21) • (S0 • S0 • S0 • CS01 • CX01) • CX21
    by Order.general-rewrite 122 auto
  equals CX01 • (CX01 • CS12 • CS12 • CS12 • CX01 • CS12) • (S0 • CS01 ^ 3 • CX21) • (S0 • S0 • S0 • CS01) • CX21 • CX01
    by right left lemma-CX01-CS12-CS12-CS12-CX01-CS12=CX21-CS01-CS01-CS01-CX21-CS01
  equals CX01 • (CX21 • CS01 • CS01 • CS01 • CX21 • CS01) • (S0 • CS01 ^ 3 • CX21) • (S0 • S0 • S0 • CS01) • CX21 • CX01
    by Order.general-rewrite 122 auto
  equals ε

lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12 : Rel ⊢ CS12 • CX01 • CS12 • CX01 === CX01 • CS12 • CX01 • CS12
lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12 =
  equational CS12 • CX01 • CS12 • CX01
    by Order.general-rewrite 122 auto
  equals (CX01 • CS12) • ((CS12 • CS12 • CS12 • CX01 • CS12 • CX01) • CS12 • CX01 • CS12 • CS12 • CS12 • CX01) • CX01 • CS12
    by right left lemma-aux-b2
  equals (CX01 • CS12) • ε • CX01 • CS12
    by general-assoc auto
  equals CX01 • CS12 • CX01 • CS12



lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01' : Rel ⊢ CS01 • CX21 • CS01 • CX21 === (CX21 • CS01 • CX21) • CS01
lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01' =
  equational CS01 • CX21 • CS01 • CX21
    by lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01
  equals CX21 • CS01 • CX21 • CS01
    by general-assoc auto
  equals (CX21 • CS01 • CX21) • CS01

lemma-aux-d1 : Rel ⊢ CS01 • CX21 • CS01 • CS01 • CS01 • CX21 === CX21 • CS01 • CS01 • CS01 • CX21 • CS01
lemma-aux-d1 =
  equational CS01 • CX21 • CS01 • CS01 • CS01 • CX21
    by Order.general-rewrite 122 auto
  equals CS01 • (CX21 • CS01 • CX21) ^ 3
    by lemma-comm-powers 1 3 lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01'
  equals (CX21 • CS01 • CX21) ^ 3 • CS01
    by Order.general-rewrite 122 auto
  equals CX21 • CS01 • CS01 • CS01 • CX21 • CS01


lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12' : Rel ⊢ CS12 • CX01 • CS12 • CX01 === (CX01 • CS12 • CX01) • CS12
lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12' =
  equational CS12 • CX01 • CS12 • CX01
    by lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12
  equals CX01 • CS12 • CX01 • CS12
    by general-assoc auto
  equals (CX01 • CS12 • CX01) • CS12

lemma-aux-d2 : Rel ⊢ CS12 • CX01 • CS12 • CS12 • CS12 • CX01 === CX01 • CS12 • CS12 • CS12 • CX01 • CS12
lemma-aux-d2 =
  equational CS12 • CX01 • CS12 • CS12 • CS12 • CX01
    by Order.general-rewrite 100 auto
  equals CS12 • (CX01 • CS12 • CX01) ^ 3
    by lemma-comm-powers 1 3 lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12'
  equals (CX01 • CS12 • CX01) ^ 3 • CS12
    by Order.general-rewrite 100 auto
  equals CX01 • CS12 • CS12 • CS12 • CX01 • CS12


lemma-CX01-CS12-CS12-CX01-CS12-CS12=CX21-CS01-CS01-CX21-CS01-CS01 : Rel ⊢ CX01 • CS12 • CS12 • CX01 • CS12 • CS12 === CX21 • CS01 • CS01 • CX21 • CS01 • CS01
lemma-CX01-CS12-CS12-CX01-CS12-CS12=CX21-CS01-CS01-CX21-CS01-CS01 =
  equational CX01 • CS12 • CS12 • CX01 • CS12 • CS12
    by Order.general-rewrite 100 auto
  equals (CX01 • CS12 • CS12 • CS12 • CX01) • (CX01 • CS12 • CS12 • CS12 • CX01 • CS12) • CS12
    by right left symm lemma-aux-d2
  equals (CX01 • CS12 • CS12 • CS12 • CX01) • (CS12 • CX01 • CS12 • CS12 • CS12 • CX01) • CS12
    by general-assoc auto
  equals (CX01 • CS12 • CS12 • CS12 • CX01 • CS12) • CX01 • CS12 • CS12 • CS12 • CX01 • CS12
    by right symm lemma-aux-d2
  equals (CX01 • CS12 • CS12 • CS12 • CX01 • CS12) • CS12 • CX01 • CS12 • CS12 • CS12 • CX01
    by left symm lemma-aux-d2
  equals (CS12 • CX01 • CS12 • CS12 • CS12 • CX01) • CS12 • CX01 • CS12 • CS12 • CS12 • CX01
    by left axiom ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21
  equals (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CS12 • CX01 • CS12 • CS12 • CS12 • CX01
    by right axiom ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21
  equals (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CS01 • CX21 • CS01 • CS01 • CS01 • CX21
    by left lemma-aux-d1
  equals (CX21 • CS01 • CS01 • CS01 • CX21 • CS01) • CS01 • CX21 • CS01 • CS01 • CS01 • CX21
    by right lemma-aux-d1
  equals (CX21 • CS01 • CS01 • CS01 • CX21 • CS01) • CX21 • CS01 • CS01 • CS01 • CX21 • CS01
    by general-assoc auto
  equals (CX21 • CS01 • CS01 • CS01 • CX21) • (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CS01
    by right left lemma-aux-d1
  equals (CX21 • CS01 • CS01 • CS01 • CX21) • (CX21 • CS01 • CS01 • CS01 • CX21 • CS01) • CS01
    by Order.general-rewrite 122 auto
  equals CX21 • CS01 • CS01 • CX21 • CS01 • CS01

lemma-CX12-CX21-CS01-CS01-CX21-CX12=CX21-CS01-CS01-CX21-CS01-CS01 : Rel ⊢ CX12 • CX21 • CS01 • CS01 • CX21 • CX12 === CX21 • CS01 • CS01 • CX21 • CS01 • CS01
lemma-CX12-CX21-CS01-CS01-CX21-CX12=CX21-CS01-CS01-CX21-CS01-CS01 =
  equational CX12 • CX21 • CS01 • CS01 • CX21 • CX12
    by Order.general-rewrite 122 auto
  equals (CX12 • CX21 • CS01 • CX21 • CX12) • CX12 • CX21 • CS01 • CX21 • CX12
    by left symm (axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12)
  equals (CX10 • CX01 • CS12 • CX01 • CX10) • CX12 • CX21 • CS01 • CX21 • CX12
    by right symm (axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12)
  equals (CX10 • CX01 • CS12 • CX01 • CX10) • CX10 • CX01 • CS12 • CX01 • CX10
    by Order.general-rewrite 122 auto
  equals CX10 • CX01 • CS12 • CS12 • CX01 • CX10
    by axiom ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12
  equals CX01 • CS12 • CS12 • CX01 • CS12 • CS12
    by lemma-CX01-CS12-CS12-CX01-CS12-CS12=CX21-CS01-CS01-CX21-CS01-CS01
  equals CX21 • CS01 • CS01 • CX21 • CS01 • CS01


lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε : Rel ⊢ CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 === ε
lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε =
  equational CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals CS01 • CS01 • (CX12 • CX21 • CX12) • CS01 • CS01 • CX21 • CS01 • CS01 • CX12 • CX21
    by right right left lemma-Swap12-alt-def
  equals CS01 • CS01 • (CX21 • CX12 • CX21) • CS01 • CS01 • CX21 • CS01 • CS01 • CX12 • CX21
    by Order.general-rewrite 122 auto
  equals (CX21 • CX12) • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • (CX21 • CS01 • CS01 • CX21 • CS01 • CS01) • CX12 • CX21
    by right right left symm (lemma-CX12-CX21-CS01-CS01-CX21-CX12=CX21-CS01-CS01-CX21-CS01-CS01)
  equals (CX21 • CX12) • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • CX12 • CX21
    by Order.general-rewrite 122 auto
  equals ε


lemma-CS12-CS12-CX10-CX01-CS12-CS12-CX10-CX01-CS12-CS12-CX10-CX01=ε : Rel ⊢ CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01 === ε
lemma-CS12-CS12-CX10-CX01-CS12-CS12-CX10-CX01-CS12-CS12-CX10-CX01=ε =
  equational CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01 • CS12 • CS12 • CX10 • CX01
    by general-comm auto
  equals CS12 • CS12 • (CX10 • CX01 • CX10) • CS12 • CS12 • CX01 • CS12 • CS12 • CX10 • CX01
    by right right left symm lemma-Swap-alt-def
  equals CS12 • CS12 • (CX01 • CX10 • CX01) • CS12 • CS12 • CX01 • CS12 • CS12 • CX10 • CX01
    by Order.general-rewrite 100 auto
  equals (CX01 • CX10) • (CX10 • CX01 • CS12 • CS12 • CX01 • CX10) • (CX01 • CS12 • CS12 • CX01 • CS12 • CS12) • CX10 • CX01
    by right right left symm (axiom ax-CX10-CX01-CS12-CS12-CX01-CX10=CX01-CS12-CS12-CX01-CS12-CS12)
  equals (CX01 • CX10) • (CX10 • CX01 • CS12 • CS12 • CX01 • CX10) • (CX10 • CX01 • CS12 • CS12 • CX01 • CX10) • CX10 • CX01
    by Order.general-rewrite 100 auto
  equals ε

lemma-CX21-CS01-CS01-CX21-CS01=CS01-CX21-CS01-CS01-CX21 : Rel ⊢ CX21 • CS01 • CS01 • CX21 • CS01 === CS01 • CX21 • CS01 • CS01 • CX21
lemma-CX21-CS01-CS01-CX21-CS01=CS01-CX21-CS01-CS01-CX21 =
  equational CX21 • CS01 • CS01 • CX21 • CS01
    by Order.general-rewrite 100 auto
  equals (CX21 • CS01 • CX21) • CX21 • CS01 • CX21 • CS01
    by right symm (lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01)
  equals (CX21 • CS01 • CX21) • CS01 • CX21 • CS01 • CX21
    by general-assoc auto
  equals (CX21 • CS01 • CX21 • CS01) • CX21 • CS01 • CX21
    by left symm (lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01)
  equals (CS01 • CX21 • CS01 • CX21) • CX21 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • CX21 • CS01 • CS01 • CX21

lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12 : Rel ⊢ CS01 • CX21 • CS01 • CS01 • CX21 • CS01 === CX12 • CX21 • CS01 • CS01 • CX21 • CX12
lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12 =
  equational CS01 • CX21 • CS01 • CS01 • CX21 • CS01
    by right lemma-CX21-CS01-CS01-CX21-CS01=CS01-CX21-CS01-CS01-CX21
  equals CS01 • CS01 • CX21 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • (ε) • CX21 • CX12 • CS01 • CS01 • CX12 • CX21
    by right right left symm (lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε)
  equals CS01 • CS01 • (CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21) • CX21 • CX12 • CS01 • CS01 • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • ((CS01 • CS01 • CX12 • CX21 • CS01 • CS01) • CX12 • CX21 • CX12) • CX21
    by right right left right lemma-Swap12-alt-def
  equals CS01 • CS01 • ((CS01 • CS01 • CX12 • CX21 • CS01 • CS01) • CX21 • CX12 • CX21) • CX21
    by Order.general-rewrite 100 auto
  equals CX12 • CX21 • CS01 • CS01 • CX21 • CX12
  


lemma-CCZ' : Rel ⊢ CX21 • CS01 • CX12 • CX21 • CS01 • CS01 === CS01 • CS01 • S1 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • S2 • S2 • S2
lemma-CCZ' =
  equational CX21 • CS01 • CX12 • CX21 • CS01 • CS01
    by Order.general-rewrite 100 auto
  equals CX21 • CS01 • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • CX12 • CX21
    by right right left symm (lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12)
  equals CX21 • CS01 • (CS01 • CX21 • CS01 • CS01 • CX21 • CS01) • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 ^ 3 • (CS01 • CX21 • CS01 • CS01 • CX21 • CS01) • CS01 • CX21 • CS01 • CX12 • CX21
    by right left lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12
  equals CS01 ^ 3 • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • CS01 • CX21 • CS01 • CX12 • CX21
    by general-comm auto
  equals CS01 • CS01 • CX12 • (CS01 • CX21 • CS01 • CS01 • CX21 • CS01) • CX12 • CX21 • CS01 • CX12 • CX21
    by right right right left lemma-CS01-CX21-CS01-CS01-CX21-CS01=CX12-CX21-CS01-CS01-CX21-CX12
  equals CS01 • CS01 • CX12 • (CX12 • CX21 • CS01 • CS01 • CX21 • CX12) • CX12 • CX21 • CS01 • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals CS01 • CS01 • (CX21 • CS01 • CS01) • CS01 • CX12 • CX21
    by general-comm auto
  equals CS01 • CS01 • CX21 • CS01 • CX12 • CS01 • CS01 • CX21
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • CX21 • CS01) • (CX12 • S2 • S1 • CS12 • CS12) • S1 ^ 2 • CS12 • CS12 • CS01 • CS01 • S1 • CX21 • S2 • S2 • S2
    by right left lemma-S2-CX12' reversed
  equals (CS01 • CS01 • CX21 • CS01) • (S2 • CX12) • S1 ^ 2 • CS12 • CS12 • CS01 • CS01 • S1 • CX21 • S2 • S2 • S2
    by general-comm auto
  equals (CS01 • CS01 • CX21 • CS01 • S2 • S1 ^ 2) • (CX12 • CS12 • CS12) • CS01 • CS01 • S1 • CX21 • S2 • S2 • S2
    by right left lemma-CX12-CZ12
  equals (CS01 • CS01 • CX21 • CS01 • S2 • S1 ^ 2) • (CS12 • CS12 • S1 • S1 • CX12) • CS01 • CS01 • S1 • CX21 • S2 • S2 • S2
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • CX21 • CS01 • S2) • CS12 • CS12 • CX12 • CS01 • CS01 • S1 • CX21 • S2 • S2 • S2
    by general-comm auto
  equals CS01 • CS01 • (CX21 • S1 • S2 • CS12 • CS12) • CX12 • CS01 • CS01 • CS01 • CX21 • S2 • S2 • S2
    by right right left lemma-S1-CX21' reversed
  equals CS01 • CS01 • (S1 • CX21) • CX12 • CS01 • CS01 • CS01 • CX21 • S2 • S2 • S2
    by general-comm auto
  equals CS01 • CS01 • S1 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • S2 • S2 • S2

lemma-CCZ : Rel ⊢ CCZ === CS01 • CS01 • CS01 • CX12 • S1 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • S2 • S2 • S2 • CS01 • CX12 • CX21
lemma-CCZ =
  equational CCZ
    by general-assoc auto
  equals CS01 • CX12 • (CX21 • CS01 • CX12 • CX21 • CS01 • CS01) • CS01 • CX12 • CX21
    by right right left lemma-CCZ'
  equals CS01 • CX12 • (CS01 • CS01 • S1 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • S2 • S2 • S2) • CS01 • CX12 • CX21
    by general-comm auto
  equals CS01 • CS01 • CS01 • CX12 • S1 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • S2 • S2 • S2 • CS01 • CX12 • CX21

lemma-X-CCZ : Rel ⊢ X0 • CCZ === CS12 • CS12 • CCZ • X0
lemma-X-CCZ =
  equational X0 • CCZ
    by general-assoc auto
  equals (X0 • CS01) • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by left axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
  equals (CS01 • CS01 • CS01 • X0 • S1) • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (X0 • CS01) • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by right left axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • X0 • S1) • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (X0 • CS01) • CS01 • CS01 • CX12 • CX21
    by right right left axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • X0 • S1) • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1) • (X0 • CS01) • CS01 • CX12 • CX21
    by right right right left axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1) • (CS01 • CS01 • CS01 • X0 • S1) • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1) • (CS01 • CS01 • CS01 • S1) • (X0 • CS01) • CX12 • CX21
    by right right right right left axiom ax-X0-CS01=CS01-CS01-CS01-X0-S1
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1) • (CS01 • CS01 • CS01 • S1) • (CS01 • CS01 • CS01 • X0 • S1) • CX12 • CX21
    by Order.general-rewrite 100 auto
  equals ((CS01 • CS01 • CS01 • S1 • CX12 • CX21) • (CS01 • CS01 • CS01 • S1 • CX12 • CX21) • ( S1) • ( S1) • (CS01 • S1) • CX12 • CX21) • X0
    by general-comm auto
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12) • (S1 • K1 • CS12 • CS12 • K1) • iI • S1 • S1 • CS01 • S1 • CX12 • CX21 • X0
    by right left lemma-S1-CX21
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12) • (K1 • CS12 • CS12 • K1 • S1 • S2 • CS12 • CS12) • iI • S1 • S1 • CS01 • S1 • CX12 • CX21 • X0
    by Order.general-rewrite 100 auto
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12) • (CX21 • S2 • CS12 • CS12) • CS01 • CX12 • CX21 • X0
    by general-comm auto
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • CS12 • CS12) • S2 • CS01 • CX12 • CX21 • X0
    by right left lemma-CX12-CX21-CZ12
  equals (CS01 • CS01 • CS01 • S1 • CX12 • CX21 • CS01 • CS01 • CS01) • (CS12 • CS12 • CX12 • CX21 • S1 • S1) • S2 • CS01 • CX12 • CX21 • X0
    by general-comm auto
  equals (CS01 • CS01 • CS01 • S1) • (CX12 • CX21 • CS12 • CS12) • CS01 • CS01 • CS01 • (CX12 • CX21 • S1 • S1) • S2 • CS01 • CX12 • CX21 • X0
    by right left lemma-CX12-CX21-CZ12
  equals (CS01 • CS01 • CS01 • S1) • (CS12 • CS12 • CX12 • CX21 • S1 • S1) • CS01 • CS01 • CS01 • (CX12 • CX21 • S1 • S1) • S2 • CS01 • CX12 • CX21 • X0
    by general-comm auto
   equals (CS12 • CS12 • CS01 • CS01 • CS01 • CX12 • S1 • CX21 • CS01 • CS01 • CS01 • CX12) • (S1 • S1 • CX21) • S1 • S1 • S2 • CS01 • CX12 • CX21 • X0
    by right left lemma-S1-S1-CX21
   equals (CS12 • CS12 • CS01 • CS01 • CS01 • CX12 • S1 • CX21 • CS01 • CS01 • CS01 • CX12) • (CX21 • S1 • S1 • S2 • S2) • S1 • S1 • S2 • CS01 • CX12 • CX21 • X0
    by Order.general-rewrite 100 auto
   equals CS12 • CS12 • (CS01 • CS01 • CS01 • CX12 • S1 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • S2 • S2 • S2 • CS01 • CX12 • CX21) • X0
    by right right left symm lemma-CCZ
  equals CS12 • CS12 • CCZ • X0










lemma-CX10-CS01 : Rel ⊢ CX10 • CS01 === S1 • CS01 ^ 3 • CX10
lemma-CX10-CS01 =
  equational CX10 • CS01
    by general-comm auto
  equals iI • K0 • CS01 • CS01 • K0 • CS01
    by right lemma-K0-CS01-CS01-K0-CS01=S1-CS01-CS01-CS01-K0-CS01-CS01-K0
  equals iI • S1 • CS01 • CS01 • CS01 • K0 • CS01 • CS01 • K0
    by general-comm auto
  equals S1 • CS01 ^ 3 • CX10

lemma-scomm1t : Rel ⊢ CX21 • CS12 === S2 • CS12 ^ 3 • CX21
lemma-scomm1t =
  equational CX21 • CS12
    by general-comm auto
  equals iI • K1 • CS12 • CS12 • K1 • CS12
    by right lemma-K1-CS12-CS12-K1-CS12=S2-CS12-CS12-CS12-K1-CS12-CS12-K1
  equals iI • S2 • CS12 • CS12 • CS12 • K1 • CS12 • CS12 • K1
    by general-comm auto
  equals S2 • CS12 ^ 3 • CX21


lemma-CX10-CS01a : Rel ⊢ CX10 • CS01 ^ 3 === S1 ^ 3 • CS01 • CX10
lemma-CX10-CS01a =
  equational CX10 • CS01 ^ 3
    by general-assoc auto
  equals (CX10 • CS01) • CS01 ^ 2
    by left lemma-CX10-CS01
  equals ( S1 • CS01 ^ 3 • CX10) • CS01 ^ 2
    by general-assoc auto
  equals ( S1 • CS01 ^ 3) • (CX10 • CS01) • CS01
    by right left lemma-CX10-CS01
  equals ( S1 • CS01 ^ 3) • (S1 • CS01 ^ 3 • CX10) • CS01
    by general-assoc auto
  equals ( S1 • CS01 ^ 3) • (S1 • CS01 ^ 3) • CX10 • CS01
    by right right lemma-CX10-CS01
  equals ( S1 • CS01 ^ 3) • (S1 • CS01 ^ 3) • S1 • CS01 ^ 3 • CX10
    by Order.general-rewrite 100 auto
  equals S1 ^ 3 • CS01 • CX10


lemma-CX21-CS12^3 : Rel ⊢ CX21 • CS12 ^ 3 === S2 ^ 3 • CS12 • CX21
lemma-CX21-CS12^3 =
  equational CX21 • CS12 ^ 3
    by general-assoc auto
  equals (CX21 • CS12) • CS12 ^ 2
    by left lemma-scomm1t
  equals ( S2 • CS12 ^ 3 • CX21) • CS12 ^ 2
    by general-assoc auto
  equals ( S2 • CS12 ^ 3) • (CX21 • CS12) • CS12
    by right left lemma-scomm1t
  equals ( S2 • CS12 ^ 3) • (S2 • CS12 ^ 3 • CX21) • CS12
    by general-assoc auto
  equals ( S2 • CS12 ^ 3) • (S2 • CS12 ^ 3) • CX21 • CS12
    by right right lemma-scomm1t
  equals ( S2 • CS12 ^ 3) • (S2 • CS12 ^ 3) • S2 • CS12 ^ 3 • CX21
    by Order.general-rewrite 211 auto
  equals S2 ^ 3 • CS12 • CX21


lemma-CX01-CS01-f : Rel ⊢ CX01 • CS01 === S0 • CS01 ^ 3 • CX01
lemma-CX01-CS01-f =
  equational CX01 • CS01
    by general-comm auto
  equals iI • K1 • CS01 • CS01 • K1 • CS01
    by right lemma-K1-CS01-CS01-K1-CS01=S0-CS01-CS01-CS01-K1-CS01-CS01-K1
  equals iI • S0 • CS01 • CS01 • CS01 • K1 • CS01 • CS01 • K1
    by general-comm auto
  equals S0 • CS01 ^ 3 • CX01

lemma-CX12-CS12 : Rel ⊢ CX12 • CS12 === S1 • CS12 ^ 3 • CX12
lemma-CX12-CS12 =
  equational CX12 • CS12
    by general-comm auto
  equals iI • K2 • CS12 • CS12 • K2 • CS12
    by right lemma-K2-CS12-CS12-K2-CS12=S1-CS12-CS12-CS12-K2-CS12-CS12-K2
  equals iI • S1 • CS12 • CS12 • CS12 • K2 • CS12 • CS12 • K2
    by general-comm auto
  equals S1 • CS12 ^ 3 • CX12


lemma-CX10-CS01^3 : Rel ⊢ CX01 • CS01 ^ 3 === S0 ^ 3 • CS01 • CX01
lemma-CX10-CS01^3 =
  equational CX01 • CS01 ^ 3
    by general-assoc auto
  equals (CX01 • CS01) • CS01 ^ 2
    by left lemma-CX01-CS01-f
  equals ( S0 • CS01 ^ 3 • CX01) • CS01 ^ 2
    by general-assoc auto
  equals ( S0 • CS01 ^ 3) • (CX01 • CS01) • CS01
    by right left lemma-CX01-CS01-f
  equals ( S0 • CS01 ^ 3) • (S0 • CS01 ^ 3 • CX01) • CS01
    by general-assoc auto
  equals ( S0 • CS01 ^ 3) • (S0 • CS01 ^ 3) • CX01 • CS01
    by right right lemma-CX01-CS01-f
  equals ( S0 • CS01 ^ 3) • (S0 • CS01 ^ 3) • S0 • CS01 ^ 3 • CX01
    by Order.general-rewrite 100 auto
  equals S0 ^ 3 • CS01 • CX01


lemma-scomm1a' : Rel ⊢ CX12 • CS12 ^ 3 === S1 ^ 3 • CS12 • CX12
lemma-scomm1a' =
  equational CX12 • CS12 ^ 3
    by general-assoc auto
  equals (CX12 • CS12) • CS12 ^ 2
    by left lemma-CX12-CS12
  equals ( S1 • CS12 ^ 3 • CX12) • CS12 ^ 2
    by general-assoc auto
  equals ( S1 • CS12 ^ 3) • (CX12 • CS12) • CS12
    by right left lemma-CX12-CS12
  equals ( S1 • CS12 ^ 3) • (S1 • CS12 ^ 3 • CX12) • CS12
    by general-assoc auto
  equals ( S1 • CS12 ^ 3) • (S1 • CS12 ^ 3) • CX12 • CS12
    by right right lemma-CX12-CS12
  equals ( S1 • CS12 ^ 3) • (S1 • CS12 ^ 3) • S1 • CS12 ^ 3 • CX12
    by Order.general-rewrite 211 auto
  equals S1 ^ 3 • CS12 • CX12


lemma-scomm1 : Rel ⊢ CX01 • CX10 • CS01 === S1 • CS01 ^ 3 • CX01 • CX10
lemma-scomm1 =
  equational CX01 • CX10 • CS01
    by general-comm auto
  equals (CX01) • CX10 • CS01
    by right lemma-CX10-CS01
  equals (CX01) • S1 • CS01 ^ 3 • CX10
    by general-assoc auto
  equals (CX01 • S1) • CS01 ^ 3 • CX10
    by left lemma-CX01-S1
  equals (S0 • S1 • CS01 • CS01 • CX01) • CS01 ^ 3 • CX10
    by general-assoc auto
  equals (S0 • S1 • CS01 • CS01) • (CX01 • CS01 ^ 3) • CX10
    by right left lemma-CX10-CS01^3
  equals (S0 • S1 • CS01 • CS01) • (S0 ^ 3 • CS01 • CX01) • CX10
    by Order.general-rewrite 100 auto
  equals S1 • CS01 ^ 3 • CX01 • CX10




lemma-scomm2 : Rel ⊢ CX12 • CX21 • CS12 === S2 • CS12 ^ 3 • CX12 • CX21
lemma-scomm2 =
  equational CX12 • CX21 • CS12
    by general-comm auto
  equals (CX12) • CX21 • CS12
    by right lemma-scomm1t
  equals (CX12) • S2 • CS12 ^ 3 • CX21
    by general-assoc auto
  equals (CX12 • S2) • CS12 ^ 3 • CX21
    by left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • CX12) • CS12 ^ 3 • CX21
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12) • (CX12 • CS12 ^ 3) • CX21
    by right left lemma-scomm1a'
  equals (S1 • S2 • CS12 • CS12) • (S1 ^ 3 • CS12 • CX12) • CX21
    by Order.general-rewrite 211 auto
  equals S2 • CS12 ^ 3 • CX12 • CX21


lemma-scomm2r : Rel ⊢ CX21 • CX12 • CS12 === S1 • CS12 ^ 3 • CX21 • CX12
lemma-scomm2r =
  equational CX21 • CX12 • CS12
    by right lemma-CX12-CS12
  equals (CX21) • S1 • CS12 ^ 3 • CX12
    by general-assoc auto
  equals (CX21 • S1) • CS12 ^ 3 • CX12
    by left lemma-CX21-S1
  equals (S2 • S1 • CS12 • CS12 • CX21) • CS12 ^ 3 • CX12
    by general-assoc auto
  equals (S2 • S1 • CS12 • CS12) • (CX21 • CS12 ^ 3) • CX12
    by right left lemma-CX21-CS12^3
  equals (S2 • S1 • CS12 • CS12) • (S2 ^ 3 • CS12 • CX21) • CX12
    by Order.general-rewrite 211 auto
  equals S1 • CS12 ^ 3 • CX21 • CX12


lemma-CX10-S0^3 : Rel ⊢ CX10 • S0 ^ 3 === S1 ^ 3 • S0 ^ 3 • CS01 ^ 2 • CX10
lemma-CX10-S0^3 =
  equational CX10 • S0 ^ 3
    by general-assoc auto
  equals (CX10 • S0) • S0 ^ 2
    by left lemma-CX10-S0
  equals (S1 • S0 • CS01 • CS01 • CX10) • S0 ^ 2
    by general-assoc auto
  equals (S1 • S0 • CS01 • CS01) • (CX10 • S0) • S0
    by right left lemma-CX10-S0
  equals (S1 • S0 • CS01 • CS01) • (S1 • S0 • CS01 • CS01 • CX10) • S0
    by general-assoc auto
  equals (S1 • S0 • CS01 • CS01) • (S1 • S0 • CS01 • CS01) • CX10 • S0
    by right right lemma-CX10-S0
  equals (S1 • S0 • CS01 • CS01) • (S1 • S0 • CS01 • CS01) • S1 • S0 • CS01 • CS01 • CX10
    by Order.general-rewrite 100 auto
  equals S1 ^ 3 • S0 ^ 3 • CS01 ^ 2 • CX10


lemma-CX21-S1^3 : Rel ⊢ CX21 • S1 ^ 3 === S2 ^ 3 • S1 ^ 3 • CS12 ^ 2 • CX21
lemma-CX21-S1^3 =
  equational CX21 • S1 ^ 3
    by general-assoc auto
  equals (CX21 • S1) • S1 ^ 2
    by left lemma-CX21-S1
  equals (S2 • S1 • CS12 • CS12 • CX21) • S1 ^ 2
    by general-assoc auto
  equals (S2 • S1 • CS12 • CS12) • (CX21 • S1) • S1
    by right left lemma-CX21-S1
  equals (S2 • S1 • CS12 • CS12) • (S2 • S1 • CS12 • CS12 • CX21) • S1
    by general-assoc auto
  equals (S2 • S1 • CS12 • CS12) • (S2 • S1 • CS12 • CS12) • CX21 • S1
    by right right lemma-CX21-S1
  equals (S2 • S1 • CS12 • CS12) • (S2 • S1 • CS12 • CS12) • S2 • S1 • CS12 • CS12 • CX21
    by Order.general-rewrite 211 auto
  equals S2 ^ 3 • S1 ^ 3 • CS12 ^ 2 • CX21


lemma-CX12-S2^3 : Rel ⊢ CX12 • S2 ^ 3 === S1 ^ 3 • S2 ^ 3 • CS12 ^ 2 • CX12
lemma-CX12-S2^3 =
  equational CX12 • S2 ^ 3
    by general-assoc auto
  equals (CX12 • S2) • S2 ^ 2
    by left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • CX12) • S2 ^ 2
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12) • (CX12 • S2) • S2
    by right left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12 • CX12) • S2
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • CX12 • S2
    by right right lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12) • (S1 • S2 • CS12 • CS12) • S1 • S2 • CS12 • CS12 • CX12
    by Order.general-rewrite 122 auto
  equals S1 ^ 3 • S2 ^ 3 • CS12 ^ 2 • CX12


lemma-scomm1a : Rel ⊢ CX10 • CX01 • CS12 • CX01 • CX10 • CS01 === CS01 • CX10 • CX01 • CS12 • CX01 • CX10
lemma-scomm1a =
  equational CX10 • CX01 • CS12 • CX01 • CX10 • CS01
    by right right right lemma-scomm1
  equals CX10 • CX01 • CS12 • S1 • CS01 ^ 3 • CX01 • CX10
    by general-comm auto
  equals CX10 • (CX01 • S1) • CS12 • CS01 ^ 3 • CX01 • CX10
    by right left lemma-CX01-S1
  equals CX10 • (S0 • S1 • CS01 • CS01 • CX01) • CS12 • CS01 ^ 3 • CX01 • CX10
    by general-assoc auto
  equals (CX10 • S0) • (S1 • CS01 • CS01 • CX01) • CS12 • CS01 ^ 3 • CX01 • CX10
    by left lemma-CX10-S0
  equals (S1 • S0 • CS01 • CS01 • CX10) • (S1 • CS01 • CS01 • CX01) • CS12 • CS01 ^ 3 • CX01 • CX10
    by general-comm auto
  equals (S1 • S0 • CS01 • CS01 • S1) • (CX10 • CS01) • (CS01 • CX01) • CS12 • CS01 ^ 3 • CX01 • CX10
    by right left lemma-CX10-CS01
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3 • CX10) • (CS01 • CX01) • CS12 • CS01 ^ 3 • CX01 • CX10
    by general-assoc auto
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3) • (CX10 • CS01) • CX01 • CS12 • CS01 ^ 3 • CX01 • CX10
    by right right left lemma-CX10-CS01
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3) • (S1 • CS01 ^ 3 • CX10) • CX01 • CS12 • CS01 ^ 3 • CX01 • CX10
    by general-comm auto
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3 • S1 • CS01 ^ 3 • CX10) • (CX01 • CS01 ^ 3) • CS12 • CX01 • CX10
    by right right left lemma-CX10-CS01^3
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3 • S1 • CS01 ^ 3 • CX10) • (S0 ^ 3 • CS01 • CX01) • CS12 • CX01 • CX10
    by general-assoc auto
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3 • S1 • CS01 ^ 3) • (CX10 • S0 ^ 3) • CS01 • CX01 • CS12 • CX01 • CX10
    by right right left lemma-CX10-S0^3
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3 • S1 • CS01 ^ 3) • (S1 ^ 3 • S0 ^ 3 • CS01 ^ 2 • CX10) • CS01 • CX01 • CS12 • CX01 • CX10
    by general-assoc auto
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3 • S1 • CS01 ^ 3) • (S1 ^ 3 • S0 ^ 3 • CS01 ^ 2) • (CX10 • CS01) • CX01 • CS12 • CX01 • CX10
    by right right right left lemma-CX10-CS01
  equals (S1 • S0 • CS01 • CS01 • S1) • (S1 • CS01 ^ 3 • S1 • CS01 ^ 3) • (S1 ^ 3 • S0 ^ 3 • CS01 ^ 2) • (S1 • CS01 ^ 3 • CX10) • CX01 • CS12 • CX01 • CX10
    by Order.general-rewrite 100 auto
  equals CS01 • CX10 • CX01 • CS12 • CX01 • CX10



lemma-scomm1a3 : Rel ⊢ CX10 • CX01 • CS12 • CX01 • CX10 • CS01 • CS01 • CS01 === CS01 • CS01 • CS01 • CX10 • CX01 • CS12 • CX01 • CX10
lemma-scomm1a3 =
  equational CX10 • CX01 • CS12 • CX01 • CX10 • CS01 • CS01 • CS01
    by general-assoc auto
  equals (CX10 • CX01 • CS12 • CX01 • CX10 • CS01) • CS01 • CS01
    by left lemma-scomm1a
  equals (CS01 • CX10 • CX01 • CS12 • CX01 • CX10) • CS01 • CS01
    by general-assoc auto
  equals CS01 • (CX10 • CX01 • CS12 • CX01 • CX10 • CS01) • CS01
    by right left lemma-scomm1a
  equals CS01 • (CS01 • CX10 • CX01 • CS12 • CX01 • CX10) • CS01
    by general-assoc auto
  equals CS01 • CS01 • (CX10 • CX01 • CS12 • CX01 • CX10 • CS01)
    by right right lemma-scomm1a
  equals CS01 • CS01 • CS01 • CX10 • CX01 • CS12 • CX01 • CX10




lemma-scomm2at : Rel ⊢ CX12 • CX21 • CS01 • CX21 • CX12 • CS12 === CS12 • CX12 • CX21 • CS01 • CX21 • CX12
lemma-scomm2at =
  equational CX12 • CX21 • CS01 • CX21 • CX12 • CS12
    by right right right lemma-scomm2r
  equals CX12 • CX21 • CS01 • S1 • CS12 ^ 3 • CX21 • CX12
    by general-comm auto
  equals CX12 • (CX21 • S1) • CS01 • CS12 ^ 3 • CX21 • CX12
    by right left lemma-CX21-S1
  equals CX12 • (S2 • S1 • CS12 • CS12 • CX21) • CS01 • CS12 ^ 3 • CX21 • CX12
    by general-assoc auto
  equals (CX12 • S2) • (S1 • CS12 • CS12 • CX21) • CS01 • CS12 ^ 3 • CX21 • CX12
    by left lemma-CX12-S2
  equals (S1 • S2 • CS12 • CS12 • CX12) • (S1 • CS12 • CS12 • CX21) • CS01 • CS12 ^ 3 • CX21 • CX12
    by general-comm auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (CX12 • CS12) • (CS12 • CX21) • CS01 • CS12 ^ 3 • CX21 • CX12
    by right left lemma-CX12-CS12
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3 • CX12) • (CS12 • CX21) • CS01 • CS12 ^ 3 • CX21 • CX12
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3) • (CX12 • CS12) • CX21 • CS01 • CS12 ^ 3 • CX21 • CX12
    by right right left lemma-CX12-CS12
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3) • (S1 • CS12 ^ 3 • CX12) • CX21 • CS01 • CS12 ^ 3 • CX21 • CX12
    by general-comm auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3 • S1 • CS12 ^ 3 • CX12) • (CX21 • CS12 ^ 3) • CS01 • CX21 • CX12
    by right right left lemma-CX21-CS12^3
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3 • S1 • CS12 ^ 3 • CX12) • (S2 ^ 3 • CS12 • CX21) • CS01 • CX21 • CX12
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3 • S1 • CS12 ^ 3) • (CX12 • S2 ^ 3) • CS12 • CX21 • CS01 • CX21 • CX12
    by right right left lemma-CX12-S2^3
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3 • S1 • CS12 ^ 3) • (S1 ^ 3 • S2 ^ 3 • CS12 ^ 2 • CX12) • CS12 • CX21 • CS01 • CX21 • CX12
    by general-assoc auto
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3 • S1 • CS12 ^ 3) • (S1 ^ 3 • S2 ^ 3 • CS12 ^ 2) • (CX12 • CS12) • CX21 • CS01 • CX21 • CX12
    by right right right left lemma-CX12-CS12
  equals (S1 • S2 • CS12 • CS12 • S1) • (S1 • CS12 ^ 3 • S1 • CS12 ^ 3) • (S1 ^ 3 • S2 ^ 3 • CS12 ^ 2) • (S1 • CS12 ^ 3 • CX12) • CX21 • CS01 • CX21 • CX12
    by Order.general-rewrite 211 auto
  equals CS12 • CX12 • CX21 • CS01 • CX21 • CX12

lemma-scomm2a3t : Rel ⊢ CX12 • CX21 • CS01 • CX21 • CX12 • CS12 • CS12 • CS12 === CS12 • CS12 • CS12 • CX12 • CX21 • CS01 • CX21 • CX12
lemma-scomm2a3t =
  equational CX12 • CX21 • CS01 • CX21 • CX12 • CS12 • CS12 • CS12
    by general-assoc auto
  equals (CX12 • CX21 • CS01 • CX21 • CX12 • CS12) • CS12 • CS12
    by left lemma-scomm2at
  equals (CS12 • CX12 • CX21 • CS01 • CX21 • CX12) • CS12 • CS12
    by general-assoc auto
  equals CS12 • (CX12 • CX21 • CS01 • CX21 • CX12 • CS12) • CS12
    by right left lemma-scomm2at
  equals CS12 • (CS12 • CX12 • CX21 • CS01 • CX21 • CX12) • CS12
    by general-assoc auto
  equals CS12 • CS12 • (CX12 • CX21 • CS01 • CX21 • CX12 • CS12)
    by right right lemma-scomm2at
  equals CS12 • CS12 • CS12 • CX12 • CX21 • CS01 • CX21 • CX12


lemma-CCZ-alt-def : Rel ⊢ CCZ === CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
lemma-CCZ-alt-def =
  equational CCZ
    by refl
  equals CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals CS01 • (CX12 • CX21 • CX12) • CS01 • CX21 • CX12 • CS01 • CS01 • CS01 • CX21
    by right left lemma-Swap12-alt-def
  equals CS01 • (CX21 • CX12 • CX21) • CS01 • CX21 • CX12 • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals CS01 • CX21 • (CX12 • CX21 • CS01 • CX21 • CX12) • CS01 • CS01 • CS01 • CX21
    by right right left symm (axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12)
  equals CS01 • CX21 • (CX10 • CX01 • CS12 • CX01 • CX10) • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals CS01 • CX21 • (CX10 • CX01 • CS12 • CX01 • CX10 • CS01 • CS01 • CS01) • CX21
    by right right left lemma-scomm1a3
  equals CS01 • CX21 • (CS01 • CS01 • CS01 • CX10 • CX01 • CS12 • CX01 • CX10) • CX21
    by general-assoc auto
  equals (CS01 • CX21 • CS01 • CS01 • CS01) • (CX10 • CX01 • CS12 • CX01 • CX10) • CX21
    by right left axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12
  equals (CS01 • CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • CS01 • CX21 • CX12) • CX21
    by general-assoc auto
  equals (CS01 • CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • CS01) • CX21 • CX12 • CX21
    by right right symm lemma-Swap12-alt-def
  equals (CS01 • CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • CS01) • CX12 • CX21 • CX12
    by general-comm auto
  equals (CS01 • CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • CX12) • CS01 • CX21 • CX12
    by right left lemma-Swap12-alt-def
  equals (CS01 • CX21 • CS01 • CS01 • CS01) • (CX21 • CX12 • CX21) • CS01 • CX21 • CX12
    by general-assoc auto
  equals (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CX12 • CX21 • CS01 • CX21 • CX12
    by right symm (axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12)
  equals (CS01 • CX21 • CS01 • CS01 • CS01 • CX21) • CX10 • CX01 • CS12 • CX01 • CX10
    by left symm (axiom ax-CS12-CX01-CS12-CS12-CS12-CX01=CS01-CX21-CS01-CS01-CS01-CX21)
  equals (CS12 • CX01 • CS12 • CS12 • CS12 • CX01) • CX10 • CX01 • CS12 • CX01 • CX10
    by general-assoc auto
  equals (CS12 • CX01 • CS12 • CS12 • CS12) • (CX01 • CX10 • CX01) • CS12 • CX01 • CX10
    by right left lemma-Swap-alt-def
  equals (CS12 • CX01 • CS12 • CS12 • CS12) • (CX10 • CX01 • CX10) • CS12 • CX01 • CX10
    by general-comm auto
  equals (CS12 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01 • CS12) • CX10 • CX01 • CX10
    by right lemma-Swap-alt-def reversed
  equals (CS12 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01 • CS12) • CX01 • CX10 • CX01
    by general-assoc auto
  equals (CS12 • CX01 • CS12 • CS12 • CS12) • (CX10 • CX01 • CS12 • CX01 • CX10) • CX01
    by right left axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12
  equals (CS12 • CX01 • CS12 • CS12 • CS12) • (CX12 • CX21 • CS01 • CX21 • CX12) • CX01
    by general-assoc auto
  equals (CS12 • CX01) • (CS12 • CS12 • CS12 • CX12 • CX21 • CS01 • CX21 • CX12) • CX01
    by right left  symm lemma-scomm2a3t
  equals (CS12 • CX01) • (CX12 • CX21 • CS01 • CX21 • CX12 • CS12 • CS12 • CS12) • CX01
    by general-assoc auto
  equals (CS12 • CX01) • (CX12 • CX21 • CS01 • CX21 • CX12) • (CS12 • CS12 • CS12) • CX01
    by right left symm (axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12)
  equals (CS12 • CX01) • (CX10 • CX01 • CS12 • CX01 • CX10) • (CS12 • CS12 • CS12) • CX01
    by general-comm auto
  equals CS12 • (CX01 • CX10 • CX01) • CS12 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
    by right left lemma-Swap-alt-def
  equals CS12 • (CX10 • CX01 • CX10) • CS12 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01
    by general-comm auto
  equals CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01


lemma-c0 : Rel ⊢ CX21 • CX12 • CX21 • CS01 • CX21 • CX12 === CX12 • CX21 • CS01 • CX21 • CX12 • CX21
lemma-c0 =
  equational CX21 • CX12 • CX21 • CS01 • CX21 • CX12
    by general-assoc auto
  equals (CX21 • CX12 • CX21) • CS01 • CX21 • CX12
    by left symm lemma-Swap12-alt-def
  equals (CX12 • CX21 • CX12) • CS01 • CX21 • CX12
    by general-comm auto
  equals (CX12 • CX21 • CS01) • CX12 • CX21 • CX12
    by right lemma-Swap12-alt-def
  equals (CX12 • CX21 • CS01) • CX21 • CX12 • CX21
    by general-assoc auto
  equals CX12 • CX21 • CS01 • CX21 • CX12 • CX21


lemma-d0 : Rel ⊢ CS01 • CS01 • CS01 • CX21 • CS01 • CX21 === CX21 • CS01 • CX21 • CS01 • CS01 • CS01
lemma-d0 =
  equational CS01 • CS01 • CS01 • CX21 • CS01 • CX21
    by right right lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01
  equals CS01 • CS01 • CX21 • CS01 • CX21 • CS01
    by general-assoc auto
  equals CS01 • (CS01 • CX21 • CS01 • CX21) • CS01
    by right left lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01
  equals CS01 • (CX21 • CS01 • CX21 • CS01) • CS01
    by general-assoc auto
  equals (CS01 • CX21 • CS01 • CX21) • CS01 • CS01
    by left lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01
  equals (CX21 • CS01 • CX21 • CS01) • CS01 • CS01
    by general-assoc auto
  equals CX21 • CS01 • CX21 • CS01 • CS01 • CS01


lemma-d1 : Rel ⊢ CS01 • CX12 • CX21 • CS01 • CX21 • CX12 === CX12 • CX21 • CS01 • CX21 • CX12 • CS01
lemma-d1 =
  equational CS01 • CX12 • CX21 • CS01 • CX21 • CX12
    by general-comm auto
  equals CX12 • (CS01 • CX21 • CS01 • CX21) • CX12
    by right left lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01
  equals CX12 • (CX21 • CS01 • CX21 • CS01) • CX12
    by general-comm auto
  equals CX12 • CX21 • CS01 • CX21 • CX12 • CS01


lemma-d2 : Rel ⊢ CS01 • CS01 • CS01 • CX12 • CX21 • CS01 • CX21 • CX12 === CX12 • CX21 • CS01 • CX21 • CX12 • CS01 • CS01 • CS01
lemma-d2 =
  equational CS01 • CS01 • CS01 • CX12 • CX21 • CS01 • CX21 • CX12
    by right right lemma-d1
  equals CS01 • CS01 • CX12 • CX21 • CS01 • CX21 • CX12 • CS01
    by general-assoc auto
  equals CS01 • (CS01 • CX12 • CX21 • CS01 • CX21 • CX12) • CS01
    by right left lemma-d1
  equals CS01 • (CX12 • CX21 • CS01 • CX21 • CX12 • CS01) • CS01
    by general-assoc auto
  equals (CS01 • CX12 • CX21 • CS01 • CX21 • CX12) • CS01 • CS01
    by left lemma-d1
  equals (CX12 • CX21 • CS01 • CX21 • CX12 • CS01) • CS01 • CS01
    by general-assoc auto
  equals CX12 • CX21 • CS01 • CX21 • CX12 • CS01 • CS01 • CS01


lemma-c1 : Rel ⊢ (CX21 • CS01 • CS01 • CS01 • CX21) • (CX12 • CX21 • CS01 • CX21 • CX12) === (CX12 • CX21 • CS01 • CX21 • CX12) • (CX21 • CS01 • CS01 • CS01 • CX21)
lemma-c1 =
  equational (CX21 • CS01 • CS01 • CS01 • CX21) • (CX12 • CX21 • CS01 • CX21 • CX12)
    by general-assoc auto
  equals (CX21 • CS01 • CS01 • CS01) • (CX21 • CX12 • CX21) • CS01 • CX21 • CX12
    by right left symm lemma-Swap12-alt-def
  equals (CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • CX12) • CS01 • CX21 • CX12
    by general-comm auto
  equals (CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • CS01) • CX12 • CX21 • CX12
    by right lemma-Swap12-alt-def
  equals (CX21 • CS01 • CS01 • CS01 • CX12 • CX21 • CS01) • CX21 • CX12 • CX21
    by general-assoc auto
  equals CX21 • (CS01 • CS01 • CS01 • CX12 • CX21 • CS01 • CX21 • CX12) • CX21
    by right left lemma-d2
  equals CX21 • (CX12 • CX21 • CS01 • CX21 • CX12 • CS01 • CS01 • CS01) • CX21
    by general-assoc auto
  equals (CX21 • CX12 • CX21 • CS01 • CX21 • CX12) • CS01 • CS01 • CS01 • CX21
    by left lemma-c0
  equals (CX12 • CX21 • CS01 • CX21 • CX12 • CX21) • CS01 • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CX12 • CX21 • CS01 • CX21 • CX12) • (CX21 • CS01 • CS01 • CS01 • CX21)

lemma-e1 : Rel ⊢ CS01 • CX21 • CS01 • CS01 • CX21 === CX21 • CS01 • CS01 • CX21 • CS01
lemma-e1 =
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
  equals CX21 • CS01 • CS01 • CX21 • CS01

lemma-CCZ-CCZ=ε : Rel ⊢ CCZ • CCZ === ε
lemma-CCZ-CCZ=ε =
  equational CCZ • CCZ
    by refl
  equals (CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21) • CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01) • (CX12 • CX21 • CX12) • CS01 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by right left lemma-Swap12-alt-def
  equals (CS01 • CX12 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01) • (CX21 • CX12 • CX21) • CS01 • CX21 • CS01 • CX12 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CX12 • CX21 • CS01) • ((CX12 • CX21 • CS01 • CS01 • CS01 • CX21) • (CX12 • CX21 • CS01 • CX21 • CX12)) • CS01 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals (CS01 • CX12 • CX21 • CX12 • CS01) • ((CX21 • CS01 • CS01 • CS01 • CX21) • (CX12 • CX21 • CS01 • CX21 • CX12)) • CS01 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by right left lemma-c1
  equals (CS01 • CX12 • CX21 • CX12 • CS01) • ((CX12 • CX21 • CS01 • CX21 • CX12) • (CX21 • CS01 • CS01 • CS01 • CX21)) • CS01 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by Order.general-rewrite 1000 auto
  equals CS01 • (CX12 • CX21 • CS01 • CX21) • CS01 • (CX21 • CX12 • CX21) • CS01 • CS01 • CS01 • CX21 • CS01 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by right right right left symm lemma-Swap12-alt-def
  equals CS01 • (CX12 • CX21 • CS01 • CX21) • CS01 • (CX12 • CX21 • CX12) • CS01 • CS01 • CS01 • CX21 • CS01 • CX21 • CS01 • CS01 • CS01 • CX12 • CX21
    by general-comm auto
  equals CS01 • (CX12 • CX21 • CS01 • CX21 • CX12) • CS01 • (CX21 • CX12) • (CS01 • CS01 • CS01 • CX21 • CS01 • CX21) • CS01 • CS01 • CS01 • CX12 • CX21
    by right right right right (left lemma-d0)
  equals CS01 • (CX12 • CX21 • CS01 • CX21 • CX12) • CS01 • (CX21 • CX12) • (CX21 • CS01 • CX21 • CS01 • CS01 • CS01) • CS01 • CS01 • CS01 • CX12 • CX21
    by Order.general-rewrite 1000 auto
  equals CS01 • (CX12 • CX21 • CS01 • CX21 • CX12) • CS01 • (CX21 • CX12 • CX21) • CS01 • CX21 • CS01 • CS01 • CX12 • CX21
    by right right right left symm lemma-Swap12-alt-def
  equals CS01 • (CX12 • CX21 • CS01 • CX21 • CX12) • CS01 • (CX12 • CX21 • CX12) • CS01 • CX21 • CS01 • CS01 • CX12 • CX21
    by Order.general-rewrite 1000 auto
  equals (CS01 • CX12 • CX21 • CS01) • (CX21 • CS01 • CX21 • CS01) • (CX12 • CX21 • CX12) • CS01 • CS01 • CX21
    by right left symm (lemma-CS01-CX21-CS01-CX21=CX21-CS01-CX21-CS01)
  equals (CS01 • CX12 • CX21 • CS01) • (CS01 • CX21 • CS01 • CX21) • (CX12 • CX21 • CX12) • CS01 • CS01 • CX21
    by right right left lemma-Swap12-alt-def
  equals (CS01 • CX12 • CX21 • CS01) • (CS01 • CX21 • CS01 • CX21) • (CX21 • CX12 • CX21) • CS01 • CS01 • CX21
    by Order.general-rewrite 1000 auto
  equals (CS01 • CX12 • CX21 • CS01) • (CS01 • CX21 • CS01 • CX12 • CX21) • CS01 • CS01 • CX21
    by general-assoc auto
  equals (CS01 • CX12) • (CX21 • CS01 • CS01 • CX21 • CS01) • CX12 • CX21 • CS01 • CS01 • CX21
    by right left symm lemma-e1
  equals (CS01 • CX12) • (CS01 • CX21 • CS01 • CS01 • CX21) • CX12 • CX21 • CS01 • CS01 • CX21
    by general-comm auto
  equals (CS01 • CS01 • CX12 • CX21 • CS01 • CS01) • (CX21 • CX12 • CX21) • CS01 • CS01 • CX21
    by right (left lemma-Swap12-alt-def reversed)
  equals (CS01 • CS01 • CX12 • CX21 • CS01 • CS01) • (CX12 • CX21 • CX12) • CS01 • CS01 • CX21
    by general-comm auto
  equals CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21 • CS01 • CS01 • CX12 • CX21
    by lemma-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21-CS01-CS01-CX12-CX21=ε
  equals ε

lemma-CX10-CS02=CS02-CS12-CCZ-CX10 : Rel ⊢ CX10 • CS02 === CS02 • CS12 • CCZ • CX10
lemma-CX10-CS02=CS02-CS12-CCZ-CX10 =
  equational CX10 • CS02
    by refl
  equals CX10 • Swap12 • CS01 • Swap12
    by Order.general-rewrite 100 auto
  equals CX10 • CX12 • CX21 • CS01 • CX21 • CX12
    by right symm (axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12)
  equals CX10 • CX10 • CX01 • CS12 • CX01 • CX10
    by Order.general-rewrite 100 auto
  equals (CX01 • CS12 • CX01) • CX10
    by general-assoc auto
  equals (CX01 • CS12 • CX01) • ε • CX10
    by right left symm lemma-CCZ-CCZ=ε
  equals (CX01 • CS12 • CX01) • (CCZ • CCZ) • CX10
    by general-assoc auto
  equals (CX01 • CS12 • CX01 • CCZ) • CCZ • CX10
    by left right right right lemma-CCZ-alt-def
  equals (CX01 • CS12 • CX01 • CS12 • CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01) • CCZ • CX10
    by general-assoc auto
  equals (CX01 • CS12 • CX01 • CS12) • (CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01) • CCZ • CX10
    by left symm (lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12)
  equals (CS12 • CX01 • CS12 • CX01) • (CX10 • CX01 • CS12 • CX10 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01) • CCZ • CX10
    by general-comm auto
  equals (CS12 • CX01 • CS12) • (CX01 • CX10 • CX01 • CX10) • CS12 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01 • CCZ • CX10
    by right left right lemma-Swap-alt-def reversed
  equals (CS12 • CX01 • CS12) • (CX01 • CX01 • CX10 • CX01) • CS12 • CX01 • CS12 • CS12 • CS12 • CX10 • CX01 • CCZ • CX10
    by Order.general-rewrite 100 auto
  equals (CS12 • CX01 • CS12 • CX10) • (CX01 • CS12 • CX01) • CS12 • CS12 • CS12 • CX10 • CX01 • CCZ • CX10
    by general-comm auto
  equals (CS12 • CX01 • CX10) • (CS12 • CX01 • CS12 • CX01) • CX10 • CS12 • CS12 • CS12 • CX01 • CCZ • CX10
    by right left lemma-CS12-CX01-CS12-CX01=CX01-CS12-CX01-CS12
  equals (CS12 • CX01 • CX10) • (CX01 • CS12 • CX01 • CS12) • CX10 • CS12 • CS12 • CS12 • CX01 • CCZ • CX10
    by Order.general-rewrite 100 auto
  equals (CS12 • CX01 • CX10) • (CX01 • CS12 • CX01) • CX10 • CX01 • CCZ • CX10
    by general-assoc auto
  equals CS12 • (CX01 • CX10 • CX01) • CS12 • CX01 • CX10 • CX01 • CCZ • CX10
    by right left lemma-Swap-alt-def
  equals CS12 • (CX10 • CX01 • CX10) • CS12 • CX01 • CX10 • CX01 • CCZ • CX10
    by general-comm auto
  equals (CS12 • CX10 • CX01 • CS12) • (CX10 • CX01 • CX10) • CX01 • CCZ • CX10
    by right left symm lemma-Swap-alt-def
  equals (CS12 • CX10 • CX01 • CS12) • (CX01 • CX10 • CX01) • CX01 • CCZ • CX10
    by Order.general-rewrite 100 auto
  equals CS12 • (CX10 • CX01 • CS12 • CX01 • CX10) • CCZ • CX10
    by right left axiom ax-CX10-CX01-CS12-CX01-CX10=CX12-CX21-CS01-CX21-CX12
  equals CS12 • (CX12 • CX21 • CS01 • CX21 • CX12) • CCZ • CX10
    by general-assoc auto
  equals ((CS12 • CX12 • CX21 • CS01 • CX21 • CX12)) • CCZ • CX10
    by left lemma-scomm2at reversed
  equals ((CX12 • CX21 • CS01 • CX21 • CX12 • CS12)) • CCZ • CX10
    by Order.general-rewrite 100 auto
  equals ((Swap12 • CS01 • Swap12) • CS12) • CCZ • CX10
    by refl
  equals (CS02 • CS12) • CCZ • CX10
    by general-assoc auto
  equals CS02 • CS12 • CCZ • CX10


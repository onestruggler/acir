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
open import Examples.Groups.Clifford+CS-3qubit.Gate

import Examples.Groups.Clifford+CS-3qubit.Step6.Rel as L

open import Examples.Groups.Clifford+CS-3qubit.Step7.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step7.MvI
open import Examples.Groups.Clifford+CS-3qubit.Step7.Order
open import Examples.Groups.Clifford+CS-3qubit.Step7.Basis-Change
open import Examples.Groups.Clifford+CS-3qubit.Step7.PLemmas
open import Examples.Groups.Clifford+CS-3qubit.Step7.Comm
open import Examples.Groups.Clifford+CS-3qubit.Step7.S7
open import Examples.Groups.Clifford+CS-3qubit.Step7.S8D

module Examples.Groups.Clifford+CS-3qubit.Step7.Lemmas where

  lemma-Swap01=CX01-Swap01-CX01-Swap01-CX01 : Rel ⊢ Swap01 === CX01 • (Swap01 • CX01 • Swap01) • CX01
  lemma-Swap01=CX01-Swap01-CX01-Swap01-CX01 =
    equational Swap01
      by axiom ax-Swap01=CX01-CX10-CX01
    equals CX01 • (CX10) • CX01
      by right right trans (symm left-unit) (left symm (axiom ax-Swap01-Swap01=ε))
    equals CX01 • CX10 • (Swap01 • Swap01) • CX01
      by general-assoc auto
    equals CX01 • (CX10 • Swap01) • Swap01 • CX01
      by right left symm (axiom ax-Swap01-CX01=CX10-Swap01)
    equals CX01 • (Swap01 • CX01) • Swap01 • CX01
      by general-assoc auto
    equals CX01 • (Swap01 • CX01 • Swap01) • CX01

  lemma-Swap12 : Rel ⊢ Swap12 === (Swap01 • Swap12 • CX01 • Swap12 • Swap01) • (Swap12 • Swap01 • Swap12 • CX01 • Swap12 • Swap01 • Swap12) • (Swap01 • Swap12 • CX01 • Swap12 • Swap01)
  lemma-Swap12 =
    equational Swap12
      by axiom ax-Swap12=CX12-CX21-CX12
    equals CX12 • CX21 • CX12
      by MvSwap.general-rewrite 100 auto
    equals (Swap01 • Swap12 • CX01 • Swap12 • Swap01) • (Swap12 • Swap01 • Swap12 • CX01 • Swap12 • Swap01 • Swap12) • (Swap01 • Swap12 • CX01 • Swap12 • Swap01)


  lemma-CCX1-CX01-CCX2-CX10-CCX0-CCX2-CCX1-CX01-CCX2-CCX0-CX10-CCX2=ε : Rel ⊢ (CCX1 • CX01 • CCX2 • CX10) • (((((((CCX0 • CCX2) • CCX1) • CX01) • CCX2) • CCX0) • CX10) • CCX2) === ε
  lemma-CCX1-CX01-CCX2-CX10-CCX0-CCX2-CCX1-CX01-CCX2-CCX0-CX10-CCX2=ε =
    equational (CCX1 • CX01 • CCX2 • CX10) • (((((((CCX0 • CCX2) • CCX1) • CX01) • CCX2) • CCX0) • CX10) • CCX2)
      by S7.general-rewrite 100 auto
    equals (CX01 • CX10 • CCX1 • CX12 • CX10 • CX01 • CCX1) • (CX12 • CX01) • CCX2 • CCX1 • CCX2 • CCX0
      by right left S7.general-rewrite 100 auto
    equals (CX01 • CX10 • CCX1 • CX12 • CX10 • CX01 • CCX1) • (CX02 • CX01 • CX12) • CCX2 • CCX1 • CCX2 • CCX0
      by S7.general-rewrite 200 auto
    equals (CX01 • CX10 • CX02) • (CX01 • CX10 • CX01) • CX12 • CX10
      by right left symm (axiom ax-Swap01=CX01-CX10-CX01)
    equals (CX01 • CX10 • CX02) • (Swap01) • CX12 • CX10
      by MvSwap.general-rewrite 10 auto
    equals (CX01 • CX10 • CX02 • CX02) • (Swap01) • CX10
      by right left axiom ax-Swap01=CX01-CX10-CX01
    equals (CX01 • CX10 • CX02 • CX02) • (CX01 • CX10 • CX01) • CX10
      by S7.general-rewrite 100 auto
    equals ε

  lemma-CX01-CX10-CX02=CX12-CX01-CX10 : Rel ⊢ CX01 • CX10 • CX02 === CX12 • CX01 • CX10
  lemma-CX01-CX10-CX02=CX12-CX01-CX10 =
    equational CX01 • CX10 • CX02
      by Order.general-rewrite 100 auto
    equals (CX01 • CX10 • CX02 • CX10 • CX01) • CX01 • CX10
      by left lemma-CX01-CX10-CX02-CX10-CX01=CX12
    equals CX12 • CX01 • CX10


  lemma-CCX1-CCX2-CX10-CCX0-CCX2-CCX1-CX01-CCX2-CCX0-CX10-CCX2-CX01=ε : Rel ⊢ (CCX1 • CCX2 • CX10) • ((((((((CCX0 • CCX2) • CCX1) • CX01) • CCX2) • CCX0) • CX10) • CCX2) • CX01) === ε
  lemma-CCX1-CCX2-CX10-CCX0-CCX2-CCX1-CX01-CCX2-CCX0-CX10-CCX2-CX01=ε =
    equational (CCX1 • CCX2 • CX10) • ((((((((CCX0 • CCX2) • CCX1) • CX01) • CCX2) • CCX0) • CX10) • CCX2) • CX01)
      by S7.general-rewrite 300 auto
    equals CX10 • CX02 • (CX01 • CX10 • CX02) • CX01 • CX10 • CX02 • CX01
      by right right left lemma-CX01-CX10-CX02=CX12-CX01-CX10
    equals CX10 • CX02 • (CX12 • CX01 • CX10) • CX01 • CX10 • CX02 • CX01
      by S7.general-rewrite 300 auto
    equals ε

  open Group-Lemmas Gate Rel group-like

  lemma-CCX1-CX01-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0 : Rel ⊢ CCX1 • CX01 • CCX2 • CX10 === CCX2 • CX10 • CCX0 • CCX2 • CX01 • CCX1 • CCX2 • CCX0
  lemma-CCX1-CX01-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0 = lemma-one-sided {w = CCX1 • CX01 • CCX2 • CX10} {u = CCX2 • CX10 • CCX0 • CCX2 • CX01 • CCX1 • CCX2 • CCX0} lemma-CCX1-CX01-CCX2-CX10-CCX0-CCX2-CCX1-CX01-CCX2-CCX0-CX10-CCX2=ε
  lemma-CCX1-CCX2-CX10=CX01-CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0 : Rel ⊢ CCX1 • CCX2 • CX10 === CX01 • CCX2 • CX10 • CCX0 • CCX2 • CX01 • CCX1 • CCX2 • CCX0
  lemma-CCX1-CCX2-CX10=CX01-CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0 = lemma-one-sided lemma-CCX1-CCX2-CX10-CCX0-CCX2-CCX1-CX01-CCX2-CCX0-CX10-CCX2-CX01=ε

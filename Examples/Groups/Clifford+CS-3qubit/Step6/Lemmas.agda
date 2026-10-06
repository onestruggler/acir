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

open import Examples.Groups.Clifford+CS-3qubit.Step6.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step6.Order
open import Examples.Groups.Clifford+CS-3qubit.Step6.Comm
open import Examples.Groups.Clifford+CS-3qubit.Step6.S8
open import Examples.Groups.Clifford+CS-3qubit.Step6.S8D
open import Examples.Groups.Clifford+CS-3qubit.Step6.PLemmas
open import Examples.Groups.Clifford+CS-3qubit.Step6.Basis-Change hiding (lemma-Swap01-Swap01=ε ; lemma-Swap12-Swap12=ε)

module Examples.Groups.Clifford+CS-3qubit.Step6.Lemmas where

  lemma-CX01-CX21-CX20=CX20-CX01 : Rel ⊢ CX01 • CX21 • CX20 === CX20 • CX01
  lemma-CX01-CX21-CX20=CX20-CX01 =
    equational CX01 • CX21 • CX20
      by right symm (axiom ax-CX20-CX21=CX21-CX20)
    equals CX01 • CX20 • CX21
      by B01.by-basis-change Swap01 Swap01 (lemma-CX10-CX21-CX20=CX21-CX10) 50 auto
    equals CX20 • CX01


  lemma-CCX0-CX02-CX20=CX02-CX20-CCX2 : Rel ⊢ CCX0 • CX02 • CX20 === CX02 • CX20 • CCX2
  lemma-CCX0-CX02-CX20=CX02-CX20-CCX2 =
    equational CCX0 • CX02 • CX20
      by B01.by-basis-change Swap01 Swap01 (lemma-CCX1-CX12-CX21=CX12-CX21-CCX2) 50 auto
    equals CX02 • CX20 • CCX2

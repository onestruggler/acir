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

module Examples.Groups.Clifford+CS-3qubit.Step7.S7 where

  isS1 : Gate -> Bool
  isS1 _ = false

  isS2 : Gate -> Bool
  isS2 CCX0-gen = true
  isS2 x = isS1 x


  isS3 : Gate -> Bool
  isS3 CCX1-gen = true
  isS3 x = isS2 x

  isS4 : Gate -> Bool
  isS4 CCX2-gen = true
  isS4 x = isS3 x

  isS5 : Gate -> Bool
  isS5 CX01-gen = true
  isS5 x = isS4 x

  isS6 : Gate -> Bool
  isS6 CX10-gen = true
  isS6 x = isS5 x

  isS7 : Gate -> Bool
  isS7 CX02-gen = true
  isS7 CX20-gen = true
  isS7 CX12-gen = true
  isS7 CX21-gen = true
  isS7 x = isS6 x

  isS8 : Gate -> Bool
  isS8 X0-gen = true
  isS8 X1-gen = true
  isS8 X2-gen = true
  isS8 x = isS7 x

  s7-step : Step-Function Gate Rel
  s7-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  s7-step (CCX1-gen ∷ CCX1-gen ∷ xs) = just (xs , at-head (lemma-CCX1-CCX1=ε))
  s7-step (CCX2-gen ∷ CCX2-gen ∷ xs) = just (xs , at-head (lemma-CCX2-CCX2=ε))
  s7-step (CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ xs) = just (CCX1-gen ∷ CCX0-gen ∷ CCX1-gen ∷ xs , at-head (axiom ax-CCX0-CCX1-CCX0=CCX1-CCX0-CCX1))
  s7-step (CCX1-gen ∷ CCX2-gen ∷ CCX1-gen ∷ xs) = just (CCX2-gen ∷ CCX1-gen ∷ CCX2-gen ∷ xs , at-head (lemma-CCX1-CCX2-CCX1=CCX2-CCX1-CCX2))
  s7-step (CCX0-gen ∷ CCX2-gen ∷ CCX0-gen ∷ xs) = just (CCX2-gen ∷ CCX0-gen ∷ CCX2-gen ∷ xs , at-head (lemma-CCX0-CCX2-CCX0=CCX2-CCX0-CCX2))
  s7-step (CCX0-gen ∷ CCX2-gen ∷ CCX1-gen ∷ CCX2-gen ∷ xs) = just (CCX2-gen ∷ CCX1-gen ∷ CCX2-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CCX2-CCX1-CCX2=CCX2-CCX1-CCX2-CCX0))
  s7-step (CCX1-gen ∷ CCX2-gen ∷ CCX0-gen ∷ CCX2-gen ∷ xs) = just (CCX2-gen ∷ CCX0-gen ∷ CCX2-gen ∷ CCX1-gen ∷ xs , at-head (lemma-CCX1-CCX2-CCX0-CCX2=CCX2-CCX0-CCX2-CCX1))
  s7-step (CCX2-gen ∷ CCX1-gen ∷ CCX0-gen ∷ CCX1-gen ∷ xs) = just (CCX1-gen ∷ CCX0-gen ∷ CCX1-gen ∷ CCX2-gen ∷ xs , at-head (lemma-CCX2-CCX1-CCX0-CCX1=CCX1-CCX0-CCX1-CCX2))
  s7-step (CX01-gen ∷ CX01-gen ∷ xs) = just (xs , at-head (axiom ax-CX01-CX01=ε))
  s7-step (CX10-gen ∷ CX10-gen ∷ xs) = just (xs , at-head (lemma-CX10-CX10=ε))
  s7-step (CX12-gen ∷ CX12-gen ∷ xs) = just (xs , at-head (lemma-CX12-CX12=ε))
  s7-step (CX21-gen ∷ CX21-gen ∷ xs) = just (xs , at-head (lemma-CX21-CX21=ε))
  s7-step (CX02-gen ∷ CX02-gen ∷ xs) = just (xs , at-head (lemma-CX02-CX02=ε))
  s7-step (CX20-gen ∷ CX20-gen ∷ xs) = just (xs , at-head (lemma-CX20-CX20=ε))
  s7-step (CCX2-gen ∷ CX12-gen ∷ xs) = just (CX12-gen ∷ CCX2-gen ∷ xs , at-head (lemma-CCX2-CX12=CX12-CCX2))
  s7-step (CCX2-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ CCX2-gen ∷ xs , at-head (lemma-CCX2-CX02=CX02-CCX2))
  s7-step (CCX1-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ CCX1-gen ∷ xs , at-head (lemma-CCX1-CX21=CX21-CCX1))
  s7-step (CCX1-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ CCX1-gen ∷ xs , at-head (lemma-CCX1-CX01=CX01-CCX1))
  s7-step (CCX0-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCX0-CX20=CX20-CCX0))
  s7-step (CCX0-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CX10=CX10-CCX0))
  s7-step (CCX2-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ CX02-gen ∷ CCX2-gen ∷ xs , at-head (axiom ax-CCX2-CX01=CX01-CX02-CCX2))
  s7-step (CCX2-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CX12-gen ∷ CCX2-gen ∷ xs , at-head (lemma-CCX2-CX10=CX10-CX12-CCX2))
  s7-step (CCX1-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ CX01-gen ∷ CCX1-gen ∷ xs , at-head (lemma-CCX1-CX02=CX02-CX01-CCX1))
  s7-step (CCX1-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ CX21-gen ∷ CCX1-gen ∷ xs , at-head (lemma-CCX1-CX20=CX20-CX21-CCX1))
  s7-step (CCX0-gen ∷ CX12-gen ∷ xs) = just (CX12-gen ∷ CX10-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCX0-CX12=CX12-CX10-CCX0))
  s7-step (CCX0-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ CX20-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCX0-CX21=CX21-CX20-CCX0))
  s7-step (CCX0-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ CCX1-gen ∷ CCX0-gen ∷ CCX1-gen ∷ xs , at-head (axiom ax-CCX0-CX01=CX01-CCX1-CCX0-CCX1))
  s7-step (CCX1-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CCX0-gen ∷ CCX1-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCX1-CX10=CX10-CCX0-CCX1-CCX0))
  s7-step (CCX2-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ CCX1-gen ∷ CCX2-gen ∷ CCX1-gen ∷ xs , at-head (lemma-CCX2-CX21=CX21-CCX1-CCX2-CCX1))
  s7-step (CCX2-gen ∷ CX20-gen ∷ CX02-gen ∷ xs) = just (CX20-gen ∷ CX02-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCX2-CX20-CX02=CX20-CX02-CCX0))
  s7-step (CX10-gen ∷ CX01-gen ∷ CX10-gen ∷ xs) = just (CX01-gen ∷ CX10-gen ∷ CX01-gen ∷ xs , at-head (lemma-CX10-CX01-CX10=CX01-CX10-CX01))
  s7-step (CX20-gen ∷ CX02-gen ∷ CX20-gen ∷ xs) = just (CX02-gen ∷ CX20-gen ∷ CX02-gen ∷ xs , at-head (lemma-CX20-CX02-CX20=CX02-CX20-CX02))
  s7-step (CX21-gen ∷ CX12-gen ∷ CX21-gen ∷ xs) = just (CX12-gen ∷ CX21-gen ∷ CX12-gen ∷ xs , at-head (lemma-CX21-CX12-CX21=CX12-CX21-CX12))
  s7-step (CX01-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ CX01-gen ∷ xs , at-head (axiom ax-CX01-CX02=CX02-CX01))
  s7-step (CX01-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ CX01-gen ∷ xs , at-head (axiom ax-CX01-CX21=CX21-CX01))
  s7-step (CX10-gen ∷ CX12-gen ∷ xs) = just (CX12-gen ∷ CX10-gen ∷ xs , at-head (lemma-CX10-CX12=CX12-CX10))
  s7-step (CX10-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ CX10-gen ∷ xs , at-head (lemma-CX10-CX20=CX20-CX10))
  s7-step (CX12-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ CX12-gen ∷ xs , at-head (lemma-CX12-CX02=CX02-CX12))
  s7-step (CX21-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ CX21-gen ∷ xs , at-head (lemma-CX21-CX20=CX20-CX21))
  s7-step (CX20-gen ∷ CX10-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ CX10-gen ∷ xs , at-head (lemma-CX20-CX10-CX21=CX21-CX10))
  s7-step (CX20-gen ∷ CX21-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CX21-gen ∷ xs , at-head (lemma-CX20-CX21-CX10=CX10-CX21))
  s7-step (CX21-gen ∷ CX01-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ CX01-gen ∷ xs , at-head (lemma-CX21-CX01-CX20=CX20-CX01))
  s7-step (CX21-gen ∷ CX02-gen ∷ CX01-gen ∷ xs) = just (CX02-gen ∷ CX21-gen ∷ xs , at-head (lemma-CX21-CX02-CX01=CX02-CX21))
  s7-step (CX02-gen ∷ CX12-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CX02-gen ∷ xs , at-head (lemma-CX02-CX12-CX10=CX10-CX02))
  s7-step (CX01-gen ∷ CX20-gen ∷ CX21-gen ∷ xs) = just (CX20-gen ∷ CX01-gen ∷ xs , at-head (lemma-CX01-CX20-CX21=CX20-CX01))
  s7-step (CX12-gen ∷ CX20-gen ∷ CX10-gen ∷ xs) = just (CX20-gen ∷ CX12-gen ∷ xs , at-head (lemma-CX12-CX20-CX10=CX20-CX12))
  s7-step (CX12-gen ∷ CX10-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ CX10-gen ∷ xs , at-head (lemma-CX12-CX10-CX02=CX02-CX10))
  s7-step (CX02-gen ∷ CX12-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ CX12-gen ∷ xs , at-head (lemma-CX02-CX12-CX01=CX01-CX12))
  s7-step (CX02-gen ∷ CX21-gen ∷ CX01-gen ∷ xs) = just (CX21-gen ∷ CX02-gen ∷ xs , at-head (lemma-CX02-CX21-CX01=CX21-CX02))
  s7-step (CX02-gen ∷ CX01-gen ∷ CX12-gen ∷ xs) = just (CX12-gen ∷ CX01-gen ∷ xs , at-head (lemma-CX02-CX01-CX12=CX12-CX01))
  s7-step (CX10-gen ∷ CX02-gen ∷ CX12-gen ∷ xs) = just (CX02-gen ∷ CX10-gen ∷ xs , at-head (lemma-CX10-CX02-CX12=CX02-CX10))
  s7-step (CX01-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ CX21-gen ∷ CX01-gen ∷ xs , at-head (lemma-CX01-CX20=CX20-CX21-CX01))
  s7-step (CX01-gen ∷ CX10-gen ∷ CX02-gen ∷ CX10-gen ∷ CX01-gen ∷ xs) = just (CX12-gen ∷ xs , at-head (lemma-CX01-CX10-CX02-CX10-CX01=CX12))
  s7-step (CX02-gen ∷ CX20-gen ∷ CX01-gen ∷ CX20-gen ∷ CX02-gen ∷ xs) = just (CX21-gen ∷ xs , at-head (lemma-CX02-CX20-CX01-CX20-CX02=CX21))
  s7-step (CX02-gen ∷ CX20-gen ∷ CX12-gen ∷ CX20-gen ∷ CX02-gen ∷ xs) = just (CX10-gen ∷ xs , at-head (lemma-CX02-CX20-CX12-CX20-CX02=CX10))
  s7-step (CX12-gen ∷ CX21-gen ∷ CX10-gen ∷ CX21-gen ∷ CX12-gen ∷ xs) = just (CX20-gen ∷ xs , at-head (lemma-CX12-CX21-CX10-CX21-CX12=CX20))
  s7-step (CX12-gen ∷ CX21-gen ∷ CX02-gen ∷ CX21-gen ∷ CX12-gen ∷ xs) = just (CX01-gen ∷ xs , at-head (lemma-CX12-CX21-CX02-CX21-CX12=CX01))
  s7-step (CCX0-gen ∷ CX02-gen ∷ CCX2-gen ∷ xs) = just (CX02-gen ∷ CCX2-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCX0-CX02-CCX2=CX02-CCX2-CCX0))
  s7-step (CCX2-gen ∷ CX20-gen ∷ CCX0-gen ∷ xs) = just (CX20-gen ∷ CCX0-gen ∷ CCX2-gen ∷ xs , at-head (lemma-CCX2-CX20-CCX0=CX20-CCX0-CCX2))
  s7-step (CCX1-gen ∷ CX12-gen ∷ CCX2-gen ∷ xs) = just (CX12-gen ∷ CCX2-gen ∷ CCX1-gen ∷ xs , at-head (lemma-CCX1-CX12-CCX2=CX12-CCX2-CCX1))
  s7-step (CX21-gen ∷ CX02-gen ∷ CX20-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ CX20-gen ∷ CX02-gen ∷ CX01-gen ∷ xs , at-head (lemma-CX21-CX02-CX20-CX02=CX02-CX20-CX02-CX01))
  s7-step _ = nothing

  module S7 = Rewriting.Step (step-cong (swap-step then s7-step))

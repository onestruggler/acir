------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
-- 
-- Part 1 of 5 of the proofs of Step4.Main's hypB that compute normal
-- forms, one lemma per relation of Step 3; in one module they took 41 s.
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

import Examples.Groups.Clifford+CS-3qubit.Step3.Rel as L

open import Examples.Groups.Clifford+CS-3qubit.Step4.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8D
open import Examples.Groups.Clifford+CS-3qubit.Step4.KD
open import Examples.Groups.Clifford+CS-3qubit.Step4.Lemmas

open import Examples.Groups.Clifford+CS-3qubit.Step4.Simple

module Examples.Groups.Clifford+CS-3qubit.Step4.HypB1 where

  hb1 : Goal L.ax-Swap01-CCX2-CCX1-CCX0-Swap12-Swap01=X1-CCX0-CCX2-CCX1-X1-CX21-CX20
  hb1 = ListNF.listnfeq' nf-p auto

  hb2 : Goal L.ax-Swap01-X1-CCX0-CCX1-CCX2=X2-CCX0-CCX2-CCX1-X1-X2-CX21-X0-CX10
  hb2 = ListNF.listnfeq' nf-p auto

  hb3 : Goal L.ax-Swap01-X1-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20
  hb3 = ListNF.listnfeq' nf-p auto

  hb4 : Goal L.ax-Swap01-X2-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-X2-CX21-X0-CX10-CX20
  hb4 = ListNF.listnfeq' nf-p auto

  hb5 : Goal L.ax-CX01-CCX2-CCX0-CX02-CCX1=X2-CCX0-CCX2-CCX1-X2-CX12-CX10
  hb5 = ListNF.listnfeq' nf-p auto

  hb6 : Goal L.ax-CX01-X1-CCX0-CCX1-CCX2=CCX0-CX21-CCX2-CX01-X1-CX20-CCX0
  hb6 = ListNF.listnfeq' nf-p auto

  hb7 : Goal L.ax-CX01-X1-CCX0-CCX2-CCX1=CX21-CCX0-CCX2-CX01-X1-CX21-CCX0
  hb7 = ListNF.listnfeq' nf-p auto

  hb8 : Goal L.ax-CX01-X2-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1-X2-CX12-CX10
  hb8 = ListNF.listnfeq' nf-p auto

  hb9 : Goal L.ax-CX01-CX21-CCX0-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX21-CCX0
  hb9 = ListNF.listnfeq' nf-p auto

  hb10 : Goal L.ax-CX01-CCX0-CX21-CCX2-CX01=X1-CCX0-CCX1-CCX2-X1-CCX0
  hb10 = ListNF.listnfeq' nf-p auto

  hb11 : Goal L.ax-CX02-CCX1-CCX0-CX01-CCX2=X1-CCX0-CCX1-CCX2-X1-CX21-CX20
  hb11 = ListNF.listnfeq' nf-p auto

  hb12 : Goal L.ax-CX02-X1-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2-X1-CX21-CX20
  hb12 = ListNF.listnfeq' nf-p auto

  hb13 : Goal L.ax-CX02-X1-CCX0-CCX2-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-X2-Swap12
  hb13 = ListNF.listnfeq' nf-p auto

  hb14 : Goal L.ax-CX02-X2-CCX0-CCX2-CCX1=CCX0-CX12-CCX1-CX02-X2-CX10-CCX0
  hb14 = ListNF.listnfeq' nf-p auto

  hb15 : Goal L.ax-CX02-CCX0-CX12-CCX1-CX02=X2-CCX0-CCX2-CCX1-X2-CCX0
  hb15 = ListNF.listnfeq' nf-p auto

  hb16 : Goal L.ax-CX02-CCX0-Swap12-CCX1-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-Swap12
  hb16 = ListNF.listnfeq' nf-p auto

  hb17 : Goal L.ax-CCX1-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX1-CCX2-X1-CX21-CX20
  hb17 = ListNF.listnfeq' nf-p auto

  hb18 : Goal L.ax-CCX1-CCX2-CCX0-CX02-CCX1=X2-CCX0-CCX2-CCX1-X2-CX12-CX10-CCX0
  hb18 = ListNF.listnfeq' nf-p auto

  hb19 : Goal L.ax-CCX1-X1-CCX0-CCX1-CCX2=CX01-CCX2-CCX0-CX01-X1-CX21-CX20
  hb19 = ListNF.listnfeq' nf-p auto

  hb20 : Goal L.ax-CCX1-X1-CCX0-CCX2-CCX1=X1-CCX0-CCX2-CCX1-CCX0
  hb20 = ListNF.listnfeq' nf-p auto

  hb21 : Goal L.ax-CCX1-X2-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1-X2-CX12-CX10-CCX0
  hb21 = ListNF.listnfeq' nf-p auto

  hb22 : Goal L.ax-CCX2-CX02-CCX1-CCX0-CX02=X2-CCX0-CCX2-CCX1-X2-CX12-CX10
  hb22 = ListNF.listnfeq' nf-p auto

  hb23 : Goal L.ax-CCX2-CCX1-CCX0-CX01-CCX2=X1-CCX0-CCX1-CCX2-X1-CX21-CX20-CCX0
  hb23 = ListNF.listnfeq' nf-p auto

  hb24 : Goal L.ax-CCX2-X1-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2-X1-CX21-CX20-CCX0
  hb24 = ListNF.listnfeq' nf-p auto

  hb25 : Goal L.ax-CCX2-X1-CCX0-CCX2-CCX1=CCX0-Swap12-CCX2-Swap01-X2-CX21-CX12-CX20
  hb25 = ListNF.listnfeq' nf-p auto

  hb26 : Goal L.ax-CCX2-X2-CCX0-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CX10
  hb26 = ListNF.listnfeq' nf-p auto

  hb27 : Goal L.ax-CCX2-CCX0-Swap12-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-CX12-CX21-CX10
  hb27 = ListNF.listnfeq' nf-p auto

  hb28 : Goal L.ax-X1-Swap01=Swap01-X0
  hb28 = ListNF.listnfeq' nf-p auto

  hb29 : Goal L.ax-X1-CX01=CX01-X1
  hb29 = ListNF.listnfeq' nf-p auto

  hb30 : Goal L.ax-X1-CX01-CCX2=CCX2-CX01-X1
  hb30 = ListNF.listnfeq' nf-p auto

  hb31 : Goal L.ax-X1-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX21-X0
  hb31 = ListNF.listnfeq' nf-p auto

  hb32 : Goal L.ax-X1-CX01-CCX2-CCX0-CX01=CCX2-CX10-CCX1-X1-CX21-X0-CX10
  hb32 = ListNF.listnfeq' nf-p auto

  hb33 : Goal L.ax-X1-CX01-CX20-CCX2=CX20-CX21-CCX2-CX01-X1
  hb33 = ListNF.listnfeq' nf-p auto

  hb34 : Goal L.ax-X1-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX21-X0
  hb34 = ListNF.listnfeq' nf-p auto

  hb35 : Goal L.ax-X1-CX01-CCX0-CX02=CX10-Swap12-CCX2-Swap01-X1-X2-CX12-CX20
  hb35 = ListNF.listnfeq' nf-p auto

  hb36 : Goal L.ax-X1-CX01-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-X0
  hb36 = ListNF.listnfeq' nf-p auto

  hb37 : Goal L.ax-X1-CX01-CCX0-CCX2-CX01=CX10-CCX2-CCX1-X2-CX21-CX12-X0-CX10
  hb37 = ListNF.listnfeq' nf-p auto

  hb38 : Goal L.ax-X1-CX02=CX02-X1
  hb38 = ListNF.listnfeq' nf-p auto

  hb39 : Goal L.ax-X1-CX02-CX01=CX02-CX01-X1
  hb39 = ListNF.listnfeq' nf-p auto

  hb40 : Goal L.ax-X1-CX02-CCX1=CX02-CCX1-X1
  hb40 = ListNF.listnfeq' nf-p auto

  hb41 : Goal L.ax-X1-CX02-CCX1-CCX0-CX02=CX20-CCX1-CCX2-CX01-X1-CX20
  hb41 = ListNF.listnfeq' nf-p auto

  hb42 : Goal L.ax-X1-CX02-CX10-CCX1=CX02-CX10-CCX1-X1-CX21-X0
  hb42 = ListNF.listnfeq' nf-p auto

  hb43 : Goal L.ax-X1-CX02-CCX0-CX01=CX02-CCX0-CX01-X1-CX21-CX20
  hb43 = ListNF.listnfeq' nf-p auto

  hb44 : Goal L.ax-X1-CCX1=CCX1-X1
  hb44 = ListNF.listnfeq' nf-p auto

  hb45 : Goal L.ax-X1-CCX1-CX01=CCX1-CX01-X1
  hb45 = ListNF.listnfeq' nf-p auto

  hb46 : Goal L.ax-X1-CCX1-CX01-CCX2=CCX1-CCX2-CX01-X1
  hb46 = ListNF.listnfeq' nf-p auto

  hb47 : Goal L.ax-X1-CCX1-CX02=CCX1-CX02-X1
  hb47 = ListNF.listnfeq' nf-p auto

  hb48 : Goal L.ax-X1-CCX1-CCX2=CCX1-CCX2-CX02-X1
  hb48 = ListNF.listnfeq' nf-p auto

  hb49 : Goal L.ax-X1-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX12-X0
  hb49 = ListNF.listnfeq' nf-p auto

  hb50 : Goal L.ax-X1-CCX1-CCX2-CX01=CCX1-CX01-CCX2-X1
  hb50 = ListNF.listnfeq' nf-p auto

  hb51 : Goal L.ax-X1-CCX1-CCX2-CX02=CCX1-CCX2-X1
  hb51 = ListNF.listnfeq' nf-p auto

  hb52 : Goal L.ax-X1-CCX1-CCX2-CCX0-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX21-X0
  hb52 = ListNF.listnfeq' nf-p auto

  hb53 : Goal L.ax-X1-CCX1-CX12-Swap01=CCX1-CX12-Swap01-X2-X0
  hb53 = ListNF.listnfeq' nf-p auto

  hb54 : Goal L.ax-X1-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-CX12-Swap01-X2-CX21-X0
  hb54 = ListNF.listnfeq' nf-p auto

  hb55 : Goal L.ax-X1-CCX1-CX20-CCX2-CX02=CX20-CCX2-CCX1-X1-CX21
  hb55 = ListNF.listnfeq' nf-p auto

  hb56 : Goal L.ax-X1-CCX1-CCX0-CX01-CCX2=CCX0-CX21-CCX2-CX01-X1-CX20-CCX0
  hb56 = ListNF.listnfeq' nf-p auto

  hb57 : Goal L.ax-X1-CCX1-CCX0-CX02=CCX1-CCX0-Swap12-Swap01-X2-Swap12-CX20
  hb57 = ListNF.listnfeq' nf-p auto

  hb58 : Goal L.ax-X1-CCX1-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-X0
  hb58 = ListNF.listnfeq' nf-p auto

  hb59 : Goal L.ax-X1-CCX1-CCX0-CX12-Swap01=CCX1-CX12-CCX0-Swap01-X1-X2-CX21-X0
  hb59 = ListNF.listnfeq' nf-p auto

  hb60 : Goal L.ax-X1-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-CX02-X1-Swap12-CX10
  hb60 = ListNF.listnfeq' nf-p auto

  hb61 : Goal L.ax-X1-CCX2=CCX2-CX02-X1
  hb61 = ListNF.listnfeq' nf-p auto

  hb62 : Goal L.ax-X1-CCX2-Swap01=CCX2-Swap01-CX12-X0
  hb62 = ListNF.listnfeq' nf-p auto

  hb63 : Goal L.ax-X1-CCX2-CX01=CX01-CCX2-X1
  hb63 = ListNF.listnfeq' nf-p auto

  hb64 : Goal L.ax-X1-CCX2-CX02=CCX2-X1
  hb64 = ListNF.listnfeq' nf-p auto

  hb65 : Goal L.ax-X1-CCX2-CX02-CCX1=CCX2-CCX1-X1
  hb65 = ListNF.listnfeq' nf-p auto

  hb66 : Goal L.ax-X1-CCX2-CCX1=CCX2-CX02-CCX1-X1
  hb66 = ListNF.listnfeq' nf-p auto

  hb67 : Goal L.ax-X1-CCX2-CCX1-CX01=CCX2-CCX1-CX02-X1
  hb67 = ListNF.listnfeq' nf-p auto

  hb68 : Goal L.ax-X1-CCX2-CCX1-CX02=CCX2-CCX1-CX01-X1
  hb68 = ListNF.listnfeq' nf-p auto

  hb69 : Goal L.ax-X1-CCX2-CCX1-CCX0-Swap12-Swap01=X2-CCX0-CCX2-CCX1-X1-CX21-CX12-X0-CX10-CX20
  hb69 = ListNF.listnfeq' nf-p auto

  hb70 : Goal L.ax-X1-CCX2-CX10-CCX1=CX01-CCX2-CCX0-CX01-X1-CX21-CX10-CX20
  hb70 = ListNF.listnfeq' nf-p auto

  hb71 : Goal L.ax-X1-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX12-CX21-X0
  hb71 = ListNF.listnfeq' nf-p auto

  hb72 : Goal L.ax-X1-CCX2-CCX0-CX01=CCX0-CX01-CCX2-X1-CX21-CX20
  hb72 = ListNF.listnfeq' nf-p auto

  hb73 : Goal L.ax-X1-CCX2-CCX0-CX02-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-X2-Swap12
  hb73 = ListNF.listnfeq' nf-p auto

  hb74 : Goal L.ax-X1-CCX2-CCX0-CX12-Swap01=CCX0-CCX2-CX01-X1-CX12-CX21-CX10-CX20
  hb74 = ListNF.listnfeq' nf-p auto

  hb75 : Goal L.ax-X1-X1-CCX0-CCX1-CCX2=CCX0-CCX1-CCX2
  hb75 = ListNF.listnfeq' nf-p auto

  hb76 : Goal L.ax-X1-X1-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1
  hb76 = ListNF.listnfeq' nf-p auto

  hb77 : Goal L.ax-X1-X2-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-X2-CX12-CX21-X0-CX20
  hb77 = ListNF.listnfeq' nf-p auto

  hb78 : Goal L.ax-X1-CX12-Swap01=CX12-Swap01-X2-X0
  hb78 = ListNF.listnfeq' nf-p auto

  hb79 : Goal L.ax-X1-CX12-CX01-CCX0-Swap01=CX10-CX12-CCX1-X2-CX21-X0
  hb79 = ListNF.listnfeq' nf-p auto

  hb80 : Goal L.ax-X1-CX12-CCX1=CX12-CCX1-CX01-X1-X2
  hb80 = ListNF.listnfeq' nf-p auto

  hb81 : Goal L.ax-X1-CX12-CCX1-CX01=CX12-CCX1-X1-X2
  hb81 = ListNF.listnfeq' nf-p auto

  hb82 : Goal L.ax-X1-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-CX21-CX12
  hb82 = ListNF.listnfeq' nf-p auto

  hb83 : Goal L.ax-X1-CX12-CCX2-Swap01=CX12-CCX2-Swap01-X2-CX12-X0
  hb83 = ListNF.listnfeq' nf-p auto

  hb84 : Goal L.ax-X1-CX12-CCX2-CCX0-Swap01=CCX0-CX12-CCX2-Swap01-X2-CX12-CX21-X0
  hb84 = ListNF.listnfeq' nf-p auto

  hb85 : Goal L.ax-X1-CX12-CCX0-Swap01=CCX0-CX12-Swap01-X2-CX21-X0
  hb85 = ListNF.listnfeq' nf-p auto

  hb86 : Goal L.ax-X1-CX21-CCX2-CX01=CX12-CCX1-CX02-X1-X2-CX12-CX21
  hb86 = ListNF.listnfeq' nf-p auto

  hb87 : Goal L.ax-X1-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-X0-CX20-CCX0
  hb87 = ListNF.listnfeq' nf-p auto

  hb88 : Goal L.ax-X1-CX21-CCX0-CCX2-CX01=CCX0-CX12-CCX1-CX02-X1-X2-CX12-CX21
  hb88 = ListNF.listnfeq' nf-p auto

  hb89 : Goal L.ax-X1-Swap12-Swap01=Swap12-Swap01-X2
  hb89 = ListNF.listnfeq' nf-p auto

  hb90 : Goal L.ax-X1-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-X2-CX12-CX10
  hb90 = ListNF.listnfeq' nf-p auto

  hb91 : Goal L.ax-X1-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-X2
  hb91 = ListNF.listnfeq' nf-p auto

  hb92 : Goal L.ax-X1-CX10-CX02-CCX1=CX10-CCX1-CX02-X1-X2-CX21-X0
  hb92 = ListNF.listnfeq' nf-p auto

  hb93 : Goal L.ax-X1-CX10-CCX1=CX10-CCX1-X1-CX21-X0
  hb93 = ListNF.listnfeq' nf-p auto

  hb94 : Goal L.ax-X1-CX10-CCX1-CX02=CX10-CX02-CCX1-X2-CX21-X0
  hb94 = ListNF.listnfeq' nf-p auto

  hb95 : Goal L.ax-X1-CX10-CCX1-CCX2-CX01=CX10-CCX2-CCX1-CX01-X1-X2-CX21-CX12-X0
  hb95 = ListNF.listnfeq' nf-p auto

  hb96 : Goal L.ax-X1-CX10-CCX2-CCX1=CX01-CCX0-CCX2-CX01-X1-CX12-CX21-CX10-CX20
  hb96 = ListNF.listnfeq' nf-p auto

  hb97 : Goal L.ax-X1-CX10-CCX2-CCX1-CX01=CX10-CCX1-CCX2-CX01-X2-CX12-CX21-X0
  hb97 = ListNF.listnfeq' nf-p auto

  hb98 : Goal L.ax-X1-CX10-CX12-CCX1=CX12-CX01-CCX0-Swap01-X1-X2-CX21-X0
  hb98 = ListNF.listnfeq' nf-p auto

  hb99 : Goal L.ax-X1-CX10-Swap12-CCX2-Swap01=CX01-CCX0-CX02-X1-CX12-CX10-CX20
  hb99 = ListNF.listnfeq' nf-p auto

  hb100 : Goal L.ax-X1-CX20-CX01-CCX2=CX20-CCX2-CX01-X1
  hb100 = ListNF.listnfeq' nf-p auto

  hb101 : Goal L.ax-X1-CX20-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1
  hb101 = ListNF.listnfeq' nf-p auto

  hb102 : Goal L.ax-X1-CX20-CCX1-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX12-X0
  hb102 = ListNF.listnfeq' nf-p auto

  hb103 : Goal L.ax-X1-CX20-CCX1-CCX2-CX01=CX02-CCX1-CCX0-CX02-X1-CX20
  hb103 = ListNF.listnfeq' nf-p auto

  hb104 : Goal L.ax-X1-CX20-CCX1-CCX2-CX02=CX20-CCX1-CCX2-X1
  hb104 = ListNF.listnfeq' nf-p auto

  hb105 : Goal L.ax-X1-CX20-CCX2=CX20-CCX2-CX02-X1
  hb105 = ListNF.listnfeq' nf-p auto

  hb106 : Goal L.ax-X1-CX20-CCX2-Swap01=CX20-CCX2-Swap01-CX12-X0
  hb106 = ListNF.listnfeq' nf-p auto

  hb107 : Goal L.ax-X1-CX20-CCX2-CX01=CX20-CX01-CCX2-X1
  hb107 = ListNF.listnfeq' nf-p auto

  hb108 : Goal L.ax-X1-CX20-CCX2-CX02=CX20-CCX2-X1
  hb108 = ListNF.listnfeq' nf-p auto

  hb109 : Goal L.ax-X1-CX20-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21
  hb109 = ListNF.listnfeq' nf-p auto

  hb110 : Goal L.ax-X1-CX20-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX02-X1
  hb110 = ListNF.listnfeq' nf-p auto

  hb111 : Goal L.ax-X1-CX20-CCX2-CCX1-CX02=CX20-CCX2-CCX1-CX01-X1
  hb111 = ListNF.listnfeq' nf-p auto

  hb112 : Goal L.ax-X1-CX20-CX21-CCX2-CX01=CX01-CX20-CCX2-X1
  hb112 = ListNF.listnfeq' nf-p auto

  hb113 : Goal L.ax-X1-CCX0-Swap01=CCX0-Swap01-CX21-X0
  hb113 = ListNF.listnfeq' nf-p auto

  hb114 : Goal L.ax-X1-CCX0-CX01=CCX0-CX01-X1-CX21-CX20
  hb114 = ListNF.listnfeq' nf-p auto

  hb115 : Goal L.ax-X1-CCX0-CX01-CCX2=CCX2-CCX0-CX01-X1-CX21-CX20
  hb115 = ListNF.listnfeq' nf-p auto

  hb116 : Goal L.ax-X1-CCX0-CX02=CCX0-Swap12-Swap01-X2-Swap12-CX20
  hb116 = ListNF.listnfeq' nf-p auto

  hb117 : Goal L.ax-X1-CCX0-CX02-CCX1=CCX0-Swap12-CCX2-Swap01-X2-CX21-CX12-CX20
  hb117 = ListNF.listnfeq' nf-p auto

  hb118 : Goal L.ax-X1-CCX0-CCX1-CX02=CCX0-CCX1-CX12-Swap01-X2-Swap12-X0-CX10-CX20
  hb118 = ListNF.listnfeq' nf-p auto

  hb119 : Goal L.ax-X1-CCX0-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX12-X0-CX20-CCX0
  hb119 = ListNF.listnfeq' nf-p auto

  hb120 : Goal L.ax-X1-CCX0-CCX1-CX12-Swap01=CCX0-CCX1-CX02-X1-Swap12-CX10-CX20
  hb120 = ListNF.listnfeq' nf-p auto

  hb121 : Goal L.ax-X1-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX21-CX12-X0
  hb121 = ListNF.listnfeq' nf-p auto

  hb122 : Goal L.ax-X1-CCX0-CCX2-CX01=CCX2-CCX0-CX12-Swap01-X2-CX21-CX12-X0-CX10
  hb122 = ListNF.listnfeq' nf-p auto

  hb123 : Goal L.ax-X1-CCX0-CX12-Swap01=CX12-CCX0-Swap01-X1-X2-CX21-X0
  hb123 = ListNF.listnfeq' nf-p auto

  hb124 : Goal L.ax-X1-CCX0-CX12-CCX1-CX02=CX21-CCX0-CCX2-CX01-X1-CX21-CX12
  hb124 = ListNF.listnfeq' nf-p auto

  hb125 : Goal L.ax-X1-CCX0-CX12-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-X1-X2-CX21-CX12-X0
  hb125 = ListNF.listnfeq' nf-p auto

  hb126 : Goal L.ax-X1-CCX0-CX21-CCX2-CX01=CCX1-CCX0-CX01-CCX2-X1-CCX0
  hb126 = ListNF.listnfeq' nf-p auto

  hb127 : Goal L.ax-X1-CCX0-Swap12-Swap01=CCX0-CX02-X1-Swap12-CX10
  hb127 = ListNF.listnfeq' nf-p auto

  hb128 : Goal L.ax-X1-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-X1-Swap12
  hb128 = ListNF.listnfeq' nf-p auto

  hb129 : Goal L.ax-X1-CCX0-Swap12-CCX2-Swap01=CCX0-CX02-CCX1-X1-CX12-CX21-CX10
  hb129 = ListNF.listnfeq' nf-p auto

  hb130 : Goal L.ax-X2-Swap01=Swap01-X2
  hb130 = ListNF.listnfeq' nf-p auto

  hb131 : Goal L.ax-X2-CX01=CX01-X2
  hb131 = ListNF.listnfeq' nf-p auto

  hb132 : Goal L.ax-X2-CX01-CCX2=CX01-CCX2-X2
  hb132 = ListNF.listnfeq' nf-p auto

  hb133 : Goal L.ax-X2-CX01-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-CX01-X2-CX10
  hb133 = ListNF.listnfeq' nf-p auto

  hb134 : Goal L.ax-X2-CX01-CCX2-CCX0-CX01=CX01-CCX2-CCX0-Swap01-X2-CX10
  hb134 = ListNF.listnfeq' nf-p auto

  hb135 : Goal L.ax-X2-CX01-CX20-CCX2=CX01-CX20-CCX2-X2-CX12-X0
  hb135 = ListNF.listnfeq' nf-p auto

  hb136 : Goal L.ax-X2-CX01-CCX0-Swap01=CX10-CCX1-X2
  hb136 = ListNF.listnfeq' nf-p auto

  hb137 : Goal L.ax-X2-CX01-CCX0-CX02=CX01-CCX0-CX02-X2-CX12-CX10
  hb137 = ListNF.listnfeq' nf-p auto

  hb138 : Goal L.ax-X2-CX01-CCX0-CCX2-Swap01=CCX2-CX10-CCX1-X2-CX12
  hb138 = ListNF.listnfeq' nf-p auto

  hb139 : Goal L.ax-X2-CX01-CCX0-CCX2-CX01=CX10-CCX1-CCX2-CX01-X2-CX10
  hb139 = ListNF.listnfeq' nf-p auto

  hb140 : Goal L.ax-X2-CX02=CX02-X2
  hb140 = ListNF.listnfeq' nf-p auto

  hb141 : Goal L.ax-X2-CX02-CX01=CX02-CX01-X2
  hb141 = ListNF.listnfeq' nf-p auto

  hb142 : Goal L.ax-X2-CX02-CCX1=CCX1-CX02-X2
  hb142 = ListNF.listnfeq' nf-p auto

  hb143 : Goal L.ax-X2-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-X1-X2-CX21-CX12-X0-CX20
  hb143 = ListNF.listnfeq' nf-p auto

  hb144 : Goal L.ax-X2-CX02-CX10-CCX1=CX20-CCX1-CCX2-Swap01-X1-Swap12-X0-CX20-CCX0
  hb144 = ListNF.listnfeq' nf-p auto

  hb145 : Goal L.ax-X2-CX02-CCX0-CX01=CX20-CCX2-Swap01-X1-X2-CX21-CX12-CX10
  hb145 = ListNF.listnfeq' nf-p auto

  hb146 : Goal L.ax-X2-CCX1=CCX1-CX01-X2
  hb146 = ListNF.listnfeq' nf-p auto

  hb147 : Goal L.ax-X2-CCX1-CX01=CCX1-X2
  hb147 = ListNF.listnfeq' nf-p auto

  hb148 : Goal L.ax-X2-CCX1-CX01-CCX2=CCX1-CCX2-X2
  hb148 = ListNF.listnfeq' nf-p auto

  hb149 : Goal L.ax-X2-CCX1-CX02=CX02-CCX1-X2
  hb149 = ListNF.listnfeq' nf-p auto

  hb150 : Goal L.ax-X2-CCX1-CCX2=CCX1-CX01-CCX2-X2
  hb150 = ListNF.listnfeq' nf-p auto

  hb151 : Goal L.ax-X2-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-X2-CX12-CX10
  hb151 = ListNF.listnfeq' nf-p auto

  hb152 : Goal L.ax-X2-CCX1-CCX2-CX01=CCX1-CCX2-CX02-X2
  hb152 = ListNF.listnfeq' nf-p auto

  hb153 : Goal L.ax-X2-CCX1-CCX2-CX02=CCX1-CCX2-CX01-X2
  hb153 = ListNF.listnfeq' nf-p auto

  hb154 : Goal L.ax-X2-CCX1-CCX2-CCX0-Swap01=X1-CCX0-CCX1-CCX2-X2-CX21-X0-CX10-CX20
  hb154 = ListNF.listnfeq' nf-p auto

  hb155 : Goal L.ax-X2-CCX1-CX12-Swap01=CCX1-CX12-Swap01-X2-CX12-CX10
  hb155 = ListNF.listnfeq' nf-p auto

  hb156 : Goal L.ax-X2-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX12-Swap01-X2-CX12-CX10
  hb156 = ListNF.listnfeq' nf-p auto

  hb157 : Goal L.ax-X2-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX01-CX12-X0
  hb157 = ListNF.listnfeq' nf-p auto

  hb158 : Goal L.ax-X2-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2-Swap01-X2
  hb158 = ListNF.listnfeq' nf-p auto

  hb159 : Goal L.ax-X2-CCX1-CCX0-CX02=CCX0-CX02-CCX1-X2-CX12-CX10
  hb159 = ListNF.listnfeq' nf-p auto

  hb160 : Goal L.ax-X2-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-X2-CX12-CX10
  hb160 = ListNF.listnfeq' nf-p auto

  hb161 : Goal L.ax-X2-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX02-X2-CX12-CX10
  hb161 = ListNF.listnfeq' nf-p auto

  hb162 : Goal L.ax-X2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX12-CX21-X0
  hb162 = ListNF.listnfeq' nf-p auto

  hb163 : Goal L.ax-X2-CCX2=CCX2-X2
  hb163 = ListNF.listnfeq' nf-p auto

  hb164 : Goal L.ax-X2-CCX2-Swap01=CCX2-Swap01-X2
  hb164 = ListNF.listnfeq' nf-p auto

  hb165 : Goal L.ax-X2-CCX2-CX01=CCX2-CX01-X2
  hb165 = ListNF.listnfeq' nf-p auto

  hb166 : Goal L.ax-X2-CCX2-CX02=CCX2-CX02-X2
  hb166 = ListNF.listnfeq' nf-p auto

  hb167 : Goal L.ax-X2-CCX2-CX02-CCX1=CCX2-CCX1-CX02-X2
  hb167 = ListNF.listnfeq' nf-p auto

  hb168 : Goal L.ax-X2-CCX2-CCX1=CCX2-CCX1-CX01-X2
  hb168 = ListNF.listnfeq' nf-p auto

  hb169 : Goal L.ax-X2-CCX2-CCX1-CX01=CCX2-CCX1-X2
  hb169 = ListNF.listnfeq' nf-p auto

  hb170 : Goal L.ax-X2-CCX2-CCX1-CX02=CCX2-CX02-CCX1-X2
  hb170 = ListNF.listnfeq' nf-p auto

  hb171 : Goal L.ax-X2-CCX2-CCX1-CCX0-Swap12-Swap01=X1-CCX0-CCX2-CCX1-X1-CX21-CX12-X0-CX10-CX20
  hb171 = ListNF.listnfeq' nf-p auto

  hb172 : Goal L.ax-X2-CCX2-CX10-CCX1=CX01-CCX0-CCX2-Swap01-X2-CX12
  hb172 = ListNF.listnfeq' nf-p auto

  hb173 : Goal L.ax-X2-CCX2-CCX0-Swap01=CCX2-CCX0-CX01-X2-CX10
  hb173 = ListNF.listnfeq' nf-p auto

  hb174 : Goal L.ax-X2-CCX2-CCX0-CX01=CCX2-CCX0-Swap01-X2-CX10
  hb174 = ListNF.listnfeq' nf-p auto

  hb175 : Goal L.ax-X2-CCX2-CCX0-CX02-CCX1=CCX0-CX12-CCX1-CX02-X2-CX10-CCX0
  hb175 = ListNF.listnfeq' nf-p auto

  hb176 : Goal L.ax-X2-CCX2-CCX0-CX12-Swap01=CX12-CCX2-CCX0-Swap01-X2
  hb176 = ListNF.listnfeq' nf-p auto

  hb177 : Goal L.ax-X2-X1-CCX0-CCX1-CCX2=CCX1-CCX2-CCX0-Swap01-X1-X2-CX21-X0-CX10
  hb177 = ListNF.listnfeq' nf-p auto

  hb178 : Goal L.ax-X2-X1-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-X2-CX12-CX21-X0-CX20
  hb178 = ListNF.listnfeq' nf-p auto

  hb179 : Goal L.ax-X2-X2-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1
  hb179 = ListNF.listnfeq' nf-p auto

  hb180 : Goal L.ax-X2-CX12-Swap01=CX12-Swap01-X2
  hb180 = ListNF.listnfeq' nf-p auto

  hb181 : Goal L.ax-X2-CX12-CX01-CCX0-Swap01=CX10-CX12-CCX1-X2
  hb181 = ListNF.listnfeq' nf-p auto

  hb182 : Goal L.ax-X2-CX12-CCX1=CX12-CCX1-CX01-X2
  hb182 = ListNF.listnfeq' nf-p auto

  hb183 : Goal L.ax-X2-CX12-CCX1-CX01=CX12-CCX1-X2
  hb183 = ListNF.listnfeq' nf-p auto

  hb184 : Goal L.ax-X2-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-X2-CX21-CX12
  hb184 = ListNF.listnfeq' nf-p auto

  hb185 : Goal L.ax-X2-CX12-CCX2-Swap01=CX12-CCX2-Swap01-X2
  hb185 = ListNF.listnfeq' nf-p auto

  hb186 : Goal L.ax-X2-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-CX12-Swap01-X2
  hb186 = ListNF.listnfeq' nf-p auto

  hb187 : Goal L.ax-X2-CX12-CCX0-Swap01=CCX0-CX12-Swap01-X2
  hb187 = ListNF.listnfeq' nf-p auto

  hb188 : Goal L.ax-X2-CX21-CCX2-CX01=CX12-CCX1-CX02-X2-CX12-CX21
  hb188 = ListNF.listnfeq' nf-p auto

  hb189 : Goal L.ax-X2-CX21-CCX0-CCX2-Swap01=CCX0-CX21-CCX2-CX01-X1-X2-CX12-CX10
  hb189 = ListNF.listnfeq' nf-p auto

  hb190 : Goal L.ax-X2-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX1-CCX2-Swap01-CX12-X0-CX10-CX20-CCX0
  hb190 = ListNF.listnfeq' nf-p auto

  hb191 : Goal L.ax-X2-Swap12-Swap01=Swap12-Swap01-X0
  hb191 = ListNF.listnfeq' nf-p auto

  hb192 : Goal L.ax-X2-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX12-X0
  hb192 = ListNF.listnfeq' nf-p auto

  hb193 : Goal L.ax-X2-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12-X0
  hb193 = ListNF.listnfeq' nf-p auto

  hb194 : Goal L.ax-X2-CX10-CX02-CCX1=CX10-CCX1-CX02-X2
  hb194 = ListNF.listnfeq' nf-p auto

  hb195 : Goal L.ax-X2-CX10-CCX1=CX01-CCX0-Swap01-X2
  hb195 = ListNF.listnfeq' nf-p auto

  hb196 : Goal L.ax-X2-CX10-CCX1-CX02=CX10-CX02-CCX1-X2
  hb196 = ListNF.listnfeq' nf-p auto

  hb197 : Goal L.ax-X2-CX10-CCX1-CCX2-CX01=CX01-CCX0-CCX2-CX01-X2-CX10
  hb197 = ListNF.listnfeq' nf-p auto

  hb198 : Goal L.ax-X2-CX10-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2
  hb198 = ListNF.listnfeq' nf-p auto

  hb199 : Goal L.ax-X2-CX10-CCX2-CCX1-CX01=CX10-CCX2-CCX1-X2
  hb199 = ListNF.listnfeq' nf-p auto

  hb200 : Goal L.ax-X2-CX10-CX12-CCX1=CX12-CX01-CCX0-Swap01-X2
  hb200 = ListNF.listnfeq' nf-p auto

  hb201 : Goal L.ax-X2-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX12-X0
  hb201 = ListNF.listnfeq' nf-p auto

  hb202 : Goal L.ax-X2-CX20-CX01-CCX2=CX20-CCX2-CX01-X1-X2-CX12-X0
  hb202 = ListNF.listnfeq' nf-p auto

  hb203 : Goal L.ax-X2-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX01-X2-CX21-CX12-X0
  hb203 = ListNF.listnfeq' nf-p auto

  hb204 : Goal L.ax-X2-CX20-CCX1-CCX2-Swap01=CX02-CX10-CCX1-X2-Swap12-CX10-CX20-CCX0
  hb204 = ListNF.listnfeq' nf-p auto

  hb205 : Goal L.ax-X2-CX20-CCX1-CCX2-CX01=CCX1-CX20-CCX2-CX02-CX12-X0
  hb205 = ListNF.listnfeq' nf-p auto

  hb206 : Goal L.ax-X2-CX20-CCX1-CCX2-CX02=CX20-CCX2-CCX1-CX02-X1-CX21-CX12-X0
  hb206 = ListNF.listnfeq' nf-p auto

  hb207 : Goal L.ax-X2-CX20-CCX2=CX20-CCX2-X2-CX12-X0
  hb207 = ListNF.listnfeq' nf-p auto

  hb208 : Goal L.ax-X2-CX20-CCX2-Swap01=CX02-CCX0-CX01-X2-CX12-CX21-CX10-CX20
  hb208 = ListNF.listnfeq' nf-p auto

  hb209 : Goal L.ax-X2-CX20-CCX2-CX01=CX20-CX01-CCX2-X1-CX12-X0
  hb209 = ListNF.listnfeq' nf-p auto

  hb210 : Goal L.ax-X2-CX20-CCX2-CX02=CX20-CCX2-CX02-CX12-X0
  hb210 = ListNF.listnfeq' nf-p auto

  hb211 : Goal L.ax-X2-CX20-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CX21-CX10
  hb211 = ListNF.listnfeq' nf-p auto

  hb212 : Goal L.ax-X2-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-X1-CX12-CX21-X0
  hb212 = ListNF.listnfeq' nf-p auto

  hb213 : Goal L.ax-X2-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX02-X1-X2-CX12-CX21-X0
  hb213 = ListNF.listnfeq' nf-p auto

  hb214 : Goal L.ax-X2-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX12-X0
  hb214 = ListNF.listnfeq' nf-p auto

  hb215 : Goal L.ax-X2-CCX0-Swap01=CCX0-CX01-X2-CX10
  hb215 = ListNF.listnfeq' nf-p auto

  hb216 : Goal L.ax-X2-CCX0-CX01=CCX0-Swap01-X2-CX10
  hb216 = ListNF.listnfeq' nf-p auto

  hb217 : Goal L.ax-X2-CCX0-CX01-CCX2=CCX0-CCX2-Swap01-X2-CX12-CX10
  hb217 = ListNF.listnfeq' nf-p auto

  hb218 : Goal L.ax-X2-CCX0-CX02=CCX0-CX02-X2-CX12-CX10
  hb218 = ListNF.listnfeq' nf-p auto

  hb219 : Goal L.ax-X2-CCX0-CX02-CCX1=CCX1-CCX0-CX02-X2-CX12-CX10
  hb219 = ListNF.listnfeq' nf-p auto

  hb220 : Goal L.ax-X2-CCX0-CCX1-CX02=CCX1-CCX0-CX12-Swap01-X2-CX12-CX10
  hb220 = ListNF.listnfeq' nf-p auto

  hb221 : Goal L.ax-X2-CCX0-CCX1-CCX2=CCX1-CCX0-CCX2-Swap01-X2-CX12-CX10
  hb221 = ListNF.listnfeq' nf-p auto

  hb222 : Goal L.ax-X2-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CX01-CCX2-X2
  hb222 = ListNF.listnfeq' nf-p auto

  hb223 : Goal L.ax-X2-CCX0-CCX1-CX12-Swap01=CCX1-CX12-CCX0-Swap01-X2-CX12-CX10
  hb223 = ListNF.listnfeq' nf-p auto

  hb224 : Goal L.ax-X2-CCX0-CCX2-Swap01=CCX0-CX01-CCX2-X2-CX12-CX10
  hb224 = ListNF.listnfeq' nf-p auto

  hb225 : Goal L.ax-X2-CCX0-CCX2-CX01=CCX0-CX12-CCX2-Swap01-X2-CX10
  hb225 = ListNF.listnfeq' nf-p auto

  hb226 : Goal L.ax-X2-CCX0-CX12-Swap01=CX12-CCX0-Swap01-X2
  hb226 = ListNF.listnfeq' nf-p auto

  hb227 : Goal L.ax-X2-CCX0-CX12-CCX1-CX02=CCX2-CCX0-CX02-CCX1-X2-CCX0
  hb227 = ListNF.listnfeq' nf-p auto

  hb228 : Goal L.ax-X2-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-CX01-X2-CX10
  hb228 = ListNF.listnfeq' nf-p auto

  hb229 : Goal L.ax-X2-CCX0-CX21-CCX2-CX01=CX21-CCX0-CCX2-Swap01-X1-CX12-X0-CX10
  hb229 = ListNF.listnfeq' nf-p auto

  hb230 : Goal L.ax-X2-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21-X0
  hb230 = ListNF.listnfeq' nf-p auto

  hb231 : Goal L.ax-X2-CCX0-Swap12-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX12-X0-CX10-CX20-CCX0
  hb231 = ListNF.listnfeq' nf-p auto

  hb232 : Goal L.ax-X2-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX12-X0
  hb232 = ListNF.listnfeq' nf-p auto

  hb233 : Goal L.ax-CX12-CX02-CCX1-CCX0-CX02=X2-CCX0-CCX2-CCX1-X2-CX12-CCX0
  hb233 = ListNF.listnfeq' nf-p auto

  hb234 : Goal L.ax-CX12-X1-CCX0-CCX1-CCX2=CX20-CCX2-CCX1-CX02-X1-X2-CX12-X0-CX10-CX20-CCX0
  hb234 = ListNF.listnfeq' nf-p auto

  hb235 : Goal L.ax-CX12-X1-CCX0-CCX2-CCX1=CX20-CCX1-CCX2-CX01-X1-X2-CX12-X0-CX10-CX20-CCX0
  hb235 = ListNF.listnfeq' nf-p auto

  hb236 : Goal L.ax-CX12-X2-CCX0-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CCX0
  hb236 = ListNF.listnfeq' nf-p auto

  hb237 : Goal L.ax-CX12-CX20-CCX1-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX12-CCX0
  hb237 = ListNF.listnfeq' nf-p auto

  hb238 : Goal L.ax-CX12-CX20-CCX2-CCX1-CX02=X1-CCX0-CCX1-CCX2-X1-CX12-CCX0
  hb238 = ListNF.listnfeq' nf-p auto

  hb239 : Goal L.ax-CX21-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX1-CCX2-X1-CX21-CCX0
  hb239 = ListNF.listnfeq' nf-p auto

  hb240 : Goal L.ax-CX21-CX01-CCX0-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX21-CCX0
  hb240 = ListNF.listnfeq' nf-p auto

  hb241 : Goal L.ax-CX21-X1-CCX0-CCX1-CCX2=CX01-CCX2-CCX0-CX01-X1-CX21-CCX0
  hb241 = ListNF.listnfeq' nf-p auto

  hb242 : Goal L.ax-CX21-X1-CCX0-CCX2-CCX1=CX01-CCX0-CCX2-CX01-X1-CX21-CCX0
  hb242 = ListNF.listnfeq' nf-p auto

  hb243 : Goal L.ax-CX21-X2-CCX0-CCX2-CCX1=CX10-CCX1-CCX2-CX01-X1-X2-CX21-X0-CX10-CX20-CCX0
  hb243 = ListNF.listnfeq' nf-p auto

  hb244 : Goal L.ax-CX21-CX10-CCX1-CCX2-CX01=X2-CCX0-CCX2-CCX1-X2-CX21-CCX0
  hb244 = ListNF.listnfeq' nf-p auto

  hb245 : Goal L.ax-Swap12-CCX1-CCX0-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-CX12-CX21-CX10
  hb245 = ListNF.listnfeq' nf-p auto

  hb246 : Goal L.ax-Swap12-X1-CCX0-CCX1-CCX2=X2-CCX0-CCX2-CCX1-Swap12
  hb246 = ListNF.listnfeq' nf-p auto

  hb247 : Goal L.ax-Swap12-X1-CCX0-CCX2-CCX1=CCX1-CCX0-CCX2-Swap01-X2-CX21-CX12-CX20
  hb247 = ListNF.listnfeq' nf-p auto

  hb248 : Goal L.ax-Swap12-X2-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-Swap12
  hb248 = ListNF.listnfeq' nf-p auto

  hb249 : Goal L.ax-X0-Swap01=Swap01-X1
  hb249 = ListNF.listnfeq' nf-p auto

  hb250 : Goal L.ax-X0-CX01=CX01-X1-X0
  hb250 = ListNF.listnfeq' nf-p auto

  hb251 : Goal L.ax-X0-CX01-CCX2=CCX2-CX01-X1-CX12-X0
  hb251 = ListNF.listnfeq' nf-p auto

  hb252 : Goal L.ax-X0-CX01-CCX2-CCX0-Swap01=CX10-CCX1-CCX2-CX01-X1-CX12-CX21-X0
  hb252 = ListNF.listnfeq' nf-p auto

  hb253 : Goal L.ax-X0-CX01-CCX2-CCX0-CX01=CX01-CCX0-CCX2-CX01-X2-CX12-CX21-X0-CX20
  hb253 = ListNF.listnfeq' nf-p auto

  hb254 : Goal L.ax-X0-CX01-CX20-CCX2=CX20-CX21-CCX2-CX01-X1-CX12-X0
  hb254 = ListNF.listnfeq' nf-p auto

  hb255 : Goal L.ax-X0-CX01-CCX0-Swap01=CX01-CCX0-Swap01-X1-CX21-X0
  hb255 = ListNF.listnfeq' nf-p auto

  hb256 : Goal L.ax-X0-CX01-CCX0-CX02=CX10-Swap12-CCX2-Swap01-X1-CX12-CX20
  hb256 = ListNF.listnfeq' nf-p auto

  hb257 : Goal L.ax-X0-CX01-CCX0-CCX2-Swap01=CX10-CCX2-CCX1-CX01-X1-CX21-CX12-X0
  hb257 = ListNF.listnfeq' nf-p auto

  hb258 : Goal L.ax-X0-CX01-CCX0-CCX2-CX01=CX01-CCX2-CCX0-CX01-X1-X2-CX21-CX12-CX10-CX20
  hb258 = ListNF.listnfeq' nf-p auto

  hb259 : Goal L.ax-X0-CX02=CX02-X2-X0
  hb259 = ListNF.listnfeq' nf-p auto

  hb260 : Goal L.ax-X0-CX02-CX01=CX02-CX01-X1-X2-X0
  hb260 = ListNF.listnfeq' nf-p auto

  hb261 : Goal L.ax-X0-CX02-CCX1=CCX1-CX02-X2-CX21-X0
  hb261 = ListNF.listnfeq' nf-p auto

  hb262 : Goal L.ax-X0-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX01-X1-CX21-CX12-X0-CX20
  hb262 = ListNF.listnfeq' nf-p auto

  hb263 : Goal L.ax-X0-CX02-CX10-CCX1=CX20-CCX1-CCX2-Swap01-X1-CX21-CX12-CCX0
  hb263 = ListNF.listnfeq' nf-p auto

  hb264 : Goal L.ax-X0-CX02-CCX0-CX01=CX20-CCX2-Swap01-X1-CX21-CX12-CX10
  hb264 = ListNF.listnfeq' nf-p auto

  hb265 : Goal L.ax-X0-CCX1=CCX1-CX21-X0
  hb265 = ListNF.listnfeq' nf-p auto

  hb266 : Goal L.ax-X0-CCX1-CX01=CCX1-CX01-X1-CX21-X0
  hb266 = ListNF.listnfeq' nf-p auto

  hb267 : Goal L.ax-X0-CCX1-CX01-CCX2=CCX2-CCX1-CX01-X1-CX21-CX12-X0
  hb267 = ListNF.listnfeq' nf-p auto

  hb268 : Goal L.ax-X0-CCX1-CX02=CX02-CCX1-X1-X2-CX21-X0
  hb268 = ListNF.listnfeq' nf-p auto

  hb269 : Goal L.ax-X0-CCX1-CCX2=CCX2-CCX1-CX21-CX12-X0
  hb269 = ListNF.listnfeq' nf-p auto

  hb270 : Goal L.ax-X0-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-X1-CX20
  hb270 = ListNF.listnfeq' nf-p auto

  hb271 : Goal L.ax-X0-CCX1-CCX2-CX01=CCX2-CCX1-CX02-X2-CX21-CX12-X0
  hb271 = ListNF.listnfeq' nf-p auto

  hb272 : Goal L.ax-X0-CCX1-CCX2-CX02=CCX2-CX02-CCX1-X1-X2-CX21-CX12-X0
  hb272 = ListNF.listnfeq' nf-p auto

  hb273 : Goal L.ax-X0-CCX1-CCX2-CCX0-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20
  hb273 = ListNF.listnfeq' nf-p auto

  hb274 : Goal L.ax-X0-CCX1-CX12-Swap01=Swap12-CCX2-Swap01-X1-CX20
  hb274 = ListNF.listnfeq' nf-p auto

  hb275 : Goal L.ax-X0-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20
  hb275 = ListNF.listnfeq' nf-p auto

  hb276 : Goal L.ax-X0-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX02-X2-CX12-X0
  hb276 = ListNF.listnfeq' nf-p auto

  hb277 : Goal L.ax-X0-CCX1-CCX0-CX01-CCX2=CX21-CCX0-CCX2-CX01-X1-CX12-X0-CX20-CCX0
  hb277 = ListNF.listnfeq' nf-p auto

  hb278 : Goal L.ax-X0-CCX1-CCX0-CX02=CCX1-CCX0-CX12-Swap01-X1-Swap12-CX10-CX20
  hb278 = ListNF.listnfeq' nf-p auto

  hb279 : Goal L.ax-X0-CCX1-CCX0-CCX2-Swap01=X2-CCX0-CCX2-CCX1-X1-X2-CX21-X0-CX10
  hb279 = ListNF.listnfeq' nf-p auto

  hb280 : Goal L.ax-X0-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX02-X2-Swap12-X0-CX10-CX20
  hb280 = ListNF.listnfeq' nf-p auto

  hb281 : Goal L.ax-X0-CCX1-CCX0-Swap12-Swap01=CCX1-CX12-CCX0-Swap01-X1-CX21-CX20
  hb281 = ListNF.listnfeq' nf-p auto

  hb282 : Goal L.ax-X0-CCX2=CCX2-CX12-X0
  hb282 = ListNF.listnfeq' nf-p auto

  hb283 : Goal L.ax-X0-CCX2-Swap01=CX12-CCX2-Swap01-X1
  hb283 = ListNF.listnfeq' nf-p auto

  hb284 : Goal L.ax-X0-CCX2-CX01=CX01-CCX2-X1-X2-CX12-X0
  hb284 = ListNF.listnfeq' nf-p auto

  hb285 : Goal L.ax-X0-CCX2-CX02=CCX2-CX02-X2-CX12-X0
  hb285 = ListNF.listnfeq' nf-p auto

  hb286 : Goal L.ax-X0-CCX2-CX02-CCX1=CCX1-CCX2-CX02-X2-CX12-CX21-X0
  hb286 = ListNF.listnfeq' nf-p auto

  hb287 : Goal L.ax-X0-CCX2-CCX1=CCX1-CCX2-CX12-CX21-X0
  hb287 = ListNF.listnfeq' nf-p auto

  hb288 : Goal L.ax-X0-CCX2-CCX1-CX01=CCX1-CX01-CCX2-X1-X2-CX12-CX21-X0
  hb288 = ListNF.listnfeq' nf-p auto

  hb289 : Goal L.ax-X0-CCX2-CCX1-CX02=CCX1-CCX2-CX01-X1-CX12-CX21-X0
  hb289 = ListNF.listnfeq' nf-p auto

  hb290 : Goal L.ax-X0-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX2-CCX0-Swap01-X1-CX21-CX20
  hb290 = ListNF.listnfeq' nf-p auto

  hb291 : Goal L.ax-X0-CCX2-CX10-CCX1=CX10-CCX2-CCX1-CX21-X0
  hb291 = ListNF.listnfeq' nf-p auto

  hb292 : Goal L.ax-X0-CCX2-CCX0-Swap01=CX12-CCX2-CCX0-Swap01-X1
  hb292 = ListNF.listnfeq' nf-p auto

  hb293 : Goal L.ax-X0-CCX2-CCX0-CX01=CCX2-CCX0-CX12-Swap01-X1-CX10
  hb293 = ListNF.listnfeq' nf-p auto

  hb294 : Goal L.ax-X0-CCX2-CCX0-CX02-CCX1=CX21-CCX0-CCX2-Swap01-X1-CX21-CX12-CX10-CX20-CCX0
  hb294 = ListNF.listnfeq' nf-p auto

  hb295 : Goal L.ax-X0-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX01-X1-X0-CX10
  hb295 = ListNF.listnfeq' nf-p auto

  hb296 : Goal L.ax-X0-X1-CCX0-CCX1-CCX2=X1-CCX0-CCX2-CCX1-CX21-CX12-X0
  hb296 = ListNF.listnfeq' nf-p auto

  hb297 : Goal L.ax-X0-X1-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-CX12-CX21-X0
  hb297 = ListNF.listnfeq' nf-p auto

  hb298 : Goal L.ax-X0-X2-CCX0-CCX2-CCX1=CCX1-CCX0-CCX2-Swap01-X2-CX21-X0-CX10-CX20
  hb298 = ListNF.listnfeq' nf-p auto

  hb299 : Goal L.ax-X0-CX12-Swap01=CX12-Swap01-X1
  hb299 = ListNF.listnfeq' nf-p auto

  hb300 : Goal L.ax-X0-CX12-CX01-CCX0-Swap01=CX12-CX01-CCX0-Swap01-X1-CX21-X0
  hb300 = ListNF.listnfeq' nf-p auto

  hb301 : Goal L.ax-X0-CX12-CCX1=CX12-CCX1-CX21-X0
  hb301 = ListNF.listnfeq' nf-p auto

  hb302 : Goal L.ax-X0-CX12-CCX1-CX01=CX12-CCX1-CX01-X1-CX21-X0
  hb302 = ListNF.listnfeq' nf-p auto

  hb303 : Goal L.ax-X0-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-Swap12-X0
  hb303 = ListNF.listnfeq' nf-p auto

  hb304 : Goal L.ax-X0-CX12-CCX2-Swap01=CCX2-Swap01-X1
  hb304 = ListNF.listnfeq' nf-p auto

  hb305 : Goal L.ax-X0-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01-X1
  hb305 = ListNF.listnfeq' nf-p auto

  hb306 : Goal L.ax-X0-CX12-CCX0-Swap01=CX12-CCX0-Swap01-X1
  hb306 = ListNF.listnfeq' nf-p auto

  hb307 : Goal L.ax-X0-CX21-CCX2-CX01=CX12-CCX1-CX02-X2-Swap12-X0
  hb307 = ListNF.listnfeq' nf-p auto

  hb308 : Goal L.ax-X0-CX21-CCX0-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-X1-X2-CX12-CX21-X0-CX10-CCX0
  hb308 = ListNF.listnfeq' nf-p auto

  hb309 : Goal L.ax-X0-CX21-CCX0-CCX2-CX01=CCX1-CCX0-CX01-CCX2-X1-X2-CX12-X0-CCX0
  hb309 = ListNF.listnfeq' nf-p auto

  hb310 : Goal L.ax-X0-Swap12-Swap01=Swap12-Swap01-X1
  hb310 = ListNF.listnfeq' nf-p auto

  hb311 : Goal L.ax-X0-Swap12-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-X1-CX20
  hb311 = ListNF.listnfeq' nf-p auto

  hb312 : Goal L.ax-X0-Swap12-CCX2-Swap01=CCX1-CX12-Swap01-X1-CX20
  hb312 = ListNF.listnfeq' nf-p auto

  hb313 : Goal L.ax-X0-CX10-CX02-CCX1=CX10-CCX1-CX02-X2-CX21-X0
  hb313 = ListNF.listnfeq' nf-p auto

  hb314 : Goal L.ax-X0-CX10-CCX1=CX10-CCX1-CX21-X0
  hb314 = ListNF.listnfeq' nf-p auto

  hb315 : Goal L.ax-X0-CX10-CCX1-CX02=CX10-CX02-CCX1-X1-X2-CX21-X0
  hb315 = ListNF.listnfeq' nf-p auto

  hb316 : Goal L.ax-X0-CX10-CCX1-CCX2-CX01=CX01-CCX2-CCX0-Swap01-X2-CX21-CX12-X0
  hb316 = ListNF.listnfeq' nf-p auto

  hb317 : Goal L.ax-X0-CX10-CCX2-CCX1=CCX2-CX10-CCX1-CX21-X0
  hb317 = ListNF.listnfeq' nf-p auto

  hb318 : Goal L.ax-X0-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-Swap01-X1-X2-CX12-CX21-X0
  hb318 = ListNF.listnfeq' nf-p auto

  hb319 : Goal L.ax-X0-CX10-CX12-CCX1=CX10-CX12-CCX1-CX21-X0
  hb319 = ListNF.listnfeq' nf-p auto

  hb320 : Goal L.ax-X0-CX10-Swap12-CCX2-Swap01=CX01-CCX0-CX02-X1-X2-CX12-X0-CX10-CX20
  hb320 = ListNF.listnfeq' nf-p auto

  hb321 : Goal L.ax-X0-CX20-CX01-CCX2=CX20-CCX2-CX01-X1-CX12-X0
  hb321 = ListNF.listnfeq' nf-p auto

  hb322 : Goal L.ax-X0-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX21-CX12-X0
  hb322 = ListNF.listnfeq' nf-p auto

  hb323 : Goal L.ax-X0-CX20-CCX1-CCX2-Swap01=CX02-CX10-CCX1-X1-X2-CX12-CX21-X0-CX10-CX20-CCX0
  hb323 = ListNF.listnfeq' nf-p auto

  hb324 : Goal L.ax-X0-CX20-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX02-X2-CX21-CX12-X0
  hb324 = ListNF.listnfeq' nf-p auto

  hb325 : Goal L.ax-X0-CX20-CCX1-CCX2-CX02=CCX1-CX20-CCX2-CX02-X2-CX12-X0
  hb325 = ListNF.listnfeq' nf-p auto

  hb326 : Goal L.ax-X0-CX20-CCX2=CX20-CCX2-CX12-X0
  hb326 = ListNF.listnfeq' nf-p auto

  hb327 : Goal L.ax-X0-CX20-CCX2-Swap01=CX02-CCX0-CX01-X1-X2-CX12-CX21-X0-CX10-CX20
  hb327 = ListNF.listnfeq' nf-p auto

  hb328 : Goal L.ax-X0-CX20-CCX2-CX01=CX20-CX01-CCX2-X1-X2-CX12-X0
  hb328 = ListNF.listnfeq' nf-p auto

  hb329 : Goal L.ax-X0-CX20-CCX2-CX02=CX20-CCX2-CX02-X2-CX12-X0
  hb329 = ListNF.listnfeq' nf-p auto

  hb330 : Goal L.ax-X0-CX20-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-X0
  hb330 = ListNF.listnfeq' nf-p auto

  hb331 : Goal L.ax-X0-CX20-CCX2-CCX1-CX01=CX02-CCX1-CCX0-CX02-X1-X2-CX12-CX21-CX10
  hb331 = ListNF.listnfeq' nf-p auto

  hb332 : Goal L.ax-X0-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX01-X1-CX12-CX21-X0
  hb332 = ListNF.listnfeq' nf-p auto

  hb333 : Goal L.ax-X0-CX20-CX21-CCX2-CX01=CX01-CX20-CCX2-X1-X2-CX12-X0
  hb333 = ListNF.listnfeq' nf-p auto

  hb334 : Goal L.ax-X0-CCX0-Swap01=CCX0-Swap01-X1
  hb334 = ListNF.listnfeq' nf-p auto

  hb335 : Goal L.ax-X0-CCX0-CX01=CCX0-CX01-X1-X0
  hb335 = ListNF.listnfeq' nf-p auto

  hb336 : Goal L.ax-X0-CCX0-CX01-CCX2=CCX0-CCX2-CX01-X1-CX12-X0
  hb336 = ListNF.listnfeq' nf-p auto

  hb337 : Goal L.ax-X0-CCX0-CX02=CCX0-CX02-X2-X0
  hb337 = ListNF.listnfeq' nf-p auto

  hb338 : Goal L.ax-X0-CCX0-CX02-CCX1=CCX0-CCX1-CX02-X2-CX21-X0
  hb338 = ListNF.listnfeq' nf-p auto

  hb339 : Goal L.ax-X0-CCX0-CCX1-CX02=CCX0-CX02-CCX1-X1-X2-CX21-X0
  hb339 = ListNF.listnfeq' nf-p auto

  hb340 : Goal L.ax-X0-CCX0-CCX1-CCX2=CCX0-CCX2-CCX1-CX21-CX12-X0
  hb340 = ListNF.listnfeq' nf-p auto

  hb341 : Goal L.ax-X0-CCX0-CCX1-CCX2-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-X1-CX20
  hb341 = ListNF.listnfeq' nf-p auto

  hb342 : Goal L.ax-X0-CCX0-CCX1-CX12-Swap01=CCX0-Swap12-CCX2-Swap01-X1-CX20
  hb342 = ListNF.listnfeq' nf-p auto

  hb343 : Goal L.ax-X0-CCX0-CCX2-Swap01=CCX0-CX12-CCX2-Swap01-X1
  hb343 = ListNF.listnfeq' nf-p auto

  hb344 : Goal L.ax-X0-CCX0-CCX2-CX01=CCX0-CX01-CCX2-X1-X2-CX12-X0
  hb344 = ListNF.listnfeq' nf-p auto

  hb345 : Goal L.ax-X0-CCX0-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-X0
  hb345 = ListNF.listnfeq' nf-p auto

  hb346 : Goal L.ax-X0-CCX0-CX12-Swap01=CCX0-CX12-Swap01-X1
  hb346 = ListNF.listnfeq' nf-p auto

  hb347 : Goal L.ax-X0-CCX0-CX12-CCX1-CX02=CCX0-CX21-CCX2-CX01-X1-Swap12-X0
  hb347 = ListNF.listnfeq' nf-p auto

  hb348 : Goal L.ax-X0-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-Swap01-X1
  hb348 = ListNF.listnfeq' nf-p auto

  hb349 : Goal L.ax-X0-CCX0-CX21-CCX2-CX01=CCX0-CX12-CCX1-CX02-X2-Swap12-X0
  hb349 = ListNF.listnfeq' nf-p auto

  hb350 : Goal L.ax-X0-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-X1
  hb350 = ListNF.listnfeq' nf-p auto

  hb351 : Goal L.ax-X0-CCX0-Swap12-CCX1-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-X1-CX20
  hb351 = ListNF.listnfeq' nf-p auto

  hb352 : Goal L.ax-X0-CCX0-Swap12-CCX2-Swap01=CCX0-CCX1-CX12-Swap01-X1-CX20
  hb352 = ListNF.listnfeq' nf-p auto

  hb353 : Goal L.ax-CX10-CCX1-CX20-CCX2-CX02=X1-CCX0-CCX2-CCX1-X1-CX21-CX10-CCX0
  hb353 = ListNF.listnfeq' nf-p auto

  hb354 : Goal L.ax-CX10-X1-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1-X0-CX10-CX20-CCX0
  hb354 = ListNF.listnfeq' nf-p auto

  hb355 : Goal L.ax-CX10-X1-CCX0-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21-X0-CX10-CX20-CCX0
  hb355 = ListNF.listnfeq' nf-p auto

  hb356 : Goal L.ax-CX10-X2-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX01-X2-X0-CX10-CX20-CCX0
  hb356 = ListNF.listnfeq' nf-p auto

  hb357 : Goal L.ax-CX10-CX20-CCX1-CCX2-CX02=X1-CCX0-CCX1-CCX2-X1-CX10-CCX0
  hb357 = ListNF.listnfeq' nf-p auto

  hb358 : Goal L.ax-CX10-CX20-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2-CX20-CCX0
  hb358 = ListNF.listnfeq' nf-p auto

  hb359 : Goal L.ax-CX20-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX2-CCX1-X1-CCX0
  hb359 = ListNF.listnfeq' nf-p auto

  hb360 : Goal L.ax-CX20-CX01-CCX0-CCX2-CX01=X1-CCX0-CCX1-CCX2-X1-CCX0
  hb360 = ListNF.listnfeq' nf-p auto

  hb361 : Goal L.ax-CX20-X1-CCX0-CCX1-CCX2=CX01-CCX0-CCX2-CX01-X1-CX20-CCX0
  hb361 = ListNF.listnfeq' nf-p auto

  hb362 : Goal L.ax-CX20-X1-CCX0-CCX2-CCX1=CX01-CCX2-CCX0-CX01-X1-CX20-CCX0
  hb362 = ListNF.listnfeq' nf-p auto

  hb363 : Goal L.ax-CX20-X2-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2-X0-CX10-CX20-CCX0
  hb363 = ListNF.listnfeq' nf-p auto

  hb364 : Goal L.ax-CX20-CX10-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2-CX20-CCX0
  hb364 = ListNF.listnfeq' nf-p auto

  hb365 : Goal L.ax-CCX0-CCX1-CX20-CCX2-CX02=X1-CCX0-CCX2-CCX1-X1-CX21
  hb365 = ListNF.listnfeq' nf-p auto

  hb366 : Goal L.ax-CCX0-X1-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1
  hb366 = ListNF.listnfeq' nf-p auto

  hb367 : Goal L.ax-CCX0-X1-CCX0-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21
  hb367 = ListNF.listnfeq' nf-p auto

  hb368 : Goal L.ax-CCX0-X2-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2
  hb368 = ListNF.listnfeq' nf-p auto

  hb369 : Goal L.ax-CCX0-CX10-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2
  hb369 = ListNF.listnfeq' nf-p auto

  hb370 : Goal L.ax-CCX0-CX20-CCX1-CCX2-CX02=X1-CCX0-CCX1-CCX2-X1
  hb370 = ListNF.listnfeq' nf-p auto

  hb371 : Goal L.ax-Swap01-CX01=CX01-CX10
  hb371 = ListNF.listnfeq' nf-s6 auto

  hb372 : Goal L.ax-Swap01-CX01-CCX2=CX01-CCX2-CX12-CX10
  hb372 = ListNF.listnfeq' nf-s7 auto

  hb373 : Goal L.ax-Swap01-CX01-CCX2-CCX0-Swap01=CX10-CCX2-CCX1
  hb373 = ListNF.listnfeq' nf-s6 auto

  hb374 : Goal L.ax-Swap01-CX01-CCX2-CCX0-CX01=CX10-CCX2-CCX1-CX01-CX10
  hb374 = ListNF.listnfeq' nf-s6 auto

  hb375 : Goal L.ax-Swap01-CX01-CX20-CCX2=CX01-CX20-CCX2-CX12-CX10
  hb375 = ListNF.listnfeq' nf-s7 auto

  hb376 : Goal L.ax-Swap01-CX01-CCX0-Swap01=CX10-CCX1
  hb376 = ListNF.listnfeq' nf-s6 auto

  hb377 : Goal L.ax-Swap01-CX01-CCX0-CX02=CX01-CCX0-CX02-CX12-CX10
  hb377 = ListNF.listnfeq' nf-s7 auto

  hb378 : Goal L.ax-Swap01-CX01-CCX0-CCX2-Swap01=CCX2-CX10-CCX1-CX12
  hb378 = ListNF.listnfeq' nf-s7 auto

  hb379 : Goal L.ax-Swap01-CX01-CCX0-CCX2-CX01=CX10-CCX1-CCX2-CX01-CX10
  hb379 = ListNF.listnfeq' nf-s6 auto

  hb380 : Goal L.ax-Swap01-CX02=CX12-Swap01
  hb380 = ListNF.listnfeq' nf-s7 auto

  hb381 : Goal L.ax-Swap01-CX02-CX01=CX02-CX01-CX12-CX10
  hb381 = ListNF.listnfeq' nf-s7 auto

  hb382 : Goal L.ax-Swap01-CX02-CCX1=CX12-CCX0-Swap01
  hb382 = ListNF.listnfeq' nf-s7 auto

  hb383 : Goal L.ax-Swap01-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CX01-CCX2-CX12-CX10-CCX0
  hb383 = ListNF.listnfeq' nf-s7 auto

  hb384 : Goal L.ax-Swap01-CX02-CX10-CCX1=CX12-CX01-CCX0-Swap01
  hb384 = ListNF.listnfeq' nf-s7 auto

  hb385 : Goal L.ax-Swap01-CX02-CCX0-CX01=CX12-CCX1-CX01-CX10
  hb385 = ListNF.listnfeq' nf-s7 auto

  hb386 : Goal L.ax-Swap01-CCX1=CCX0-Swap01
  hb386 = ListNF.listnfeq' nf-s6 auto

  hb387 : Goal L.ax-Swap01-CCX1-CX01=CCX0-CX01-CX10
  hb387 = ListNF.listnfeq' nf-s6 auto

  hb388 : Goal L.ax-Swap01-CCX1-CX01-CCX2=CCX0-CX01-CCX2-CX12-CX10
  hb388 = ListNF.listnfeq' nf-s7 auto

  hb389 : Goal L.ax-Swap01-CCX1-CX02=CCX0-CX12-Swap01
  hb389 = ListNF.listnfeq' nf-s7 auto

  hb390 : Goal L.ax-Swap01-CCX1-CCX2=CCX0-CCX2-Swap01
  hb390 = ListNF.listnfeq' nf-s6 auto

  hb391 : Goal L.ax-Swap01-CCX1-CCX2-Swap01=CX20-CCX2-CX20-CCX0
  hb391 = ListNF.listnfeq' nf-s7 auto

  hb392 : Goal L.ax-Swap01-CCX1-CCX2-CX01=CCX0-CCX2-CX01-CX10
  hb392 = ListNF.listnfeq' nf-s6 auto

  hb393 : Goal L.ax-Swap01-CCX1-CCX2-CX02=CCX0-CX12-CCX2-Swap01
  hb393 = ListNF.listnfeq' nf-s7 auto

  hb394 : Goal L.ax-Swap01-CCX1-CCX2-CCX0-Swap01=CCX0-CCX2-CCX1
  hb394 = ListNF.listnfeq' nf-s6 auto

  hb395 : Goal L.ax-Swap01-CCX1-CX12-Swap01=CCX0-CX02
  hb395 = ListNF.listnfeq' nf-s7 auto

  hb396 : Goal L.ax-Swap01-CCX1-CX12-CCX0-Swap01=CCX0-CX02-CCX1
  hb396 = ListNF.listnfeq' nf-s7 auto

  hb397 : Goal L.ax-Swap01-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX1-CCX2-Swap01-CX20-CCX0
  hb397 = ListNF.listnfeq' nf-s7 auto

  hb398 : Goal L.ax-Swap01-CCX1-CCX0-CX01-CCX2=CX02-CCX1-CCX0-CX02-CX12-CCX0
  hb398 = ListNF.listnfeq' nf-s7 auto

  hb399 : Goal L.ax-Swap01-CCX1-CCX0-CX02=CCX0-CCX1-CX12-Swap01
  hb399 = ListNF.listnfeq' nf-s7 auto

  hb400 : Goal L.ax-Swap01-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2
  hb400 = ListNF.listnfeq' nf-s6 auto

  hb401 : Goal L.ax-Swap01-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX02
  hb401 = ListNF.listnfeq' nf-s7 auto

  hb402 : Goal L.ax-Swap01-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-Swap12
  hb402 = ListNF.listnfeq' nf-s7 auto

  hb403 : Goal L.ax-Swap01-CCX2=CCX2-Swap01
  hb403 = ListNF.listnfeq' nf-s6 auto

  hb404 : Goal L.ax-Swap01-CCX2-Swap01=CCX2
  hb404 = ListNF.listnfeq' nf-s6 auto

  hb405 : Goal L.ax-Swap01-CCX2-CX01=CCX2-CX01-CX10
  hb405 = ListNF.listnfeq' nf-s6 auto

  hb406 : Goal L.ax-Swap01-CCX2-CX02=CX12-CCX2-Swap01
  hb406 = ListNF.listnfeq' nf-s7 auto

  hb407 : Goal L.ax-Swap01-CCX2-CX02-CCX1=CX12-CCX2-CCX0-Swap01
  hb407 = ListNF.listnfeq' nf-s7 auto

  hb408 : Goal L.ax-Swap01-CCX2-CCX1=CCX2-CCX0-Swap01
  hb408 = ListNF.listnfeq' nf-s6 auto

  hb409 : Goal L.ax-Swap01-CCX2-CCX1-CX01=CCX2-CCX0-CX01-CX10
  hb409 = ListNF.listnfeq' nf-s6 auto

  hb410 : Goal L.ax-Swap01-CCX2-CCX1-CX02=CCX2-CCX0-CX12-Swap01
  hb410 = ListNF.listnfeq' nf-s7 auto

  hb411 : Goal L.ax-Swap01-CCX2-CX10-CCX1=CX01-CCX0-CCX2-Swap01-CX12
  hb411 = ListNF.listnfeq' nf-s7 auto

  hb412 : Goal L.ax-Swap01-CCX2-CCX0-Swap01=CCX2-CCX1
  hb412 = ListNF.listnfeq' nf-s6 auto

  hb413 : Goal L.ax-Swap01-CCX2-CCX0-CX01=CCX2-CCX1-CX01-CX10
  hb413 = ListNF.listnfeq' nf-s6 auto

  hb414 : Goal L.ax-Swap01-CCX2-CCX0-CX02-CCX1=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0
  hb414 = ListNF.listnfeq' nf-s7 auto

  hb415 : Goal L.ax-Swap01-CCX2-CCX0-CX12-Swap01=CCX2-CCX1-CX02
  hb415 = ListNF.listnfeq' nf-s7 auto

  hb416 : Goal L.ax-Swap01-CX12-Swap01=CX02
  hb416 = ListNF.listnfeq' nf-s7 auto

  hb417 : Goal L.ax-Swap01-CX12-CX01-CCX0-Swap01=CX02-CX10-CCX1
  hb417 = ListNF.listnfeq' nf-s7 auto

  hb418 : Goal L.ax-Swap01-CX12-CCX1=CX20-CCX2-Swap01-CX21-CX12
  hb418 = ListNF.listnfeq' nf-s7 auto

  hb419 : Goal L.ax-Swap01-CX12-CCX1-CX01=CX02-CCX0-CX01-CX10
  hb419 = ListNF.listnfeq' nf-s7 auto

  hb420 : Goal L.ax-Swap01-CX12-CCX1-CX02=CX20-CX01-CCX2-Swap12-CX20
  hb420 = ListNF.listnfeq' nf-s7 auto

  hb421 : Goal L.ax-Swap01-CX12-CCX2-Swap01=CCX2-CX02
  hb421 = ListNF.listnfeq' nf-s7 auto

  hb422 : Goal L.ax-Swap01-CX12-CCX2-CCX0-Swap01=CCX2-CX02-CCX1
  hb422 = ListNF.listnfeq' nf-s7 auto

  hb423 : Goal L.ax-Swap01-CX12-CCX0-Swap01=CX02-CCX1
  hb423 = ListNF.listnfeq' nf-s7 auto

  hb424 : Goal L.ax-Swap01-CX21-CCX2-CX01=CX20-CCX2-CX01-CX10
  hb424 = ListNF.listnfeq' nf-s7 auto

  hb425 : Goal L.ax-Swap01-CX21-CCX0-CCX2-Swap01=CX20-CCX1-CCX2
  hb425 = ListNF.listnfeq' nf-s7 auto

  hb426 : Goal L.ax-Swap01-CX21-CCX0-CCX2-CX01=CX20-CCX1-CCX2-CX01-CX10
  hb426 = ListNF.listnfeq' nf-s7 auto

  hb427 : Goal L.ax-Swap01-Swap12-Swap01=Swap12-Swap01-Swap12
  hb427 = ListNF.listnfeq' nf-s7 auto

  hb428 : Goal L.ax-Swap01-Swap12-CCX1-CCX2-Swap01=CX20-CCX2-CX02-CX20-CCX0
  hb428 = ListNF.listnfeq' nf-s7 auto

  hb429 : Goal L.ax-Swap01-Swap12-CCX2-Swap01=CCX0-Swap12-Swap01-Swap12
  hb429 = ListNF.listnfeq' nf-s7 auto

  hb430 : Goal L.ax-Swap01-CX10-CX02-CCX1=CX10-CCX1-CX02
  hb430 = ListNF.listnfeq' nf-s7 auto

  hb431 : Goal L.ax-Swap01-CX10-CCX1=CX01-CCX0-Swap01
  hb431 = ListNF.listnfeq' nf-s6 auto

  hb432 : Goal L.ax-Swap01-CX10-CCX1-CX02=CX10-CX02-CCX1
  hb432 = ListNF.listnfeq' nf-s7 auto

  hb433 : Goal L.ax-Swap01-CX10-CCX1-CCX2-CX01=CX01-CCX0-CCX2-CX01-CX10
  hb433 = ListNF.listnfeq' nf-s6 auto

  hb434 : Goal L.ax-Swap01-CX10-CCX2-CCX1=CX01-CCX2-CCX0-Swap01
  hb434 = ListNF.listnfeq' nf-s6 auto

  hb435 : Goal L.ax-Swap01-CX10-CCX2-CCX1-CX01=CX01-CCX2-CCX0-CX01-CX10
  hb435 = ListNF.listnfeq' nf-s6 auto

  hb436 : Goal L.ax-Swap01-CX10-CX12-CCX1=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0
  hb436 = ListNF.listnfeq' nf-s7 auto

  hb437 : Goal L.ax-Swap01-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX12
  hb437 = ListNF.listnfeq' nf-s7 auto

  hb438 : Goal L.ax-Swap01-CX20-CX01-CCX2=CX12-CCX1-CX02-Swap12-CX10
  hb438 = ListNF.listnfeq' nf-s7 auto

  hb439 : Goal L.ax-Swap01-CX20-CCX1-CCX2=CX21-CCX0-CCX2-Swap01
  hb439 = ListNF.listnfeq' nf-s7 auto

  hb440 : Goal L.ax-Swap01-CX20-CCX1-CCX2-Swap01=CX10-CX12-CCX1-Swap12-CX10-CX20-CCX0
  hb440 = ListNF.listnfeq' nf-s7 auto

  hb441 : Goal L.ax-Swap01-CX20-CCX1-CCX2-CX01=CX21-CCX0-CCX2-CX01-CX10
  hb441 = ListNF.listnfeq' nf-s7 auto

  hb442 : Goal L.ax-Swap01-CX20-CCX1-CCX2-CX02=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10-CX20-CCX0
  hb442 = ListNF.listnfeq' nf-s7 auto

  hb443 : Goal L.ax-Swap01-CX20-CCX2=CCX1-CCX2-Swap01-CX20-CCX0
  hb443 = ListNF.listnfeq' nf-s7 auto

  hb444 : Goal L.ax-Swap01-CX20-CCX2-Swap01=CX12-CCX1-CX12-CX21
  hb444 = ListNF.listnfeq' nf-s7 auto

  hb445 : Goal L.ax-Swap01-CX20-CCX2-CX01=CX21-CCX2-CX01-CX10
  hb445 = ListNF.listnfeq' nf-s7 auto

  hb446 : Goal L.ax-Swap01-CX20-CCX2-CX02=Swap12-CCX1-CCX2-Swap01-CX20-CCX0
  hb446 = ListNF.listnfeq' nf-s7 auto

  hb447 : Goal L.ax-Swap01-CX20-CCX2-CCX1=CCX0-CCX1-CCX2-Swap01-CX21-CCX0
  hb447 = ListNF.listnfeq' nf-s7 auto

  hb448 : Goal L.ax-Swap01-CX20-CCX2-CCX1-CX01=CCX0-CX21-CCX2-CX01-CX21-CX10-CX20
  hb448 = ListNF.listnfeq' nf-s7 auto

  hb449 : Goal L.ax-Swap01-CX20-CCX2-CCX1-CX02=CCX0-CX12-CCX1-CX02-CX21-CX12-CX10-CX20
  hb449 = ListNF.listnfeq' nf-s7 auto

  hb450 : Goal L.ax-Swap01-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX10
  hb450 = ListNF.listnfeq' nf-s7 auto

  hb451 : Goal L.ax-Swap01-CCX0-Swap01=CCX1
  hb451 = ListNF.listnfeq' nf-s6 auto

  hb452 : Goal L.ax-Swap01-CCX0-CX01=CCX1-CX01-CX10
  hb452 = ListNF.listnfeq' nf-s6 auto

  hb453 : Goal L.ax-Swap01-CCX0-CX01-CCX2=CCX1-CX01-CCX2-CX12-CX10
  hb453 = ListNF.listnfeq' nf-s7 auto

  hb454 : Goal L.ax-Swap01-CCX0-CX02=CCX1-CX12-Swap01
  hb454 = ListNF.listnfeq' nf-s7 auto

  hb455 : Goal L.ax-Swap01-CCX0-CX02-CCX1=CCX1-CX12-CCX0-Swap01
  hb455 = ListNF.listnfeq' nf-s7 auto

  hb456 : Goal L.ax-Swap01-CCX0-CCX1-CX02=CCX1-CCX0-CX12-Swap01
  hb456 = ListNF.listnfeq' nf-s7 auto

  hb457 : Goal L.ax-Swap01-CCX0-CCX1-CCX2=CCX1-CCX0-CCX2-Swap01
  hb457 = ListNF.listnfeq' nf-s6 auto

  hb458 : Goal L.ax-Swap01-CCX0-CCX1-CCX2-Swap01=CX20-CCX2-CCX1-CX21-CX20-CCX0
  hb458 = ListNF.listnfeq' nf-s7 auto

  hb459 : Goal L.ax-Swap01-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX02
  hb459 = ListNF.listnfeq' nf-s7 auto

  hb460 : Goal L.ax-Swap01-CCX0-CCX2-Swap01=CCX1-CCX2
  hb460 = ListNF.listnfeq' nf-s6 auto

  hb461 : Goal L.ax-Swap01-CCX0-CCX2-CX01=CCX1-CCX2-CX01-CX10
  hb461 = ListNF.listnfeq' nf-s6 auto

  hb462 : Goal L.ax-Swap01-CCX0-CCX2-CCX1=CCX1-CCX2-CCX0-Swap01
  hb462 = ListNF.listnfeq' nf-s6 auto

  hb463 : Goal L.ax-Swap01-CCX0-CX12-Swap01=CCX1-CX02
  hb463 = ListNF.listnfeq' nf-s7 auto

  hb464 : Goal L.ax-Swap01-CCX0-CX12-CCX1-CX02=CX20-CCX2-CCX1-CX02-CX12-CX21-CX20
  hb464 = ListNF.listnfeq' nf-s7 auto

  hb465 : Goal L.ax-Swap01-CCX0-CX12-CCX2-Swap01=CCX1-CCX2-CX02
  hb465 = ListNF.listnfeq' nf-s7 auto

  hb466 : Goal L.ax-Swap01-CCX0-CX21-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21-CX10
  hb466 = ListNF.listnfeq' nf-s7 auto

  hb467 : Goal L.ax-Swap01-CCX0-Swap12-Swap01=Swap12-CCX2-Swap01-Swap12
  hb467 = ListNF.listnfeq' nf-s7 auto

  hb468 : Goal L.ax-Swap01-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX20-CCX0
  hb468 = ListNF.listnfeq' nf-s7 auto

  hb469 : Goal L.ax-Swap01-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-Swap12
  hb469 = ListNF.listnfeq' nf-s7 auto

  hb470 : Goal L.ax-CX01-Swap01=Swap01-CX10
  hb470 = ListNF.listnfeq' nf-s6 auto

  hb471 : Goal L.ax-CX01-CX01-CCX2=CCX2
  hb471 = ListNF.listnfeq' nf-s6 auto

  hb472 : Goal L.ax-CX01-CX01-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01
  hb472 = ListNF.listnfeq' nf-s6 auto

  hb473 : Goal L.ax-CX01-CX01-CCX2-CCX0-CX01=CCX2-CCX0-CX01
  hb473 = ListNF.listnfeq' nf-s6 auto

  hb474 : Goal L.ax-CX01-CX01-CX20-CCX2=CX20-CCX2
  hb474 = ListNF.listnfeq' nf-s7 auto

  hb475 : Goal L.ax-CX01-CX01-CCX0-Swap01=CCX0-Swap01
  hb475 = ListNF.listnfeq' nf-s6 auto

  hb476 : Goal L.ax-CX01-CX01-CCX0-CX02=CCX0-CX02
  hb476 = ListNF.listnfeq' nf-s7 auto

  hb477 : Goal L.ax-CX01-CX01-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01
  hb477 = ListNF.listnfeq' nf-s6 auto

  hb478 : Goal L.ax-CX01-CX01-CCX0-CCX2-CX01=CCX0-CCX2-CX01
  hb478 = ListNF.listnfeq' nf-s6 auto

  hb479 : Goal L.ax-CX01-CX02=CX02-CX01
  hb479 = ListNF.listnfeq' nf-s7 auto

  hb480 : Goal L.ax-CX01-CX02-CX01=CX02
  hb480 = ListNF.listnfeq' nf-s7 auto

  hb481 : Goal L.ax-CX01-CX02-CCX1=CCX1-CX02
  hb481 = ListNF.listnfeq' nf-s7 auto

  hb482 : Goal L.ax-CX01-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX21-CX20
  hb482 = ListNF.listnfeq' nf-s7 auto

  hb483 : Goal L.ax-CX01-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10
  hb483 = ListNF.listnfeq' nf-s7 auto

  hb484 : Goal L.ax-CX01-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10
  hb484 = ListNF.listnfeq' nf-s7 auto

  hb485 : Goal L.ax-CX01-CCX1=CCX1-CX01
  hb485 = ListNF.listnfeq' nf-s6 auto

  hb486 : Goal L.ax-CX01-CCX1-CX01=CCX1
  hb486 = ListNF.listnfeq' nf-s6 auto

  hb487 : Goal L.ax-CX01-CCX1-CX01-CCX2=CCX1-CCX2
  hb487 = ListNF.listnfeq' nf-s6 auto

  hb488 : Goal L.ax-CX01-CCX1-CX02=CX02-CCX1
  hb488 = ListNF.listnfeq' nf-s7 auto

  hb489 : Goal L.ax-CX01-CCX1-CCX2=CCX1-CX01-CCX2
  hb489 = ListNF.listnfeq' nf-s6 auto

  hb490 : Goal L.ax-CX01-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX12-CX10
  hb490 = ListNF.listnfeq' nf-s7 auto

  hb491 : Goal L.ax-CX01-CCX1-CCX2-CX01=CCX1-CCX2-CX02
  hb491 = ListNF.listnfeq' nf-s7 auto

  hb492 : Goal L.ax-CX01-CCX1-CCX2-CX02=CCX1-CCX2-CX01
  hb492 = ListNF.listnfeq' nf-s7 auto

  hb493 : Goal L.ax-CX01-CCX1-CCX2-CCX0-Swap01=CX21-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0
  hb493 = ListNF.listnfeq' nf-s7 auto

  hb494 : Goal L.ax-CX01-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CX12-CX10
  hb494 = ListNF.listnfeq' nf-s7 auto

  hb495 : Goal L.ax-CX01-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX02-CX12-CX10
  hb495 = ListNF.listnfeq' nf-s7 auto

  hb496 : Goal L.ax-CX01-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX01
  hb496 = ListNF.listnfeq' nf-s7 auto

  hb497 : Goal L.ax-CX01-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2
  hb497 = ListNF.listnfeq' nf-s6 auto

  hb498 : Goal L.ax-CX01-CCX1-CCX0-CX02=CCX0-CX02-CCX1
  hb498 = ListNF.listnfeq' nf-s7 auto

  hb499 : Goal L.ax-CX01-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-CX10
  hb499 = ListNF.listnfeq' nf-s7 auto

  hb500 : Goal L.ax-CX01-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX12-Swap01-CX12-CX10
  hb500 = ListNF.listnfeq' nf-s7 auto

  hb501 : Goal L.ax-CX01-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX12
  hb501 = ListNF.listnfeq' nf-s7 auto

  hb502 : Goal L.ax-CX01-CCX2-Swap01=CCX2-Swap01-CX12-CX10
  hb502 = ListNF.listnfeq' nf-s7 auto

  hb503 : Goal L.ax-CX01-CCX2-CX01=CCX2-CX02
  hb503 = ListNF.listnfeq' nf-s7 auto

  hb504 : Goal L.ax-CX01-CCX2-CX02=CCX2-CX01
  hb504 = ListNF.listnfeq' nf-s7 auto

  hb505 : Goal L.ax-CX01-CCX2-CX02-CCX1=CCX2-CCX1-CX01
  hb505 = ListNF.listnfeq' nf-s7 auto

  hb506 : Goal L.ax-CX01-CCX2-CCX1=CCX2-CCX1-CX02
  hb506 = ListNF.listnfeq' nf-s7 auto

  hb507 : Goal L.ax-CX01-CCX2-CCX1-CX01=CCX2-CX02-CCX1
  hb507 = ListNF.listnfeq' nf-s7 auto

  hb508 : Goal L.ax-CX01-CCX2-CCX1-CX02=CCX2-CCX1
  hb508 = ListNF.listnfeq' nf-s7 auto

  hb509 : Goal L.ax-CX01-CCX2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX10
  hb509 = ListNF.listnfeq' nf-s7 auto

  hb510 : Goal L.ax-CX01-CCX2-CX10-CCX1=CCX0-CX01-CCX2-CX10
  hb510 = ListNF.listnfeq' nf-s6 auto

  hb511 : Goal L.ax-CX01-CCX2-CCX0-CX12-Swap01=CX10-CCX2-CCX1
  hb511 = ListNF.listnfeq' nf-s7 auto

  hb512 : Goal L.ax-CX01-CX12-Swap01=CX12-Swap01-CX12-CX10
  hb512 = ListNF.listnfeq' nf-s7 auto

  hb513 : Goal L.ax-CX01-CX12-CX01-CCX0-Swap01=CX20-CCX2-CX01-CX21-CX12-CX20
  hb513 = ListNF.listnfeq' nf-s7 auto

  hb514 : Goal L.ax-CX01-CX12-CCX1=CX12-CCX1-CX02
  hb514 = ListNF.listnfeq' nf-s7 auto

  hb515 : Goal L.ax-CX01-CX12-CCX1-CX01=CX21-CCX2-CX01-CX21-CX12
  hb515 = ListNF.listnfeq' nf-s7 auto

  hb516 : Goal L.ax-CX01-CX12-CCX1-CX02=CX12-CCX1
  hb516 = ListNF.listnfeq' nf-s7 auto

  hb517 : Goal L.ax-CX01-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CX10
  hb517 = ListNF.listnfeq' nf-s7 auto

  hb518 : Goal L.ax-CX01-CX12-CCX2-CCX0-Swap01=CX10-CCX2-CCX1-CX01
  hb518 = ListNF.listnfeq' nf-s7 auto

  hb519 : Goal L.ax-CX01-CX12-CCX0-Swap01=CX10-CCX1-CX02
  hb519 = ListNF.listnfeq' nf-s7 auto

  hb520 : Goal L.ax-CX01-CX21-CCX2-CX01=CX12-CCX1-CX01-CX12-CX21
  hb520 = ListNF.listnfeq' nf-s7 auto

  hb521 : Goal L.ax-CX01-CX21-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0
  hb521 = ListNF.listnfeq' nf-s7 auto

  hb522 : Goal L.ax-CX01-Swap12-Swap01=Swap12-Swap01-CX12
  hb522 = ListNF.listnfeq' nf-s7 auto

  hb523 : Goal L.ax-CX01-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX10
  hb523 = ListNF.listnfeq' nf-s7 auto

  hb524 : Goal L.ax-CX01-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12
  hb524 = ListNF.listnfeq' nf-s7 auto

  hb525 : Goal L.ax-CX01-CX10-CX02-CCX1=CCX0-CX12-Swap01
  hb525 = ListNF.listnfeq' nf-s7 auto

  hb526 : Goal L.ax-CX01-CX10-CCX1=CCX0-CX01-CX10
  hb526 = ListNF.listnfeq' nf-s6 auto

  hb527 : Goal L.ax-CX01-CX10-CCX1-CX02=CX12-CCX0-Swap01
  hb527 = ListNF.listnfeq' nf-s7 auto

  hb528 : Goal L.ax-CX01-CX10-CCX1-CCX2-CX01=CCX0-CX12-CCX2-Swap01
  hb528 = ListNF.listnfeq' nf-s7 auto

  hb529 : Goal L.ax-CX01-CX10-CCX2-CCX1=CCX2-CCX0-CX12-Swap01
  hb529 = ListNF.listnfeq' nf-s7 auto

  hb530 : Goal L.ax-CX01-CX10-CCX2-CCX1-CX01=CX12-CCX2-CCX0-Swap01
  hb530 = ListNF.listnfeq' nf-s7 auto

  hb531 : Goal L.ax-CX01-CX10-CX12-CCX1=CX20-CX01-CCX2-Swap12-CX20
  hb531 = ListNF.listnfeq' nf-s7 auto

  hb532 : Goal L.ax-CX01-CX10-Swap12-CCX2-Swap01=CCX0-Swap12-Swap01-CX12-CX21
  hb532 = ListNF.listnfeq' nf-s7 auto

  hb533 : Goal L.ax-CX01-CX20-CX01-CCX2=CX10-CX12-CCX1-Swap12-CX10
  hb533 = ListNF.listnfeq' nf-s7 auto

  hb534 : Goal L.ax-CX01-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX02-CX21
  hb534 = ListNF.listnfeq' nf-s7 auto

  hb535 : Goal L.ax-CX01-CX20-CCX1-CCX2-Swap01=CX20-CCX2-Swap01-CX12-CX10-CX20-CCX0
  hb535 = ListNF.listnfeq' nf-s7 auto

  hb536 : Goal L.ax-CX01-CX20-CCX1-CCX2-CX01=CCX1-CX20-CCX2-CX02
  hb536 = ListNF.listnfeq' nf-s7 auto

  hb537 : Goal L.ax-CX01-CX20-CCX1-CCX2-CX02=CX20-CCX2-CCX1-CX01-CX21
  hb537 = ListNF.listnfeq' nf-s7 auto

  hb538 : Goal L.ax-CX01-CX20-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX12-CX10-CX20-CCX0
  hb538 = ListNF.listnfeq' nf-s7 auto

  hb539 : Goal L.ax-CX01-CX20-CCX2-CX01=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10
  hb539 = ListNF.listnfeq' nf-s7 auto

  hb540 : Goal L.ax-CX01-CX20-CCX2-CX02=CX20-CX21-CCX2-CX01
  hb540 = ListNF.listnfeq' nf-s7 auto

  hb541 : Goal L.ax-CX01-CX20-CCX2-CCX1=CX02-CCX1-CCX0-CX02-CX21-CX20
  hb541 = ListNF.listnfeq' nf-s7 auto

  hb542 : Goal L.ax-CX01-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX02-CX21
  hb542 = ListNF.listnfeq' nf-s7 auto

  hb543 : Goal L.ax-CX01-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX21
  hb543 = ListNF.listnfeq' nf-s7 auto

  hb544 : Goal L.ax-CX01-CX20-CX21-CCX2-CX01=CX20-CCX2-CX02
  hb544 = ListNF.listnfeq' nf-s7 auto

  hb545 : Goal L.ax-CX01-CCX0-CX01=CX10-CCX1-CX10
  hb545 = ListNF.listnfeq' nf-s6 auto

  hb546 : Goal L.ax-CX01-CCX0-CX01-CCX2=CCX2-CX10-CCX1-CX10
  hb546 = ListNF.listnfeq' nf-s6 auto

  hb547 : Goal L.ax-CX01-CCX0-CX02-CCX1=CCX1-CCX0-CX02
  hb547 = ListNF.listnfeq' nf-s7 auto

  hb548 : Goal L.ax-CX01-CCX0-CCX1-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX10
  hb548 = ListNF.listnfeq' nf-s7 auto

  hb549 : Goal L.ax-CX01-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2
  hb549 = ListNF.listnfeq' nf-s6 auto

  hb550 : Goal L.ax-CX01-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10
  hb550 = ListNF.listnfeq' nf-s7 auto

  hb551 : Goal L.ax-CX01-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CX12-CX10
  hb551 = ListNF.listnfeq' nf-s7 auto

  hb552 : Goal L.ax-CX01-CCX0-CCX2-CCX1=CCX0-CX12-CCX1-CX02-CX12-CCX0
  hb552 = ListNF.listnfeq' nf-s7 auto

  hb553 : Goal L.ax-CX01-CCX0-CX12-Swap01=CX10-CX02-CCX1
  hb553 = ListNF.listnfeq' nf-s7 auto

  hb554 : Goal L.ax-CX01-CCX0-CX12-CCX1-CX02=CCX0-CCX2-CCX1-CX12-CX10-CCX0
  hb554 = ListNF.listnfeq' nf-s7 auto

  hb555 : Goal L.ax-CX01-CCX0-CX12-CCX2-Swap01=CX10-CCX1-CCX2-CX01
  hb555 = ListNF.listnfeq' nf-s7 auto

  hb556 : Goal L.ax-CX01-CCX0-Swap12-Swap01=CX10-Swap12-CCX2-Swap01-CX21-CX12
  hb556 = ListNF.listnfeq' nf-s7 auto

  hb557 : Goal L.ax-CX01-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10
  hb557 = ListNF.listnfeq' nf-s7 auto

  hb558 : Goal L.ax-CX01-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX12
  hb558 = ListNF.listnfeq' nf-s7 auto

  hb559 : Goal L.ax-CX02-Swap01=Swap01-CX12
  hb559 = ListNF.listnfeq' nf-s7 auto

  hb560 : Goal L.ax-CX02-CX01-CCX2=CCX2-CX01
  hb560 = ListNF.listnfeq' nf-s7 auto

  hb561 : Goal L.ax-CX02-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12
  hb561 = ListNF.listnfeq' nf-s7 auto

  hb562 : Goal L.ax-CX02-CX01-CCX2-CCX0-CX01=CCX2-CX10-CCX1-CX10
  hb562 = ListNF.listnfeq' nf-s7 auto

  hb563 : Goal L.ax-CX02-CX01-CX20-CCX2=CX01-CCX0-CX02-CX20
  hb563 = ListNF.listnfeq' nf-s7 auto

  hb564 : Goal L.ax-CX02-CX01-CCX0-Swap01=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0
  hb564 = ListNF.listnfeq' nf-s7 auto

  hb565 : Goal L.ax-CX02-CX01-CCX0-CX02=CX01-CX20-CCX2-CX20
  hb565 = ListNF.listnfeq' nf-s7 auto

  hb566 : Goal L.ax-CX02-CX01-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX12
  hb566 = ListNF.listnfeq' nf-s7 auto

  hb567 : Goal L.ax-CX02-CX01-CCX0-CCX2-CX01=CX10-CCX2-CCX1-CX01-CX12-CX10
  hb567 = ListNF.listnfeq' nf-s7 auto

  hb568 : Goal L.ax-CX02-CX02-CX01=CX01
  hb568 = ListNF.listnfeq' nf-s7 auto

  hb569 : Goal L.ax-CX02-CX02-CCX1=CCX1
  hb569 = ListNF.listnfeq' nf-s7 auto

  hb570 : Goal L.ax-CX02-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CX02
  hb570 = ListNF.listnfeq' nf-s7 auto

  hb571 : Goal L.ax-CX02-CX02-CX10-CCX1=CX10-CCX1
  hb571 = ListNF.listnfeq' nf-s7 auto

  hb572 : Goal L.ax-CX02-CX02-CCX0-CX01=CCX0-CX01
  hb572 = ListNF.listnfeq' nf-s7 auto

  hb573 : Goal L.ax-CX02-CCX1-CX01=CCX1-CX02
  hb573 = ListNF.listnfeq' nf-s7 auto

  hb574 : Goal L.ax-CX02-CCX1-CX01-CCX2=CCX1-CCX2-CX02
  hb574 = ListNF.listnfeq' nf-s7 auto

  hb575 : Goal L.ax-CX02-CCX1-CX02=CCX1-CX01
  hb575 = ListNF.listnfeq' nf-s7 auto

  hb576 : Goal L.ax-CX02-CCX1-CCX2=CCX1-CCX2-CX01
  hb576 = ListNF.listnfeq' nf-s7 auto

  hb577 : Goal L.ax-CX02-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX10
  hb577 = ListNF.listnfeq' nf-s7 auto

  hb578 : Goal L.ax-CX02-CCX1-CCX2-CX01=CCX1-CCX2
  hb578 = ListNF.listnfeq' nf-s7 auto

  hb579 : Goal L.ax-CX02-CCX1-CCX2-CX02=CCX1-CX01-CCX2
  hb579 = ListNF.listnfeq' nf-s7 auto

  hb580 : Goal L.ax-CX02-CCX1-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CX10
  hb580 = ListNF.listnfeq' nf-s7 auto

  hb581 : Goal L.ax-CX02-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CX10
  hb581 = ListNF.listnfeq' nf-s7 auto

  hb582 : Goal L.ax-CX02-CCX1-CX12-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX20
  hb582 = ListNF.listnfeq' nf-s7 auto

  hb583 : Goal L.ax-CX02-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX2-Swap01-CX21-CX12
  hb583 = ListNF.listnfeq' nf-s7 auto

  hb584 : Goal L.ax-CX02-CCX1-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-Swap12-CX10-CX20-CCX0
  hb584 = ListNF.listnfeq' nf-s7 auto

  hb585 : Goal L.ax-CX02-CCX1-CCX0-CX12-Swap01=CX20-CCX1-CCX2-Swap12-CX20
  hb585 = ListNF.listnfeq' nf-s7 auto

  hb586 : Goal L.ax-CX02-CCX1-CCX0-Swap12-Swap01=CX20-CCX1-CCX2-CX01-Swap12
  hb586 = ListNF.listnfeq' nf-s7 auto

  hb587 : Goal L.ax-CX02-CCX2=CCX2-CX02
  hb587 = ListNF.listnfeq' nf-s7 auto

  hb588 : Goal L.ax-CX02-CCX2-Swap01=CCX2-Swap01-CX12
  hb588 = ListNF.listnfeq' nf-s7 auto

  hb589 : Goal L.ax-CX02-CCX2-CX01=CX01-CCX2
  hb589 = ListNF.listnfeq' nf-s7 auto

  hb590 : Goal L.ax-CX02-CCX2-CX02=CCX2
  hb590 = ListNF.listnfeq' nf-s7 auto

  hb591 : Goal L.ax-CX02-CCX2-CX02-CCX1=CCX2-CCX1
  hb591 = ListNF.listnfeq' nf-s7 auto

  hb592 : Goal L.ax-CX02-CCX2-CCX1=CCX2-CX02-CCX1
  hb592 = ListNF.listnfeq' nf-s7 auto

  hb593 : Goal L.ax-CX02-CCX2-CCX1-CX01=CCX2-CCX1-CX02
  hb593 = ListNF.listnfeq' nf-s7 auto

  hb594 : Goal L.ax-CX02-CCX2-CCX1-CX02=CCX2-CCX1-CX01
  hb594 = ListNF.listnfeq' nf-s7 auto

  hb595 : Goal L.ax-CX02-CCX2-CCX1-CCX0-Swap12-Swap01=CX21-CCX0-CCX2-CX01-CX12-CX21-CCX0
  hb595 = ListNF.listnfeq' nf-s7 auto

  hb596 : Goal L.ax-CX02-CCX2-CX10-CCX1=CX01-CCX2-CCX0-CX01-CX10
  hb596 = ListNF.listnfeq' nf-s7 auto

  hb597 : Goal L.ax-CX02-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX12
  hb597 = ListNF.listnfeq' nf-s7 auto

  hb598 : Goal L.ax-CX02-CCX2-CCX0-CX01=CCX0-CX01-CCX2
  hb598 = ListNF.listnfeq' nf-s7 auto

  hb599 : Goal L.ax-CX02-CCX2-CCX0-CX02-CCX1=CCX0-CCX2-CCX1
  hb599 = ListNF.listnfeq' nf-s7 auto

  hb600 : Goal L.ax-CX02-CCX2-CCX0-CX12-Swap01=CCX0-CX12-CCX2-Swap01-CX12
  hb600 = ListNF.listnfeq' nf-s7 auto

  hb601 : Goal L.ax-CX02-CX12-Swap01=CX12-Swap01-CX12
  hb601 = ListNF.listnfeq' nf-s7 auto

  hb602 : Goal L.ax-CX02-CX12-CX01-CCX0-Swap01=CX10-CCX1-CX02
  hb602 = ListNF.listnfeq' nf-s7 auto

  hb603 : Goal L.ax-CX02-CX12-CCX1=CX21-CCX2-CX01-CX21-CX12
  hb603 = ListNF.listnfeq' nf-s7 auto

  hb604 : Goal L.ax-CX02-CX12-CCX1-CX01=CX12-CCX1-CX02
  hb604 = ListNF.listnfeq' nf-s7 auto

  hb605 : Goal L.ax-CX02-CX12-CCX1-CX02=CX12-CCX1-CX01
  hb605 = ListNF.listnfeq' nf-s7 auto

  hb606 : Goal L.ax-CX02-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CX12
  hb606 = ListNF.listnfeq' nf-s7 auto

  hb607 : Goal L.ax-CX02-CX12-CCX2-CCX0-Swap01=CCX0-CCX2-CX01-CX12-CX10
  hb607 = ListNF.listnfeq' nf-s7 auto

  hb608 : Goal L.ax-CX02-CX12-CCX0-Swap01=CX20-CCX2-CX01-CX21-CX12-CX20
  hb608 = ListNF.listnfeq' nf-s7 auto

  hb609 : Goal L.ax-CX02-CX21-CCX2-CX01=CX12-CCX1-CX12-CX21
  hb609 = ListNF.listnfeq' nf-s7 auto

  hb610 : Goal L.ax-CX02-CX21-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-Swap12-CX10-CX20-CCX0
  hb610 = ListNF.listnfeq' nf-s7 auto

  hb611 : Goal L.ax-CX02-CX21-CCX0-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX21-CX12-CX20-CCX0
  hb611 = ListNF.listnfeq' nf-s7 auto

  hb612 : Goal L.ax-CX02-Swap12-Swap01=Swap12-Swap01-CX10
  hb612 = ListNF.listnfeq' nf-s7 auto

  hb613 : Goal L.ax-CX02-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX12-CX10
  hb613 = ListNF.listnfeq' nf-s7 auto

  hb614 : Goal L.ax-CX02-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12-CX10
  hb614 = ListNF.listnfeq' nf-s7 auto

  hb615 : Goal L.ax-CX02-CX10-CX02-CCX1=CX10-CX12-CCX1
  hb615 = ListNF.listnfeq' nf-s7 auto

  hb616 : Goal L.ax-CX02-CX10-CCX1-CX02=CX12-CX01-CCX0-Swap01
  hb616 = ListNF.listnfeq' nf-s7 auto

  hb617 : Goal L.ax-CX02-CX10-CCX1-CCX2-CX01=CX10-CCX2-CCX1-CX12
  hb617 = ListNF.listnfeq' nf-s7 auto

  hb618 : Goal L.ax-CX02-CX10-CCX2-CCX1=CX10-CCX1-CCX2-CX01-CX12
  hb618 = ListNF.listnfeq' nf-s7 auto

  hb619 : Goal L.ax-CX02-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-CX01-CX12-CX10
  hb619 = ListNF.listnfeq' nf-s7 auto

  hb620 : Goal L.ax-CX02-CX10-CX12-CCX1=CX10-CX02-CCX1
  hb620 = ListNF.listnfeq' nf-s7 auto

  hb621 : Goal L.ax-CX02-CX10-Swap12-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX12
  hb621 = ListNF.listnfeq' nf-s7 auto

  hb622 : Goal L.ax-CX02-CX20-CX01-CCX2=CCX0-CX12-Swap01-Swap12-CX10
  hb622 = ListNF.listnfeq' nf-s7 auto

  hb623 : Goal L.ax-CX02-CX20-CCX1-CCX2=CCX1-CCX0-CX12-Swap01-Swap12-CX10
  hb623 = ListNF.listnfeq' nf-s7 auto

  hb624 : Goal L.ax-CX02-CX20-CCX1-CCX2-Swap01=CX01-CCX0-Swap01-Swap12-CX10-CX20-CCX0
  hb624 = ListNF.listnfeq' nf-s7 auto

  hb625 : Goal L.ax-CX02-CX20-CCX1-CCX2-CX01=CCX1-CCX0-Swap12-Swap01-Swap12
  hb625 = ListNF.listnfeq' nf-s7 auto

  hb626 : Goal L.ax-CX02-CX20-CCX1-CCX2-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10
  hb626 = ListNF.listnfeq' nf-s7 auto

  hb627 : Goal L.ax-CX02-CX20-CCX2=CCX0-CX02-CX20
  hb627 = ListNF.listnfeq' nf-s7 auto

  hb628 : Goal L.ax-CX02-CX20-CCX2-Swap01=CCX0-Swap01-CX12-CX21
  hb628 = ListNF.listnfeq' nf-s7 auto

  hb629 : Goal L.ax-CX02-CX20-CCX2-CX01=CX12-CCX0-Swap01-CX12-CX21-CX10
  hb629 = ListNF.listnfeq' nf-s7 auto

  hb630 : Goal L.ax-CX02-CX20-CCX2-CX02=CCX0-Swap12-Swap01-Swap12
  hb630 = ListNF.listnfeq' nf-s7 auto

  hb631 : Goal L.ax-CX02-CX20-CCX2-CCX1=CCX0-CX02-CCX1-CX21-CX20
  hb631 = ListNF.listnfeq' nf-s7 auto

  hb632 : Goal L.ax-CX02-CX20-CCX2-CCX1-CX01=CCX0-CCX1-CX02-CX20
  hb632 = ListNF.listnfeq' nf-s7 auto

  hb633 : Goal L.ax-CX02-CX20-CCX2-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10
  hb633 = ListNF.listnfeq' nf-s7 auto

  hb634 : Goal L.ax-CX02-CX20-CX21-CCX2-CX01=CX10-Swap12-CCX2-Swap01-CX12
  hb634 = ListNF.listnfeq' nf-s7 auto

  hb635 : Goal L.ax-CX02-CCX0-Swap01=CX20-CCX2-Swap01-CX21-CX12
  hb635 = ListNF.listnfeq' nf-s7 auto

  hb636 : Goal L.ax-CX02-CCX0-CX01-CCX2=CCX2-CCX0-CX01
  hb636 = ListNF.listnfeq' nf-s7 auto

  hb637 : Goal L.ax-CX02-CCX0-CX02=CX20-CCX2-CX20
  hb637 = ListNF.listnfeq' nf-s7 auto

  hb638 : Goal L.ax-CX02-CCX0-CX02-CCX1=CX20-CCX2-CCX1-CX21-CX20
  hb638 = ListNF.listnfeq' nf-s7 auto

  hb639 : Goal L.ax-CX02-CCX0-CCX1-CX02=CX20-CCX2-CCX1-CX01-CX20
  hb639 = ListNF.listnfeq' nf-s7 auto

  hb640 : Goal L.ax-CX02-CCX0-CCX1-CCX2=CCX0-CX21-CCX2-CX01-CX21-CCX0
  hb640 = ListNF.listnfeq' nf-s7 auto

  hb641 : Goal L.ax-CX02-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX10
  hb641 = ListNF.listnfeq' nf-s7 auto

  hb642 : Goal L.ax-CX02-CCX0-CCX1-CX12-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX20
  hb642 = ListNF.listnfeq' nf-s7 auto

  hb643 : Goal L.ax-CX02-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX12
  hb643 = ListNF.listnfeq' nf-s7 auto

  hb644 : Goal L.ax-CX02-CCX0-CCX2-CX01=CX12-CCX2-CCX0-Swap01-CX12-CX10
  hb644 = ListNF.listnfeq' nf-s7 auto

  hb645 : Goal L.ax-CX02-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1
  hb645 = ListNF.listnfeq' nf-s7 auto

  hb646 : Goal L.ax-CX02-CCX0-CX12-Swap01=CX20-CX01-CCX2-Swap12-CX20
  hb646 = ListNF.listnfeq' nf-s7 auto

  hb647 : Goal L.ax-CX02-CCX0-CX12-CCX2-Swap01=CCX2-CCX0-CX12-Swap01-CX12
  hb647 = ListNF.listnfeq' nf-s7 auto

  hb648 : Goal L.ax-CX02-CCX0-CX21-CCX2-CX01=CCX0-CCX1-CCX2-CX21-CX20-CCX0
  hb648 = ListNF.listnfeq' nf-s7 auto

  hb649 : Goal L.ax-CX02-CCX0-Swap12-Swap01=CX20-CCX2-CX02-Swap12
  hb649 = ListNF.listnfeq' nf-s7 auto

  hb650 : Goal L.ax-CX02-CCX0-Swap12-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX12-CX21
  hb650 = ListNF.listnfeq' nf-s7 auto

  hb651 : Goal L.ax-CCX1-Swap01=Swap01-CCX0
  hb651 = ListNF.listnfeq' nf-s7 auto

  hb652 : Goal L.ax-CCX1-CX01-CCX2-CCX0-Swap01=CX21-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0
  hb652 = ListNF.listnfeq' nf-s7 auto

  hb653 : Goal L.ax-CCX1-CX01-CX20-CCX2=CX02-CCX1-CCX0-CX02-CX20
  hb653 = ListNF.listnfeq' nf-s7 auto

  hb654 : Goal L.ax-CCX1-CX01-CCX0-Swap01=CCX0-Swap01-CX10-CCX0
  hb654 = ListNF.listnfeq' nf-s6 auto

  hb655 : Goal L.ax-CCX1-CX01-CCX0-CX02=CCX0-CX02-CCX1
  hb655 = ListNF.listnfeq' nf-s7 auto

  hb656 : Goal L.ax-CCX1-CX01-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-CX10
  hb656 = ListNF.listnfeq' nf-s7 auto

  hb657 : Goal L.ax-CCX1-CX01-CCX0-CCX2-CX01=CX01-CCX0-CCX2-CX01-CCX0
  hb657 = ListNF.listnfeq' nf-s6 auto

  hb658 : Goal L.ax-CCX1-CX02-CX01=CX02-CCX1
  hb658 = ListNF.listnfeq' nf-s7 auto

  hb659 : Goal L.ax-CCX1-CX02-CCX1=CX02-CX01
  hb659 = ListNF.listnfeq' nf-s7 auto

  hb660 : Goal L.ax-CCX1-CX02-CCX1-CCX0-CX02=CX01-CX20-CCX2-CX20
  hb660 = ListNF.listnfeq' nf-s7 auto

  hb661 : Goal L.ax-CCX1-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10-CCX0
  hb661 = ListNF.listnfeq' nf-s7 auto

  hb662 : Goal L.ax-CCX1-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10-CCX0
  hb662 = ListNF.listnfeq' nf-s7 auto

  hb663 : Goal L.ax-CCX1-CCX1-CX01=CX01
  hb663 = ListNF.listnfeq' nf-s6 auto

  hb664 : Goal L.ax-CCX1-CCX1-CX01-CCX2=CX01-CCX2
  hb664 = ListNF.listnfeq' nf-s6 auto

  hb665 : Goal L.ax-CCX1-CCX1-CX02=CX02
  hb665 = ListNF.listnfeq' nf-s7 auto

  hb666 : Goal L.ax-CCX1-CCX1-CCX2-Swap01=CCX2-Swap01
  hb666 = ListNF.listnfeq' nf-s6 auto

  hb667 : Goal L.ax-CCX1-CCX1-CCX2-CX01=CCX2-CX01
  hb667 = ListNF.listnfeq' nf-s6 auto

  hb668 : Goal L.ax-CCX1-CCX1-CCX2-CX02=CCX2-CX02
  hb668 = ListNF.listnfeq' nf-s7 auto

  hb669 : Goal L.ax-CCX1-CCX1-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01
  hb669 = ListNF.listnfeq' nf-s6 auto

  hb670 : Goal L.ax-CCX1-CCX1-CX12-Swap01=CX12-Swap01
  hb670 = ListNF.listnfeq' nf-s7 auto

  hb671 : Goal L.ax-CCX1-CCX1-CX12-CCX0-Swap01=CX12-CCX0-Swap01
  hb671 = ListNF.listnfeq' nf-s7 auto

  hb672 : Goal L.ax-CCX1-CCX1-CX20-CCX2-CX02=CX20-CCX2-CX02
  hb672 = ListNF.listnfeq' nf-s7 auto

  hb673 : Goal L.ax-CCX1-CCX1-CCX0-CX01-CCX2=CCX0-CX01-CCX2
  hb673 = ListNF.listnfeq' nf-s6 auto

  hb674 : Goal L.ax-CCX1-CCX1-CCX0-CX02=CCX0-CX02
  hb674 = ListNF.listnfeq' nf-s7 auto

  hb675 : Goal L.ax-CCX1-CCX1-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01
  hb675 = ListNF.listnfeq' nf-s6 auto

  hb676 : Goal L.ax-CCX1-CCX1-CCX0-CX12-Swap01=CCX0-CX12-Swap01
  hb676 = ListNF.listnfeq' nf-s7 auto

  hb677 : Goal L.ax-CCX1-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01
  hb677 = ListNF.listnfeq' nf-s7 auto

  hb678 : Goal L.ax-CCX1-CCX2-CX02-CCX1=CX12-CCX1-CX01-CX12
  hb678 = ListNF.listnfeq' nf-s7 auto

  hb679 : Goal L.ax-CCX1-CCX2-CCX1=CX12-CCX1-CX12
  hb679 = ListNF.listnfeq' nf-s7 auto

  hb680 : Goal L.ax-CCX1-CCX2-CCX1-CX01=CX21-CCX2-CX01-CX21
  hb680 = ListNF.listnfeq' nf-s7 auto

  hb681 : Goal L.ax-CCX1-CCX2-CCX1-CX02=CX12-CCX1-CX02-CX12
  hb681 = ListNF.listnfeq' nf-s7 auto

  hb682 : Goal L.ax-CCX1-CCX2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CCX0
  hb682 = ListNF.listnfeq' nf-s7 auto

  hb683 : Goal L.ax-CCX1-CCX2-CX10-CCX1=CCX0-CCX1-CCX2-CX10
  hb683 = ListNF.listnfeq' nf-s6 auto

  hb684 : Goal L.ax-CCX1-CCX2-CCX0-CX01=CCX0-CX21-CCX2-CX01-CX21-CCX0
  hb684 = ListNF.listnfeq' nf-s7 auto

  hb685 : Goal L.ax-CCX1-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX12-Swap01-CCX0
  hb685 = ListNF.listnfeq' nf-s7 auto

  hb686 : Goal L.ax-CCX1-CX12-CX01-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX20
  hb686 = ListNF.listnfeq' nf-s7 auto

  hb687 : Goal L.ax-CCX1-CX12-CCX1=CCX2-CCX1-CX12
  hb687 = ListNF.listnfeq' nf-s7 auto

  hb688 : Goal L.ax-CCX1-CX12-CCX1-CX01=CCX2-CX02-CCX1-CX12
  hb688 = ListNF.listnfeq' nf-s7 auto

  hb689 : Goal L.ax-CCX1-CX12-CCX1-CX02=CCX2-CCX1-CX02-CX12
  hb689 = ListNF.listnfeq' nf-s7 auto

  hb690 : Goal L.ax-CCX1-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CCX0
  hb690 = ListNF.listnfeq' nf-s7 auto

  hb691 : Goal L.ax-CCX1-CX12-CCX2-CCX0-Swap01=CX10-CCX2-CCX1-CX01-CX10-CCX0
  hb691 = ListNF.listnfeq' nf-s7 auto

  hb692 : Goal L.ax-CCX1-CX21-CCX2-CX01=CCX2-CCX1-CX01-CX21
  hb692 = ListNF.listnfeq' nf-s7 auto

  hb693 : Goal L.ax-CCX1-CX21-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0
  hb693 = ListNF.listnfeq' nf-s7 auto

  hb694 : Goal L.ax-CCX1-CX21-CCX0-CCX2-CX01=CX21-CCX0-CCX2-CX01-CCX0
  hb694 = ListNF.listnfeq' nf-s7 auto

  hb695 : Goal L.ax-CCX1-Swap12-Swap01=Swap12-CCX2-Swap01
  hb695 = ListNF.listnfeq' nf-s7 auto

  hb696 : Goal L.ax-CCX1-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CCX0
  hb696 = ListNF.listnfeq' nf-s7 auto

  hb697 : Goal L.ax-CCX1-Swap12-CCX2-Swap01=Swap12-Swap01
  hb697 = ListNF.listnfeq' nf-s7 auto

  hb698 : Goal L.ax-CCX1-CX10-CX02-CCX1=CCX0-CCX1-CX12-Swap01-CX12-CX10
  hb698 = ListNF.listnfeq' nf-s7 auto

  hb699 : Goal L.ax-CCX1-CX10-CCX1=CX10-CCX1-CCX0
  hb699 = ListNF.listnfeq' nf-s6 auto

  hb700 : Goal L.ax-CCX1-CX10-CCX1-CX02=CCX0-CCX1-CX02-CX12-CX10
  hb700 = ListNF.listnfeq' nf-s7 auto

  hb701 : Goal L.ax-CCX1-CX10-CCX1-CCX2-CX01=CCX0-CX12-CCX2-Swap01-CX10-CCX0
  hb701 = ListNF.listnfeq' nf-s7 auto

  hb702 : Goal L.ax-CCX1-CX10-CCX2-CCX1=CX10-CCX2-CCX1-CCX0
  hb702 = ListNF.listnfeq' nf-s6 auto

  hb703 : Goal L.ax-CCX1-CX10-CCX2-CCX1-CX01=CX12-CCX2-CCX0-Swap01-CX10-CCX0
  hb703 = ListNF.listnfeq' nf-s7 auto

  hb704 : Goal L.ax-CCX1-CX10-CX12-CCX1=CX20-CCX1-CCX2-Swap12-CX20
  hb704 = ListNF.listnfeq' nf-s7 auto

  hb705 : Goal L.ax-CCX1-CX10-Swap12-CCX2-Swap01=CCX0-Swap12-CCX2-Swap01-CX21
  hb705 = ListNF.listnfeq' nf-s7 auto

  hb706 : Goal L.ax-CCX1-CX20-CX01-CCX2=CX20-CCX2-CCX1-CX02-CX21
  hb706 = ListNF.listnfeq' nf-s7 auto

  hb707 : Goal L.ax-CCX1-CX20-CCX1-CCX2=CX10-CX12-CCX1-Swap12-CX10
  hb707 = ListNF.listnfeq' nf-s7 auto

  hb708 : Goal L.ax-CCX1-CX20-CCX1-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0
  hb708 = ListNF.listnfeq' nf-s7 auto

  hb709 : Goal L.ax-CCX1-CX20-CCX1-CCX2-CX01=CX20-CX21-CCX2-CX01
  hb709 = ListNF.listnfeq' nf-s7 auto

  hb710 : Goal L.ax-CCX1-CX20-CCX1-CCX2-CX02=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10
  hb710 = ListNF.listnfeq' nf-s7 auto

  hb711 : Goal L.ax-CCX1-CX20-CCX2=CX20-CCX2-CCX1-CX21
  hb711 = ListNF.listnfeq' nf-s7 auto

  hb712 : Goal L.ax-CCX1-CX20-CCX2-Swap01=CX20-CCX2-Swap01-CX20-CCX0
  hb712 = ListNF.listnfeq' nf-s7 auto

  hb713 : Goal L.ax-CCX1-CX20-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21
  hb713 = ListNF.listnfeq' nf-s7 auto

  hb714 : Goal L.ax-CCX1-CX20-CCX2-CCX1=CX20-CCX2-CX21
  hb714 = ListNF.listnfeq' nf-s7 auto

  hb715 : Goal L.ax-CCX1-CX20-CCX2-CCX1-CX01=CX20-CCX2-CX01-CX21
  hb715 = ListNF.listnfeq' nf-s7 auto

  hb716 : Goal L.ax-CCX1-CX20-CCX2-CCX1-CX02=CX20-CX01-CCX2-CX21
  hb716 = ListNF.listnfeq' nf-s7 auto

  hb717 : Goal L.ax-CCX1-CX20-CX21-CCX2-CX01=CX20-CCX1-CCX2-CX01
  hb717 = ListNF.listnfeq' nf-s7 auto

  hb718 : Goal L.ax-CCX1-CCX0-Swap01=CX01-CCX0-Swap01-CX10-CCX0
  hb718 = ListNF.listnfeq' nf-s6 auto

  hb719 : Goal L.ax-CCX1-CCX0-CX01=CCX0-CX01-CCX0
  hb719 = ListNF.listnfeq' nf-s6 auto

  hb720 : Goal L.ax-CCX1-CCX0-CX02-CCX1=CX01-CCX0-CX02
  hb720 = ListNF.listnfeq' nf-s7 auto

  hb721 : Goal L.ax-CCX1-CCX0-CCX1-CX02=CX10-CCX1-CX02-CX12-CX10
  hb721 = ListNF.listnfeq' nf-s7 auto

  hb722 : Goal L.ax-CCX1-CCX0-CCX1-CCX2=CCX2-CX10-CCX1-CX10
  hb722 = ListNF.listnfeq' nf-s6 auto

  hb723 : Goal L.ax-CCX1-CCX0-CCX1-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10
  hb723 = ListNF.listnfeq' nf-s7 auto

  hb724 : Goal L.ax-CCX1-CCX0-CCX1-CX12-Swap01=CX10-CX02-CCX1-CX12-CX10
  hb724 = ListNF.listnfeq' nf-s7 auto

  hb725 : Goal L.ax-CCX1-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1-CCX0
  hb725 = ListNF.listnfeq' nf-s6 auto

  hb726 : Goal L.ax-CCX1-CCX0-CX12-CCX1-CX02=CCX0-CX12-CCX1-CX02-CX10-CCX0
  hb726 = ListNF.listnfeq' nf-s7 auto

  hb727 : Goal L.ax-CCX1-CCX0-CX12-CCX2-Swap01=CX10-CCX1-CCX2-CX01-CX10-CCX0
  hb727 = ListNF.listnfeq' nf-s7 auto

  hb728 : Goal L.ax-CCX1-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20-CCX0
  hb728 = ListNF.listnfeq' nf-s7 auto

  hb729 : Goal L.ax-CCX1-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CCX0
  hb729 = ListNF.listnfeq' nf-s7 auto

  hb730 : Goal L.ax-CCX1-CCX0-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX21
  hb730 = ListNF.listnfeq' nf-s7 auto

  hb731 : Goal L.ax-CCX2-CX01-CCX2=CX02-CX01
  hb731 = ListNF.listnfeq' nf-s7 auto

  hb732 : Goal L.ax-CCX2-CX01-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0
  hb732 = ListNF.listnfeq' nf-s7 auto

  hb733 : Goal L.ax-CCX2-CX01-CCX2-CCX0-CX01=CX02-CX10-CCX1-CX10
  hb733 = ListNF.listnfeq' nf-s7 auto

  hb734 : Goal L.ax-CCX2-CX01-CX20-CCX2=CX01-CCX0-CX02-CX20-CCX0
  hb734 = ListNF.listnfeq' nf-s7 auto

  hb735 : Goal L.ax-CCX2-CX01-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12
  hb735 = ListNF.listnfeq' nf-s7 auto

  hb736 : Goal L.ax-CCX2-CX01-CCX0-CX02=CX01-CX20-CCX2-CX20-CCX0
  hb736 = ListNF.listnfeq' nf-s7 auto

  hb737 : Goal L.ax-CCX2-CX01-CCX0-CCX2-Swap01=CX01-CCX0-Swap01-CX12
  hb737 = ListNF.listnfeq' nf-s7 auto

  hb738 : Goal L.ax-CCX2-CX01-CCX0-CCX2-CX01=CX10-CCX1-CX02-CX12-CX10
  hb738 = ListNF.listnfeq' nf-s7 auto

  hb739 : Goal L.ax-CCX2-CX02-CX01=CX01-CCX2
  hb739 = ListNF.listnfeq' nf-s7 auto

  hb740 : Goal L.ax-CCX2-CX02-CX10-CCX1=CX01-CCX2-CCX0-CX01-CX10
  hb740 = ListNF.listnfeq' nf-s7 auto

  hb741 : Goal L.ax-CCX2-CX02-CCX0-CX01=CCX0-CX01-CCX2
  hb741 = ListNF.listnfeq' nf-s7 auto

  hb742 : Goal L.ax-CCX2-CCX1-CX01-CCX2=CX12-CCX1-CX01-CX12
  hb742 = ListNF.listnfeq' nf-s7 auto

  hb743 : Goal L.ax-CCX2-CCX1-CCX2=CX12-CCX1-CX12
  hb743 = ListNF.listnfeq' nf-s7 auto

  hb744 : Goal L.ax-CCX2-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CCX0
  hb744 = ListNF.listnfeq' nf-s6 auto

  hb745 : Goal L.ax-CCX2-CCX1-CCX2-CX01=CX21-CCX2-CX01-CX21
  hb745 = ListNF.listnfeq' nf-s7 auto

  hb746 : Goal L.ax-CCX2-CCX1-CCX2-CX02=CX12-CCX1-CX02-CX12
  hb746 = ListNF.listnfeq' nf-s7 auto

  hb747 : Goal L.ax-CCX2-CCX1-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CCX0
  hb747 = ListNF.listnfeq' nf-s6 auto

  hb748 : Goal L.ax-CCX2-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CCX0
  hb748 = ListNF.listnfeq' nf-s7 auto

  hb749 : Goal L.ax-CCX2-CCX1-CX12-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0
  hb749 = ListNF.listnfeq' nf-s7 auto

  hb750 : Goal L.ax-CCX2-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX1-CCX2-Swap01-Swap12-CX20
  hb750 = ListNF.listnfeq' nf-s7 auto

  hb751 : Goal L.ax-CCX2-CCX1-CCX0-CX02=CCX0-CX12-CCX1-CX02-CX12-CCX0
  hb751 = ListNF.listnfeq' nf-s7 auto

  hb752 : Goal L.ax-CCX2-CCX1-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CCX0
  hb752 = ListNF.listnfeq' nf-s6 auto

  hb753 : Goal L.ax-CCX2-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CCX0
  hb753 = ListNF.listnfeq' nf-s7 auto

  hb754 : Goal L.ax-CCX2-CCX2-Swap01=Swap01
  hb754 = ListNF.listnfeq' nf-s6 auto

  hb755 : Goal L.ax-CCX2-CCX2-CX02=CX02
  hb755 = ListNF.listnfeq' nf-s7 auto

  hb756 : Goal L.ax-CCX2-CCX2-CX02-CCX1=CX02-CCX1
  hb756 = ListNF.listnfeq' nf-s7 auto

  hb757 : Goal L.ax-CCX2-CCX2-CCX1=CCX1
  hb757 = ListNF.listnfeq' nf-s6 auto

  hb758 : Goal L.ax-CCX2-CCX2-CCX1-CX01=CCX1-CX01
  hb758 = ListNF.listnfeq' nf-s6 auto

  hb759 : Goal L.ax-CCX2-CCX2-CCX1-CX02=CCX1-CX02
  hb759 = ListNF.listnfeq' nf-s7 auto

  hb760 : Goal L.ax-CCX2-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-Swap12-Swap01
  hb760 = ListNF.listnfeq' nf-s7 auto

  hb761 : Goal L.ax-CCX2-CCX2-CX10-CCX1=CX10-CCX1
  hb761 = ListNF.listnfeq' nf-s6 auto

  hb762 : Goal L.ax-CCX2-CCX2-CCX0-Swap01=CCX0-Swap01
  hb762 = ListNF.listnfeq' nf-s6 auto

  hb763 : Goal L.ax-CCX2-CCX2-CCX0-CX01=CCX0-CX01
  hb763 = ListNF.listnfeq' nf-s6 auto

  hb764 : Goal L.ax-CCX2-CCX2-CCX0-CX02-CCX1=CCX0-CX02-CCX1
  hb764 = ListNF.listnfeq' nf-s7 auto

  hb765 : Goal L.ax-CCX2-CCX2-CCX0-CX12-Swap01=CCX0-CX12-Swap01
  hb765 = ListNF.listnfeq' nf-s7 auto

  hb766 : Goal L.ax-CCX2-CX12-Swap01=CX12-CCX2-Swap01
  hb766 = ListNF.listnfeq' nf-s7 auto

  hb767 : Goal L.ax-CCX2-CX12-CX01-CCX0-Swap01=CX10-CCX2-CCX1-CX01
  hb767 = ListNF.listnfeq' nf-s7 auto

  hb768 : Goal L.ax-CCX2-CX12-CCX1=CCX1-CCX2-CX12
  hb768 = ListNF.listnfeq' nf-s7 auto

  hb769 : Goal L.ax-CCX2-CX12-CCX1-CX01=CCX1-CX01-CCX2-CX12
  hb769 = ListNF.listnfeq' nf-s7 auto

  hb770 : Goal L.ax-CCX2-CX12-CCX1-CX02=CCX1-CCX2-CX02-CX12
  hb770 = ListNF.listnfeq' nf-s7 auto

  hb771 : Goal L.ax-CCX2-CX12-CCX2-Swap01=CX12-Swap01
  hb771 = ListNF.listnfeq' nf-s7 auto

  hb772 : Goal L.ax-CCX2-CX12-CCX2-CCX0-Swap01=CX12-CCX0-Swap01
  hb772 = ListNF.listnfeq' nf-s7 auto

  hb773 : Goal L.ax-CCX2-CX12-CCX0-Swap01=CX12-CCX2-CCX0-Swap01
  hb773 = ListNF.listnfeq' nf-s7 auto

  hb774 : Goal L.ax-CCX2-CX21-CCX2-CX01=CCX1-CCX2-CX01-CX21
  hb774 = ListNF.listnfeq' nf-s7 auto

  hb775 : Goal L.ax-CCX2-CX21-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CCX0
  hb775 = ListNF.listnfeq' nf-s7 auto

  hb776 : Goal L.ax-CCX2-CX21-CCX0-CCX2-CX01=CX20-CCX1-CCX2-CX01-CX21-CX20-CCX0
  hb776 = ListNF.listnfeq' nf-s7 auto

  hb777 : Goal L.ax-CCX2-Swap12-Swap01=Swap12-Swap01-CCX0
  hb777 = ListNF.listnfeq' nf-s7 auto

  hb778 : Goal L.ax-CCX2-Swap12-CCX1-CCX2-Swap01=Swap12-CCX2-Swap01
  hb778 = ListNF.listnfeq' nf-s7 auto

  hb779 : Goal L.ax-CCX2-Swap12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01
  hb779 = ListNF.listnfeq' nf-s7 auto

  hb780 : Goal L.ax-CCX2-CX10-CX02-CCX1=CX10-CCX1-CCX2-CX01-CX12
  hb780 = ListNF.listnfeq' nf-s7 auto

  hb781 : Goal L.ax-CCX2-CX10-CCX1-CX02=CX01-CCX0-CCX2-CX01-CX12-CX10
  hb781 = ListNF.listnfeq' nf-s7 auto

  hb782 : Goal L.ax-CCX2-CX10-CCX1-CCX2-CX01=CX10-CX02-CCX1-CX12
  hb782 = ListNF.listnfeq' nf-s7 auto

  hb783 : Goal L.ax-CCX2-CX10-CCX2-CCX1=CX10-CX12-CCX1
  hb783 = ListNF.listnfeq' nf-s7 auto

  hb784 : Goal L.ax-CCX2-CX10-CCX2-CCX1-CX01=CX12-CX01-CCX0-Swap01
  hb784 = ListNF.listnfeq' nf-s7 auto

  hb785 : Goal L.ax-CCX2-CX10-CX12-CCX1=CX10-CCX2-CCX1
  hb785 = ListNF.listnfeq' nf-s7 auto

  hb786 : Goal L.ax-CCX2-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX20-CCX0
  hb786 = ListNF.listnfeq' nf-s7 auto

  hb787 : Goal L.ax-CCX2-CX20-CX01-CCX2=CCX0-CX12-CCX2-Swap01-CX21-CX12-CX10
  hb787 = ListNF.listnfeq' nf-s7 auto

  hb788 : Goal L.ax-CCX2-CX20-CCX1-CCX2=CX20-CCX1-CCX2-CCX0
  hb788 = ListNF.listnfeq' nf-s7 auto

  hb789 : Goal L.ax-CCX2-CX20-CCX1-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0
  hb789 = ListNF.listnfeq' nf-s7 auto

  hb790 : Goal L.ax-CCX2-CX20-CCX1-CCX2-CX01=CX21-CCX0-CCX2-CX01-CX21-CCX0
  hb790 = ListNF.listnfeq' nf-s7 auto

  hb791 : Goal L.ax-CCX2-CX20-CCX1-CCX2-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10-CX20-CCX0
  hb791 = ListNF.listnfeq' nf-s7 auto

  hb792 : Goal L.ax-CCX2-CX20-CCX2=CX20-CCX2-CCX0
  hb792 = ListNF.listnfeq' nf-s7 auto

  hb793 : Goal L.ax-CCX2-CX20-CCX2-Swap01=CCX0-CCX2-Swap01-CX21
  hb793 = ListNF.listnfeq' nf-s7 auto

  hb794 : Goal L.ax-CCX2-CX20-CCX2-CX01=CCX0-CCX2-CX01-CX21-CX20
  hb794 = ListNF.listnfeq' nf-s7 auto

  hb795 : Goal L.ax-CCX2-CX20-CCX2-CX02=CCX0-Swap12-Swap01-Swap12-CX20-CCX0
  hb795 = ListNF.listnfeq' nf-s7 auto

  hb796 : Goal L.ax-CCX2-CX20-CCX2-CCX1=CCX0-CCX2-CCX1-CX21-CX20
  hb796 = ListNF.listnfeq' nf-s7 auto

  hb797 : Goal L.ax-CCX2-CX20-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX01-CCX0
  hb797 = ListNF.listnfeq' nf-s7 auto

  hb798 : Goal L.ax-CCX2-CX20-CCX2-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10-CX20-CCX0
  hb798 = ListNF.listnfeq' nf-s7 auto

  hb799 : Goal L.ax-CCX2-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX20-CCX0
  hb799 = ListNF.listnfeq' nf-s7 auto

  hb800 : Goal L.ax-CCX2-CCX0-CX01-CCX2=CX02-CCX0-CX01
  hb800 = ListNF.listnfeq' nf-s7 auto

  hb801 : Goal L.ax-CCX2-CCX0-CX02=CCX0-CX02-CCX0
  hb801 = ListNF.listnfeq' nf-s7 auto

  hb802 : Goal L.ax-CCX2-CCX0-CCX1-CX02=CCX0-CCX1-CX02-CCX0
  hb802 = ListNF.listnfeq' nf-s7 auto

  hb803 : Goal L.ax-CCX2-CCX0-CCX1-CCX2=CCX0-CCX1-CCX2-CCX0
  hb803 = ListNF.listnfeq' nf-s6 auto

  hb804 : Goal L.ax-CCX2-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CCX0
  hb804 = ListNF.listnfeq' nf-s6 auto

  hb805 : Goal L.ax-CCX2-CCX0-CCX1-CX12-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX10-CX20-CCX0
  hb805 = ListNF.listnfeq' nf-s7 auto

  hb806 : Goal L.ax-CCX2-CCX0-CCX2-Swap01=CX20-CCX2-Swap01-CX21
  hb806 = ListNF.listnfeq' nf-s7 auto

  hb807 : Goal L.ax-CCX2-CCX0-CCX2-CX01=CX20-CCX2-CX01-CX21-CX20
  hb807 = ListNF.listnfeq' nf-s7 auto

  hb808 : Goal L.ax-CCX2-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX21-CX20
  hb808 = ListNF.listnfeq' nf-s7 auto

  hb809 : Goal L.ax-CCX2-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10-CCX0
  hb809 = ListNF.listnfeq' nf-s7 auto

  hb810 : Goal L.ax-CCX2-CCX0-CX12-CCX2-Swap01=CX20-CX01-CCX2-CX12-CX21-CX10-CX20
  hb810 = ListNF.listnfeq' nf-s7 auto

  hb811 : Goal L.ax-CCX2-CCX0-CX21-CCX2-CX01=CCX0-CX21-CCX2-CX01-CX20-CCX0
  hb811 = ListNF.listnfeq' nf-s7 auto

  hb812 : Goal L.ax-CCX2-CCX0-Swap12-Swap01=CX20-CCX2-CX02-Swap12-CX10-CCX0
  hb812 = ListNF.listnfeq' nf-s7 auto

  hb813 : Goal L.ax-CCX2-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CX20-CCX2-CX02-Swap12-CX10
  hb813 = ListNF.listnfeq' nf-s7 auto

  hb814 : Goal L.ax-CX12-CX01=CX02-CX01-CX12
  hb814 = ListNF.listnfeq' nf-s7 auto

  hb815 : Goal L.ax-CX12-CX01-CCX2=CCX2-CX01-CX12
  hb815 = ListNF.listnfeq' nf-s7 auto

  hb816 : Goal L.ax-CX12-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-CX01-CX12-CX10
  hb816 = ListNF.listnfeq' nf-s7 auto

  hb817 : Goal L.ax-CX12-CX01-CCX2-CCX0-CX01=CX10-CCX1-CCX2-CX01-CX12-CX10
  hb817 = ListNF.listnfeq' nf-s7 auto

  hb818 : Goal L.ax-CX12-CX01-CX20-CCX2=CX01-CCX0-CX02-CX10-CX20
  hb818 = ListNF.listnfeq' nf-s7 auto

  hb819 : Goal L.ax-CX12-CX01-CCX0-CX02=CX01-CX20-CCX2-CX10-CX20
  hb819 = ListNF.listnfeq' nf-s7 auto

  hb820 : Goal L.ax-CX12-CX01-CCX0-CCX2-Swap01=CX10-CCX2-CCX1-CX01-CX12
  hb820 = ListNF.listnfeq' nf-s7 auto

  hb821 : Goal L.ax-CX12-CX01-CCX0-CCX2-CX01=CX01-CCX2-CCX0-Swap01-CX12-CX10
  hb821 = ListNF.listnfeq' nf-s7 auto

  hb822 : Goal L.ax-CX12-CX02=CX02-CX12
  hb822 = ListNF.listnfeq' nf-s7 auto

  hb823 : Goal L.ax-CX12-CX02-CX01=CX01-CX12
  hb823 = ListNF.listnfeq' nf-s7 auto

  hb824 : Goal L.ax-CX12-CX02-CCX1=CX21-CCX2-CX01-CX21-CX12
  hb824 = ListNF.listnfeq' nf-s7 auto

  hb825 : Goal L.ax-CX12-CX02-CX10-CCX1=CX10-CX02-CCX1
  hb825 = ListNF.listnfeq' nf-s7 auto

  hb826 : Goal L.ax-CX12-CX02-CCX0-CX01=CX20-CX01-CCX2-Swap12-CX10-CX20
  hb826 = ListNF.listnfeq' nf-s7 auto

  hb827 : Goal L.ax-CX12-CCX1-CX01-CCX2=CCX2-CCX1-CX01-CX12
  hb827 = ListNF.listnfeq' nf-s7 auto

  hb828 : Goal L.ax-CX12-CCX1-CCX2=CCX2-CCX1-CX12
  hb828 = ListNF.listnfeq' nf-s7 auto

  hb829 : Goal L.ax-CX12-CCX1-CCX2-Swap01=CCX1-CX12-Swap01-CCX0
  hb829 = ListNF.listnfeq' nf-s7 auto

  hb830 : Goal L.ax-CX12-CCX1-CCX2-CX01=CCX2-CX02-CCX1-CX12
  hb830 = ListNF.listnfeq' nf-s7 auto

  hb831 : Goal L.ax-CX12-CCX1-CCX2-CX02=CCX2-CCX1-CX02-CX12
  hb831 = ListNF.listnfeq' nf-s7 auto

  hb832 : Goal L.ax-CX12-CCX1-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0
  hb832 = ListNF.listnfeq' nf-s7 auto

  hb833 : Goal L.ax-CX12-CCX1-CX12-Swap01=CCX1-CCX2-Swap01-CCX0
  hb833 = ListNF.listnfeq' nf-s7 auto

  hb834 : Goal L.ax-CX12-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CCX0
  hb834 = ListNF.listnfeq' nf-s7 auto

  hb835 : Goal L.ax-CX12-CCX1-CX20-CCX2-CX02=CCX2-CCX1-CCX0-Swap12-Swap01-CX12-CX21-CX10-CX20-CCX0
  hb835 = ListNF.listnfeq' nf-s7 auto

  hb836 : Goal L.ax-CX12-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CX12-Swap01-CX12-CCX0
  hb836 = ListNF.listnfeq' nf-s7 auto

  hb837 : Goal L.ax-CX12-CCX1-CCX0-CX02=CCX0-CX12-CCX1-CX02-CX12-CX10
  hb837 = ListNF.listnfeq' nf-s7 auto

  hb838 : Goal L.ax-CX12-CCX1-CCX0-CCX2-Swap01=CX20-CCX2-CCX1-CX01-CX10-CX20-CCX0
  hb838 = ListNF.listnfeq' nf-s7 auto

  hb839 : Goal L.ax-CX12-CCX1-CCX0-CX12-Swap01=CCX0-CX21-CCX2-CX01-CX21-CX10
  hb839 = ListNF.listnfeq' nf-s7 auto

  hb840 : Goal L.ax-CX12-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CCX0
  hb840 = ListNF.listnfeq' nf-s7 auto

  hb841 : Goal L.ax-CX12-CCX2=CCX2-CX12
  hb841 = ListNF.listnfeq' nf-s7 auto

  hb842 : Goal L.ax-CX12-CCX2-CX01=CX01-CCX2-CX12
  hb842 = ListNF.listnfeq' nf-s7 auto

  hb843 : Goal L.ax-CX12-CCX2-CX02=CCX2-CX02-CX12
  hb843 = ListNF.listnfeq' nf-s7 auto

  hb844 : Goal L.ax-CX12-CCX2-CX02-CCX1=CCX1-CCX2-CX01-CX12
  hb844 = ListNF.listnfeq' nf-s7 auto

  hb845 : Goal L.ax-CX12-CCX2-CCX1=CCX1-CCX2-CX12
  hb845 = ListNF.listnfeq' nf-s7 auto

  hb846 : Goal L.ax-CX12-CCX2-CCX1-CX01=CCX1-CX01-CCX2-CX12
  hb846 = ListNF.listnfeq' nf-s7 auto

  hb847 : Goal L.ax-CX12-CCX2-CCX1-CX02=CCX1-CCX2-CX02-CX12
  hb847 = ListNF.listnfeq' nf-s7 auto

  hb848 : Goal L.ax-CX12-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CX20-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0
  hb848 = ListNF.listnfeq' nf-s7 auto

  hb849 : Goal L.ax-CX12-CCX2-CX10-CCX1=CX10-CCX2-CCX1
  hb849 = ListNF.listnfeq' nf-s7 auto

  hb850 : Goal L.ax-CX12-CCX2-CCX0-CX01=CCX2-CCX0-CX12-Swap01-CX10
  hb850 = ListNF.listnfeq' nf-s7 auto

  hb851 : Goal L.ax-CX12-CCX2-CCX0-CX02-CCX1=CCX0-CX02-CCX1-CX10-CCX0
  hb851 = ListNF.listnfeq' nf-s7 auto

  hb852 : Goal L.ax-CX12-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX01-CX10
  hb852 = ListNF.listnfeq' nf-s7 auto

  hb853 : Goal L.ax-CX12-CX12-Swap01=Swap01
  hb853 = ListNF.listnfeq' nf-s7 auto

  hb854 : Goal L.ax-CX12-CX12-CX01-CCX0-Swap01=CX01-CCX0-Swap01
  hb854 = ListNF.listnfeq' nf-s7 auto

  hb855 : Goal L.ax-CX12-CX12-CCX1=CCX1
  hb855 = ListNF.listnfeq' nf-s7 auto

  hb856 : Goal L.ax-CX12-CX12-CCX1-CX01=CCX1-CX01
  hb856 = ListNF.listnfeq' nf-s7 auto

  hb857 : Goal L.ax-CX12-CX12-CCX1-CX02=CCX1-CX02
  hb857 = ListNF.listnfeq' nf-s7 auto

  hb858 : Goal L.ax-CX12-CX12-CCX2-Swap01=CCX2-Swap01
  hb858 = ListNF.listnfeq' nf-s7 auto

  hb859 : Goal L.ax-CX12-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01
  hb859 = ListNF.listnfeq' nf-s7 auto

  hb860 : Goal L.ax-CX12-CX12-CCX0-Swap01=CCX0-Swap01
  hb860 = ListNF.listnfeq' nf-s7 auto

  hb861 : Goal L.ax-CX12-CX21-CCX2-CX01=CX02-CCX1-CX12-CX21
  hb861 = ListNF.listnfeq' nf-s7 auto

  hb862 : Goal L.ax-CX12-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CX02-Swap12-CX10
  hb862 = ListNF.listnfeq' nf-s7 auto

  hb863 : Goal L.ax-CX12-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX2-Swap01-CX10
  hb863 = ListNF.listnfeq' nf-s7 auto

  hb864 : Goal L.ax-CX12-Swap12-Swap01=Swap12-Swap01-CX20
  hb864 = ListNF.listnfeq' nf-s7 auto

  hb865 : Goal L.ax-CX12-Swap12-CCX1-CCX2-Swap01=Swap12-CCX2-Swap01-CX20-CCX0
  hb865 = ListNF.listnfeq' nf-s7 auto

  hb866 : Goal L.ax-CX12-Swap12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX20-CCX0
  hb866 = ListNF.listnfeq' nf-s7 auto

  hb867 : Goal L.ax-CX12-CX10-CX02-CCX1=CX02-CX10-CCX1
  hb867 = ListNF.listnfeq' nf-s7 auto

  hb868 : Goal L.ax-CX12-CX10-CCX1=CX10-CX12-CCX1
  hb868 = ListNF.listnfeq' nf-s7 auto

  hb869 : Goal L.ax-CX12-CX10-CCX1-CX02=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0
  hb869 = ListNF.listnfeq' nf-s7 auto

  hb870 : Goal L.ax-CX12-CX10-CCX1-CCX2-CX01=CX01-CCX2-CCX0-CX01-CX12-CX10
  hb870 = ListNF.listnfeq' nf-s7 auto

  hb871 : Goal L.ax-CX12-CX10-CCX2-CCX1=CCX2-CX10-CCX1
  hb871 = ListNF.listnfeq' nf-s7 auto

  hb872 : Goal L.ax-CX12-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-Swap01-CX12
  hb872 = ListNF.listnfeq' nf-s7 auto

  hb873 : Goal L.ax-CX12-CX10-CX12-CCX1=CX10-CCX1
  hb873 = ListNF.listnfeq' nf-s7 auto

  hb874 : Goal L.ax-CX12-CX10-Swap12-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10
  hb874 = ListNF.listnfeq' nf-s7 auto

  hb875 : Goal L.ax-CX12-CX20-CX01-CCX2=CX02-CCX0-CX01-Swap12-CX10-CX20
  hb875 = ListNF.listnfeq' nf-s7 auto

  hb876 : Goal L.ax-CX12-CX20-CCX1-CCX2=CCX0-CCX1-CCX2-Swap12-CX10-CX20-CCX0
  hb876 = ListNF.listnfeq' nf-s7 auto

  hb877 : Goal L.ax-CX12-CX20-CCX1-CCX2-Swap01=CX10-CCX1-CX02-Swap12-CX10-CX20-CCX0
  hb877 = ListNF.listnfeq' nf-s7 auto

  hb878 : Goal L.ax-CX12-CX20-CCX1-CCX2-CX02=CCX1-CCX2-CCX0-Swap01-CX12-CX21-CX10-CX20-CCX0
  hb878 = ListNF.listnfeq' nf-s7 auto

  hb879 : Goal L.ax-CX12-CX20-CCX2=CX20-CCX2-CX10
  hb879 = ListNF.listnfeq' nf-s7 auto

  hb880 : Goal L.ax-CX12-CX20-CCX2-Swap01=CX20-CCX2-CX01-CX10
  hb880 = ListNF.listnfeq' nf-s7 auto

  hb881 : Goal L.ax-CX12-CX20-CCX2-CX01=CX20-CCX2-Swap01-CX10
  hb881 = ListNF.listnfeq' nf-s7 auto

  hb882 : Goal L.ax-CX12-CX20-CCX2-CX02=CX20-CCX2-CX02-CX12-CX10
  hb882 = ListNF.listnfeq' nf-s7 auto

  hb883 : Goal L.ax-CX12-CX20-CCX2-CCX1=CCX0-CCX2-CCX1-CX21-CX10-CX20-CCX0
  hb883 = ListNF.listnfeq' nf-s7 auto

  hb884 : Goal L.ax-CX12-CX20-CCX2-CCX1-CX01=CCX1-CCX0-CCX2-Swap01-CX10-CX20-CCX0
  hb884 = ListNF.listnfeq' nf-s7 auto

  hb885 : Goal L.ax-CX12-CX20-CX21-CCX2-CX01=CX10-Swap12-CCX2-Swap01-CX10
  hb885 = ListNF.listnfeq' nf-s7 auto

  hb886 : Goal L.ax-CX12-CCX0-CX01=CCX0-CX12-Swap01-CX10
  hb886 = ListNF.listnfeq' nf-s7 auto

  hb887 : Goal L.ax-CX12-CCX0-CX01-CCX2=CCX0-CX12-CCX2-Swap01-CX12-CX10
  hb887 = ListNF.listnfeq' nf-s7 auto

  hb888 : Goal L.ax-CX12-CCX0-CX02=CCX0-CX02-CX10
  hb888 = ListNF.listnfeq' nf-s7 auto

  hb889 : Goal L.ax-CX12-CCX0-CX02-CCX1=CCX2-CCX0-CX02-CCX1-CX10-CCX0
  hb889 = ListNF.listnfeq' nf-s7 auto

  hb890 : Goal L.ax-CX12-CCX0-CCX1-CX02=CX21-CCX0-CCX2-Swap01-Swap12-CX20
  hb890 = ListNF.listnfeq' nf-s7 auto

  hb891 : Goal L.ax-CX12-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-Swap12-CX10-CX20-CCX0
  hb891 = ListNF.listnfeq' nf-s7 auto

  hb892 : Goal L.ax-CX12-CCX0-CCX1-CCX2-Swap01=CCX1-CX12-CCX0-Swap01-CCX0
  hb892 = ListNF.listnfeq' nf-s7 auto

  hb893 : Goal L.ax-CX12-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX01-CCX2-CX12-CX10-CCX0
  hb893 = ListNF.listnfeq' nf-s7 auto

  hb894 : Goal L.ax-CX12-CCX0-CCX2-Swap01=CCX0-CCX2-CX01-CX10
  hb894 = ListNF.listnfeq' nf-s7 auto

  hb895 : Goal L.ax-CX12-CCX0-CCX2-CX01=CCX0-CCX2-Swap01-CX10
  hb895 = ListNF.listnfeq' nf-s7 auto

  hb896 : Goal L.ax-CX12-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX21-CX10-CX20-CCX0
  hb896 = ListNF.listnfeq' nf-s7 auto

  hb897 : Goal L.ax-CX12-CCX0-CX12-Swap01=CCX0-CX01-CX10
  hb897 = ListNF.listnfeq' nf-s7 auto

  hb898 : Goal L.ax-CX12-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10
  hb898 = ListNF.listnfeq' nf-s7 auto

  hb899 : Goal L.ax-CX12-CCX0-CX12-CCX2-Swap01=CCX0-CX01-CCX2-CX12-CX10
  hb899 = ListNF.listnfeq' nf-s7 auto

  hb900 : Goal L.ax-CX12-CCX0-CX21-CCX2-CX01=CCX1-CCX0-CX12-Swap01-CX21-CX10-CX20
  hb900 = ListNF.listnfeq' nf-s7 auto

  hb901 : Goal L.ax-CX12-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21-CX20
  hb901 = ListNF.listnfeq' nf-s7 auto

  hb902 : Goal L.ax-CX12-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX20-CCX0
  hb902 = ListNF.listnfeq' nf-s7 auto

  hb903 : Goal L.ax-CX12-CCX0-Swap12-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10
  hb903 = ListNF.listnfeq' nf-s7 auto

  hb904 : Goal L.ax-CX21-Swap01=Swap01-CX20
  hb904 = ListNF.listnfeq' nf-s7 auto

  hb905 : Goal L.ax-CX21-CX01=CX01-CX21
  hb905 = ListNF.listnfeq' nf-s7 auto

  hb906 : Goal L.ax-CX21-CX01-CCX2=CX12-CCX1-CX02-CX12-CX21
  hb906 = ListNF.listnfeq' nf-s7 auto

  hb907 : Goal L.ax-CX21-CX01-CCX2-CCX0-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0
  hb907 = ListNF.listnfeq' nf-s7 auto

  hb908 : Goal L.ax-CX21-CX01-CX20-CCX2=CX20-CX01-CCX2
  hb908 = ListNF.listnfeq' nf-s7 auto

  hb909 : Goal L.ax-CX21-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX21-CX20
  hb909 = ListNF.listnfeq' nf-s7 auto

  hb910 : Goal L.ax-CX21-CX01-CCX0-CX02=CX10-CX02-CCX1-Swap12-CX10-CX20
  hb910 = ListNF.listnfeq' nf-s7 auto

  hb911 : Goal L.ax-CX21-CX01-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0
  hb911 = ListNF.listnfeq' nf-s7 auto

  hb912 : Goal L.ax-CX21-CX02=CX02-CX01-CX21
  hb912 = ListNF.listnfeq' nf-s7 auto

  hb913 : Goal L.ax-CX21-CX02-CX01=CX02-CX21
  hb913 = ListNF.listnfeq' nf-s7 auto

  hb914 : Goal L.ax-CX21-CX02-CCX1=CCX1-CX02-CX21
  hb914 = ListNF.listnfeq' nf-s7 auto

  hb915 : Goal L.ax-CX21-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX02-CX21-CX20
  hb915 = ListNF.listnfeq' nf-s7 auto

  hb916 : Goal L.ax-CX21-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10-CX20
  hb916 = ListNF.listnfeq' nf-s7 auto

  hb917 : Goal L.ax-CX21-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10-CX20
  hb917 = ListNF.listnfeq' nf-s7 auto

  hb918 : Goal L.ax-CX21-CCX1=CCX1-CX21
  hb918 = ListNF.listnfeq' nf-s7 auto

  hb919 : Goal L.ax-CX21-CCX1-CX01=CCX1-CX01-CX21
  hb919 = ListNF.listnfeq' nf-s7 auto

  hb920 : Goal L.ax-CX21-CCX1-CX01-CCX2=CCX2-CCX1-CX02-CX21
  hb920 = ListNF.listnfeq' nf-s7 auto

  hb921 : Goal L.ax-CX21-CCX1-CX02=CX02-CCX1-CX21
  hb921 = ListNF.listnfeq' nf-s7 auto

  hb922 : Goal L.ax-CX21-CCX1-CCX2=CCX2-CCX1-CX21
  hb922 = ListNF.listnfeq' nf-s7 auto

  hb923 : Goal L.ax-CX21-CCX1-CCX2-Swap01=CCX2-Swap01-CX20-CCX0
  hb923 = ListNF.listnfeq' nf-s7 auto

  hb924 : Goal L.ax-CX21-CCX1-CCX2-CX01=CCX2-CCX1-CX01-CX21
  hb924 = ListNF.listnfeq' nf-s7 auto

  hb925 : Goal L.ax-CX21-CCX1-CCX2-CX02=CCX2-CX02-CCX1-CX21
  hb925 = ListNF.listnfeq' nf-s7 auto

  hb926 : Goal L.ax-CX21-CCX1-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0
  hb926 = ListNF.listnfeq' nf-s7 auto

  hb927 : Goal L.ax-CX21-CCX1-CX12-Swap01=Swap12-CCX2-Swap01-CX20
  hb927 = ListNF.listnfeq' nf-s7 auto

  hb928 : Goal L.ax-CX21-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX20
  hb928 = ListNF.listnfeq' nf-s7 auto

  hb929 : Goal L.ax-CX21-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX02
  hb929 = ListNF.listnfeq' nf-s7 auto

  hb930 : Goal L.ax-CX21-CCX1-CCX0-CX01-CCX2=CCX0-CX01-CCX2-CX20-CCX0
  hb930 = ListNF.listnfeq' nf-s7 auto

  hb931 : Goal L.ax-CX21-CCX1-CCX0-CX02=CCX1-CCX0-CX12-Swap01-Swap12-CX10-CX20
  hb931 = ListNF.listnfeq' nf-s7 auto

  hb932 : Goal L.ax-CX21-CCX1-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0
  hb932 = ListNF.listnfeq' nf-s7 auto

  hb933 : Goal L.ax-CX21-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX02-Swap12-CX10-CX20
  hb933 = ListNF.listnfeq' nf-s7 auto

  hb934 : Goal L.ax-CX21-CCX1-CCX0-Swap12-Swap01=CCX1-CX12-CCX0-Swap01-CX21-CX20
  hb934 = ListNF.listnfeq' nf-s7 auto

  hb935 : Goal L.ax-CX21-CCX2=CX12-CCX1-CX12-CX21
  hb935 = ListNF.listnfeq' nf-s7 auto

  hb936 : Goal L.ax-CX21-CCX2-Swap01=CCX1-CCX2-Swap01-CX20-CCX0
  hb936 = ListNF.listnfeq' nf-s7 auto

  hb937 : Goal L.ax-CX21-CCX2-CX02=CX12-CCX1-CX01-CX12-CX21
  hb937 = ListNF.listnfeq' nf-s7 auto

  hb938 : Goal L.ax-CX21-CCX2-CX02-CCX1=CCX1-CCX2-CX02-CX21
  hb938 = ListNF.listnfeq' nf-s7 auto

  hb939 : Goal L.ax-CX21-CCX2-CCX1=CCX1-CCX2-CX21
  hb939 = ListNF.listnfeq' nf-s7 auto

  hb940 : Goal L.ax-CX21-CCX2-CCX1-CX01=CCX1-CCX2-CX01-CX21
  hb940 = ListNF.listnfeq' nf-s7 auto

  hb941 : Goal L.ax-CX21-CCX2-CCX1-CX02=CCX1-CX01-CCX2-CX21
  hb941 = ListNF.listnfeq' nf-s7 auto

  hb942 : Goal L.ax-CX21-CCX2-CCX1-CCX0-Swap12-Swap01=CX10-CCX2-CCX1-CX01-CX21-CX10-CX20-CCX0
  hb942 = ListNF.listnfeq' nf-s7 auto

  hb943 : Goal L.ax-CX21-CCX2-CX10-CCX1=CCX0-CCX1-CCX2-CX10-CX20-CCX0
  hb943 = ListNF.listnfeq' nf-s7 auto

  hb944 : Goal L.ax-CX21-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CX21-CCX0
  hb944 = ListNF.listnfeq' nf-s7 auto

  hb945 : Goal L.ax-CX21-CCX2-CCX0-CX01=CCX0-CX21-CCX2-CX01-CX21-CX20
  hb945 = ListNF.listnfeq' nf-s7 auto

  hb946 : Goal L.ax-CX21-CCX2-CCX0-CX02-CCX1=CCX0-CX12-CCX2-Swap01-CX21-CX12-CX10-CX20-CCX0
  hb946 = ListNF.listnfeq' nf-s7 auto

  hb947 : Goal L.ax-CX21-CCX2-CCX0-CX12-Swap01=CCX0-CX12-CCX1-CX02-CX21-CX12-CX10-CX20
  hb947 = ListNF.listnfeq' nf-s7 auto

  hb948 : Goal L.ax-CX21-CX12-Swap01=Swap12-Swap01-CX20
  hb948 = ListNF.listnfeq' nf-s7 auto

  hb949 : Goal L.ax-CX21-CX12-CX01-CCX0-Swap01=CX20-CCX2-CX02-CX21-CX12-CX20
  hb949 = ListNF.listnfeq' nf-s7 auto

  hb950 : Goal L.ax-CX21-CX12-CCX1=CCX2-CX21-CX12
  hb950 = ListNF.listnfeq' nf-s7 auto

  hb951 : Goal L.ax-CX21-CX12-CCX1-CX01=CCX2-CX02-CX21-CX12
  hb951 = ListNF.listnfeq' nf-s7 auto

  hb952 : Goal L.ax-CX21-CX12-CCX1-CX02=CX01-CCX2-CX21-CX12
  hb952 = ListNF.listnfeq' nf-s7 auto

  hb953 : Goal L.ax-CX21-CX12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX20-CCX0
  hb953 = ListNF.listnfeq' nf-s7 auto

  hb954 : Goal L.ax-CX21-CX12-CCX2-CCX0-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CCX0
  hb954 = ListNF.listnfeq' nf-s7 auto

  hb955 : Goal L.ax-CX21-CX12-CCX0-Swap01=CCX0-Swap12-Swap01-CX21-CX20
  hb955 = ListNF.listnfeq' nf-s7 auto

  hb956 : Goal L.ax-CX21-CX21-CCX2-CX01=CCX2-CX01
  hb956 = ListNF.listnfeq' nf-s7 auto

  hb957 : Goal L.ax-CX21-CX21-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01
  hb957 = ListNF.listnfeq' nf-s7 auto

  hb958 : Goal L.ax-CX21-CX21-CCX0-CCX2-CX01=CCX0-CCX2-CX01
  hb958 = ListNF.listnfeq' nf-s7 auto

  hb959 : Goal L.ax-CX21-Swap12-Swap01=CX12-Swap01-CX20
  hb959 = ListNF.listnfeq' nf-s7 auto

  hb960 : Goal L.ax-CX21-Swap12-CCX1-CCX2-Swap01=CX12-CCX2-Swap01-CX20-CCX0
  hb960 = ListNF.listnfeq' nf-s7 auto

  hb961 : Goal L.ax-CX21-Swap12-CCX2-Swap01=CCX1-CX12-Swap01-CX20
  hb961 = ListNF.listnfeq' nf-s7 auto

  hb962 : Goal L.ax-CX21-CX10-CX02-CCX1=CX01-CCX0-CX02-Swap12-CX10-CX20
  hb962 = ListNF.listnfeq' nf-s7 auto

  hb963 : Goal L.ax-CX21-CX10-CCX1=CX10-CCX1-CX20
  hb963 = ListNF.listnfeq' nf-s7 auto

  hb964 : Goal L.ax-CX21-CX10-CCX1-CX02=CX10-Swap12-CCX2-Swap01-Swap12-CX20
  hb964 = ListNF.listnfeq' nf-s7 auto

  hb965 : Goal L.ax-CX21-CX10-CCX2-CCX1=CCX0-CCX2-CCX1-Swap12-CX10-CX20-CCX0
  hb965 = ListNF.listnfeq' nf-s7 auto

  hb966 : Goal L.ax-CX21-CX10-CCX2-CCX1-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX21-CX10-CX20-CCX0
  hb966 = ListNF.listnfeq' nf-s7 auto

  hb967 : Goal L.ax-CX21-CX10-CX12-CCX1=CX20-CCX2-Swap12-CX20
  hb967 = ListNF.listnfeq' nf-s7 auto

  hb968 : Goal L.ax-CX21-CX10-Swap12-CCX2-Swap01=CX10-CCX1-CX02-Swap12-CX10
  hb968 = ListNF.listnfeq' nf-s7 auto

  hb969 : Goal L.ax-CX21-CX20-CX01-CCX2=CX01-CX20-CCX2
  hb969 = ListNF.listnfeq' nf-s7 auto

  hb970 : Goal L.ax-CX21-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX21
  hb970 = ListNF.listnfeq' nf-s7 auto

  hb971 : Goal L.ax-CX21-CX20-CCX1-CCX2-Swap01=CX20-CCX2-Swap01-CX20-CCX0
  hb971 = ListNF.listnfeq' nf-s7 auto

  hb972 : Goal L.ax-CX21-CX20-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21
  hb972 = ListNF.listnfeq' nf-s7 auto

  hb973 : Goal L.ax-CX21-CX20-CCX1-CCX2-CX02=CCX1-CX20-CCX2-CX02
  hb973 = ListNF.listnfeq' nf-s7 auto

  hb974 : Goal L.ax-CX21-CX20-CCX2=CX10-CX12-CCX1-Swap12-CX10
  hb974 = ListNF.listnfeq' nf-s7 auto

  hb975 : Goal L.ax-CX21-CX20-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0
  hb975 = ListNF.listnfeq' nf-s7 auto

  hb976 : Goal L.ax-CX21-CX20-CCX2-CX01=CX20-CX21-CCX2-CX01
  hb976 = ListNF.listnfeq' nf-s7 auto

  hb977 : Goal L.ax-CX21-CX20-CCX2-CX02=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10
  hb977 = ListNF.listnfeq' nf-s7 auto

  hb978 : Goal L.ax-CX21-CX20-CCX2-CCX1=CX20-CCX1-CCX2-CX21
  hb978 = ListNF.listnfeq' nf-s7 auto

  hb979 : Goal L.ax-CX21-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX01-CX21
  hb979 = ListNF.listnfeq' nf-s7 auto

  hb980 : Goal L.ax-CX21-CX20-CCX2-CCX1-CX02=CX02-CCX1-CCX0-CX02-CX21-CX20
  hb980 = ListNF.listnfeq' nf-s7 auto

  hb981 : Goal L.ax-CX21-CX20-CX21-CCX2-CX01=CX20-CCX2-CX01
  hb981 = ListNF.listnfeq' nf-s7 auto

  hb982 : Goal L.ax-CX21-CCX0-Swap01=CCX0-Swap01-CX21-CX20
  hb982 = ListNF.listnfeq' nf-s7 auto

  hb983 : Goal L.ax-CX21-CCX0-CX01=CCX0-CX01-CX20
  hb983 = ListNF.listnfeq' nf-s7 auto

  hb984 : Goal L.ax-CX21-CCX0-CX01-CCX2=CCX1-CCX0-CX01-CCX2-CX20-CCX0
  hb984 = ListNF.listnfeq' nf-s7 auto

  hb985 : Goal L.ax-CX21-CCX0-CX02=CCX0-CX12-Swap01-Swap12-CX10-CX20
  hb985 = ListNF.listnfeq' nf-s7 auto

  hb986 : Goal L.ax-CX21-CCX0-CX02-CCX1=CCX0-CCX1-CX12-Swap01-CX21-CX12-CX10
  hb986 = ListNF.listnfeq' nf-s7 auto

  hb987 : Goal L.ax-CX21-CCX0-CCX1-CX02=CCX0-Swap12-CCX2-Swap01-Swap12-CX20
  hb987 = ListNF.listnfeq' nf-s7 auto

  hb988 : Goal L.ax-CX21-CCX0-CCX1-CCX2=CCX2-CX10-CCX1-CX10-CX20-CCX0
  hb988 = ListNF.listnfeq' nf-s7 auto

  hb989 : Goal L.ax-CX21-CCX0-CCX1-CCX2-Swap01=CCX2-CCX0-Swap01-CX21-CX20-CCX0
  hb989 = ListNF.listnfeq' nf-s7 auto

  hb990 : Goal L.ax-CX21-CCX0-CCX1-CX12-Swap01=CCX0-CX02-CCX1-CX12-CX21-CX10-CX20
  hb990 = ListNF.listnfeq' nf-s7 auto

  hb991 : Goal L.ax-CX21-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-Swap12-CX10-CX20-CCX0
  hb991 = ListNF.listnfeq' nf-s7 auto

  hb992 : Goal L.ax-CX21-CCX0-CX12-Swap01=CCX0-CX02-Swap12-CX10-CX20
  hb992 = ListNF.listnfeq' nf-s7 auto

  hb993 : Goal L.ax-CX21-CCX0-CX12-CCX1-CX02=CCX2-CCX0-CX12-Swap01-CX12-CX21-CX20
  hb993 = ListNF.listnfeq' nf-s7 auto

  hb994 : Goal L.ax-CX21-CCX0-CX12-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10-CX20-CCX0
  hb994 = ListNF.listnfeq' nf-s7 auto

  hb995 : Goal L.ax-CX21-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20
  hb995 = ListNF.listnfeq' nf-s7 auto

  hb996 : Goal L.ax-CX21-CCX0-Swap12-Swap01=CX12-CCX0-Swap01-CX21-CX20
  hb996 = ListNF.listnfeq' nf-s7 auto

  hb997 : Goal L.ax-CX21-CCX0-Swap12-CCX1-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-CX21-CX20-CCX0
  hb997 = ListNF.listnfeq' nf-s7 auto

  hb998 : Goal L.ax-CX21-CCX0-Swap12-CCX2-Swap01=CCX0-CCX1-CX02-Swap12-CX10
  hb998 = ListNF.listnfeq' nf-s7 auto

  hb999 : Goal L.ax-Swap12-CX01=CX02-Swap12
  hb999 = ListNF.listnfeq' nf-s7 auto

  hb1000 : Goal L.ax-Swap12-CX01-CCX2=CX02-CCX1-Swap12
  hb1000 = ListNF.listnfeq' nf-s7 auto

  hb1001 : Goal L.ax-Swap12-CX01-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-CX01-Swap12
  hb1001 = ListNF.listnfeq' nf-s7 auto

  hb1002 : Goal L.ax-Swap12-CX01-CCX2-CCX0-CX01=CX02-CCX1-CCX0-CX02-Swap12
  hb1002 = ListNF.listnfeq' nf-s7 auto

  hb1003 : Goal L.ax-Swap12-CX01-CX20-CCX2=CX02-CX10-CCX1-Swap12
  hb1003 = ListNF.listnfeq' nf-s7 auto

  hb1004 : Goal L.ax-Swap12-CX01-CCX0-Swap01=CX20-CCX2-CX02-Swap12
  hb1004 = ListNF.listnfeq' nf-s7 auto

  hb1005 : Goal L.ax-Swap12-CX01-CCX0-CX02=CX02-CCX0-CX01-Swap12
  hb1005 = ListNF.listnfeq' nf-s7 auto

  hb1006 : Goal L.ax-Swap12-CX01-CCX0-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX12-CX21
  hb1006 = ListNF.listnfeq' nf-s7 auto

  hb1007 : Goal L.ax-Swap12-CX01-CCX0-CCX2-CX01=CX20-CCX2-CCX1-CX01-Swap12-CX10
  hb1007 = ListNF.listnfeq' nf-s7 auto

  hb1008 : Goal L.ax-Swap12-CX02=CX01-Swap12
  hb1008 = ListNF.listnfeq' nf-s7 auto

  hb1009 : Goal L.ax-Swap12-CX02-CX01=CX02-CX01-Swap12
  hb1009 = ListNF.listnfeq' nf-s7 auto

  hb1010 : Goal L.ax-Swap12-CX02-CCX1=CX01-CCX2-Swap12
  hb1010 = ListNF.listnfeq' nf-s7 auto

  hb1011 : Goal L.ax-Swap12-CX02-CCX1-CCX0-CX02=CX01-CCX2-CCX0-CX01-Swap12
  hb1011 = ListNF.listnfeq' nf-s7 auto

  hb1012 : Goal L.ax-Swap12-CX02-CX10-CCX1=CX01-CX20-CCX2-Swap12
  hb1012 = ListNF.listnfeq' nf-s7 auto

  hb1013 : Goal L.ax-Swap12-CX02-CCX0-CX01=CX01-CCX0-CX02-Swap12
  hb1013 = ListNF.listnfeq' nf-s7 auto

  hb1014 : Goal L.ax-Swap12-CCX1=CCX2-Swap12
  hb1014 = ListNF.listnfeq' nf-s7 auto

  hb1015 : Goal L.ax-Swap12-CCX1-CX01=CCX2-CX02-Swap12
  hb1015 = ListNF.listnfeq' nf-s7 auto

  hb1016 : Goal L.ax-Swap12-CCX1-CX01-CCX2=CCX2-CX02-CCX1-Swap12
  hb1016 = ListNF.listnfeq' nf-s7 auto

  hb1017 : Goal L.ax-Swap12-CCX1-CX02=CCX2-CX01-Swap12
  hb1017 = ListNF.listnfeq' nf-s7 auto

  hb1018 : Goal L.ax-Swap12-CCX1-CCX2=CCX2-CCX1-Swap12
  hb1018 = ListNF.listnfeq' nf-s7 auto

  hb1019 : Goal L.ax-Swap12-CCX1-CCX2-CX01=CCX2-CCX1-CX02-Swap12
  hb1019 = ListNF.listnfeq' nf-s7 auto

  hb1020 : Goal L.ax-Swap12-CCX1-CCX2-CX02=CCX2-CCX1-CX01-Swap12
  hb1020 = ListNF.listnfeq' nf-s7 auto

  hb1021 : Goal L.ax-Swap12-CCX1-CCX2-CCX0-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01
  hb1021 = ListNF.listnfeq' nf-s7 auto

  hb1022 : Goal L.ax-Swap12-CCX1-CX12-Swap01=CX12-CCX2-Swap01-CX20
  hb1022 = ListNF.listnfeq' nf-s7 auto

  hb1023 : Goal L.ax-Swap12-CCX1-CX12-CCX0-Swap01=CX12-CCX2-CCX0-Swap01-CX21-CX20
  hb1023 = ListNF.listnfeq' nf-s7 auto

  hb1024 : Goal L.ax-Swap12-CCX1-CX20-CCX2-CX02=CX01-CCX0-CCX2-Swap01-CX21-CX12
  hb1024 = ListNF.listnfeq' nf-s7 auto

  hb1025 : Goal L.ax-Swap12-CCX1-CCX0-CX01-CCX2=CCX2-CCX0-CX02-CCX1-Swap12
  hb1025 = ListNF.listnfeq' nf-s7 auto

  hb1026 : Goal L.ax-Swap12-CCX1-CCX0-CX02=CCX2-CCX0-CX01-Swap12
  hb1026 = ListNF.listnfeq' nf-s7 auto

  hb1027 : Goal L.ax-Swap12-CCX1-CCX0-CX12-Swap01=CCX2-CCX0-CX12-Swap01-CX20
  hb1027 = ListNF.listnfeq' nf-s7 auto

  hb1028 : Goal L.ax-Swap12-CCX1-CCX0-Swap12-Swap01=CCX2-CCX0-Swap01
  hb1028 = ListNF.listnfeq' nf-s7 auto

  hb1029 : Goal L.ax-Swap12-CCX2=CCX1-Swap12
  hb1029 = ListNF.listnfeq' nf-s7 auto

  hb1030 : Goal L.ax-Swap12-CCX2-CX01=CCX1-CX02-Swap12
  hb1030 = ListNF.listnfeq' nf-s7 auto

  hb1031 : Goal L.ax-Swap12-CCX2-CX02=CCX1-CX01-Swap12
  hb1031 = ListNF.listnfeq' nf-s7 auto

  hb1032 : Goal L.ax-Swap12-CCX2-CX02-CCX1=CCX1-CX01-CCX2-Swap12
  hb1032 = ListNF.listnfeq' nf-s7 auto

  hb1033 : Goal L.ax-Swap12-CCX2-CCX1=CCX1-CCX2-Swap12
  hb1033 = ListNF.listnfeq' nf-s7 auto

  hb1034 : Goal L.ax-Swap12-CCX2-CCX1-CX01=CCX1-CCX2-CX02-Swap12
  hb1034 = ListNF.listnfeq' nf-s7 auto

  hb1035 : Goal L.ax-Swap12-CCX2-CCX1-CX02=CCX1-CCX2-CX01-Swap12
  hb1035 = ListNF.listnfeq' nf-s7 auto

  hb1036 : Goal L.ax-Swap12-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX2-CCX0-Swap01
  hb1036 = ListNF.listnfeq' nf-s7 auto

  hb1037 : Goal L.ax-Swap12-CCX2-CX10-CCX1=CX20-CCX2-CCX1-CX12-CX21
  hb1037 = ListNF.listnfeq' nf-s7 auto

  hb1038 : Goal L.ax-Swap12-CCX2-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01
  hb1038 = ListNF.listnfeq' nf-s7 auto

  hb1039 : Goal L.ax-Swap12-CCX2-CCX0-CX01=CCX1-CCX0-CX02-Swap12
  hb1039 = ListNF.listnfeq' nf-s7 auto

  hb1040 : Goal L.ax-Swap12-CCX2-CCX0-CX02-CCX1=CCX1-CCX0-CX01-CCX2-Swap12
  hb1040 = ListNF.listnfeq' nf-s7 auto

  hb1041 : Goal L.ax-Swap12-CCX2-CCX0-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CX20
  hb1041 = ListNF.listnfeq' nf-s7 auto

  hb1042 : Goal L.ax-Swap12-CX12-Swap01=CX12-Swap01-CX20
  hb1042 = ListNF.listnfeq' nf-s7 auto

  hb1043 : Goal L.ax-Swap12-CX12-CX01-CCX0-Swap01=CX12-CX01-CCX0-Swap01-CX21-CX20
  hb1043 = ListNF.listnfeq' nf-s7 auto

  hb1044 : Goal L.ax-Swap12-CX12-CCX1=CX12-CCX1-CX21
  hb1044 = ListNF.listnfeq' nf-s7 auto

  hb1045 : Goal L.ax-Swap12-CX12-CCX1-CX01=CX12-CCX1-CX01-CX21
  hb1045 = ListNF.listnfeq' nf-s7 auto

  hb1046 : Goal L.ax-Swap12-CX12-CCX1-CX02=CX21-CCX2-CX01-Swap12
  hb1046 = ListNF.listnfeq' nf-s7 auto

  hb1047 : Goal L.ax-Swap12-CX12-CCX2-Swap01=CCX1-CX12-Swap01-CX20
  hb1047 = ListNF.listnfeq' nf-s7 auto

  hb1048 : Goal L.ax-Swap12-CX12-CCX2-CCX0-Swap01=CCX1-CX12-CCX0-Swap01-CX21-CX20
  hb1048 = ListNF.listnfeq' nf-s7 auto

  hb1049 : Goal L.ax-Swap12-CX12-CCX0-Swap01=CX12-CCX0-Swap01-CX21-CX20
  hb1049 = ListNF.listnfeq' nf-s7 auto

  hb1050 : Goal L.ax-Swap12-CX21-CCX2-CX01=CX12-CCX1-CX02-Swap12
  hb1050 = ListNF.listnfeq' nf-s7 auto

  hb1051 : Goal L.ax-Swap12-CX21-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10
  hb1051 = ListNF.listnfeq' nf-s7 auto

  hb1052 : Goal L.ax-Swap12-CX21-CCX0-CCX2-CX01=CX21-CCX0-CCX2-Swap01-CX10
  hb1052 = ListNF.listnfeq' nf-s7 auto

  hb1053 : Goal L.ax-Swap12-Swap12-Swap01=Swap01
  hb1053 = ListNF.listnfeq' nf-s7 auto

  hb1054 : Goal L.ax-Swap12-Swap12-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01
  hb1054 = ListNF.listnfeq' nf-s7 auto

  hb1055 : Goal L.ax-Swap12-Swap12-CCX2-Swap01=CCX2-Swap01
  hb1055 = ListNF.listnfeq' nf-s7 auto

  hb1056 : Goal L.ax-Swap12-CX10-CX02-CCX1=CX20-CX01-CCX2-Swap12
  hb1056 = ListNF.listnfeq' nf-s7 auto

  hb1057 : Goal L.ax-Swap12-CX10-CCX1=CX20-CCX2-Swap12
  hb1057 = ListNF.listnfeq' nf-s7 auto

  hb1058 : Goal L.ax-Swap12-CX10-CCX1-CX02=CX20-CCX2-CX01-Swap12
  hb1058 = ListNF.listnfeq' nf-s7 auto

  hb1059 : Goal L.ax-Swap12-CX10-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX02-Swap12
  hb1059 = ListNF.listnfeq' nf-s7 auto

  hb1060 : Goal L.ax-Swap12-CX10-CCX2-CCX1=CX20-CCX1-CCX2-Swap12
  hb1060 = ListNF.listnfeq' nf-s7 auto

  hb1061 : Goal L.ax-Swap12-CX10-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX02-Swap12
  hb1061 = ListNF.listnfeq' nf-s7 auto

  hb1062 : Goal L.ax-Swap12-CX10-CX12-CCX1=CX10-CX12-CCX1-CX20
  hb1062 = ListNF.listnfeq' nf-s7 auto

  hb1063 : Goal L.ax-Swap12-CX10-Swap12-CCX2-Swap01=CX20-CCX2-Swap01
  hb1063 = ListNF.listnfeq' nf-s7 auto

  hb1064 : Goal L.ax-Swap12-CX20-CX01-CCX2=CX10-CX02-CCX1-Swap12
  hb1064 = ListNF.listnfeq' nf-s7 auto

  hb1065 : Goal L.ax-Swap12-CX20-CCX1-CCX2=CX10-CCX2-CCX1-Swap12
  hb1065 = ListNF.listnfeq' nf-s7 auto

  hb1066 : Goal L.ax-Swap12-CX20-CCX1-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10-CX20-CCX0
  hb1066 = ListNF.listnfeq' nf-s7 auto

  hb1067 : Goal L.ax-Swap12-CX20-CCX1-CCX2-CX01=CX01-CCX2-CCX0-Swap01-Swap12
  hb1067 = ListNF.listnfeq' nf-s7 auto

  hb1068 : Goal L.ax-Swap12-CX20-CCX1-CCX2-CX02=CX10-CCX2-CCX1-CX01-Swap12
  hb1068 = ListNF.listnfeq' nf-s7 auto

  hb1069 : Goal L.ax-Swap12-CX20-CCX2=CX10-CCX1-Swap12
  hb1069 = ListNF.listnfeq' nf-s7 auto

  hb1070 : Goal L.ax-Swap12-CX20-CCX2-Swap01=CX10-Swap12-CCX2-Swap01
  hb1070 = ListNF.listnfeq' nf-s7 auto

  hb1071 : Goal L.ax-Swap12-CX20-CCX2-CX01=CX10-CCX1-CX02-Swap12
  hb1071 = ListNF.listnfeq' nf-s7 auto

  hb1072 : Goal L.ax-Swap12-CX20-CCX2-CX02=CX01-CCX0-Swap01-Swap12
  hb1072 = ListNF.listnfeq' nf-s7 auto

  hb1073 : Goal L.ax-Swap12-CX20-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX12
  hb1073 = ListNF.listnfeq' nf-s7 auto

  hb1074 : Goal L.ax-Swap12-CX20-CCX2-CCX1-CX01=CX01-CCX0-CCX2-CX01-Swap12-CX20
  hb1074 = ListNF.listnfeq' nf-s7 auto

  hb1075 : Goal L.ax-Swap12-CX20-CCX2-CCX1-CX02=CX10-CCX1-CCX2-CX01-Swap12
  hb1075 = ListNF.listnfeq' nf-s7 auto

  hb1076 : Goal L.ax-Swap12-CX20-CX21-CCX2-CX01=CX20-CCX1-CCX2-Swap01-CX10-CX20-CCX0
  hb1076 = ListNF.listnfeq' nf-s7 auto

  hb1077 : Goal L.ax-Swap12-CCX0-Swap01=CCX0-Swap12-Swap01
  hb1077 = ListNF.listnfeq' nf-s7 auto

  hb1078 : Goal L.ax-Swap12-CCX0-CX01=CCX0-CX02-Swap12
  hb1078 = ListNF.listnfeq' nf-s7 auto

  hb1079 : Goal L.ax-Swap12-CCX0-CX01-CCX2=CCX0-CX02-CCX1-Swap12
  hb1079 = ListNF.listnfeq' nf-s7 auto

  hb1080 : Goal L.ax-Swap12-CCX0-CX02=CCX0-CX01-Swap12
  hb1080 = ListNF.listnfeq' nf-s7 auto

  hb1081 : Goal L.ax-Swap12-CCX0-CX02-CCX1=CCX0-CX01-CCX2-Swap12
  hb1081 = ListNF.listnfeq' nf-s7 auto

  hb1082 : Goal L.ax-Swap12-CCX0-CCX1-CX02=CCX0-CCX2-CX01-Swap12
  hb1082 = ListNF.listnfeq' nf-s7 auto

  hb1083 : Goal L.ax-Swap12-CCX0-CCX1-CCX2=CCX0-CCX2-CCX1-Swap12
  hb1083 = ListNF.listnfeq' nf-s7 auto

  hb1084 : Goal L.ax-Swap12-CCX0-CCX1-CCX2-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01
  hb1084 = ListNF.listnfeq' nf-s7 auto

  hb1085 : Goal L.ax-Swap12-CCX0-CCX1-CX12-Swap01=CCX0-CX12-CCX2-Swap01-CX20
  hb1085 = ListNF.listnfeq' nf-s7 auto

  hb1086 : Goal L.ax-Swap12-CCX0-CCX2-Swap01=CCX0-Swap12-CCX2-Swap01
  hb1086 = ListNF.listnfeq' nf-s7 auto

  hb1087 : Goal L.ax-Swap12-CCX0-CCX2-CX01=CCX0-CCX1-CX02-Swap12
  hb1087 = ListNF.listnfeq' nf-s7 auto

  hb1088 : Goal L.ax-Swap12-CCX0-CCX2-CCX1=CCX0-CCX1-CCX2-Swap12
  hb1088 = ListNF.listnfeq' nf-s7 auto

  hb1089 : Goal L.ax-Swap12-CCX0-CX12-Swap01=CCX0-CX12-Swap01-CX20
  hb1089 = ListNF.listnfeq' nf-s7 auto

  hb1090 : Goal L.ax-Swap12-CCX0-CX12-CCX1-CX02=CCX0-CX21-CCX2-CX01-Swap12
  hb1090 = ListNF.listnfeq' nf-s7 auto

  hb1091 : Goal L.ax-Swap12-CCX0-CX12-CCX2-Swap01=CCX0-CCX1-CX12-Swap01-CX20
  hb1091 = ListNF.listnfeq' nf-s7 auto

  hb1092 : Goal L.ax-Swap12-CCX0-CX21-CCX2-CX01=CCX0-CX12-CCX1-CX02-Swap12
  hb1092 = ListNF.listnfeq' nf-s7 auto

  hb1093 : Goal L.ax-Swap12-CCX0-Swap12-Swap01=CCX0-Swap01
  hb1093 = ListNF.listnfeq' nf-s7 auto

  hb1094 : Goal L.ax-Swap12-CCX0-Swap12-CCX1-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01
  hb1094 = ListNF.listnfeq' nf-s7 auto

  hb1095 : Goal L.ax-Swap12-CCX0-Swap12-CCX2-Swap01=CCX0-CCX2-Swap01
  hb1095 = ListNF.listnfeq' nf-s7 auto

  hb1096 : Goal L.ax-CX10-Swap01=CX01-CX10
  hb1096 = ListNF.listnfeq' nf-s6 auto

  hb1097 : Goal L.ax-CX10-CX01=Swap01-CX10
  hb1097 = ListNF.listnfeq' nf-s6 auto

  hb1098 : Goal L.ax-CX10-CX01-CCX2=CCX2-Swap01-CX12-CX10
  hb1098 = ListNF.listnfeq' nf-s7 auto

  hb1099 : Goal L.ax-CX10-CX01-CCX2-CCX0-Swap01=CCX2-CCX1-CX02
  hb1099 = ListNF.listnfeq' nf-s7 auto

  hb1100 : Goal L.ax-CX10-CX01-CCX2-CCX0-CX01=CCX2-CX02-CCX1-CX10
  hb1100 = ListNF.listnfeq' nf-s7 auto

  hb1101 : Goal L.ax-CX10-CX01-CX20-CCX2=CCX1-CCX2-Swap01-CX12-CX10-CX20-CCX0
  hb1101 = ListNF.listnfeq' nf-s7 auto

  hb1102 : Goal L.ax-CX10-CX01-CCX0-Swap01=CCX1-CX01
  hb1102 = ListNF.listnfeq' nf-s6 auto

  hb1103 : Goal L.ax-CX10-CX01-CCX0-CX02=CCX1-CX12-Swap01-CX12-CX10
  hb1103 = ListNF.listnfeq' nf-s7 auto

  hb1104 : Goal L.ax-CX10-CX01-CCX0-CCX2-Swap01=CCX1-CX01-CCX2
  hb1104 = ListNF.listnfeq' nf-s6 auto

  hb1105 : Goal L.ax-CX10-CX01-CCX0-CCX2-CX01=CCX1-CCX2-CX02-CX10
  hb1105 = ListNF.listnfeq' nf-s7 auto

  hb1106 : Goal L.ax-CX10-CX02=CX02-CX12-CX10
  hb1106 = ListNF.listnfeq' nf-s7 auto

  hb1107 : Goal L.ax-CX10-CX02-CX01=CX12-Swap01-CX12-CX10
  hb1107 = ListNF.listnfeq' nf-s7 auto

  hb1108 : Goal L.ax-CX10-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CCX2-Swap01-CX12-CX10-CCX0
  hb1108 = ListNF.listnfeq' nf-s7 auto

  hb1109 : Goal L.ax-CX10-CX02-CX10-CCX1=CX21-CCX2-CX01-CX21-CX12
  hb1109 = ListNF.listnfeq' nf-s7 auto

  hb1110 : Goal L.ax-CX10-CX02-CCX0-CX01=CX20-CCX2-CX01-CX21-CX12-CX10-CX20
  hb1110 = ListNF.listnfeq' nf-s7 auto

  hb1111 : Goal L.ax-CX10-CCX1-CX01=CX01-CCX0-Swap01
  hb1111 = ListNF.listnfeq' nf-s6 auto

  hb1112 : Goal L.ax-CX10-CCX1-CX01-CCX2=CX01-CCX0-CCX2-Swap01
  hb1112 = ListNF.listnfeq' nf-s6 auto

  hb1113 : Goal L.ax-CX10-CCX1-CCX2=CCX2-CX10-CCX1-CX12
  hb1113 = ListNF.listnfeq' nf-s7 auto

  hb1114 : Goal L.ax-CX10-CCX1-CCX2-Swap01=CX01-CX20-CCX2-CX12-CX10-CX20-CCX0
  hb1114 = ListNF.listnfeq' nf-s7 auto

  hb1115 : Goal L.ax-CX10-CCX1-CCX2-CX02=CX01-CCX0-CCX2-CX01-CX10
  hb1115 = ListNF.listnfeq' nf-s7 auto

  hb1116 : Goal L.ax-CX10-CCX1-CCX2-CCX0-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX10-CX20-CCX0
  hb1116 = ListNF.listnfeq' nf-s7 auto

  hb1117 : Goal L.ax-CX10-CCX1-CX12-Swap01=CX01-CCX0-CX02-CX12-CX10
  hb1117 = ListNF.listnfeq' nf-s7 auto

  hb1118 : Goal L.ax-CX10-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX12-Swap01
  hb1118 = ListNF.listnfeq' nf-s7 auto

  hb1119 : Goal L.ax-CX10-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2-Swap01-CX12-CX10
  hb1119 = ListNF.listnfeq' nf-s7 auto

  hb1120 : Goal L.ax-CX10-CCX1-CCX0-CX02=CCX0-CCX1-CX02-CX12-CX10
  hb1120 = ListNF.listnfeq' nf-s7 auto

  hb1121 : Goal L.ax-CX10-CCX1-CCX0-CCX2-Swap01=CX02-CCX1-CCX0-CX02-CX12-CCX0
  hb1121 = ListNF.listnfeq' nf-s7 auto

  hb1122 : Goal L.ax-CX10-CCX1-CCX0-CX12-Swap01=CCX0-CX02-CCX1-CX12-CX10
  hb1122 = ListNF.listnfeq' nf-s7 auto

  hb1123 : Goal L.ax-CX10-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX21
  hb1123 = ListNF.listnfeq' nf-s7 auto

  hb1124 : Goal L.ax-CX10-CCX2=CCX2-CX12-CX10
  hb1124 = ListNF.listnfeq' nf-s7 auto

  hb1125 : Goal L.ax-CX10-CCX2-Swap01=CX01-CCX2-CX12-CX10
  hb1125 = ListNF.listnfeq' nf-s7 auto

  hb1126 : Goal L.ax-CX10-CCX2-CX01=CX12-CCX2-Swap01-CX10
  hb1126 = ListNF.listnfeq' nf-s7 auto

  hb1127 : Goal L.ax-CX10-CCX2-CX02=CCX2-CX02-CX10
  hb1127 = ListNF.listnfeq' nf-s7 auto

  hb1128 : Goal L.ax-CX10-CCX2-CX02-CCX1=CX01-CCX2-CCX0-CX01-CX10
  hb1128 = ListNF.listnfeq' nf-s7 auto

  hb1129 : Goal L.ax-CX10-CCX2-CCX1-CX02=CX01-CCX2-CCX0-Swap01
  hb1129 = ListNF.listnfeq' nf-s7 auto

  hb1130 : Goal L.ax-CX10-CCX2-CCX1-CCX0-Swap12-Swap01=CX20-CCX1-CCX2-CX01-CX10-CX20-CCX0
  hb1130 = ListNF.listnfeq' nf-s7 auto

  hb1131 : Goal L.ax-CX10-CCX2-CX10-CCX1=CCX1-CCX2-CX12
  hb1131 = ListNF.listnfeq' nf-s7 auto

  hb1132 : Goal L.ax-CX10-CCX2-CCX0-Swap01=CCX2-CCX0-CX12-Swap01
  hb1132 = ListNF.listnfeq' nf-s7 auto

  hb1133 : Goal L.ax-CX10-CCX2-CCX0-CX01=CX12-CCX2-CCX0-Swap01-CX10
  hb1133 = ListNF.listnfeq' nf-s7 auto

  hb1134 : Goal L.ax-CX10-CCX2-CCX0-CX02-CCX1=CCX0-CX21-CCX2-CX01-CX21-CX12-CX10-CCX0
  hb1134 = ListNF.listnfeq' nf-s7 auto

  hb1135 : Goal L.ax-CX10-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-Swap01
  hb1135 = ListNF.listnfeq' nf-s7 auto

  hb1136 : Goal L.ax-CX10-CX12-Swap01=CX02-CX01-CX12-CX10
  hb1136 = ListNF.listnfeq' nf-s7 auto

  hb1137 : Goal L.ax-CX10-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01
  hb1137 = ListNF.listnfeq' nf-s7 auto

  hb1138 : Goal L.ax-CX10-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01
  hb1138 = ListNF.listnfeq' nf-s7 auto

  hb1139 : Goal L.ax-CX10-CX12-CCX1-CX02=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0
  hb1139 = ListNF.listnfeq' nf-s7 auto

  hb1140 : Goal L.ax-CX10-CX12-CCX2-Swap01=CCX2-CX01-CX10
  hb1140 = ListNF.listnfeq' nf-s7 auto

  hb1141 : Goal L.ax-CX10-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-CX01-CX10
  hb1141 = ListNF.listnfeq' nf-s7 auto

  hb1142 : Goal L.ax-CX10-CX12-CCX0-Swap01=CCX0-CX12-Swap01
  hb1142 = ListNF.listnfeq' nf-s7 auto

  hb1143 : Goal L.ax-CX10-CX21-CCX2-CX01=CX02-CX10-CCX1-CX12-CX21
  hb1143 = ListNF.listnfeq' nf-s7 auto

  hb1144 : Goal L.ax-CX10-CX21-CCX0-CCX2-Swap01=CCX0-CX12-CCX1-CX02-Swap12-CX10
  hb1144 = ListNF.listnfeq' nf-s7 auto

  hb1145 : Goal L.ax-CX10-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX1-CCX2-Swap01-CX10-CX20-CCX0
  hb1145 = ListNF.listnfeq' nf-s7 auto

  hb1146 : Goal L.ax-CX10-Swap12-Swap01=Swap12-Swap01-CX21
  hb1146 = ListNF.listnfeq' nf-s7 auto

  hb1147 : Goal L.ax-CX10-Swap12-CCX1-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10-CX20-CCX0
  hb1147 = ListNF.listnfeq' nf-s7 auto

  hb1148 : Goal L.ax-CX10-CX10-CX02-CCX1=CX02-CCX1
  hb1148 = ListNF.listnfeq' nf-s7 auto

  hb1149 : Goal L.ax-CX10-CX10-CCX1=CCX1
  hb1149 = ListNF.listnfeq' nf-s6 auto

  hb1150 : Goal L.ax-CX10-CX10-CCX1-CX02=CCX1-CX02
  hb1150 = ListNF.listnfeq' nf-s7 auto

  hb1151 : Goal L.ax-CX10-CX10-CCX1-CCX2-CX01=CCX1-CCX2-CX01
  hb1151 = ListNF.listnfeq' nf-s6 auto

  hb1152 : Goal L.ax-CX10-CX10-CCX2-CCX1=CCX2-CCX1
  hb1152 = ListNF.listnfeq' nf-s6 auto

  hb1153 : Goal L.ax-CX10-CX10-CCX2-CCX1-CX01=CCX2-CCX1-CX01
  hb1153 = ListNF.listnfeq' nf-s6 auto

  hb1154 : Goal L.ax-CX10-CX10-CX12-CCX1=CX12-CCX1
  hb1154 = ListNF.listnfeq' nf-s7 auto

  hb1155 : Goal L.ax-CX10-CX10-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01
  hb1155 = ListNF.listnfeq' nf-s7 auto

  hb1156 : Goal L.ax-CX10-CX20-CX01-CCX2=CX20-CCX2-Swap01-CX12-CX10
  hb1156 = ListNF.listnfeq' nf-s7 auto

  hb1157 : Goal L.ax-CX10-CX20-CCX1-CCX2=CCX0-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0
  hb1157 = ListNF.listnfeq' nf-s7 auto

  hb1158 : Goal L.ax-CX10-CX20-CCX1-CCX2-Swap01=CX12-CCX1-CX02-Swap12-CX10-CX20-CCX0
  hb1158 = ListNF.listnfeq' nf-s7 auto

  hb1159 : Goal L.ax-CX10-CX20-CCX1-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10-CX20-CCX0
  hb1159 = ListNF.listnfeq' nf-s7 auto

  hb1160 : Goal L.ax-CX10-CX20-CCX2=CX20-CCX2-CX12-CX10
  hb1160 = ListNF.listnfeq' nf-s7 auto

  hb1161 : Goal L.ax-CX10-CX20-CCX2-Swap01=CX20-CX01-CCX2-CX12-CX10
  hb1161 = ListNF.listnfeq' nf-s7 auto

  hb1162 : Goal L.ax-CX10-CX20-CCX2-CX01=CX02-CCX0-CX01-CX12-CX21-CX20
  hb1162 = ListNF.listnfeq' nf-s7 auto

  hb1163 : Goal L.ax-CX10-CX20-CCX2-CX02=CX20-CCX2-CX02-CX10
  hb1163 = ListNF.listnfeq' nf-s7 auto

  hb1164 : Goal L.ax-CX10-CX20-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0
  hb1164 = ListNF.listnfeq' nf-s7 auto

  hb1165 : Goal L.ax-CX10-CX20-CCX2-CCX1-CX02=CCX1-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0
  hb1165 = ListNF.listnfeq' nf-s7 auto

  hb1166 : Goal L.ax-CX10-CX20-CX21-CCX2-CX01=Swap12-CCX1-CCX2-Swap01-CX10-CX20-CCX0
  hb1166 = ListNF.listnfeq' nf-s7 auto

  hb1167 : Goal L.ax-CX10-CCX0-Swap01=CCX0-CX01-CX10
  hb1167 = ListNF.listnfeq' nf-s6 auto

  hb1168 : Goal L.ax-CX10-CCX0-CX01=CCX0-Swap01-CX10
  hb1168 = ListNF.listnfeq' nf-s6 auto

  hb1169 : Goal L.ax-CX10-CCX0-CX01-CCX2=CCX0-CCX2-Swap01-CX12-CX10
  hb1169 = ListNF.listnfeq' nf-s7 auto

  hb1170 : Goal L.ax-CX10-CCX0-CX02=CCX0-CX02-CX12-CX10
  hb1170 = ListNF.listnfeq' nf-s7 auto

  hb1171 : Goal L.ax-CX10-CCX0-CX02-CCX1=CCX1-CCX0-CX12-Swap01-CX12-CX10
  hb1171 = ListNF.listnfeq' nf-s7 auto

  hb1172 : Goal L.ax-CX10-CCX0-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10
  hb1172 = ListNF.listnfeq' nf-s7 auto

  hb1173 : Goal L.ax-CX10-CCX0-CCX1-CCX2=CX20-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0
  hb1173 = ListNF.listnfeq' nf-s7 auto

  hb1174 : Goal L.ax-CX10-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CX01-CCX2-CX12-CX10
  hb1174 = ListNF.listnfeq' nf-s7 auto

  hb1175 : Goal L.ax-CX10-CCX0-CCX1-CX12-Swap01=CCX1-CX12-CCX0-Swap01
  hb1175 = ListNF.listnfeq' nf-s7 auto

  hb1176 : Goal L.ax-CX10-CCX0-CCX2-Swap01=CCX0-CX01-CCX2-CX12-CX10
  hb1176 = ListNF.listnfeq' nf-s7 auto

  hb1177 : Goal L.ax-CX10-CCX0-CCX2-CX01=CCX0-CX12-CCX2-Swap01-CX10
  hb1177 = ListNF.listnfeq' nf-s7 auto

  hb1178 : Goal L.ax-CX10-CCX0-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0
  hb1178 = ListNF.listnfeq' nf-s7 auto

  hb1179 : Goal L.ax-CX10-CCX0-CX12-Swap01=CX12-CCX0-Swap01
  hb1179 = ListNF.listnfeq' nf-s7 auto

  hb1180 : Goal L.ax-CX10-CCX0-CX12-CCX1-CX02=CX21-CCX0-CCX2-Swap01-Swap12-CX20
  hb1180 = ListNF.listnfeq' nf-s7 auto

  hb1181 : Goal L.ax-CX10-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-CX01-CX10
  hb1181 = ListNF.listnfeq' nf-s7 auto

  hb1182 : Goal L.ax-CX10-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX20-CCX0
  hb1182 = ListNF.listnfeq' nf-s7 auto

  hb1183 : Goal L.ax-CX10-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21
  hb1183 = ListNF.listnfeq' nf-s7 auto

  hb1184 : Goal L.ax-CX10-CCX0-Swap12-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10-CX20-CCX0
  hb1184 = ListNF.listnfeq' nf-s7 auto

  hb1185 : Goal L.ax-CX10-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21
  hb1185 = ListNF.listnfeq' nf-s7 auto

  hb1186 : Goal L.ax-CX20-Swap01=Swap01-CX21
  hb1186 = ListNF.listnfeq' nf-s7 auto

  hb1187 : Goal L.ax-CX20-CX01=CX01-CX21-CX20
  hb1187 = ListNF.listnfeq' nf-s7 auto

  hb1188 : Goal L.ax-CX20-CX01-CCX2-CCX0-Swap01=CCX1-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0
  hb1188 = ListNF.listnfeq' nf-s7 auto

  hb1189 : Goal L.ax-CX20-CX01-CX20-CCX2=CX12-CCX1-CX02-CX12-CX21
  hb1189 = ListNF.listnfeq' nf-s7 auto

  hb1190 : Goal L.ax-CX20-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX20
  hb1190 = ListNF.listnfeq' nf-s7 auto

  hb1191 : Goal L.ax-CX20-CX01-CCX0-CX02=CX10-CCX1-CX02-CX12-CX21-CX10-CX20
  hb1191 = ListNF.listnfeq' nf-s7 auto

  hb1192 : Goal L.ax-CX20-CX01-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10-CX20-CCX0
  hb1192 = ListNF.listnfeq' nf-s7 auto

  hb1193 : Goal L.ax-CX20-CX02=Swap12-Swap01-Swap12-CX20
  hb1193 = ListNF.listnfeq' nf-s7 auto

  hb1194 : Goal L.ax-CX20-CX02-CX01=CX12-Swap01-CX21-CX12-CX10
  hb1194 = ListNF.listnfeq' nf-s7 auto

  hb1195 : Goal L.ax-CX20-CX02-CCX1=Swap12-CCX2-Swap01-CX21-CX12-CX20
  hb1195 = ListNF.listnfeq' nf-s7 auto

  hb1196 : Goal L.ax-CX20-CX02-CCX1-CCX0-CX02=CCX1-CX01-CCX2-CX20
  hb1196 = ListNF.listnfeq' nf-s7 auto

  hb1197 : Goal L.ax-CX20-CX02-CX10-CCX1=Swap12-CCX1-CCX2-Swap01-CX21-CX12-CX10-CX20-CCX0
  hb1197 = ListNF.listnfeq' nf-s7 auto

  hb1198 : Goal L.ax-CX20-CX02-CCX0-CX01=CX12-CCX2-Swap01-CX21-CX12-CX10
  hb1198 = ListNF.listnfeq' nf-s7 auto

  hb1199 : Goal L.ax-CX20-CCX1=CCX1-CX21-CX20
  hb1199 = ListNF.listnfeq' nf-s7 auto

  hb1200 : Goal L.ax-CX20-CCX1-CX01=CCX1-CX01-CX20
  hb1200 = ListNF.listnfeq' nf-s7 auto

  hb1201 : Goal L.ax-CX20-CCX1-CX01-CCX2=CX02-CCX1-CCX0-CX02-CX20
  hb1201 = ListNF.listnfeq' nf-s7 auto

  hb1202 : Goal L.ax-CX20-CCX1-CX02=CCX1-CX12-Swap01-Swap12-CX10-CX20
  hb1202 = ListNF.listnfeq' nf-s7 auto

  hb1203 : Goal L.ax-CX20-CCX1-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0
  hb1203 = ListNF.listnfeq' nf-s7 auto

  hb1204 : Goal L.ax-CX20-CCX1-CX12-Swap01=CCX1-CX02-Swap12-CX10-CX20
  hb1204 = ListNF.listnfeq' nf-s7 auto

  hb1205 : Goal L.ax-CX20-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-CX02-CX21-CX12-CX10
  hb1205 = ListNF.listnfeq' nf-s7 auto

  hb1206 : Goal L.ax-CX20-CCX1-CX20-CCX2-CX02=CCX2-CX02-CCX1-CX21
  hb1206 = ListNF.listnfeq' nf-s7 auto

  hb1207 : Goal L.ax-CX20-CCX1-CCX0-CX01-CCX2=CCX0-CX12-CCX1-CX02-CX12-CX21-CX20-CCX0
  hb1207 = ListNF.listnfeq' nf-s7 auto

  hb1208 : Goal L.ax-CX20-CCX1-CCX0-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10-CX20
  hb1208 = ListNF.listnfeq' nf-s7 auto

  hb1209 : Goal L.ax-CX20-CCX1-CCX0-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10-CX20-CCX0
  hb1209 = ListNF.listnfeq' nf-s7 auto

  hb1210 : Goal L.ax-CX20-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-Swap12-Swap01-CX20
  hb1210 = ListNF.listnfeq' nf-s7 auto

  hb1211 : Goal L.ax-CX20-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-CX12-Swap01-CX20
  hb1211 = ListNF.listnfeq' nf-s7 auto

  hb1212 : Goal L.ax-CX20-CCX2-CX02-CCX1=CCX1-CX20-CCX2-CX02-CX21
  hb1212 = ListNF.listnfeq' nf-s7 auto

  hb1213 : Goal L.ax-CX20-CCX2-CCX1-CCX0-Swap12-Swap01=CX10-CCX1-CCX2-CX01-CX10-CX20-CCX0
  hb1213 = ListNF.listnfeq' nf-s7 auto

  hb1214 : Goal L.ax-CX20-CCX2-CX10-CCX1=CCX0-CCX2-CCX1-CX21-CX10-CX20-CCX0
  hb1214 = ListNF.listnfeq' nf-s7 auto

  hb1215 : Goal L.ax-CX20-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX21
  hb1215 = ListNF.listnfeq' nf-s7 auto

  hb1216 : Goal L.ax-CX20-CCX2-CCX0-CX01=CCX0-CCX2-CX01-CX21-CX20
  hb1216 = ListNF.listnfeq' nf-s7 auto

  hb1217 : Goal L.ax-CX20-CCX2-CCX0-CX02-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CX12-CX20
  hb1217 = ListNF.listnfeq' nf-s7 auto

  hb1218 : Goal L.ax-CX20-CCX2-CCX0-CX12-Swap01=CCX0-CX01-CCX2-CX12-CX21-CX10-CX20
  hb1218 = ListNF.listnfeq' nf-s7 auto

  hb1219 : Goal L.ax-CX20-CX12-Swap01=CX02-CX01-CX12-CX21-CX10-CX20
  hb1219 = ListNF.listnfeq' nf-s7 auto

  hb1220 : Goal L.ax-CX20-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01-CX20
  hb1220 = ListNF.listnfeq' nf-s7 auto

  hb1221 : Goal L.ax-CX20-CX12-CCX1=CX10-CX12-CCX1-CX21-CX20
  hb1221 = ListNF.listnfeq' nf-s7 auto

  hb1222 : Goal L.ax-CX20-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01-CX20
  hb1222 = ListNF.listnfeq' nf-s7 auto

  hb1223 : Goal L.ax-CX20-CX12-CCX1-CX02=CX01-CX20-CCX2-CX21-CX12
  hb1223 = ListNF.listnfeq' nf-s7 auto

  hb1224 : Goal L.ax-CX20-CX12-CCX2-Swap01=CX02-CCX0-CX01-CX12-CX21-CX10-CX20
  hb1224 = ListNF.listnfeq' nf-s7 auto

  hb1225 : Goal L.ax-CX20-CX12-CCX2-CCX0-Swap01=CCX0-CX12-CCX2-Swap01-CX21
  hb1225 = ListNF.listnfeq' nf-s7 auto

  hb1226 : Goal L.ax-CX20-CX12-CCX0-Swap01=CCX0-CX12-Swap01-CX21
  hb1226 = ListNF.listnfeq' nf-s7 auto

  hb1227 : Goal L.ax-CX20-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX20-CCX0
  hb1227 = ListNF.listnfeq' nf-s7 auto

  hb1228 : Goal L.ax-CX20-CX21-CCX0-CCX2-CX01=CCX0-CX21-CCX2-CX01
  hb1228 = ListNF.listnfeq' nf-s7 auto

  hb1229 : Goal L.ax-CX20-Swap12-Swap01=CX02-Swap12-CX10
  hb1229 = ListNF.listnfeq' nf-s7 auto

  hb1230 : Goal L.ax-CX20-Swap12-CCX1-CCX2-Swap01=CX02-CX10-CCX1-CX12-CX21-CX10-CX20-CCX0
  hb1230 = ListNF.listnfeq' nf-s7 auto

  hb1231 : Goal L.ax-CX20-Swap12-CCX2-Swap01=CX02-CCX1-CX12-CX21-CX10
  hb1231 = ListNF.listnfeq' nf-s7 auto

  hb1232 : Goal L.ax-CX20-CX10-CX02-CCX1=CX10-Swap12-CCX2-Swap01-CX21-CX12-CX20
  hb1232 = ListNF.listnfeq' nf-s7 auto

  hb1233 : Goal L.ax-CX20-CX10-CCX1=CX10-CCX1-CX21-CX20
  hb1233 = ListNF.listnfeq' nf-s7 auto

  hb1234 : Goal L.ax-CX20-CX10-CCX1-CX02=CX01-CCX0-CX02-CX21-CX12-CX10
  hb1234 = ListNF.listnfeq' nf-s7 auto

  hb1235 : Goal L.ax-CX20-CX10-CCX1-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10-CX20-CCX0
  hb1235 = ListNF.listnfeq' nf-s7 auto

  hb1236 : Goal L.ax-CX20-CX10-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0
  hb1236 = ListNF.listnfeq' nf-s7 auto

  hb1237 : Goal L.ax-CX20-CX10-CX12-CCX1=CX12-CCX1-CX21-CX20
  hb1237 = ListNF.listnfeq' nf-s7 auto

  hb1238 : Goal L.ax-CX20-CX10-Swap12-CCX2-Swap01=CX10-CX02-CCX1-CX12-CX21-CX10
  hb1238 = ListNF.listnfeq' nf-s7 auto

  hb1239 : Goal L.ax-CX20-CX20-CX01-CCX2=CX01-CCX2
  hb1239 = ListNF.listnfeq' nf-s7 auto

  hb1240 : Goal L.ax-CX20-CX20-CCX1-CCX2=CCX1-CCX2
  hb1240 = ListNF.listnfeq' nf-s7 auto

  hb1241 : Goal L.ax-CX20-CX20-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01
  hb1241 = ListNF.listnfeq' nf-s7 auto

  hb1242 : Goal L.ax-CX20-CX20-CCX1-CCX2-CX01=CCX1-CCX2-CX01
  hb1242 = ListNF.listnfeq' nf-s7 auto

  hb1243 : Goal L.ax-CX20-CX20-CCX1-CCX2-CX02=CCX1-CCX2-CX02
  hb1243 = ListNF.listnfeq' nf-s7 auto

  hb1244 : Goal L.ax-CX20-CX20-CCX2=CCX2
  hb1244 = ListNF.listnfeq' nf-s7 auto

  hb1245 : Goal L.ax-CX20-CX20-CCX2-Swap01=CCX2-Swap01
  hb1245 = ListNF.listnfeq' nf-s7 auto

  hb1246 : Goal L.ax-CX20-CX20-CCX2-CX01=CCX2-CX01
  hb1246 = ListNF.listnfeq' nf-s7 auto

  hb1247 : Goal L.ax-CX20-CX20-CCX2-CX02=CCX2-CX02
  hb1247 = ListNF.listnfeq' nf-s7 auto

  hb1248 : Goal L.ax-CX20-CX20-CCX2-CCX1=CCX2-CCX1
  hb1248 = ListNF.listnfeq' nf-s7 auto

  hb1249 : Goal L.ax-CX20-CX20-CCX2-CCX1-CX01=CCX2-CCX1-CX01
  hb1249 = ListNF.listnfeq' nf-s7 auto

  hb1250 : Goal L.ax-CX20-CX20-CCX2-CCX1-CX02=CCX2-CCX1-CX02
  hb1250 = ListNF.listnfeq' nf-s7 auto

  hb1251 : Goal L.ax-CX20-CX20-CX21-CCX2-CX01=CX21-CCX2-CX01
  hb1251 = ListNF.listnfeq' nf-s7 auto

  hb1252 : Goal L.ax-CX20-CCX0-Swap01=CCX0-Swap01-CX21
  hb1252 = ListNF.listnfeq' nf-s7 auto

  hb1253 : Goal L.ax-CX20-CCX0-CX01=CCX0-CX01-CX21-CX20
  hb1253 = ListNF.listnfeq' nf-s7 auto

  hb1254 : Goal L.ax-CX20-CCX0-CX01-CCX2=CCX2-CCX0-CX12-Swap01-CX21-CX12-CX10
  hb1254 = ListNF.listnfeq' nf-s7 auto

  hb1255 : Goal L.ax-CX20-CCX0-CX02=CCX0-Swap12-Swap01-Swap12-CX20
  hb1255 = ListNF.listnfeq' nf-s7 auto

  hb1256 : Goal L.ax-CX20-CCX0-CX02-CCX1=CCX0-Swap12-CCX2-Swap01-CX21-CX12-CX20
  hb1256 = ListNF.listnfeq' nf-s7 auto

  hb1257 : Goal L.ax-CX20-CCX0-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10-CX20
  hb1257 = ListNF.listnfeq' nf-s7 auto

  hb1258 : Goal L.ax-CX20-CCX0-CCX1-CCX2=CX10-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0
  hb1258 = ListNF.listnfeq' nf-s7 auto

  hb1259 : Goal L.ax-CX20-CCX0-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX20-CCX0
  hb1259 = ListNF.listnfeq' nf-s7 auto

  hb1260 : Goal L.ax-CX20-CCX0-CCX1-CX12-Swap01=CCX0-CCX1-CX02-Swap12-CX10-CX20
  hb1260 = ListNF.listnfeq' nf-s7 auto

  hb1261 : Goal L.ax-CX20-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX21
  hb1261 = ListNF.listnfeq' nf-s7 auto

  hb1262 : Goal L.ax-CX20-CCX0-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20
  hb1262 = ListNF.listnfeq' nf-s7 auto

  hb1263 : Goal L.ax-CX20-CCX0-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX10-CX20-CCX0
  hb1263 = ListNF.listnfeq' nf-s7 auto

  hb1264 : Goal L.ax-CX20-CCX0-CX12-Swap01=CX12-CCX0-Swap01-CX21
  hb1264 = ListNF.listnfeq' nf-s7 auto

  hb1265 : Goal L.ax-CX20-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX01-CCX2-CX21-CX12-CX10-CCX0
  hb1265 = ListNF.listnfeq' nf-s7 auto

  hb1266 : Goal L.ax-CX20-CCX0-CX12-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-CX21
  hb1266 = ListNF.listnfeq' nf-s7 auto

  hb1267 : Goal L.ax-CX20-CCX0-CX21-CCX2-CX01=CX21-CCX0-CCX2-CX01
  hb1267 = ListNF.listnfeq' nf-s7 auto

  hb1268 : Goal L.ax-CX20-CCX0-Swap12-Swap01=CCX0-CX02-Swap12-CX10
  hb1268 = ListNF.listnfeq' nf-s7 auto

  hb1269 : Goal L.ax-CX20-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10
  hb1269 = ListNF.listnfeq' nf-s7 auto

  hb1270 : Goal L.ax-CX20-CCX0-Swap12-CCX2-Swap01=CCX0-CX02-CCX1-CX12-CX21-CX10
  hb1270 = ListNF.listnfeq' nf-s7 auto

  hb1271 : Goal L.ax-CCX0-CX01-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-Swap01-CCX0
  hb1271 = ListNF.listnfeq' nf-s6 auto

  hb1272 : Goal L.ax-CCX0-CX01-CCX2-CCX0-CX01=CCX2-CX02-CCX1-CCX0
  hb1272 = ListNF.listnfeq' nf-s7 auto

  hb1273 : Goal L.ax-CCX0-CX01-CX20-CCX2=CCX1-CCX0-CX01-CCX2-CX20-CCX0
  hb1273 = ListNF.listnfeq' nf-s7 auto

  hb1274 : Goal L.ax-CCX0-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CCX0
  hb1274 = ListNF.listnfeq' nf-s6 auto

  hb1275 : Goal L.ax-CCX0-CX01-CCX0-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX10
  hb1275 = ListNF.listnfeq' nf-s7 auto

  hb1276 : Goal L.ax-CCX0-CX01-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10
  hb1276 = ListNF.listnfeq' nf-s7 auto

  hb1277 : Goal L.ax-CCX0-CX01-CCX0-CCX2-CX01=CCX1-CCX2-CX02-CCX0
  hb1277 = ListNF.listnfeq' nf-s7 auto

  hb1278 : Goal L.ax-CCX0-CX02-CX01=CX12-CCX0-Swap01-CX12-CX10
  hb1278 = ListNF.listnfeq' nf-s7 auto

  hb1279 : Goal L.ax-CCX0-CX02-CCX1-CCX0-CX02=CCX1-CX01-CCX2-CCX0
  hb1279 = ListNF.listnfeq' nf-s7 auto

  hb1280 : Goal L.ax-CCX0-CX02-CX10-CCX1=CCX2-CCX0-CX02-CCX1-CX10-CCX0
  hb1280 = ListNF.listnfeq' nf-s7 auto

  hb1281 : Goal L.ax-CCX0-CX02-CCX0-CX01=CX12-CCX2-CCX0-Swap01-CX12-CX10
  hb1281 = ListNF.listnfeq' nf-s7 auto

  hb1282 : Goal L.ax-CCX0-CCX1=CX10-CCX1-CX10-CCX0
  hb1282 = ListNF.listnfeq' nf-s6 auto

  hb1283 : Goal L.ax-CCX0-CCX1-CX01=CCX1-CX01-CCX0
  hb1283 = ListNF.listnfeq' nf-s6 auto

  hb1284 : Goal L.ax-CCX0-CCX1-CX01-CCX2=CX02-CCX1-CCX0-CX02-CCX0
  hb1284 = ListNF.listnfeq' nf-s7 auto

  hb1285 : Goal L.ax-CCX0-CCX1-CCX2-CX01=CCX1-CCX2-CX01-CCX0
  hb1285 = ListNF.listnfeq' nf-s6 auto

  hb1286 : Goal L.ax-CCX0-CCX1-CCX2-CX02=CX01-CCX0-CCX2-CX01-CCX0
  hb1286 = ListNF.listnfeq' nf-s7 auto

  hb1287 : Goal L.ax-CCX0-CCX1-CCX2-CCX0-Swap01=CCX1-CCX2-CCX0-Swap01-CCX0
  hb1287 = ListNF.listnfeq' nf-s6 auto

  hb1288 : Goal L.ax-CCX0-CCX1-CX12-CCX0-Swap01=CX01-CCX0-CX02-CX12-CX10
  hb1288 = ListNF.listnfeq' nf-s7 auto

  hb1289 : Goal L.ax-CCX0-CCX1-CCX0-CX01-CCX2=CX01-CX20-CCX2-CX20-CCX0
  hb1289 = ListNF.listnfeq' nf-s7 auto

  hb1290 : Goal L.ax-CCX0-CCX1-CCX0-CX02=CX10-CCX1-CX02-CX12-CX10
  hb1290 = ListNF.listnfeq' nf-s7 auto

  hb1291 : Goal L.ax-CCX0-CCX1-CCX0-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10
  hb1291 = ListNF.listnfeq' nf-s7 auto

  hb1292 : Goal L.ax-CCX0-CCX1-CCX0-CX12-Swap01=CX10-CX02-CCX1-CX12-CX10
  hb1292 = ListNF.listnfeq' nf-s7 auto

  hb1293 : Goal L.ax-CCX0-CCX1-CCX0-Swap12-Swap01=CX10-Swap12-CCX2-Swap01-CX21
  hb1293 = ListNF.listnfeq' nf-s7 auto

  hb1294 : Goal L.ax-CCX0-CCX2=CX20-CCX2-CX20-CCX0
  hb1294 = ListNF.listnfeq' nf-s7 auto

  hb1295 : Goal L.ax-CCX0-CCX2-CX02=CCX2-CX02-CCX0
  hb1295 = ListNF.listnfeq' nf-s7 auto

  hb1296 : Goal L.ax-CCX0-CCX2-CX02-CCX1=CX01-CCX2-CCX0-CX01-CCX0
  hb1296 = ListNF.listnfeq' nf-s7 auto

  hb1297 : Goal L.ax-CCX0-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX01-CX20-CCX0
  hb1297 = ListNF.listnfeq' nf-s7 auto

  hb1298 : Goal L.ax-CCX0-CCX2-CCX1-CX02=CCX2-CCX1-CX02-CCX0
  hb1298 = ListNF.listnfeq' nf-s7 auto

  hb1299 : Goal L.ax-CCX0-CCX2-CCX1-CCX0-Swap12-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CCX0
  hb1299 = ListNF.listnfeq' nf-s7 auto

  hb1300 : Goal L.ax-CCX0-CCX2-CX10-CCX1=CX20-CCX2-CCX1-CX21-CX10-CX20-CCX0
  hb1300 = ListNF.listnfeq' nf-s7 auto

  hb1301 : Goal L.ax-CCX0-CCX2-CCX0-Swap01=CX20-CCX2-Swap01-CX21
  hb1301 = ListNF.listnfeq' nf-s7 auto

  hb1302 : Goal L.ax-CCX0-CCX2-CCX0-CX01=CX20-CCX2-CX01-CX21-CX20
  hb1302 = ListNF.listnfeq' nf-s7 auto

  hb1303 : Goal L.ax-CCX0-CCX2-CCX0-CX02-CCX1=CX02-CX10-CCX1-CX10-CCX0
  hb1303 = ListNF.listnfeq' nf-s7 auto

  hb1304 : Goal L.ax-CCX0-CCX2-CCX0-CX12-Swap01=CX20-CX01-CCX2-CX12-CX21-CX10-CX20
  hb1304 = ListNF.listnfeq' nf-s7 auto

  hb1305 : Goal L.ax-CCX0-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01-CCX0
  hb1305 = ListNF.listnfeq' nf-s7 auto

  hb1306 : Goal L.ax-CCX0-CX12-CCX1=CX12-CCX1-CX10-CCX0
  hb1306 = ListNF.listnfeq' nf-s7 auto

  hb1307 : Goal L.ax-CCX0-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01-CCX0
  hb1307 = ListNF.listnfeq' nf-s7 auto


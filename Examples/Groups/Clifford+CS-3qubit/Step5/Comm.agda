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
open import Relation.Nullary using (Dec ; yes ; no ; does)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _*_)
open import Data.Nat.Properties using (_≟_ ; _≤?_)
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

open import Examples.Groups.Clifford+CS-3qubit.Step5.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step5.S8

module Examples.Groups.Clifford+CS-3qubit.Step5.Comm where

  -- Commutativity.
  comm : (x y : Gate) -> Maybe (commutes Rel x y)

  comm CX01-gen CX21-gen = just (axiom ax-CX01-CX21=CX21-CX01)
  comm CX01-gen CX02-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CX01-gen X1-gen = just (axiom ax-CX01-X1=X1-CX01)
  comm CX01-gen X2-gen = just (axiom ax-CX01-X2=X2-CX01)
  comm CX01-gen S0-gen = just (axiom ax-CX01-S0=S0-CX01)
  comm CX01-gen S2-gen = just (axiom ax-CX01-S2=S2-CX01)
  comm CX01-gen CS02-gen = just (axiom ax-CX01-CS02=CS02-CX01)
  comm CX01-gen iI-gen = just (axiom ax-CX01-iI=iI-CX01)
  comm CX01-gen CCX1-gen = just (symm (axiom ax-CCX1-CX01=CX01-CCX1))
  
  comm CX10-gen CX12-gen = just (symm (axiom ax-CX12-CX10=CX10-CX12))
  comm CX10-gen CX20-gen = just (axiom ax-CX10-CX20=CX20-CX10)
  comm CX10-gen X0-gen = just (axiom ax-CX10-X0=X0-CX10)
  comm CX10-gen X2-gen = just (axiom ax-CX10-X2=X2-CX10)
  comm CX10-gen S1-gen = just (axiom ax-CX10-S1=S1-CX10)
  comm CX10-gen S2-gen = just (axiom ax-CX10-S2=S2-CX10)
  comm CX10-gen CS12-gen = just (axiom ax-CX10-CS12=CS12-CX10)
  comm CX10-gen iI-gen = just (axiom ax-CX10-iI=iI-CX10)
  comm CX10-gen CCX0-gen = just (symm (axiom ax-CCX0-CX10=CX10-CCX0))
  
  comm CX12-gen CX10-gen = just (axiom ax-CX12-CX10=CX10-CX12)
  comm CX12-gen CX02-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CX12-gen X0-gen = just (axiom ax-CX12-X0=X0-CX12)
  comm CX12-gen X2-gen = just (axiom ax-CX12-X2=X2-CX12)
  comm CX12-gen S0-gen = just (axiom ax-CX12-S0=S0-CX12)
  comm CX12-gen S1-gen = just (axiom ax-CX12-S1=S1-CX12)
  comm CX12-gen CS01-gen = just (axiom ax-CX12-CS01=CS01-CX12)
  comm CX12-gen iI-gen = just (axiom ax-CX12-iI=iI-CX12)
  comm CX12-gen K0-gen = just (axiom ax-CX12-K0=K0-CX12)
  comm CX12-gen CCX2-gen = just (ListNF.listnfeq' nf-s8e auto)
  
  comm CX21-gen CX01-gen = just (symm (axiom ax-CX01-CX21=CX21-CX01))
  comm CX21-gen CX20-gen = just (axiom ax-CX21-CX20=CX20-CX21)
  comm CX21-gen X0-gen = just (axiom ax-CX21-X0=X0-CX21)
  comm CX21-gen X1-gen = just (axiom ax-CX21-X1=X1-CX21)
  comm CX21-gen S0-gen = just (axiom ax-CX21-S0=S0-CX21)
  comm CX21-gen S2-gen = just (axiom ax-CX21-S2=S2-CX21)
  comm CX21-gen CS02-gen = just (axiom ax-CX21-CS02=CS02-CX21)
  comm CX21-gen iI-gen = just (axiom ax-CX21-iI=iI-CX21)
  comm CX21-gen K0-gen = just (axiom ax-CX21-K0=K0-CX21)
  comm CX21-gen CCX1-gen = just (symm (axiom ax-CCX1-CX21=CX21-CCX1))
  
  comm CX02-gen CX01-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CX02-gen CX12-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CX02-gen X1-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CX02-gen X2-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CX02-gen S0-gen = just (axiom ax-CX02-S0=S0-CX02)
  comm CX02-gen S1-gen = just (axiom ax-CX02-S1=S1-CX02)
  comm CX02-gen CS01-gen = just (axiom ax-CX02-CS01=CS01-CX02)
  comm CX02-gen iI-gen = just (axiom ax-CX02-iI=iI-CX02)
  comm CX02-gen CCX2-gen = just (ListNF.listnfeq' nf-s8e auto)
  
  comm CX20-gen CX10-gen = just (axiom ax-CX20-CX10=CX10-CX20)
  comm CX20-gen CX21-gen = just (axiom ax-CX20-CX21=CX21-CX20)
  comm CX20-gen X0-gen = just (axiom ax-CX20-X0=X0-CX20)
  comm CX20-gen X1-gen = just (axiom ax-CX20-X1=X1-CX20)
  comm CX20-gen S1-gen = just (axiom ax-CX20-S1=S1-CX20)
  comm CX20-gen S2-gen = just (axiom ax-CX20-S2=S2-CX20)
  comm CX20-gen iI-gen = just (axiom ax-CX20-iI=iI-CX20)
  comm CX20-gen CCX0-gen = just (symm (axiom ax-CCX0-CX20=CX20-CCX0))

  comm X0-gen CCX0-gen = just (symm (axiom ax-CCX0-X0=X0-CCX0))
  comm X0-gen CX10-gen = just (symm (axiom ax-CX10-X0=X0-CX10))
  comm X0-gen CX12-gen = just (symm (axiom ax-CX12-X0=X0-CX12))
  comm X0-gen CX21-gen = just (symm (axiom ax-CX21-X0=X0-CX21))
  comm X0-gen CX20-gen = just (symm (axiom ax-CX20-X0=X0-CX20))
  comm X0-gen X1-gen = just (symm (axiom ax-X1-X0=X0-X1))
  comm X0-gen X2-gen = just (symm (axiom ax-X2-X0=X0-X2))
  comm X0-gen Swap12-gen = just (symm (axiom ax-Swap12-X0=X0-Swap12))
  comm X0-gen S1-gen = just (axiom ax-X0-S1=S1-X0)
  comm X0-gen S2-gen = just (axiom ax-X0-S2=S2-X0)
  comm X0-gen CS12-gen = just (axiom ax-X0-CS12=CS12-X0)
  comm X0-gen iI-gen = just (axiom ax-X0-iI=iI-X0)
  
  comm X1-gen CCX1-gen = just (symm (axiom ax-CCX1-X1=X1-CCX1))
  comm X1-gen CX01-gen = just (symm (axiom ax-CX01-X1=X1-CX01))
  comm X1-gen CX21-gen = just (symm (axiom ax-CX21-X1=X1-CX21))
  comm X1-gen CX02-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm X1-gen CX20-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm X1-gen X0-gen = just (axiom ax-X1-X0=X0-X1)
  comm X1-gen X2-gen = just (symm (axiom ax-X2-X1=X1-X2))
  comm X1-gen S0-gen = just (axiom ax-X1-S0=S0-X1)
  comm X1-gen S2-gen = just (axiom ax-X1-S2=S2-X1)
  comm X1-gen CS02-gen = just (axiom ax-X1-CS02=CS02-X1)
  comm X1-gen iI-gen = just (axiom ax-X1-iI=iI-X1)
  comm X1-gen K0-gen = just (axiom ax-X1-K0=K0-X1)
  
  comm X2-gen CCX2-gen = just (symm (axiom ax-CCX2-X2=X2-CCX2))
  comm X2-gen CX01-gen = just (symm (axiom ax-CX01-X2=X2-CX01))
  comm X2-gen CX10-gen = just (axiom ax-X2-CX10=CX10-X2)
  comm X2-gen CX12-gen = just (symm (axiom ax-CX12-X2=X2-CX12))
  comm X2-gen CX02-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm X2-gen X0-gen = just (axiom ax-X2-X0=X0-X2)
  comm X2-gen X1-gen = just (axiom ax-X2-X1=X1-X2)
  comm X2-gen Swap01-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm X2-gen S0-gen = just (axiom ax-X2-S0=S0-X2)
  comm X2-gen S1-gen = just (axiom ax-X2-S1=S1-X2)
  comm X2-gen CS01-gen = just (axiom ax-X2-CS01=CS01-X2)
  comm X2-gen iI-gen = just (axiom ax-X2-iI=iI-X2)
  comm X2-gen K0-gen = just (axiom ax-X2-K0=K0-X2)
  
  comm Swap01-gen CCX2-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm Swap01-gen X2-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm Swap01-gen S2-gen = just (axiom ax-Swap01-S2=S2-Swap01)
  comm Swap01-gen CS01-gen = just (axiom ax-Swap01-CS01=CS01-Swap01)
  comm Swap01-gen CCZ-gen = just (axiom ax-Swap01-CCZ=CCZ-Swap01)
  comm Swap01-gen iI-gen = just (axiom ax-Swap01-iI=iI-Swap01)
  
  comm Swap12-gen CCX0-gen = just (axiom ax-Swap12-CCX0=CCX0-Swap12)
  comm Swap12-gen X0-gen = just (axiom ax-Swap12-X0=X0-Swap12)
  comm Swap12-gen S0-gen = just (axiom ax-Swap12-S0=S0-Swap12)
  comm Swap12-gen CS12-gen = just (axiom ax-Swap12-CS12=CS12-Swap12)
  comm Swap12-gen CCZ-gen = just (axiom ax-Swap12-CCZ=CCZ-Swap12)
  comm Swap12-gen iI-gen = just (axiom ax-Swap12-iI=iI-Swap12)
  comm Swap12-gen K0-gen = just (axiom ax-Swap12-K0=K0-Swap12)
  
  comm S0-gen CCX1-gen = just (symm (axiom ax-CCX1-S0=S0-CCX1))
  comm S0-gen CCX2-gen = just (symm (axiom ax-CCX2-S0=S0-CCX2))
  comm S0-gen CX01-gen = just (symm (axiom ax-CX01-S0=S0-CX01))
  comm S0-gen CX12-gen = just (symm (axiom ax-CX12-S0=S0-CX12))
  comm S0-gen CX21-gen = just (symm (axiom ax-CX21-S0=S0-CX21))
  comm S0-gen CX02-gen = just (symm (axiom ax-CX02-S0=S0-CX02))
  comm S0-gen Swap12-gen = just (symm (axiom ax-Swap12-S0=S0-Swap12))
  comm S0-gen X1-gen = just (symm (axiom ax-X1-S0=S0-X1))
  comm S0-gen X2-gen = just (symm (axiom ax-X2-S0=S0-X2))
  comm S0-gen S1-gen = just (symm (axiom ax-S1-S0=S0-S1))
  comm S0-gen S2-gen = just (symm (axiom ax-S2-S0=S0-S2))
  comm S0-gen CS01-gen = just (symm (axiom ax-CS01-S0=S0-CS01))
  comm S0-gen CS12-gen = just (symm (axiom ax-CS12-S0=S0-CS12))
  comm S0-gen CS02-gen = just (symm (axiom ax-CS02-S0=S0-CS02))
  comm S0-gen CCZ-gen = just (symm (axiom ax-CCZ-S0=S0-CCZ))
  comm S0-gen iI-gen = just (symm (axiom ax-iI-S0=S0-iI))
  
  comm S1-gen CCX0-gen = just (symm (axiom ax-CCX0-S1=S1-CCX0))
  comm S1-gen CCX2-gen = just (symm (axiom ax-CCX2-S1=S1-CCX2))
  comm S1-gen CX10-gen = just (symm (axiom ax-CX10-S1=S1-CX10))
  comm S1-gen CX12-gen = just (symm (axiom ax-CX12-S1=S1-CX12))
  comm S1-gen CX02-gen = just (symm (axiom ax-CX02-S1=S1-CX02))
  comm S1-gen CX20-gen = just (symm (axiom ax-CX20-S1=S1-CX20))
  comm S1-gen X0-gen = just (symm (axiom ax-X0-S1=S1-X0))
  comm S1-gen X2-gen = just (symm (axiom ax-X2-S1=S1-X2))
  comm S1-gen S0-gen = just (axiom ax-S1-S0=S0-S1)
  comm S1-gen S2-gen = just (symm (axiom ax-S2-S1=S1-S2))
  comm S1-gen CS01-gen = just (symm (axiom ax-CS01-S1=S1-CS01))
  comm S1-gen CS12-gen = just (symm (axiom ax-CS12-S1=S1-CS12))
  comm S1-gen CS02-gen = just (symm (axiom ax-CS02-S1=S1-CS02))
  comm S1-gen CCZ-gen = just (symm (axiom ax-CCZ-S1=S1-CCZ))
  comm S1-gen iI-gen = just (symm (axiom ax-iI-S1=S1-iI))
  comm S1-gen K0-gen = just (axiom ax-S1-K0=K0-S1)
  
  comm S2-gen CCX0-gen = just (symm (axiom ax-CCX0-S2=S2-CCX0))
  comm S2-gen CCX1-gen = just (symm (axiom ax-CCX1-S2=S2-CCX1))
  comm S2-gen CX01-gen = just (symm (axiom ax-CX01-S2=S2-CX01))
  comm S2-gen CX10-gen = just (symm (axiom ax-CX10-S2=S2-CX10))
  comm S2-gen CX21-gen = just (symm (axiom ax-CX21-S2=S2-CX21))
  comm S2-gen CX20-gen = just (symm (axiom ax-CX20-S2=S2-CX20))
  comm S2-gen X0-gen = just (symm (axiom ax-X0-S2=S2-X0))
  comm S2-gen X1-gen = just (symm (axiom ax-X1-S2=S2-X1))
  comm S2-gen Swap01-gen = just (symm (axiom ax-Swap01-S2=S2-Swap01))
  comm S2-gen S0-gen = just (axiom ax-S2-S0=S0-S2)
  comm S2-gen S1-gen = just (axiom ax-S2-S1=S1-S2)
  comm S2-gen CS01-gen = just (symm (axiom ax-CS01-S2=S2-CS01))
  comm S2-gen CS12-gen = just (symm (axiom ax-CS12-S2=S2-CS12))
  comm S2-gen CS02-gen = just (symm (axiom ax-CS02-S2=S2-CS02))
  comm S2-gen CCZ-gen = just (symm (axiom ax-CCZ-S2=S2-CCZ))
  comm S2-gen iI-gen = just (symm (axiom ax-iI-S2=S2-iI))
  comm S2-gen K0-gen = just (axiom ax-S2-K0=K0-S2)
  
  comm CS01-gen CCX2-gen = just (symm (axiom ax-CCX2-CS01=CS01-CCX2))
  comm CS01-gen CX12-gen = just (symm (axiom ax-CX12-CS01=CS01-CX12))
  comm CS01-gen CX02-gen = just (symm (axiom ax-CX02-CS01=CS01-CX02))
  comm CS01-gen X2-gen = just (symm (axiom ax-X2-CS01=CS01-X2))
  comm CS01-gen Swap01-gen = just (symm (axiom ax-Swap01-CS01=CS01-Swap01))
  comm CS01-gen S0-gen = just (axiom ax-CS01-S0=S0-CS01)
  comm CS01-gen S1-gen = just (axiom ax-CS01-S1=S1-CS01)
  comm CS01-gen S2-gen = just (axiom ax-CS01-S2=S2-CS01)
  comm CS01-gen CS12-gen = just (symm (axiom ax-CS12-CS01=CS01-CS12))
  comm CS01-gen CS02-gen = just (symm (axiom ax-CS02-CS01=CS01-CS02))
  comm CS01-gen CCZ-gen = just (symm (axiom ax-CCZ-CS01=CS01-CCZ))
  comm CS01-gen iI-gen = just (symm (axiom ax-iI-CS01=CS01-iI))
  
  comm CS12-gen CCX0-gen = just (symm (axiom ax-CCX0-CS12=CS12-CCX0))
  comm CS12-gen CX10-gen = just (symm (axiom ax-CX10-CS12=CS12-CX10))
  comm CS12-gen CX20-gen = just (symm (axiom ax-CX20-CS12=CS12-CX20))
  comm CS12-gen X0-gen = just (symm (axiom ax-X0-CS12=CS12-X0))
  comm CS12-gen Swap12-gen = just (symm (axiom ax-Swap12-CS12=CS12-Swap12))
  comm CS12-gen S0-gen = just (axiom ax-CS12-S0=S0-CS12)
  comm CS12-gen S1-gen = just (axiom ax-CS12-S1=S1-CS12)
  comm CS12-gen S2-gen = just (axiom ax-CS12-S2=S2-CS12)
  comm CS12-gen CS01-gen = just (axiom ax-CS12-CS01=CS01-CS12)
  comm CS12-gen CS02-gen = just (axiom ax-CS12-CS02=CS02-CS12)
  comm CS12-gen CCZ-gen = just (symm (axiom ax-CCZ-CS12=CS12-CCZ))
  comm CS12-gen iI-gen = just (symm (axiom ax-iI-CS12=CS12-iI))
  comm CS12-gen K0-gen = just (axiom ax-CS12-K0=K0-CS12)
  
  comm CS02-gen CCX1-gen = just (symm (axiom ax-CCX1-CS02=CS02-CCX1))
  comm CS02-gen CX01-gen = just (symm (axiom ax-CX01-CS02=CS02-CX01))
  comm CS02-gen CX21-gen = just (symm (axiom ax-CX21-CS02=CS02-CX21))
  comm CS02-gen X1-gen = just (symm (axiom ax-X1-CS02=CS02-X1))
  comm CS02-gen S0-gen = just (axiom ax-CS02-S0=S0-CS02)
  comm CS02-gen S1-gen = just (axiom ax-CS02-S1=S1-CS02)
  comm CS02-gen S2-gen = just (axiom ax-CS02-S2=S2-CS02)
  comm CS02-gen CS01-gen = just (axiom ax-CS02-CS01=CS01-CS02)
  comm CS02-gen CS12-gen = just (symm (axiom ax-CS12-CS02=CS02-CS12))
  comm CS02-gen CCZ-gen = just (symm (axiom ax-CCZ-CS02=CS02-CCZ))
  comm CS02-gen iI-gen = just (symm (axiom ax-iI-CS02=CS02-iI))
  
  comm CCZ-gen Swap01-gen = just (symm (axiom ax-Swap01-CCZ=CCZ-Swap01))
  comm CCZ-gen Swap12-gen = just (symm (axiom ax-Swap12-CCZ=CCZ-Swap12))
  comm CCZ-gen S0-gen = just (axiom ax-CCZ-S0=S0-CCZ)
  comm CCZ-gen S1-gen = just (axiom ax-CCZ-S1=S1-CCZ)
  comm CCZ-gen S2-gen = just (axiom ax-CCZ-S2=S2-CCZ)
  comm CCZ-gen CS01-gen = just (axiom ax-CCZ-CS01=CS01-CCZ)
  comm CCZ-gen CS12-gen = just (axiom ax-CCZ-CS12=CS12-CCZ)
  comm CCZ-gen CS02-gen = just (axiom ax-CCZ-CS02=CS02-CCZ)
  comm CCZ-gen iI-gen = just (symm (axiom ax-iI-CCZ=CCZ-iI))
  
  comm iI-gen CCX0-gen = just (axiom ax-iI-CCX0=CCX0-iI)
  comm iI-gen CCX1-gen = just (axiom ax-iI-CCX1=CCX1-iI)
  comm iI-gen CCX2-gen = just (axiom ax-iI-CCX2=CCX2-iI)
  comm iI-gen CX01-gen = just (axiom ax-iI-CX01=CX01-iI)
  comm iI-gen CX10-gen = just (axiom ax-iI-CX10=CX10-iI)
  comm iI-gen CX12-gen = just (axiom ax-iI-CX12=CX12-iI)
  comm iI-gen CX21-gen = just (axiom ax-iI-CX21=CX21-iI)
  comm iI-gen CX02-gen = just (axiom ax-iI-CX02=CX02-iI)
  comm iI-gen CX20-gen = just (axiom ax-iI-CX20=CX20-iI)
  comm iI-gen X0-gen = just (axiom ax-iI-X0=X0-iI)
  comm iI-gen X1-gen = just (axiom ax-iI-X1=X1-iI)
  comm iI-gen X2-gen = just (axiom ax-iI-X2=X2-iI)
  comm iI-gen Swap01-gen = just (axiom ax-iI-Swap01=Swap01-iI)
  comm iI-gen Swap12-gen = just (axiom ax-iI-Swap12=Swap12-iI)
  comm iI-gen S0-gen = just (axiom ax-iI-S0=S0-iI)
  comm iI-gen S1-gen = just (axiom ax-iI-S1=S1-iI)
  comm iI-gen S2-gen = just (axiom ax-iI-S2=S2-iI)
  comm iI-gen CS01-gen = just (axiom ax-iI-CS01=CS01-iI)
  comm iI-gen CS12-gen = just (axiom ax-iI-CS12=CS12-iI)
  comm iI-gen CS02-gen = just (axiom ax-iI-CS02=CS02-iI)
  comm iI-gen CCZ-gen = just (axiom ax-iI-CCZ=CCZ-iI)
  comm iI-gen K0-gen = just (axiom ax-iI-K0=K0-iI)
  
  comm K0-gen CX12-gen = just (symm (axiom ax-CX12-K0=K0-CX12))
  comm K0-gen CX21-gen = just (symm (axiom ax-CX21-K0=K0-CX21))
  comm K0-gen X1-gen = just (symm (axiom ax-X1-K0=K0-X1))
  comm K0-gen X2-gen = just (symm (axiom ax-X2-K0=K0-X2))
  comm K0-gen Swap12-gen = just (symm (axiom ax-Swap12-K0=K0-Swap12))
  comm K0-gen S1-gen = just (symm (axiom ax-S1-K0=K0-S1))
  comm K0-gen S2-gen = just (symm (axiom ax-S2-K0=K0-S2))
  comm K0-gen CS12-gen = just (symm (axiom ax-CS12-K0=K0-CS12))
  comm K0-gen iI-gen = just (symm (axiom ax-iI-K0=K0-iI))
  
  comm CCX0-gen CX10-gen = just (axiom ax-CCX0-CX10=CX10-CCX0)
  comm CCX0-gen CX20-gen = just (axiom ax-CCX0-CX20=CX20-CCX0)
  comm CCX0-gen X0-gen = just (axiom ax-CCX0-X0=X0-CCX0)
  comm CCX0-gen Swap12-gen = just (symm (axiom ax-Swap12-CCX0=CCX0-Swap12))
  comm CCX0-gen S1-gen = just (axiom ax-CCX0-S1=S1-CCX0)
  comm CCX0-gen S2-gen = just (axiom ax-CCX0-S2=S2-CCX0)
  comm CCX0-gen CS12-gen = just (axiom ax-CCX0-CS12=CS12-CCX0)
  comm CCX0-gen iI-gen = just (axiom ax-CCX0-iI=iI-CCX0)
  
  comm CCX1-gen CX01-gen = just (axiom ax-CCX1-CX01=CX01-CCX1)
  comm CCX1-gen CX21-gen = just (axiom ax-CCX1-CX21=CX21-CCX1)
  comm CCX1-gen X1-gen = just (axiom ax-CCX1-X1=X1-CCX1)
  comm CCX1-gen S0-gen = just (axiom ax-CCX1-S0=S0-CCX1)
  comm CCX1-gen S2-gen = just (axiom ax-CCX1-S2=S2-CCX1)
  comm CCX1-gen CS02-gen = just (axiom ax-CCX1-CS02=CS02-CCX1)
  comm CCX1-gen iI-gen = just (axiom ax-CCX1-iI=iI-CCX1)
  
  comm CCX2-gen CX12-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CCX2-gen CX02-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CCX2-gen X2-gen = just (axiom ax-CCX2-X2=X2-CCX2)
  comm CCX2-gen Swap01-gen = just (ListNF.listnfeq' nf-s8e auto)
  comm CCX2-gen S0-gen = just (axiom ax-CCX2-S0=S0-CCX2)
  comm CCX2-gen S1-gen = just (axiom ax-CCX2-S1=S1-CCX2)
  comm CCX2-gen CS01-gen = just (axiom ax-CCX2-CS01=CS01-CCX2)
  comm CCX2-gen iI-gen = just (axiom ax-CCX2-iI=iI-CCX2)
  comm x y = nothing

  -- We number the generators for the purpose of ordering them.
  ord : Gate -> ℕ
  ord CCX0-gen = 28
  ord CCX1-gen = 27
  ord CCX2-gen = 26
  ord CX01-gen = 25
  ord CX10-gen = 24
  ord CX12-gen = 23
  ord CX21-gen = 22
  ord CX02-gen = 21
  ord CX20-gen = 20
  ord X0-gen = 19
  ord X1-gen = 18
  ord X2-gen = 17
  ord Swap01-gen = 16
  ord Swap12-gen = 15
  ord S0-gen = 14
  ord S1-gen = 13
  ord S2-gen = 12
  ord CS01-gen = 11
  ord CS12-gen = 10
  ord CS02-gen = 9
  ord CCZ-gen = 8
  ord iI-gen = 7
  ord CCK'-gen = 6
  ord CK10-gen = 5
  ord CK20-gen = 4
  ord K0-gen = 3
  ord K1-gen = 2
  ord K2-gen = 1
  
  -- Ordering of generators.
  less : Gate -> Gate -> Bool
  less x y with ord x ≤? ord y
  less x y | yes _ = true
  less x y | no _ = false
  
  open Commuting Gate Rel comm less public

  nf-comm : ListNF Rel
  nf-comm = record { listnf = comm-canonical ; lemma-listnf = lemma-comm-canonical }


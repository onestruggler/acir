------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
-- 
-- The translations between the gates and the simplified gates of Step 4,
-- taken out of Step4.Main (which re-exports them) so that the lemmas of
-- hypB can live in modules of their own (Step4.HypB1 ...), each typed by
-- Goal: the statement of hypB for one relation of Step 3.
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

module Examples.Groups.Clifford+CS-3qubit.Step4.Simple where

  -- Translation from Gate to simplified Gate.
  simple-of-gen : Gate -> Word Gate
  simple-of-gen CCX0-gen = CCX0
  simple-of-gen CCX1-gen = CCX1
  simple-of-gen CCX2-gen = CCX2
  simple-of-gen CX01-gen = CX01
  simple-of-gen CX10-gen = CX10
  simple-of-gen CX12-gen = CX12
  simple-of-gen CX21-gen = CX21
  simple-of-gen CX02-gen = CX02
  simple-of-gen CX20-gen = CX20
  simple-of-gen X0-gen = X0
  simple-of-gen X1-gen = X1
  simple-of-gen X2-gen = X2
  simple-of-gen Swap01-gen = Swap01
  simple-of-gen Swap12-gen = Swap12
  simple-of-gen S0-gen = S0
  simple-of-gen S1-gen = S1
  simple-of-gen S2-gen = S2
  simple-of-gen CS01-gen = CS01
  simple-of-gen CS12-gen = CS12
  simple-of-gen CS02-gen = CS02
  simple-of-gen CCZ-gen = CCZ
  simple-of-gen iI-gen = iI
  simple-of-gen CCK'-gen = CCK'
  simple-of-gen CK10-gen = CK10
  simple-of-gen CK20-gen = CK20
  simple-of-gen K0-gen = K0
  simple-of-gen K1-gen = K1
  simple-of-gen K2-gen = K2

  -- Translation from simplified Gate to Gate.
  gen-of-simple : Gate -> Word Gate
  gen-of-simple CCX0-gen = CCX0
  gen-of-simple CCX1-gen = CCX1
  gen-of-simple CCX2-gen = CCX2
  gen-of-simple CX01-gen = CX01
  gen-of-simple CX10-gen = CX10
  gen-of-simple CX12-gen = CX12
  gen-of-simple CX21-gen = CX21
  gen-of-simple CX02-gen = CX02
  gen-of-simple CX20-gen = CX20
  gen-of-simple X0-gen = X0
  gen-of-simple X1-gen = X1
  gen-of-simple X2-gen = X2
  gen-of-simple Swap01-gen = Swap01
  gen-of-simple Swap12-gen = Swap12
  gen-of-simple S0-gen = S0
  gen-of-simple S1-gen = S1
  gen-of-simple S2-gen = S2
  gen-of-simple CS01-gen = CS01
  gen-of-simple CS12-gen = CS12
  gen-of-simple CS02-gen = CS02
  gen-of-simple CCZ-gen = CCZ
  gen-of-simple iI-gen = iI
  gen-of-simple CCK'-gen = CCK'
  gen-of-simple CK10-gen = CK10
  gen-of-simple CK20-gen = CK20
  gen-of-simple K0-gen = K0
  gen-of-simple K1-gen = K1
  gen-of-simple K2-gen = K2

  simple-of-gen-star = simple-of-gen ʷ

  -- What hypB proves for a relation of Step 3.
  Goal : ∀ {u t : Word Gate} -> u === t ∈ L.Rel -> Set
  Goal {u} {t} _ = Rel ⊢ simple-of-gen-star u === simple-of-gen-star t

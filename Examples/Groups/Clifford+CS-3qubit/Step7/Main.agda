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
open import Examples.Groups.Clifford+CS-3qubit.Step7.Lemmas

module Examples.Groups.Clifford+CS-3qubit.Step7.Main where

  -- Translation from Gate to simplified Gate.
  simple-of-gen : Gate -> Word Gate
  simple-of-gen CCX0-gen = CCX0
  simple-of-gen CCX1-gen = Swap01 • CCX0 • Swap01
  simple-of-gen CCX2-gen = Swap12 • Swap01 • CCX0 • Swap01 • Swap12
  simple-of-gen CX01-gen = CX01
  simple-of-gen CX10-gen = Swap01 • CX01 • Swap01
  simple-of-gen CX12-gen = Swap01 • Swap12 • CX01 • Swap12 • Swap01
  simple-of-gen CX21-gen = Swap12 • Swap01 • Swap12 • CX01 • Swap12 • Swap01 • Swap12
  simple-of-gen CX02-gen = Swap12 • CX01 • Swap12
  simple-of-gen CX20-gen = Swap12 • Swap01 • CX01 • Swap01 • Swap12
  simple-of-gen X0-gen = X0
  simple-of-gen X1-gen = Swap01 • X0 • Swap01
  simple-of-gen X2-gen = Swap12 • Swap01 • X0 • Swap01 • Swap12
  simple-of-gen Swap01-gen = Swap01
  simple-of-gen Swap12-gen = Swap12
  simple-of-gen S0-gen = S0
  simple-of-gen S1-gen = Swap01 • S0 • Swap01
  simple-of-gen S2-gen = Swap12 • Swap01 • S0 • Swap01 • Swap12
  simple-of-gen CS01-gen = CS01
  simple-of-gen CS12-gen = Swap01 • Swap12 • CS01 • Swap12 • Swap01
  simple-of-gen CS02-gen = Swap12 • CS01 • Swap12
  simple-of-gen CCZ-gen = CCZ
  simple-of-gen iI-gen = iI
  simple-of-gen CCK'-gen = K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
  simple-of-gen CK10-gen = CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI
  simple-of-gen CK20-gen = CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI
  simple-of-gen K0-gen = K0
  simple-of-gen K1-gen = Swap01 • K0 • Swap01
  simple-of-gen K2-gen = Swap12 • Swap01 • K0 • Swap01 • Swap12

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

  hypA : ∀ (x : Gate) -> Rel ⊢ [ x ]ʷ === simple-of-gen-star (gen-of-simple x)
  hypA CCX0-gen = refl
  hypA CCX1-gen = MvSwap01.general-rewrite 20 auto
  hypA CCX2-gen = MvSwap.general-rewrite 20 auto
  hypA CX01-gen = refl
  hypA CX10-gen = MvSwap.general-rewrite 20 auto
  hypA CX12-gen = MvSwap.general-rewrite 50 auto
  hypA CX21-gen = MvSwap.general-rewrite 20 auto
  hypA CX02-gen = MvSwap.general-rewrite 20 auto
  hypA CX20-gen = MvSwap.general-rewrite 20 auto
  hypA X0-gen = refl
  hypA X1-gen = MvSwap.general-rewrite 20 auto
  hypA X2-gen = MvSwap.general-rewrite 20 auto
  hypA Swap01-gen = refl
  hypA Swap12-gen = refl
  hypA S0-gen = refl
  hypA S1-gen = MvSwap.general-rewrite 20 auto
  hypA S2-gen = MvSwap.general-rewrite 20 auto
  hypA CS01-gen = refl
  hypA CS12-gen = MvSwap.general-rewrite 20 auto
  hypA CS02-gen = MvSwap.general-rewrite 20 auto
  hypA CCZ-gen = refl
  hypA iI-gen = refl
  hypA CCK'-gen = axiom ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI
  hypA CK10-gen = axiom ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI
  hypA CK20-gen = axiom ax-CK20=CS02-K0-CS02-K0-CS02-S2-S2-S2-iI
  hypA K0-gen = refl
  hypA K1-gen = axiom ax-K1=Swap01-K0-Swap01
  hypA K2-gen = axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12

  open Group-Lemmas Gate Rel group-like

  hypB : ∀ {u t : Word Gate} -> u === t ∈ L.Rel -> Rel ⊢ simple-of-gen-star u === simple-of-gen-star t


  hypB L.ax-Swap12-Swap01-Swap12=Swap01-Swap12-Swap01 = axiom ax-Swap12-Swap01-Swap12=Swap01-Swap12-Swap01
  hypB L.ax-K1=Swap01-K0-Swap01 = refl
  hypB L.ax-K2=Swap12-Swap01-K0-Swap01-Swap12 = refl
  hypB L.ax-Swap01-K0-Swap01-K0=K0-Swap01-K0-Swap01 = (axiom ax-Swap01-K0-Swap01-K0=K0-Swap01-K0-Swap01)
  hypB L.ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI = MvSwap.general-rewrite 20 auto
  hypB L.ax-CK20=CS02-K0-CS02-K0-CS02-S2-S2-S2-iI = MvSwap.general-rewrite 20 auto
  hypB L.ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI = MvSwap.general-rewrite 50 auto
  hypB L.ax-Swap01=CX01-CX10-CX01 = up-to-swap 100 auto (axiom ax-Swap01=CX01-CX10-CX01)
  hypB L.ax-Swap12=CX12-CX21-CX12 = up-to-swap 100 auto (axiom ax-Swap12=CX12-CX21-CX12)
  hypB L.ax-Swap01=CX10-CX01-CX10 = B01.by-basis-change Swap01 Swap01 (lemma-Swap01=CX01-Swap01-CX01-Swap01-CX01) 50 auto
  hypB L.ax-Swap12=CX21-CX12-CX21 = by-basis-change Swap12 Swap12 (lemma-Swap12) 50 auto
  hypB L.ax-Swap01-X0=X1-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap01-X1=X0-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap01-CX12=CX02-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap01-CX21=CX20-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap01-CX02=CX12-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap01-CX20=CX21-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap01-CCX2=CCX2-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap01-CCX0=CCX1-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap01-CCX1=CCX0-Swap01 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-X1=X2-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-X2=X1-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-CX01=CX02-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-CX10=CX20-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-CX02=CX01-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-CX20=CX10-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-CCX2=CCX1-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-CCX1=CCX2-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-Swap12-CCX0=CCX0-Swap12 = MvSwap.general-rewrite 20 auto
  hypB L.ax-CX01-CX02=CX02-CX01 = SA.general-rewrite 50 auto
  hypB L.ax-CCX0-CCX0=ε = Order.general-rewrite 20 auto
  hypB L.ax-CX01-CX01=ε = Order.general-rewrite 20 auto
  hypB L.ax-CX10-CX10=ε = Order.general-rewrite 20 auto
  hypB L.ax-CX12-CX12=ε = Order.general-rewrite 20 auto
  hypB L.ax-CX21-CX21=ε = Order.general-rewrite 20 auto
  hypB L.ax-X0-X0=ε = Order.general-rewrite 20 auto
  hypB L.ax-S0-S0-S0-S0=ε = Order.general-rewrite 20 auto
  hypB L.ax-CS01-CS01-CS01-CS01=ε = Order.general-rewrite 20 auto
  hypB L.ax-CS12-CS12-CS12-CS12=ε = Order.general-rewrite 20 auto
  hypB L.ax-CCZ-CCZ=ε = Order.general-rewrite 20 auto
  hypB L.ax-iI-iI-iI-iI=ε = Order.general-rewrite 20 auto
  hypB L.ax-K0-K0=iI-iI-iI = Order.general-rewrite 20 auto
  hypB L.ax-iI-CCX0=CCX0-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CX01=CX01-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-X0=X0-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-Swap01=Swap01-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-Swap12=Swap12-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0=S0-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CS01=CS01-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CS12=CS12-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CCZ=CCZ-iI = mvI.general-rewrite 20 auto
  hypB L.ax-X0-S0=S0-S0-S0-iI-X0 = axiom ax-X0-S0=S0-S0-S0-iI-X0
  hypB L.ax-X0-S1=S1-X0 = SA.general-rewrite 50 auto
  hypB L.ax-X0-CS01=S1-CS01-CS01-CS01-X0 = SA.general-rewrite 50 auto
  hypB L.ax-X0-CS12=CS12-X0 = SA.general-rewrite 50 auto
  hypB L.ax-X0-CCZ=CS12-CS12-CCZ-X0 = SA.general-rewrite 50 auto
  hypB L.ax-CX10-S0=S0-S1-CS01-CS01-CX10 = SA.general-rewrite 50 auto
  hypB L.ax-CX10-S1=S1-CX10 = SA.general-rewrite 50 auto
  hypB L.ax-CX10-S2=S2-CX10 = SA.general-rewrite 50 auto
  hypB L.ax-CX10-CS01=S1-CS01-CS01-CS01-CX10 = SA.general-rewrite 50 auto
  hypB L.ax-CX10-CS12=CS12-CX10 = SA.general-rewrite 50 auto
  hypB L.ax-CX10-CS02=CS02-CS12-CCZ-CX10 = SA.general-rewrite 50 auto
  hypB L.ax-CX10-CCZ=CS12-CS12-CCZ-CX10 = SA.general-rewrite 50 auto
  hypB L.ax-CCX0-S0=S0-CS12-CCZ-CCX0 = SA.general-rewrite 50 auto
  hypB L.ax-CCX0-S1=S1-CCX0 = SA.general-rewrite 50 auto
  hypB L.ax-CCX0-CS01=CS01-CS12-CCZ-CCX0 = SA.general-rewrite 50 auto
  hypB L.ax-CCX0-CS12=CS12-CCX0 = SA.general-rewrite 50 auto
  hypB L.ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0 = SA.general-rewrite 50 auto
  hypB L.ax-CX10=K0-CS01-CS01-K0-iI = up-to-swap 100 auto (lemma-CX10=K0-CS01-CS01-K0-iI)
  hypB L.ax-S1-S0=S0-S1 = SA.general-rewrite 50 auto
  hypB L.ax-CS01-S0=S0-CS01 = SA.general-rewrite 50 auto
  hypB L.ax-CS01-S1=S1-CS01 = SA.general-rewrite 50 auto
  hypB L.ax-CS01-S2=S2-CS01 = SA.general-rewrite 50 auto
  hypB L.ax-CS12-CS01=CS01-CS12 = SA.general-rewrite 50 auto
  hypB L.ax-CS02-CS01=CS01-CS02 = SA.general-rewrite 50 auto
  hypB L.ax-CCZ-S0=S0-CCZ = SA.general-rewrite 50 auto
  hypB L.ax-CCZ-CS01=CS01-CCZ = SA.general-rewrite 50 auto
  hypB L.ax-Swap01-S0=S1-Swap01 = SA.general-rewrite 50 auto
  hypB L.ax-Swap01-S1=S0-Swap01 = SA.general-rewrite 50 auto
  hypB L.ax-Swap01-S2=S2-Swap01 = SA.general-rewrite 50 auto
  hypB L.ax-Swap01-CS01=CS01-Swap01 = axiom ax-Swap01-CS01=CS01-Swap01
  hypB L.ax-Swap01-CS02=CS12-Swap01 = SA.general-rewrite 50 auto
  hypB L.ax-Swap01-CS12=CS02-Swap01 = SA.general-rewrite 50 auto
  hypB L.ax-Swap01-CCZ=CCZ-Swap01 = axiom ax-Swap01-CCZ=CCZ-Swap01
  hypB L.ax-Swap12-S0=S0-Swap12 = axiom ax-Swap12-S0=S0-Swap12
  hypB L.ax-Swap12-S1=S2-Swap12 = SA.general-rewrite 50 auto
  hypB L.ax-Swap12-S2=S1-Swap12 = SA.general-rewrite 50 auto
  hypB L.ax-Swap12-CS01=CS02-Swap12 = SA.general-rewrite 50 auto
  hypB L.ax-Swap12-CS02=CS01-Swap12 = SA.general-rewrite 50 auto
  hypB L.ax-Swap12-CS12=CS12-Swap12 = SA.general-rewrite 50 auto
  hypB L.ax-Swap12-CCZ=CCZ-Swap12 = axiom ax-Swap12-CCZ=CCZ-Swap12


  hypB L.ax-CX02=CX01-CCX2-CX01-CCX2 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CX10=CX10-CCX0-CCX1-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CCX0-CX01=CX01-CCX0-CCX1-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CCX0-CX10=CX10-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CX02-CX21=CX21-CCX2-CX01-CCX2 = S7.general-rewrite 50 auto
  hypB L.ax-CX20-CX21=CX21-CX20 = S7.general-rewrite 50 auto
  hypB L.ax-CX12-CX20=CX20-CCX2-CX10-CCX2 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX10-CX20=CX20-CX10 = S7.general-rewrite 50 auto
  hypB L.ax-CX10-CX21=CX21-CX20-CX10 = S7.general-rewrite 50 auto
  hypB L.ax-CX01-CX21=CX21-CX01 = S7.general-rewrite 50 auto
  hypB L.ax-CCX2-CX20=CX20-CCX0-CCX2-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX2-CX21=CX21-CCX1-CCX2-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CX20=CX21-CX20-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CCX0-CX20=CX20-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CCX0-CX21=CX21-CX20-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CCX0-CCX1=CCX0-CCX1-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CCX0-CCX2=CCX0-CCX2-CCX0-CCX1-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX1-CCX2-CX01=CX01-CCX2-CX01-CCX1-CCX2-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CX10-CX01-CX10=CX01-CX10-CX01 = S7.general-rewrite 50 auto
  hypB L.ax-CX01-CX01-CX10=CX10 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CX01-CX10=CX01-CX10-CCX0-CCX1-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CCX2-CX10=CX01-CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0 = up-to-swap 200 auto lemma-CCX1-CCX2-CX10=CX01-CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0
  hypB L.ax-CCX0-CCX2-CX10=CX10-CCX2-CX10-CCX0-CCX2-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CX02-CX12-CX21=CX12-CX21-CCX2-CX01-CCX2 = S7.general-rewrite 50 auto
  hypB L.ax-CX02-CX21-CX20=CX01-CX02-CX20-CX01 = S7.general-rewrite 50 auto
  hypB L.ax-CX20-CX02-CX20=CX02-CX20-CX01-CCX2-CX01-CCX2 = S7.general-rewrite 50 auto
  hypB L.ax-CX20-CX12-CX21=CX12-CX21-CX10 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX12-CX02-CX20=CX02-CX20-CCX2-CX10-CCX2 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX12-CX21-CX20=CX01-CX02-CX20-CCX2-CX10-CCX2-CX01 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX21-CX02-CX20=CX02-CX20-CX01 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX10-CX02-CX20=CX02-CX20-CX10-CCX2-CX10-CCX2 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX10-CX12-CX21=CX01-CX02-CX20-CX01-CX10-CCX2-CX01-CCX2 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX01-CX12-CX21=CX12-CX21-CX01-CCX2-CX01-CCX2 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX01-CX21-CX20=CX20-CX01 = S7.general-rewrite 50 auto
  hypB L.ax-CCX2-CX02-CX20=CX02-CX20-CCX0-CCX2-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX2-CX12-CX21=CX12-CX21-CCX1-CCX2-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CCX2-CX21-CX20=CX01-CX02-CX20-CCX0-CCX2-CX01-CCX0-CCX1-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX1-CX02-CX20=CX02-CX20-CX01-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CX21-CX20=CX20-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CCX0-CX12-CX21=CX12-CX21-CX10-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX0-CX21-CX20=CX21-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CX01-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX1-CCX2-CCX1-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX2-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0-CCX1-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX1-CX01-CCX2-CX01=CCX2-CX01-CCX1-CCX2-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX0-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CX10-CX01-CCX2-CX10=CX01-CCX2-CX10-CX01 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX01-CX10-CCX2-CX10=CX10-CCX2-CX10-CX01 = S7.general-rewrite 50 auto
  hypB L.ax-CCX2-CX01-CCX2-CX10=CX01-CCX2-CX10-CX01-CCX2-CX01 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CX10-CCX2-CX10=CX10-CCX2-CX10-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CCX1-CX01-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0 = up-to-swap 100 auto lemma-CCX1-CX01-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0
  hypB L.ax-CCX0-CX10-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CCX0 = S7.general-rewrite 50 auto
  hypB L.ax-CCX0-CX01-CCX2-CX10=CX01-CCX2-CX10-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CX02-CX01-CX02-CX20=CX21-CX20-CX01 = S7.general-rewrite 50 auto
  hypB L.ax-CX20-CX01-CX02-CX20=CX01-CX02-CX20-CCX2-CX01-CCX2 = S7.general-rewrite 50 auto
  hypB L.ax-CX12-CX01-CX02-CX20=CX21-CX20-CX01-CCX2-CX10-CCX2 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX21-CX01-CX02-CX20=CX01-CX02-CX20-CX01 = S7.general-rewrite 100 auto
  hypB L.ax-CX10-CX01-CX02-CX20=CX12-CX21-CX01-CCX2-CX10-CX01-CCX2 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CX01-CX01-CX02-CX20=CX02-CX20 = S7.general-rewrite 50 auto
  hypB L.ax-CCX2-CX01-CX02-CX20=CX21-CX20-CX01-CCX0-CCX2-CCX0 = lemma-one-sided (S7.general-rewrite 100 auto)
  hypB L.ax-CCX1-CX01-CX02-CX20=CX01-CX02-CX20-CX01-CCX1 = S7.general-rewrite 50 auto
  hypB L.ax-CCX0-CX01-CX02-CX20=CX01-CX02-CX20-CCX2-CX01-CCX1-CCX2 = lemma-one-sided (S7.general-rewrite 100 auto)


  hypB L.ax-X1-X0=X0-X1 = SA.general-rewrite 50 auto
  hypB L.ax-X2-X0=X0-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-X1=X1-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CX02=CX02-X0-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CX20=CX20-X0 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CX12=CX12-X0 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CX21=CX21-X0 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CX10=CX10-X0 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CX01=CX01-X0-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CCX2=CCX2-CX12-X0 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CCX1=CCX1-CX21-X0 = SA2.general-rewrite 50 auto
  hypB L.ax-X0-CCX0=CCX0-X0 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CX02=CX02-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CX20=CX20-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CX12=CX12-X1-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CX21=CX21-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CX10=CX10-X0-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CX01=CX01-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CCX2=CCX2-CX02-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CCX1=CCX1-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X1-CCX0=CCX0-CX20-X1 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CX02=CX02-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CX20=CX20-X0-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CX12=CX12-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CX21=CX21-X1-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CX10=CX10-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CX01=CX01-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CCX2=CCX2-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CCX1=CCX1-CX01-X2 = SA2.general-rewrite 50 auto
  hypB L.ax-X2-CCX0=CCX0-CX10-X2 = SA2.general-rewrite 50 auto
  
  hypB L.ax-iI-K0=K0-iI = axiom ax-iI-K0=K0-iI
  hypB L.ax-S1-K0=K0-S1 = SA.general-rewrite 20 auto
  hypB L.ax-S2-K0=K0-S2 = by-basis-change Swap12 Swap12 (hypB L.ax-S1-K0=K0-S1) 20 auto
  hypB L.ax-X1-K0=K0-X1 = SA.general-rewrite 20 auto
  hypB L.ax-X2-K0=K0-X2 = by-basis-change Swap12 Swap12 (hypB L.ax-X1-K0=K0-X1) 20 auto
  hypB L.ax-CS12-K0=K0-CS12 = SA.general-rewrite 20 auto
  hypB L.ax-CX12-K0=K0-CX12 = SA.general-rewrite 20 auto
  hypB L.ax-CX21-K0=K0-CX21 = by-basis-change Swap12 Swap12 (hypB L.ax-CX12-K0=K0-CX12) 20 auto
  hypB L.ax-Swap12-K0=K0-Swap12 = SA.general-rewrite 20 auto
  hypB L.ax-S0-S0-K0=K0-X0 = axiom ax-S0-S0-K0=K0-X0
  hypB L.ax-CS01-CS01-K0=K0-CX10 = SA.general-rewrite 20 auto
  hypB L.ax-CS02-CS02-K0=K0-CX20 = by-basis-change Swap12 Swap12 (hypB L.ax-CS01-CS01-K0=K0-CX10) 20 auto
  hypB L.ax-CCZ-K0=K0-CCX0 = SA.general-rewrite 20 auto
  hypB L.ax-X0-K0=K0-S0-S0 = lemma-X0-K0=K0-S0-S0
  hypB L.ax-CX10-K0=K0-CS01-CS01 = SA.general-rewrite 20 auto
  hypB L.ax-CX20-K0=K0-CS02-CS02 = by-basis-change Swap12 Swap12 (hypB L.ax-CX10-K0=K0-CS01-CS01) 20 auto
  hypB L.ax-CCX0-K0=K0-CCZ = SA.general-rewrite 20 auto
  hypB L.ax-S0-K0-S0-K0-S0-K0=iI-iI-iI = axiom ax-S0-K0-S0-K0-S0-K0=iI-iI-iI
  hypB L.ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 = SA.general-rewrite 20 auto
  hypB L.ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ = SA.general-rewrite 20 auto

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
import Examples.Groups.Clifford+CS-3qubit.Gate as LG
open CliffordCS

import Examples.Groups.Clifford+CS-3qubit.Step7.Rel as L

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
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap8
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap9a
open import Examples.Groups.Clifford+CS-3qubit.Step8.Swap9

module Examples.Groups.Clifford+CS-3qubit.Step8.Main where

  -- Translation from Gate to simplified Gate.
  simple-of-gen : LG.Gate -> Word Gen
  simple-of-gen LG.CCX0-gen = CCX0
  simple-of-gen LG.CCX1-gen = CCX1
  simple-of-gen LG.CCX2-gen = CCX2
  simple-of-gen LG.CX01-gen = CX01
  simple-of-gen LG.CX10-gen = CX10
  simple-of-gen LG.CX12-gen = CX12
  simple-of-gen LG.CX21-gen = CX21
  simple-of-gen LG.CX02-gen = CX02
  simple-of-gen LG.CX20-gen = CX20
  simple-of-gen LG.X0-gen = X0
  simple-of-gen LG.X1-gen = X1
  simple-of-gen LG.X2-gen = X2
  simple-of-gen LG.Swap01-gen = Swap01
  simple-of-gen LG.Swap12-gen = Swap12
  simple-of-gen LG.S0-gen = S0
  simple-of-gen LG.S1-gen = S1
  simple-of-gen LG.S2-gen = S2
  simple-of-gen LG.CS01-gen = CS01
  simple-of-gen LG.CS12-gen = CS12
  simple-of-gen LG.CS02-gen = CS02
  simple-of-gen LG.CCZ-gen = CCZ
  simple-of-gen LG.iI-gen = iI
  simple-of-gen LG.CCK'-gen = CCK'
  simple-of-gen LG.CK10-gen = CK10
  simple-of-gen LG.CK20-gen = CK20
  simple-of-gen LG.K0-gen = K0
  simple-of-gen LG.K1-gen = K1
  simple-of-gen LG.K2-gen = K2

  -- Translation from simplified Gate to Gate.
  gen-of-simple : Gen -> Word LG.Gate
  gen-of-simple S0-gen = LG.S0
  gen-of-simple S1-gen = LG.S1
  gen-of-simple S2-gen = LG.S2
  gen-of-simple CS01-gen = LG.CS01
  gen-of-simple CS12-gen = LG.CS12
  gen-of-simple iI-gen = LG.iI
  gen-of-simple K0-gen = LG.K0
  gen-of-simple K1-gen = LG.K1
  gen-of-simple K2-gen = LG.K2

  simple-of-gen-star = simple-of-gen ʷ

  hypA : ∀ (x : Gen) -> Rel ⊢ [ x ]ʷ === simple-of-gen-star (gen-of-simple x)
  hypA S0-gen = refl
  hypA S1-gen = refl
  hypA S2-gen = refl
  hypA CS01-gen = refl
  hypA CS12-gen = refl
  hypA iI-gen = refl
  hypA K0-gen = refl
  hypA K1-gen = refl
  hypA K2-gen = refl

  hypB : ∀ {u t : Word LG.Gate} -> u === t ∈ L.Rel -> Rel ⊢ simple-of-gen-star u === simple-of-gen-star t

  hypB L.ax-K1=Swap01-K0-Swap01 = hypB1
  hypB L.ax-K2=Swap12-Swap01-K0-Swap01-Swap12 = hypB2
  hypB L.ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-CK20=CS02-K0-CS02-K0-CS02-S2-S2-S2-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI = Order.general-rewrite 100 auto
  hypB L.ax-iI-K0=K0-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-S1-K0=K0-S1 = Monoidal.general-rewrite 100 auto
  hypB L.ax-X1-K0=K0-X1 = Monoidal.general-rewrite 100 auto
  hypB L.ax-CS12-K0=K0-CS12 = Monoidal.general-rewrite 100 auto
  hypB L.ax-CX12-K0=K0-CX12 = Monoidal.general-rewrite 100 auto
  hypB L.ax-Swap12-K0=K0-Swap12 = Monoidal.general-rewrite 100 auto
  hypB L.ax-S0-S0-K0=K0-X0 = Order.general-rewrite 100 auto
  hypB L.ax-CS01-CS01-K0=K0-CX10 = Order.general-rewrite 100 auto
  hypB L.ax-CCZ-K0=K0-CCX0 = Order.general-rewrite 100 auto
  hypB L.ax-S0-K0-S0-K0-S0-K0=iI-iI-iI = Order.general-rewrite 100 auto
  hypB L.ax-Swap01-K0-Swap01-K0=K0-Swap01-K0-Swap01 = hypB3
  hypB L.ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 = axiom ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01
  hypB L.ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ = lemma-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ
  hypB L.ax-X0-S0=S0-S0-S0-iI-X0 = mvSL.general-rewrite 200 auto
  hypB L.ax-X0-S1=S1-X0 = Monoidal.general-rewrite 100 auto
  hypB L.ax-X0-CS01=S1-CS01-CS01-CS01-X0 = lemma-X0-CS01=S1-CS01-CS01-CS01-X0
  hypB L.ax-X0-CS12=CS12-X0 = Monoidal.general-rewrite 100 auto
  hypB L.ax-X0-CCZ=CS12-CS12-CCZ-X0 = lemma-X-CCZ 
  hypB L.ax-CX10-S0=S0-S1-CS01-CS01-CX10 = lemma-CX10-S0'
  hypB L.ax-CX10-S1=S1-CX10 = Order.general-rewrite 100 auto
  hypB L.ax-CX10-S2=S2-CX10 = Order.general-rewrite 100 auto
  hypB L.ax-CX10-CS01=S1-CS01-CS01-CS01-CX10 = mvSCSL.general-rewrite 200 auto
  hypB L.ax-CX10-CS12=CS12-CX10 = Order.general-rewrite 100 auto
  hypB L.ax-CX10-CS02=CS02-CS12-CCZ-CX10 = lemma-CX10-CS02=CS02-CS12-CCZ-CX10
  hypB L.ax-CX10-CCZ=CS12-CS12-CCZ-CX10 = lemma-CX10-CCZ=CS12-CS12-CCZ-CX10
  hypB L.ax-CCX0-S0=S0-CS12-CCZ-CCX0 = lemma-CCX0-S0=S0-CS12-CCZ-CCX0
  hypB L.ax-CCX0-S1=S1-CCX0 = lemma-CCX0-S1=S1-CCX0
  hypB L.ax-CCX0-CS01=CS01-CS12-CCZ-CCX0 = lemma-CCX0-CS01=CS01-CS12-CCZ-CCX0
  hypB L.ax-CCX0-CS12=CS12-CCX0 = lemma-CCX0-CS12=CS12-CCX0
  hypB L.ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0 = lemma-CCX0-CCZ=CS12-CS12-CCZ-CCX0
  hypB L.ax-S1-S0=S0-S1 = Monoidal.general-rewrite 100 auto
  hypB L.ax-CS01-S0=S0-CS01 = Monoidal.general-rewrite 100 auto
  hypB L.ax-CS01-S2=S2-CS01 = Monoidal.general-rewrite 100 auto
  hypB L.ax-CS12-CS01=CS01-CS12 = Order.general-rewrite 100 auto
  hypB L.ax-CCZ-S0=S0-CCZ = Monoidal.general-rewrite 100 auto
  hypB L.ax-CCZ-CS01=CS01-CCZ = lemma-CCZ-CS01=CS01-CCZ
  hypB L.ax-CCX0-CCX0=ε = lemma-CCX0-CCX0=ε
  hypB L.ax-CCX0-CCX1-CCX0=CCX1-CCX0-CCX1 = lemma-CCX0-CCX1-CCX0=CCX1-CCX0-CCX1
  hypB L.ax-CCX0-CCX2-CCX1-CCX2=CCX2-CCX1-CCX2-CCX0 = lemma-CCX0-CCX2-CCX1-CCX2=CCX2-CCX1-CCX2-CCX0
  hypB L.ax-CX01-CX01=ε = Order.general-rewrite 100 auto
  hypB L.ax-CCX0-CX10=CX10-CCX0 = lemma-CCX0-CX10=CX10-CCX0
  hypB L.ax-CCX0-CX01=CX01-CCX1-CCX0-CCX1 = lemma-CCX0-CX01=CX01-CCX1-CCX0-CCX1
  hypB L.ax-CCX2-CX01=CX01-CX02-CCX2 = lemma-CCX2-CX01=CX01-CX02-CCX2
  hypB L.ax-CX01-CX02=CX02-CX01 = lemma-CX01-CX02=CX02-CX01
  hypB L.ax-CX01-CX21=CX21-CX01 = Order.general-rewrite 100 auto
  hypB L.ax-CX10-CX02=CX02-CX12-CX10 = lemma-CX10-CX02=CX02-CX12-CX10
  hypB L.ax-CX10-CX21=CX21-CX20-CX10 = lemma-CX10-CX21=CX21-CX20-CX10
  hypB L.ax-X1-X0=X0-X1 = Monoidal.general-rewrite 100 auto
  hypB L.ax-X0-CX12=CX12-X0 = Monoidal.general-rewrite 100 auto
  hypB L.ax-X0-CX10=CX10-X0 = Order.general-rewrite 100 auto
  hypB L.ax-X0-CX01=CX01-X0-X1 = lemma-X0-CX01=CX01-X0-X1
  hypB L.ax-X0-CCX1=CCX1-CX21-X0 = lemma-X0-CCX1=CCX1-CX21-X0
  hypB L.ax-X0-CCX0=CCX0-X0 = Order.general-rewrite 100 auto
  hypB L.ax-X0-X0=ε = Order.general-rewrite 100 auto
  hypB L.ax-S0-S0-S0-S0=ε = Order.general-rewrite 100 auto
  hypB L.ax-CS01-CS01-CS01-CS01=ε = Order.general-rewrite 100 auto
  hypB L.ax-CCZ-CCZ=ε = lemma-CCZ-CCZ=ε
  hypB L.ax-iI-iI-iI-iI=ε = Monoidal.general-rewrite 100 auto
  hypB L.ax-K0-K0=iI-iI-iI = Order.general-rewrite 100 auto
  hypB L.ax-iI-CCX0=CCX0-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-iI-CX01=CX01-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-iI-X0=X0-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-iI-S0=S0-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-iI-CS01=CS01-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-iI-CCZ=CCZ-iI = Monoidal.general-rewrite 100 auto
  
  hypB L.ax-Swap01-Swap01=ε = Order.general-rewrite 100 auto
  hypB L.ax-Swap12-Swap12=ε = Order.general-rewrite 100 auto
  hypB L.ax-Swap01=CX01-CX10-CX01 = Order.general-rewrite 100 auto
  hypB L.ax-Swap12=CX12-CX21-CX12 = Monoidal.general-rewrite 100 auto
  hypB L.ax-Swap12-Swap01-Swap12=Swap01-Swap12-Swap01 = lemma-Swap12-Swap01-Swap12=Swap01-Swap12-Swap01
  hypB L.ax-Swap01-X0=X1-Swap01 = lemma-Swap01-X0=X1-Swap01
  hypB L.ax-Swap01-X1=X0-Swap01 = MvSwap01.general-rewrite 100 auto
  hypB L.ax-Swap01-X2=X2-Swap01 = Order.general-rewrite 100 auto
  hypB L.ax-Swap01-CX01=CX10-Swap01 = lemma-Swap01-CX01=CX10-Swap01
  hypB L.ax-Swap01-CX10=CX01-Swap01 = lemma-Swap01-CX10=CX01-Swap01
  hypB L.ax-Swap01-CX12=CX02-Swap01 = lemma-Swap01-CX12=CX02-Swap01
  hypB L.ax-Swap01-CX21=CX20-Swap01 = lemma-Swap01-CX21=CX20-Swap01
  hypB L.ax-Swap01-CX02=CX12-Swap01 = lemma-Swap01-CX02=CX12-Swap01
  hypB L.ax-Swap01-CX20=CX21-Swap01 = lemma-Swap01-CX20=CX21-Swap01
  hypB L.ax-Swap01-CCX2=CCX2-Swap01 = lemma-Swap01-CCX2=CCX2-Swap01
  hypB L.ax-Swap01-CCX0=CCX1-Swap01 = lemma-Swap01-CCX0=CCX1-Swap01
  hypB L.ax-Swap01-CCX1=CCX0-Swap01 = lemma-Swap01-CCX1=CCX0-Swap01
  hypB L.ax-Swap01-S0=S1-Swap01 = lemma-Swap01-S0=S1-Swap01
  hypB L.ax-Swap01-S1=S0-Swap01 = lemma-Swap01-S1=S0-Swap01
  hypB L.ax-Swap01-S2=S2-Swap01 = Order.general-rewrite 100 auto
  hypB L.ax-Swap01-CS01=CS01-Swap01 = lemma-Swap01-CS01=CS01-Swap01
  hypB L.ax-Swap01-CS02=CS12-Swap01 = lemma-Swap01-CS02=CS12-Swap01
  hypB L.ax-Swap01-CS12=CS02-Swap01 = lemma-Swap01-CS12=CS02-Swap01
  hypB L.ax-Swap01-CCZ=CCZ-Swap01 = lemma-Swap01-CCZ=CCZ-Swap01 
  hypB L.ax-iI-Swap01=Swap01-iI = Monoidal.general-rewrite 100 auto
  hypB L.ax-Swap12-X0=X0-Swap12 = Monoidal.general-rewrite 100 auto
  hypB L.ax-Swap12-X1=X2-Swap12 = MvSwap12.general-rewrite 100 auto
  hypB L.ax-Swap12-X2=X1-Swap12 = MvSwap12.general-rewrite 100 auto
  hypB L.ax-Swap12-CX01=CX02-Swap12 = lemma-Swap12-CX01=CX02-Swap12
  hypB L.ax-Swap12-CX10=CX20-Swap12 = lemma-Swap12-CX10=CX20-Swap12
  hypB L.ax-Swap12-CX12=CX21-Swap12 = lemma-Swap12-CX12=CX21-Swap12
  hypB L.ax-Swap12-CX21=CX12-Swap12 = lemma-Swap12-CX21=CX12-Swap12
  hypB L.ax-Swap12-CX02=CX01-Swap12 = lemma-Swap12-CX02=CX01-Swap12
  hypB L.ax-Swap12-CX20=CX10-Swap12 = Order.general-rewrite 100 auto
  hypB L.ax-Swap12-CCX2=CCX1-Swap12 = lemma-Swap12-CCX2=CCX1-Swap12
  hypB L.ax-Swap12-CCX1=CCX2-Swap12 = lemma-Swap12-CCX1=CCX2-Swap12
  hypB L.ax-Swap12-CCX0=CCX0-Swap12 = lemma-Swap12-CCX0=CCX0-Swap12
  hypB L.ax-Swap12-S0=S0-Swap12 = Monoidal.general-rewrite 100 auto
  hypB L.ax-Swap12-S1=S2-Swap12 = lemma-Swap12-S1=S2-Swap12
  hypB L.ax-Swap12-S2=S1-Swap12 = lemma-Swap12-S2=S1-Swap12
  hypB L.ax-Swap12-CS01=CS02-Swap12 = Order.general-rewrite 100 auto
  hypB L.ax-Swap12-CS02=CS01-Swap12 = Order.general-rewrite 100 auto
  hypB L.ax-Swap12-CS12=CS12-Swap12 = lemma-Swap12-CS12=CS12-Swap12
  hypB L.ax-Swap12-CCZ=CCZ-Swap12 = lemma-Swap12-CCZ=CCZ-Swap12
  hypB L.ax-iI-Swap12=Swap12-iI = Monoidal.general-rewrite 100 auto

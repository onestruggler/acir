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

import Examples.Groups.Clifford+CS-3qubit.Step5.Rel as L

open import Examples.Groups.Clifford+CS-3qubit.Step6.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step6.Order
open import Examples.Groups.Clifford+CS-3qubit.Step6.Comm
open import Examples.Groups.Clifford+CS-3qubit.Step6.S8
open import Examples.Groups.Clifford+CS-3qubit.Step6.S8D
open import Examples.Groups.Clifford+CS-3qubit.Step6.KD
open import Examples.Groups.Clifford+CS-3qubit.Step6.PLemmas
open import Examples.Groups.Clifford+CS-3qubit.Step6.Lemmas
open import Examples.Groups.Clifford+CS-3qubit.Step6.Basis-Change hiding (lemma-Swap01-Swap01=ε ; lemma-Swap12-Swap12=ε)

module Examples.Groups.Clifford+CS-3qubit.Step6.Main where

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
  hypA CCX1-gen = refl
  hypA CCX2-gen = refl
  hypA CX01-gen = refl
  hypA CX10-gen = refl
  hypA CX12-gen = refl
  hypA CX21-gen = refl
  hypA CX02-gen = refl
  hypA CX20-gen = refl
  hypA X0-gen = refl
  hypA X1-gen = refl
  hypA X2-gen = refl
  hypA Swap01-gen = refl
  hypA Swap12-gen = refl
  hypA S0-gen = refl
  hypA S1-gen = refl
  hypA S2-gen = refl
  hypA CS01-gen = refl
  hypA CS12-gen = refl
  hypA CS02-gen = refl
  hypA CCZ-gen = refl
  hypA iI-gen = refl
  hypA CCK'-gen = axiom ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI
  hypA CK10-gen = axiom ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI
  hypA CK20-gen = axiom ax-CK20=CS02-K0-CS02-K0-CS02-S2-S2-S2-iI
  hypA K0-gen = refl
  hypA K1-gen = axiom ax-K1=Swap01-K0-Swap01
  hypA K2-gen = axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12

  hypB : ∀ {u t : Word Gate} -> u === t ∈ L.Rel -> Rel ⊢ simple-of-gen-star u === simple-of-gen-star t

  hypB L.ax-K1=Swap01-K0-Swap01 = refl
  hypB L.ax-K2=Swap12-Swap01-K0-Swap01-Swap12 = refl
  hypB L.ax-Swap01-K0-Swap01-K0=K0-Swap01-K0-Swap01 = axiom ax-Swap01-K0-Swap01-K0=K0-Swap01-K0-Swap01
  hypB L.ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI = refl
  hypB L.ax-CK20=CS02-K0-CS02-K0-CS02-S2-S2-S2-iI = refl
  hypB L.ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI = refl
  hypB L.ax-Swap01=CX01-CX10-CX01 = axiom ax-Swap01=CX01-CX10-CX01
  hypB L.ax-Swap12=CX12-CX21-CX12 = axiom ax-Swap12=CX12-CX21-CX12
  
  hypB L.ax-CCX0-CCX0=ε = axiom ax-CCX0-CCX0=ε
  hypB L.ax-CCX1-CCX1=ε = lemma-CCX1-CCX1=ε
  hypB L.ax-CCX2-CCX2=ε = lemma-CCX2-CCX2=ε
  hypB L.ax-CX01-CX01=ε = axiom ax-CX01-CX01=ε
  hypB L.ax-CX10-CX10=ε = axiom ax-CX10-CX10=ε
  hypB L.ax-CX12-CX12=ε = axiom ax-CX12-CX12=ε
  hypB L.ax-CX21-CX21=ε = axiom ax-CX21-CX21=ε
  hypB L.ax-CX02-CX02=ε = lemma-CX02-CX02=ε
  hypB L.ax-CX20-CX20=ε = lemma-CX20-CX20=ε
  hypB L.ax-X0-X0=ε = axiom ax-X0-X0=ε
  hypB L.ax-X1-X1=ε = lemma-X1-X1=ε
  hypB L.ax-X2-X2=ε = lemma-X2-X2=ε
  hypB L.ax-Swap01-Swap01=ε = lemma-Swap01-Swap01=ε
  hypB L.ax-Swap12-Swap12=ε = lemma-Swap12-Swap12=ε
  hypB L.ax-S0-S0-S0-S0=ε = axiom ax-S0-S0-S0-S0=ε
  hypB L.ax-S1-S1-S1-S1=ε = lemma-S1-S1-S1-S1=ε
  hypB L.ax-S2-S2-S2-S2=ε = lemma-S2-S2-S2-S2=ε
  hypB L.ax-CS01-CS01-CS01-CS01=ε = axiom ax-CS01-CS01-CS01-CS01=ε
  hypB L.ax-CS12-CS12-CS12-CS12=ε = axiom ax-CS12-CS12-CS12-CS12=ε
  hypB L.ax-CS02-CS02-CS02-CS02=ε = lemma-CS02-CS02-CS02-CS02=ε
  hypB L.ax-CCZ-CCZ=ε = axiom ax-CCZ-CCZ=ε
  hypB L.ax-iI-iI-iI-iI=ε = axiom ax-iI-iI-iI-iI=ε
  
  hypB L.ax-K0-K0=iI-iI-iI = axiom ax-K0-K0=iI-iI-iI
  hypB L.ax-iI-CCX0=CCX0-iI = axiom ax-iI-CCX0=CCX0-iI
  hypB L.ax-iI-CCX1=CCX1-iI = lemma-iI-CCX1=CCX1-iI
  hypB L.ax-iI-CCX2=CCX2-iI = lemma-iI-CCX2=CCX2-iI
  hypB L.ax-iI-CX01=CX01-iI = axiom ax-iI-CX01=CX01-iI
  hypB L.ax-iI-CX10=CX10-iI = lemma-iI-CX10=CX10-iI
  hypB L.ax-iI-CX12=CX12-iI = lemma-iI-CX12=CX12-iI
  hypB L.ax-iI-CX21=CX21-iI = lemma-iI-CX21=CX21-iI
  hypB L.ax-iI-CX02=CX02-iI = lemma-iI-CX02=CX02-iI
  hypB L.ax-iI-CX20=CX20-iI = lemma-iI-CX20=CX20-iI
  hypB L.ax-iI-X0=X0-iI = axiom ax-iI-X0=X0-iI
  hypB L.ax-iI-X1=X1-iI = lemma-iI-X1=X1-iI
  hypB L.ax-iI-X2=X2-iI = lemma-iI-X2=X2-iI
  hypB L.ax-iI-Swap01=Swap01-iI = axiom ax-iI-Swap01=Swap01-iI
  hypB L.ax-iI-Swap12=Swap12-iI = axiom ax-iI-Swap12=Swap12-iI
  hypB L.ax-iI-S0=S0-iI = axiom ax-iI-S0=S0-iI
  hypB L.ax-iI-S1=S1-iI = lemma-iI-S1=S1-iI
  hypB L.ax-iI-S2=S2-iI = lemma-iI-S2=S2-iI
  hypB L.ax-iI-CS01=CS01-iI = axiom ax-iI-CS01=CS01-iI
  hypB L.ax-iI-CS12=CS12-iI = axiom ax-iI-CS12=CS12-iI
  hypB L.ax-iI-CS02=CS02-iI = lemma-iI-CS02=CS02-iI
  hypB L.ax-iI-CCZ=CCZ-iI = axiom ax-iI-CCZ=CCZ-iI
  
  hypB L.ax-X0-S0=S0-S0-S0-iI-X0 = axiom ax-X0-S0=S0-S0-S0-iI-X0
  hypB L.ax-X0-S1=S1-X0 = axiom ax-X0-S1=S1-X0
  hypB L.ax-X0-S2=S2-X0 = by-basis-change Swap12 Swap12 (axiom ax-X0-S1=S1-X0) 50 auto
  hypB L.ax-X0-CS01=S1-CS01-CS01-CS01-X0 = axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0
  hypB L.ax-X0-CS12=CS12-X0 = axiom ax-X0-CS12=CS12-X0
  hypB L.ax-X0-CS02=S2-CS02-CS02-CS02-X0 = by-basis-change Swap12 Swap12 (axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0) 50 auto
  hypB L.ax-X0-CCZ=CS12-CS12-CCZ-X0 = axiom ax-X0-CCZ=CS12-CS12-CCZ-X0
  hypB L.ax-X0-iI=iI-X0 = symm (axiom ax-iI-X0=X0-iI)
  hypB L.ax-CX10-S0=S0-S1-CS01-CS01-CX10 = axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10
  hypB L.ax-CX10-S1=S1-CX10 = axiom ax-CX10-S1=S1-CX10
  hypB L.ax-CX10-S2=S2-CX10 = axiom ax-CX10-S2=S2-CX10
  hypB L.ax-CX10-CS01=S1-CS01-CS01-CS01-CX10 = axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10
  hypB L.ax-CX10-CS12=CS12-CX10 = axiom ax-CX10-CS12=CS12-CX10
  hypB L.ax-CX10-CS02=CS02-CS12-CCZ-CX10 = axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10
  hypB L.ax-CX10-CCZ=CS12-CS12-CCZ-CX10 = axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10
  hypB L.ax-CX10-iI=iI-CX10 = symm (lemma-iI-CX10=CX10-iI)
  hypB L.ax-CX20-S0=S0-S2-CS02-CS02-CX20 = lemma-CX20-S0=S0-S2-CS02-CS02-CX20
  hypB L.ax-CX20-S1=S1-CX20 = lemma-CX20-S1=S1-CX20
  hypB L.ax-CX20-S2=S2-CX20 = lemma-CX20-S2=S2-CX20
  hypB L.ax-CX20-CS01=CS01-CS12-CCZ-CX20 = lemma-CX20-CS01=CS01-CS12-CCZ-CX20
  hypB L.ax-CX20-CS12=CS12-CX20 = lemma-CX20-CS12=CS12-CX20
  hypB L.ax-CX20-CS02=S2-CS02-CS02-CS02-CX20 = lemma-CX20-CS02=S2-CS02-CS02-CS02-CX20
  hypB L.ax-CX20-CCZ=CS12-CS12-CCZ-CX20 = lemma-CX20-CCZ=CS12-CS12-CCZ-CX20
  hypB L.ax-CX20-iI=iI-CX20 = symm (lemma-iI-CX20=CX20-iI)
  hypB L.ax-CCX0-S0=S0-CS12-CCZ-CCX0 = axiom ax-CCX0-S0=S0-CS12-CCZ-CCX0
  hypB L.ax-CCX0-S1=S1-CCX0 = axiom ax-CCX0-S1=S1-CCX0
  hypB L.ax-CCX0-S2=S2-CCX0 = lemma-CCX0-S2=S2-CCX0
  hypB L.ax-CCX0-CS01=CS01-CS12-CCZ-CCX0 = axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0
  hypB L.ax-CCX0-CS12=CS12-CCX0 = axiom ax-CCX0-CS12=CS12-CCX0
  hypB L.ax-CCX0-CS02=CS02-CS12-CCZ-CCX0 = lemma-CCX0-CS02=CS02-CS12-CCZ-CCX0
  hypB L.ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0 = axiom ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0
  hypB L.ax-CCX0-iI=iI-CCX0 = symm (axiom ax-iI-CCX0=CCX0-iI)
  hypB L.ax-CX10=K0-CS01-CS01-K0-iI = axiom ax-CX10=K0-CS01-CS01-K0-iI
  hypB L.ax-S1-S0=S0-S1 = axiom ax-S1-S0=S0-S1
  hypB L.ax-S2-S0=S0-S2 = lemma-S2-S0=S0-S2
  hypB L.ax-S2-S1=S1-S2 = lemma-S2-S1=S1-S2
  hypB L.ax-CS01-S0=S0-CS01 = axiom ax-CS01-S0=S0-CS01
  hypB L.ax-CS01-S1=S1-CS01 = axiom ax-CS01-S1=S1-CS01
  hypB L.ax-CS01-S2=S2-CS01 = axiom ax-CS01-S2=S2-CS01
  hypB L.ax-CS12-S0=S0-CS12 = lemma-CS12-S0=S0-CS12
  hypB L.ax-CS12-S1=S1-CS12 = lemma-CS12-S1=S1-CS12
  hypB L.ax-CS12-S2=S2-CS12 = lemma-CS12-S2=S2-CS12
  hypB L.ax-CS12-CS01=CS01-CS12 = axiom ax-CS12-CS01=CS01-CS12
  hypB L.ax-CS12-CS02=CS02-CS12 = lemma-CS12-CS02=CS02-CS12
  hypB L.ax-CS02-S0=S0-CS02 = lemma-CS02-S0=S0-CS02
  hypB L.ax-CS02-S1=S1-CS02 = lemma-CS02-S1=S1-CS02
  hypB L.ax-CS02-S2=S2-CS02 = lemma-CS02-S2=S2-CS02
  hypB L.ax-CS02-CS01=CS01-CS02 = axiom ax-CS02-CS01=CS01-CS02
  hypB L.ax-CCZ-S0=S0-CCZ = axiom ax-CCZ-S0=S0-CCZ
  hypB L.ax-CCZ-S1=S1-CCZ = lemma-CCZ-S1=S1-CCZ
  hypB L.ax-CCZ-S2=S2-CCZ = lemma-CCZ-S2=S2-CCZ
  hypB L.ax-CCZ-CS01=CS01-CCZ = axiom ax-CCZ-CS01=CS01-CCZ
  hypB L.ax-CCZ-CS12=CS12-CCZ = lemma-CCZ-CS12=CS12-CCZ
  hypB L.ax-CCZ-CS02=CS02-CCZ = lemma-CCZ-CS02=CS02-CCZ
  hypB L.ax-Swap01-S0=S1-Swap01 = axiom ax-Swap01-S0=S1-Swap01
  hypB L.ax-Swap01-S1=S0-Swap01 = axiom ax-Swap01-S1=S0-Swap01
  hypB L.ax-Swap01-S2=S2-Swap01 = axiom ax-Swap01-S2=S2-Swap01
  hypB L.ax-Swap01-CS01=CS01-Swap01 = axiom ax-Swap01-CS01=CS01-Swap01
  hypB L.ax-Swap01-CS02=CS12-Swap01 = axiom ax-Swap01-CS02=CS12-Swap01
  hypB L.ax-Swap01-CS12=CS02-Swap01 = axiom ax-Swap01-CS12=CS02-Swap01
  hypB L.ax-Swap01-CCZ=CCZ-Swap01 = axiom ax-Swap01-CCZ=CCZ-Swap01
  hypB L.ax-Swap01-iI=iI-Swap01 = symm (axiom ax-iI-Swap01=Swap01-iI)
  hypB L.ax-CX01-S0=S0-CX01 = lemma-CX01-S0=S0-CX01
  hypB L.ax-CX01-S1=S0-S1-CS01-CS01-CX01 = lemma-CX01-S1=S0-S1-CS01-CS01-CX01
  hypB L.ax-CX01-S2=S2-CX01 = lemma-CX01-S2=S2-CX01
  hypB L.ax-CX01-CS01=S0-CS01-CS01-CS01-CX01 = lemma-CX01-CS01=S0-CS01-CS01-CS01-CX01
  hypB L.ax-CX01-CS02=CS02-CX01 = lemma-CX01-CS02=CS02-CX01
  hypB L.ax-CX01-CS12=CS02-CS12-CCZ-CX01 = lemma-CX01-CS12=CS02-CS12-CCZ-CX01
  hypB L.ax-CX01-CCZ=CS02-CS02-CCZ-CX01 = lemma-CX01-CCZ=CS02-CS02-CCZ-CX01
  hypB L.ax-CX01-iI=iI-CX01 = symm (axiom ax-iI-CX01=CX01-iI)
  hypB L.ax-CX02-S0=S0-CX02 = lemma-CX02-S0=S0-CX02
  hypB L.ax-CX02-S1=S1-CX02 = lemma-CX02-S1=S1-CX02
  hypB L.ax-CX02-S2=S0-S2-CS02-CS02-CX02 = lemma-CX02-S2=S0-S2-CS02-CS02-CX02
  hypB L.ax-CX02-CS01=CS01-CX02 = lemma-CX02-CS01=CS01-CX02
  hypB L.ax-CX02-CS02=S0-CS02-CS02-CS02-CX02 = lemma-CX02-CS02=S0-CS02-CS02-CS02-CX02
  hypB L.ax-CX02-CS12=CS01-CS12-CCZ-CX02 = lemma-CX02-CS12=CS01-CS12-CCZ-CX02
  hypB L.ax-CX02-CCZ=CS01-CS01-CCZ-CX02 = lemma-CX02-CCZ=CS01-CS01-CCZ-CX02
  hypB L.ax-CX02-iI=iI-CX02 = symm (lemma-iI-CX02=CX02-iI)
  hypB L.ax-CCX1-S0=S0-CCX1 = lemma-CCX1-S0=S0-CCX1
  hypB L.ax-CCX1-S1=S1-CS02-CCZ-CCX1 = lemma-CCX1-S1=S1-CS02-CCZ-CCX1
  hypB L.ax-CCX1-S2=S2-CCX1 = lemma-CCX1-S2=S2-CCX1
  hypB L.ax-CCX1-CS01=CS01-CS02-CCZ-CCX1 = lemma-CCX1-CS01=CS01-CS02-CCZ-CCX1
  hypB L.ax-CCX1-CS02=CS02-CCX1 = lemma-CCX1-CS02=CS02-CCX1
  hypB L.ax-CCX1-CS12=CS02-CS12-CCZ-CCX1 = lemma-CCX1-CS12=CS02-CS12-CCZ-CCX1
  hypB L.ax-CCX1-CCZ=CS02-CS02-CCZ-CCX1 = lemma-CCX1-CCZ=CS02-CS02-CCZ-CCX1
  hypB L.ax-CCX1-iI=iI-CCX1 = symm (lemma-iI-CCX1=CCX1-iI)
  hypB L.ax-CCX2-S0=S0-CCX2 = lemma-CCX2-S0=S0-CCX2
  hypB L.ax-CCX2-S1=S1-CCX2 = lemma-CCX2-S1=S1-CCX2
  hypB L.ax-CCX2-S2=S2-CS01-CCZ-CCX2 = lemma-CCX2-S2=S2-CS01-CCZ-CCX2
  hypB L.ax-CCX2-CS01=CS01-CCX2 = lemma-CCX2-CS01=CS01-CCX2
  hypB L.ax-CCX2-CS02=CS01-CS02-CCZ-CCX2 = lemma-CCX2-CS02=CS01-CS02-CCZ-CCX2
  hypB L.ax-CCX2-CS12=CS01-CS12-CCZ-CCX2 = lemma-CCX2-CS12=CS01-CS12-CCZ-CCX2
  hypB L.ax-CCX2-CCZ=CS01-CS01-CCZ-CCX2 = lemma-CCX2-CCZ=CS01-CS01-CCZ-CCX2
  hypB L.ax-CCX2-iI=iI-CCX2 = symm (lemma-iI-CCX2=CCX2-iI)
  hypB L.ax-X1-S0=S0-X1 = lemma-X1-S0=S0-X1
  hypB L.ax-X1-S1=S1-S1-S1-iI-X1 = lemma-X1-S1=S1-S1-S1-iI-X1
  hypB L.ax-X1-S2=S2-X1 = lemma-X1-S2=S2-X1
  hypB L.ax-X1-CS01=S0-CS01-CS01-CS01-X1 = lemma-X1-CS01=S0-CS01-CS01-CS01-X1
  hypB L.ax-X1-CS02=CS02-X1 = lemma-X1-CS02=CS02-X1
  hypB L.ax-X1-CS12=S2-CS12-CS12-CS12-X1 = lemma-X1-CS12=S2-CS12-CS12-CS12-X1
  hypB L.ax-X1-CCZ=CS02-CS02-CCZ-X1 = lemma-X1-CCZ=CS02-CS02-CCZ-X1
  hypB L.ax-X1-iI=iI-X1 = symm (lemma-iI-X1=X1-iI)
  hypB L.ax-X2-S0=S0-X2 = lemma-X2-S0=S0-X2
  hypB L.ax-X2-S1=S1-X2 = lemma-X2-S1=S1-X2
  hypB L.ax-X2-S2=S2-S2-S2-iI-X2 = lemma-X2-S2=S2-S2-S2-iI-X2
  hypB L.ax-X2-CS01=CS01-X2 = lemma-X2-CS01=CS01-X2
  hypB L.ax-X2-CS02=S0-CS02-CS02-CS02-X2 = lemma-X2-CS02=S0-CS02-CS02-CS02-X2
  hypB L.ax-X2-CS12=S1-CS12-CS12-CS12-X2 = lemma-X2-CS12=S1-CS12-CS12-CS12-X2
  hypB L.ax-X2-CCZ=CS01-CS01-CCZ-X2 = lemma-X2-CCZ=CS01-CS01-CCZ-X2
  hypB L.ax-X2-iI=iI-X2 = symm (lemma-iI-X2=X2-iI)
  hypB L.ax-CX12-S0=S0-CX12 = lemma-CX12-S0=S0-CX12
  hypB L.ax-CX12-S1=S1-CX12 = lemma-CX12-S1=S1-CX12
  hypB L.ax-CX12-S2=S1-S2-CS12-CS12-CX12 = lemma-CX12-S2=S1-S2-CS12-CS12-CX12
  hypB L.ax-CX12-CS01=CS01-CX12 = lemma-CX12-CS01=CS01-CX12
  hypB L.ax-CX12-CS02=CS01-CS02-CCZ-CX12 = lemma-CX12-CS02=CS01-CS02-CCZ-CX12
  hypB L.ax-CX12-CS12=S1-CS12-CS12-CS12-CX12 = lemma-CX12-CS12=S1-CS12-CS12-CS12-CX12
  hypB L.ax-CX12-CCZ=CS01-CS01-CCZ-CX12 = lemma-CX12-CCZ=CS01-CS01-CCZ-CX12
  hypB L.ax-CX12-iI=iI-CX12 = symm (lemma-iI-CX12=CX12-iI)
  hypB L.ax-CX21-S0=S0-CX21 = lemma-CX21-S0=S0-CX21
  hypB L.ax-CX21-S1=S1-S2-CS12-CS12-CX21 = lemma-CX21-S1=S1-S2-CS12-CS12-CX21
  hypB L.ax-CX21-S2=S2-CX21 = lemma-CX21-S2=S2-CX21
  hypB L.ax-CX21-CS01=CS01-CS02-CCZ-CX21 = lemma-CX21-CS01=CS01-CS02-CCZ-CX21
  hypB L.ax-CX21-CS02=CS02-CX21 = lemma-CX21-CS02=CS02-CX21
  hypB L.ax-CX21-CS12=S2-CS12-CS12-CS12-CX21 = lemma-CX21-CS12=S2-CS12-CS12-CS12-CX21
  hypB L.ax-CX21-CCZ=CS02-CS02-CCZ-CX21 = lemma-CX21-CCZ=CS02-CS02-CCZ-CX21
  hypB L.ax-CX21-iI=iI-CX21 = symm (lemma-iI-CX21=CX21-iI)
  hypB L.ax-Swap12-S0=S0-Swap12 = axiom ax-Swap12-S0=S0-Swap12
  hypB L.ax-Swap12-S1=S2-Swap12 = axiom ax-Swap12-S1=S2-Swap12
  hypB L.ax-Swap12-S2=S1-Swap12 = axiom ax-Swap12-S2=S1-Swap12
  hypB L.ax-Swap12-CS01=CS02-Swap12 = axiom ax-Swap12-CS01=CS02-Swap12
  hypB L.ax-Swap12-CS02=CS01-Swap12 = axiom ax-Swap12-CS02=CS01-Swap12
  hypB L.ax-Swap12-CS12=CS12-Swap12 = axiom ax-Swap12-CS12=CS12-Swap12
  hypB L.ax-Swap12-CCZ=CCZ-Swap12 = axiom ax-Swap12-CCZ=CCZ-Swap12
  hypB L.ax-Swap12-iI=iI-Swap12 = symm (axiom ax-iI-Swap12=Swap12-iI)
  
  hypB L.ax-CCX1-CCX0-CCX1=CCX0-CCX1-CCX0 = axiom ax-CCX1-CCX0-CCX1=CCX0-CCX1-CCX0
  hypB L.ax-CCX0-CCX0-CCX1=CCX1 = Order.general-rewrite 10 auto
  hypB L.ax-CCX2-CCX1-CCX2=CCX1-CCX2-CCX1 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-CCX1-CCX0-CCX1=CCX0-CCX1-CCX0) 50 auto
  hypB L.ax-CCX2-CCX0-CCX2=CCX0-CCX2-CCX0 = by-basis-change Swap12 Swap12 (axiom ax-CCX1-CCX0-CCX1=CCX0-CCX1-CCX0) 50 auto
  hypB L.ax-CCX1-CCX1-CCX2=CCX2 = Order.general-rewrite 10 auto
  hypB L.ax-CCX1-CCX0-CCX2=CCX0-CCX2-CCX0-CCX1-CCX0 = axiom ax-CCX1-CCX0-CCX2=CCX0-CCX2-CCX0-CCX1-CCX0
  hypB L.ax-CCX0-CCX1-CCX2=CCX1-CCX2-CCX0-CCX1-CCX0 = lemma-CCX0-CCX1-CCX2=CCX1-CCX2-CCX0-CCX1-CCX0
  hypB L.ax-CCX0-CCX0-CCX2=CCX2 = Order.general-rewrite 10 auto
  hypB L.ax-CX01-CX01-CCX2-CX01=CCX2-CX01 = Order.general-rewrite 10 auto
  hypB L.ax-CX01-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX1-CCX2-CCX1-CCX0 = axiom ax-CX01-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX1-CCX2-CCX1-CCX0
  hypB L.ax-CCX2-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX2 = lemma-CCX2-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX2
  hypB L.ax-CCX2-CCX2-CX01=CX01 = Order.general-rewrite 10 auto
  hypB L.ax-CCX2-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0-CCX1-CCX0 = axiom ax-CCX2-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0-CCX1-CCX0
  hypB L.ax-CCX1-CX01=CX01-CCX1 = B01.by-basis-change Swap01 Swap01 (axiom ax-CCX0-CX10=CX10-CCX0) 50 auto
  hypB L.ax-CCX1-CX01-CCX2-CX01=CCX2-CX01-CCX1-CCX2-CCX1 = axiom ax-CCX1-CX01-CCX2-CX01=CCX2-CX01-CCX1-CCX2-CCX1
  hypB L.ax-CCX1-CCX2-CX01=CX01-CCX2-CX01-CCX1-CCX2-CCX1 = axiom ax-CCX1-CCX2-CX01=CX01-CCX2-CX01-CCX1-CCX2-CCX1
  hypB L.ax-CCX1-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0 = axiom ax-CCX1-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0
  hypB L.ax-CCX0-CX01=CX01-CCX0-CCX1-CCX0 = axiom ax-CCX0-CX01=CX01-CCX0-CCX1-CCX0
  hypB L.ax-CCX0-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX0 = axiom ax-CCX0-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX0
  hypB L.ax-CCX0-CCX0-CCX2-CX01=CCX2-CX01 = Order.general-rewrite 10 auto
  hypB L.ax-CX10-CX10-CCX2-CX10=CCX2-CX10 = Order.general-rewrite 10 auto
  hypB L.ax-CX10-CX01-CX10=CX01-CX10-CX01 = axiom ax-CX10-CX01-CX10=CX01-CX10-CX01
  hypB L.ax-CX10-CX01-CCX2-CX10=CX01-CCX2-CX10-CX01 = axiom ax-CX10-CX01-CCX2-CX10=CX01-CCX2-CX10-CX01
  hypB L.ax-CX01-CX10-CCX2-CX10=CX10-CCX2-CX10-CX01 = axiom ax-CX01-CX10-CCX2-CX10=CX10-CCX2-CX10-CX01
  hypB L.ax-CX01-CX01-CX10=CX10 = axiom ax-CX01-CX01-CX10=CX10
  hypB L.ax-CX01-CX01-CCX2-CX10=CCX2-CX10 = Order.general-rewrite 10 auto
  hypB L.ax-CCX2-CX10-CCX2-CX10=CX10-CCX2-CX10-CCX2 = B01.by-basis-change Swap01 Swap01 (lemma-CCX2-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX2) 50 auto
  hypB L.ax-CCX2-CX01-CX10=CX01-CX10-CX01-CCX2-CX01 = lemma-CCX2-CX01-CX10=CX01-CX10-CX01-CCX2-CX01
  hypB L.ax-CCX2-CX01-CCX2-CX10=CX01-CCX2-CX10-CX01-CCX2-CX01 = axiom ax-CCX2-CX01-CCX2-CX10=CX01-CCX2-CX10-CX01-CCX2-CX01
  hypB L.ax-CCX2-CCX2-CX10=CX10 = Order.general-rewrite 10 auto
  hypB L.ax-CCX1-CX10=CX10-CCX0-CCX1-CCX0 = axiom ax-CCX1-CX10=CX10-CCX0-CCX1-CCX0
  hypB L.ax-CCX1-CX10-CCX2-CX10=CX10-CCX2-CX10-CCX1 = axiom ax-CCX1-CX10-CCX2-CX10=CX10-CCX2-CX10-CCX1
  hypB L.ax-CCX1-CX01-CX10=CX01-CX10-CCX0-CCX1-CCX0 = axiom ax-CCX1-CX01-CX10=CX01-CX10-CCX0-CCX1-CCX0
  hypB L.ax-CCX1-CX01-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0 = axiom ax-CCX1-CX01-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0
  hypB L.ax-CCX1-CCX2-CX10=CX01-CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0 = axiom ax-CCX1-CCX2-CX10=CX01-CCX2-CX10-CCX0-CCX2-CX01-CCX1-CCX2-CCX0
  hypB L.ax-CCX0-CX10=CX10-CCX0 = axiom ax-CCX0-CX10=CX10-CCX0
  hypB L.ax-CCX0-CX10-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CCX0 = axiom ax-CCX0-CX10-CCX2-CX10=CCX2-CX10-CCX0-CCX2-CCX0
  hypB L.ax-CCX0-CX01-CX10=CX01-CX10-CCX1 = lemma-CCX0-CX01-CX10=CX01-CX10-CCX1
  hypB L.ax-CCX0-CX01-CCX2-CX10=CX01-CCX2-CX10-CCX1 = axiom ax-CCX0-CX01-CCX2-CX10=CX01-CCX2-CX10-CCX1
  hypB L.ax-CCX0-CCX2-CX10=CX10-CCX2-CX10-CCX0-CCX2-CCX0 = axiom ax-CCX0-CCX2-CX10=CX10-CCX2-CX10-CCX0-CCX2-CCX0
  hypB L.ax-CX02=CX01-CCX2-CX01-CCX2 = axiom ax-CX02=CX01-CCX2-CX01-CCX2
  hypB L.ax-CX02-CX02-CX20=CX20 = Order.general-rewrite 10 auto
  hypB L.ax-CX02-CX12-CX21=CX12-CX21-CCX2-CX01-CCX2 = axiom ax-CX02-CX12-CX21=CX12-CX21-CCX2-CX01-CCX2
  hypB L.ax-CX02-CX21=CX21-CCX2-CX01-CCX2 = axiom ax-CX02-CX21=CX21-CCX2-CX01-CCX2
  hypB L.ax-CX02-CX21-CX20=CX01-CX02-CX20-CX01 = axiom ax-CX02-CX21-CX20=CX01-CX02-CX20-CX01
  hypB L.ax-CX02-CX01-CX02-CX20=CX21-CX20-CX01 = axiom ax-CX02-CX01-CX02-CX20=CX21-CX20-CX01
  hypB L.ax-CX20-CX02-CX20=CX02-CX20-CX01-CCX2-CX01-CCX2 = axiom ax-CX20-CX02-CX20=CX02-CX20-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX20-CX12-CX21=CX12-CX21-CX10 = axiom ax-CX20-CX12-CX21=CX12-CX21-CX10
  hypB L.ax-CX20-CX21=CX21-CX20 = axiom ax-CX20-CX21=CX21-CX20
  hypB L.ax-CX20-CX21-CX20=CX21 = lemma-CX20-CX21-CX20=CX21
  hypB L.ax-CX20-CX01-CX02-CX20=CX01-CX02-CX20-CCX2-CX01-CCX2 = axiom ax-CX20-CX01-CX02-CX20=CX01-CX02-CX20-CCX2-CX01-CCX2
  hypB L.ax-CX12=CX10-CCX2-CX10-CCX2 = B01.by-basis-change Swap01 Swap01 (axiom ax-CX02=CX01-CCX2-CX01-CCX2) 50 auto
  hypB L.ax-CX12-CX02-CX20=CX02-CX20-CCX2-CX10-CCX2 = axiom ax-CX12-CX02-CX20=CX02-CX20-CCX2-CX10-CCX2
  hypB L.ax-CX12-CX20=CX20-CCX2-CX10-CCX2 = axiom ax-CX12-CX20=CX20-CCX2-CX10-CCX2
  hypB L.ax-CX12-CX12-CX21=CX21 = Order.general-rewrite 10 auto
  hypB L.ax-CX12-CX21-CX20=CX01-CX02-CX20-CCX2-CX10-CCX2-CX01 = axiom ax-CX12-CX21-CX20=CX01-CX02-CX20-CCX2-CX10-CCX2-CX01
  hypB L.ax-CX12-CX01-CX02-CX20=CX21-CX20-CX01-CCX2-CX10-CCX2 = axiom ax-CX12-CX01-CX02-CX20=CX21-CX20-CX01-CCX2-CX10-CCX2
  hypB L.ax-CX21-CX02-CX20=CX02-CX20-CX01 = axiom ax-CX21-CX02-CX20=CX02-CX20-CX01
  hypB L.ax-CX21-CX12-CX21=CX12-CX21-CX10-CCX2-CX10-CCX2 = lemma-CX21-CX12-CX21=CX12-CX21-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX21-CX21-CX20=CX20 = Order.general-rewrite 10 auto
  hypB L.ax-CX21-CX01-CX02-CX20=CX01-CX02-CX20-CX01 = axiom ax-CX21-CX01-CX02-CX20=CX01-CX02-CX20-CX01
  hypB L.ax-CX10-CX02-CX20=CX02-CX20-CX10-CCX2-CX10-CCX2 = axiom ax-CX10-CX02-CX20=CX02-CX20-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX10-CX20=CX20-CX10 = axiom ax-CX10-CX20=CX20-CX10
  hypB L.ax-CX10-CX12-CX21=CX01-CX02-CX20-CX01-CX10-CCX2-CX01-CCX2 = axiom ax-CX10-CX12-CX21=CX01-CX02-CX20-CX01-CX10-CCX2-CX01-CCX2
  hypB L.ax-CX10-CX21=CX21-CX20-CX10 = axiom ax-CX10-CX21=CX21-CX20-CX10
  hypB L.ax-CX10-CX21-CX20=CX21-CX10 = lemma-CX10-CX21-CX20=CX21-CX10
  hypB L.ax-CX10-CX01-CX02-CX20=CX12-CX21-CX01-CCX2-CX10-CX01-CCX2 = axiom ax-CX10-CX01-CX02-CX20=CX12-CX21-CX01-CCX2-CX10-CX01-CCX2
  hypB L.ax-CX01-CX20=CX21-CX20-CX01 = lemma-CX01-CX20=CX21-CX20-CX01
  hypB L.ax-CX01-CX12-CX21=CX12-CX21-CX01-CCX2-CX01-CCX2 = axiom ax-CX01-CX12-CX21=CX12-CX21-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX01-CX21=CX21-CX01 = axiom ax-CX01-CX21=CX21-CX01
  hypB L.ax-CX01-CX21-CX20=CX20-CX01 = lemma-CX01-CX21-CX20=CX20-CX01
  hypB L.ax-CX01-CX01-CX02-CX20=CX02-CX20 = Order.general-rewrite 10 auto
  hypB L.ax-CCX2-CX02-CX20=CX02-CX20-CCX0-CCX2-CCX0 = axiom ax-CCX2-CX02-CX20=CX02-CX20-CCX0-CCX2-CCX0
  hypB L.ax-CCX2-CX20=CX20-CCX0-CCX2-CCX0 = axiom ax-CCX2-CX20=CX20-CCX0-CCX2-CCX0
  hypB L.ax-CCX2-CX12-CX21=CX12-CX21-CCX1-CCX2-CCX1 = axiom ax-CCX2-CX12-CX21=CX12-CX21-CCX1-CCX2-CCX1
  hypB L.ax-CCX2-CX21=CX21-CCX1-CCX2-CCX1 = axiom ax-CCX2-CX21=CX21-CCX1-CCX2-CCX1
  hypB L.ax-CCX2-CX21-CX20=CX01-CX02-CX20-CCX0-CCX2-CX01-CCX0-CCX1-CCX0 = axiom ax-CCX2-CX21-CX20=CX01-CX02-CX20-CCX0-CCX2-CX01-CCX0-CCX1-CCX0
  hypB L.ax-CCX2-CX01-CX02-CX20=CX21-CX20-CX01-CCX0-CCX2-CCX0 = axiom ax-CCX2-CX01-CX02-CX20=CX21-CX20-CX01-CCX0-CCX2-CCX0
  hypB L.ax-CCX1-CX02-CX20=CX02-CX20-CX01-CCX1 = axiom ax-CCX1-CX02-CX20=CX02-CX20-CX01-CCX1
  hypB L.ax-CCX1-CX20=CX21-CX20-CCX1 = axiom ax-CCX1-CX20=CX21-CX20-CCX1
  hypB L.ax-CCX1-CX12-CX21=CX12-CX21-CCX2 = lemma-CCX1-CX12-CX21=CX12-CX21-CCX2
  hypB L.ax-CCX1-CX21=CX21-CCX1 = B01.by-basis-change Swap01 Swap01 (axiom ax-CCX0-CX20=CX20-CCX0) 50 auto
  hypB L.ax-CCX1-CX21-CX20=CX20-CCX1 = axiom ax-CCX1-CX21-CX20=CX20-CCX1
  hypB L.ax-CCX1-CX01-CX02-CX20=CX01-CX02-CX20-CX01-CCX1 = axiom ax-CCX1-CX01-CX02-CX20=CX01-CX02-CX20-CX01-CCX1
  hypB L.ax-CCX0-CX02-CX20=CX02-CX20-CCX2 = B01.by-basis-change Swap01 Swap01 (lemma-CCX1-CX12-CX21=CX12-CX21-CCX2) 50 auto
  hypB L.ax-CCX0-CX20=CX20-CCX0 = axiom ax-CCX0-CX20=CX20-CCX0
  hypB L.ax-CCX0-CX12-CX21=CX12-CX21-CX10-CCX0 = axiom ax-CCX0-CX12-CX21=CX12-CX21-CX10-CCX0
  hypB L.ax-CCX0-CX21=CX21-CX20-CCX0 = axiom ax-CCX0-CX21=CX21-CX20-CCX0
  hypB L.ax-CCX0-CX21-CX20=CX21-CCX0 = axiom ax-CCX0-CX21-CX20=CX21-CCX0
  hypB L.ax-CCX0-CX01-CX02-CX20=CX01-CX02-CX20-CCX2-CX01-CCX1-CCX2 = axiom ax-CCX0-CX01-CX02-CX20=CX01-CX02-CX20-CCX2-CX01-CCX1-CCX2

  hypB L.ax-X0-X0-X1=X1 = lemma-X0-X0-X1=X1
  hypB L.ax-X0-X0-X1-X2=X1-X2 = lemma-X0-X0-X1-X2=X1-X2
  hypB L.ax-X0-X0-X2=X2 = lemma-X0-X0-X2=X2
  hypB L.ax-X1-X0=X0-X1 = lemma-X1-X0=X0-X1
  hypB L.ax-X1-X0-X1=X0 = lemma-X1-X0-X1=X0
  hypB L.ax-X1-X0-X1-X2=X0-X2 = lemma-X1-X0-X1-X2=X0-X2
  hypB L.ax-X1-X0-X2=X0-X1-X2 = lemma-X1-X0-X2=X0-X1-X2
  hypB L.ax-X1-X1-X2=X2 = lemma-X1-X1-X2=X2
  hypB L.ax-X2-X0=X0-X2 = lemma-X2-X0=X0-X2
  hypB L.ax-X2-X0-X1=X0-X1-X2 = lemma-X2-X0-X1=X0-X1-X2
  hypB L.ax-X2-X0-X1-X2=X0-X1 = lemma-X2-X0-X1-X2=X0-X1
  hypB L.ax-X2-X0-X2=X0 = lemma-X2-X0-X2=X0
  hypB L.ax-X2-X1=X1-X2 = lemma-X2-X1=X1-X2
  hypB L.ax-X2-X1-X2=X1 = lemma-X2-X1-X2=X1
  hypB L.ax-CX01-X0=X0-X1-CX01 = lemma-CX01-X0=X0-X1-CX01
  hypB L.ax-CX01-X0-X1=X0-CX01 = lemma-CX01-X0-X1=X0-CX01
  hypB L.ax-CX01-X0-X1-X2=X0-X2-CX01 = lemma-CX01-X0-X1-X2=X0-X2-CX01
  hypB L.ax-CX01-X0-X2=X0-X1-X2-CX01 = lemma-CX01-X0-X2=X0-X1-X2-CX01
  hypB L.ax-CX01-X1=X1-CX01 = lemma-CX01-X1=X1-CX01
  hypB L.ax-CX01-X1-X2=X1-X2-CX01 = lemma-CX01-X1-X2=X1-X2-CX01
  hypB L.ax-CX01-X2=X2-CX01 = lemma-CX01-X2=X2-CX01
  hypB L.ax-CX02-X0=X0-X2-CX01-CCX2-CX01-CCX2 = lemma-CX02-X0=X0-X2-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX02-X0-X1=X0-X1-X2-CX01-CCX2-CX01-CCX2 = lemma-CX02-X0-X1=X0-X1-X2-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX02-X0-X1-X2=X0-X1-CX01-CCX2-CX01-CCX2 = lemma-CX02-X0-X1-X2=X0-X1-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX02-X0-X2=X0-CX01-CCX2-CX01-CCX2 = lemma-CX02-X0-X2=X0-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX02-X1=X1-CX01-CCX2-CX01-CCX2 = lemma-CX02-X1=X1-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX02-X1-X2=X1-X2-CX01-CCX2-CX01-CCX2 = lemma-CX02-X1-X2=X1-X2-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX02-X2=X2-CX01-CCX2-CX01-CCX2 = lemma-CX02-X2=X2-CX01-CCX2-CX01-CCX2
  hypB L.ax-CX10-X0=X0-CX10 = lemma-CX10-X0=X0-CX10
  hypB L.ax-CX10-X0-X1=X1-CX10 = lemma-CX10-X0-X1=X1-CX10
  hypB L.ax-CX10-X0-X1-X2=X1-X2-CX10 = lemma-CX10-X0-X1-X2=X1-X2-CX10
  hypB L.ax-CX10-X0-X2=X0-X2-CX10 = lemma-CX10-X0-X2=X0-X2-CX10
  hypB L.ax-CX10-X1=X0-X1-CX10 = lemma-CX10-X1=X0-X1-CX10
  hypB L.ax-CX10-X1-X2=X0-X1-X2-CX10 = lemma-CX10-X1-X2=X0-X1-X2-CX10
  hypB L.ax-CX10-X2=X2-CX10 = lemma-CX10-X2=X2-CX10
  hypB L.ax-CX12-X0=X0-CX10-CCX2-CX10-CCX2 = lemma-CX12-X0=X0-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX12-X0-X1=X0-X1-X2-CX10-CCX2-CX10-CCX2 = lemma-CX12-X0-X1=X0-X1-X2-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX12-X0-X1-X2=X0-X1-CX10-CCX2-CX10-CCX2 = lemma-CX12-X0-X1-X2=X0-X1-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX12-X0-X2=X0-X2-CX10-CCX2-CX10-CCX2 = lemma-CX12-X0-X2=X0-X2-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX12-X1=X1-X2-CX10-CCX2-CX10-CCX2 = lemma-CX12-X1=X1-X2-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX12-X1-X2=X1-CX10-CCX2-CX10-CCX2 = lemma-CX12-X1-X2=X1-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX12-X2=X2-CX10-CCX2-CX10-CCX2 = lemma-CX12-X2=X2-CX10-CCX2-CX10-CCX2
  hypB L.ax-CX20-X0=X0-CX20 = lemma-CX20-X0=X0-CX20
  hypB L.ax-CX20-X0-X1=X0-X1-CX20 = lemma-CX20-X0-X1=X0-X1-CX20
  hypB L.ax-CX20-X0-X1-X2=X1-X2-CX20 = lemma-CX20-X0-X1-X2=X1-X2-CX20
  hypB L.ax-CX20-X0-X2=X2-CX20 = lemma-CX20-X0-X2=X2-CX20
  hypB L.ax-CX20-X1=X1-CX20 = lemma-CX20-X1=X1-CX20
  hypB L.ax-CX20-X1-X2=X0-X1-X2-CX20 = lemma-CX20-X1-X2=X0-X1-X2-CX20
  hypB L.ax-CX20-X2=X0-X2-CX20 = lemma-CX20-X2=X0-X2-CX20
  hypB L.ax-CX21-X0=X0-CX21 = lemma-CX21-X0=X0-CX21
  hypB L.ax-CX21-X0-X1=X0-X1-CX21 = lemma-CX21-X0-X1=X0-X1-CX21
  hypB L.ax-CX21-X0-X1-X2=X0-X2-CX21 = lemma-CX21-X0-X1-X2=X0-X2-CX21
  hypB L.ax-CX21-X0-X2=X0-X1-X2-CX21 = lemma-CX21-X0-X2=X0-X1-X2-CX21
  hypB L.ax-CX21-X1=X1-CX21 = lemma-CX21-X1=X1-CX21
  hypB L.ax-CX21-X1-X2=X2-CX21 = lemma-CX21-X1-X2=X2-CX21
  hypB L.ax-CX21-X2=X1-X2-CX21 = lemma-CX21-X2=X1-X2-CX21
  hypB L.ax-CCX2-X0=X0-CX10-CCX2-CX10 = lemma-CCX2-X0=X0-CX10-CCX2-CX10
  hypB L.ax-CCX2-X0-X1=X0-X1-X2-CX10-CCX2-CX10-CX01-CCX2-CX01-CCX2 = lemma-CCX2-X0-X1=X0-X1-X2-CX10-CCX2-CX10-CX01-CCX2-CX01-CCX2
  hypB L.ax-CCX2-X0-X1-X2=X0-X1-CX10-CCX2-CX10-CX01-CCX2-CX01-CCX2 = lemma-CCX2-X0-X1-X2=X0-X1-CX10-CCX2-CX10-CX01-CCX2-CX01-CCX2
  hypB L.ax-CCX2-X0-X2=X0-X2-CX10-CCX2-CX10 = lemma-CCX2-X0-X2=X0-X2-CX10-CCX2-CX10
  hypB L.ax-CCX2-X1=X1-CX01-CCX2-CX01 = lemma-CCX2-X1=X1-CX01-CCX2-CX01
  hypB L.ax-CCX2-X1-X2=X1-X2-CX01-CCX2-CX01 = lemma-CCX2-X1-X2=X1-X2-CX01-CCX2-CX01
  hypB L.ax-CCX2-X2=X2-CCX2 = lemma-CCX2-X2=X2-CCX2
  hypB L.ax-CCX1-X0=X0-CX21-CCX1 = lemma-CCX1-X0=X0-CX21-CCX1
  hypB L.ax-CCX1-X0-X1=X0-X1-CX21-CCX1 = lemma-CCX1-X0-X1=X0-X1-CX21-CCX1
  hypB L.ax-CCX1-X0-X1-X2=X0-X2-CX21-CX01-CCX1 = lemma-CCX1-X0-X1-X2=X0-X2-CX21-CX01-CCX1
  hypB L.ax-CCX1-X0-X2=X0-X1-X2-CX21-CX01-CCX1 = lemma-CCX1-X0-X2=X0-X1-X2-CX21-CX01-CCX1
  hypB L.ax-CCX1-X1=X1-CCX1 = lemma-CCX1-X1=X1-CCX1
  hypB L.ax-CCX1-X1-X2=X1-X2-CX01-CCX1 = lemma-CCX1-X1-X2=X1-X2-CX01-CCX1
  hypB L.ax-CCX1-X2=X2-CX01-CCX1 = lemma-CCX1-X2=X2-CX01-CCX1
  hypB L.ax-CCX0-X0=X0-CCX0 = lemma-CCX0-X0=X0-CCX0
  hypB L.ax-CCX0-X0-X1=X0-X1-CX20-CCX0 = lemma-CCX0-X0-X1=X0-X1-CX20-CCX0
  hypB L.ax-CCX0-X0-X1-X2=X1-X2-CX20-CX10-CCX0 = lemma-CCX0-X0-X1-X2=X1-X2-CX20-CX10-CCX0
  hypB L.ax-CCX0-X0-X2=X0-X2-CX10-CCX0 = lemma-CCX0-X0-X2=X0-X2-CX10-CCX0
  hypB L.ax-CCX0-X1=X1-CX20-CCX0 = lemma-CCX0-X1=X1-CX20-CCX0
  hypB L.ax-CCX0-X1-X2=X0-X1-X2-CX20-CX10-CCX0 = lemma-CCX0-X1-X2=X0-X1-X2-CX20-CX10-CCX0
  hypB L.ax-CCX0-X2=X2-CX10-CCX0 = lemma-CCX0-X2=X2-CX10-CCX0
  hypB L.ax-X1-CX10=X0-CX10-X1 = lemma-X1-CX10=X0-CX10-X1
  hypB L.ax-X1-CX20=CX20-X1 = lemma-X1-CX20=CX20-X1
  hypB L.ax-X1-CCX0=CX20-CCX0-X1 = lemma-X1-CCX0=CX20-CCX0-X1
  hypB L.ax-X2-CX10=CX10-X2 = lemma-X2-CX10=CX10-X2
  hypB L.ax-X2-CX20=X0-CX20-X2 = lemma-X2-CX20=X0-CX20-X2
  hypB L.ax-X2-CCX0=CX10-CCX0-X2 = lemma-X2-CCX0=CX10-CCX0-X2
  hypB L.ax-CX12-X0=X0-CX12 = lemma-CX12-X0=X0-CX12


  hypB L.ax-CX12-CX10=CX10-CX12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX12-CX20=CX10-CX20-CX12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX12-CCX0=CX10-CCX0-CX12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX21-CX10=CX10-CX20-CX21 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX21-CX20=CX20-CX21 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX21-CCX0=CX20-CCX0-CX21 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-Swap12-X0=X0-Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-Swap12-CX10=CX20-Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-Swap12-CX20=CX10-Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-Swap12-CCX0=CCX0-Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX20-CX10=CX10-CX20 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-Swap12-X1=X2-Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-Swap12-X2=X1-Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-Swap12-CX12=CX21-Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-Swap12-CX21=CX12-Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX12-X2=X2-CX12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX12-X1=X1-X2-CX12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX12-CX21-CX12=Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX21-CX12-CX21=Swap12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX12-Swap12=CX21-CX12 = ListNF.listnfeq' nf-s8e auto
  hypB L.ax-CX21-Swap12=CX12-CX21 = ListNF.listnfeq' nf-s8e auto
  
  hypB L.ax-iI-K0=K0-iI = axiom ax-iI-K0=K0-iI
  hypB L.ax-S1-K0=K0-S1 = axiom ax-S1-K0=K0-S1
  hypB L.ax-S2-K0=K0-S2 = axiom ax-S2-K0=K0-S2
  hypB L.ax-X1-K0=K0-X1 = axiom ax-X1-K0=K0-X1
  hypB L.ax-X2-K0=K0-X2 = axiom ax-X2-K0=K0-X2
  hypB L.ax-CS12-K0=K0-CS12 = axiom ax-CS12-K0=K0-CS12
  hypB L.ax-CX12-K0=K0-CX12 = axiom ax-CX12-K0=K0-CX12
  hypB L.ax-CX21-K0=K0-CX21 = axiom ax-CX21-K0=K0-CX21
  hypB L.ax-Swap12-K0=K0-Swap12 = axiom ax-Swap12-K0=K0-Swap12
  hypB L.ax-S0-S0-K0=K0-X0 = axiom ax-S0-S0-K0=K0-X0
  hypB L.ax-CS01-CS01-K0=K0-CX10 = axiom ax-CS01-CS01-K0=K0-CX10
  hypB L.ax-CS02-CS02-K0=K0-CX20 = axiom ax-CS02-CS02-K0=K0-CX20
  hypB L.ax-CCZ-K0=K0-CCX0 = axiom ax-CCZ-K0=K0-CCX0
  hypB L.ax-X0-K0=K0-S0-S0 = axiom ax-X0-K0=K0-S0-S0
  hypB L.ax-CX10-K0=K0-CS01-CS01 = axiom ax-CX10-K0=K0-CS01-CS01
  hypB L.ax-CX20-K0=K0-CS02-CS02 = axiom ax-CX20-K0=K0-CS02-CS02
  hypB L.ax-CCX0-K0=K0-CCZ = axiom ax-CCX0-K0=K0-CCZ
  hypB L.ax-S0-K0-S0-K0-S0-K0=iI-iI-iI = axiom ax-S0-K0-S0-K0-S0-K0=iI-iI-iI
  hypB L.ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01 = axiom ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01
  hypB L.ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ = axiom ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ

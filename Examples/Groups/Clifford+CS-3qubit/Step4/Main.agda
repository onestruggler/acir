------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --call-by-name #-}

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

module Examples.Groups.Clifford+CS-3qubit.Step4.Main where

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
  hypA CCK'-gen = refl
  hypA CK10-gen = refl
  hypA CK20-gen = refl
  hypA K0-gen = refl
  hypA K1-gen = refl
  hypA K2-gen = refl


  hypB : ∀ {u t : Word Gate} -> u === t ∈ L.Rel -> Rel ⊢ simple-of-gen-star u === simple-of-gen-star t

  hypB L.ax-K1=Swap01-K0-Swap01 = axiom ax-K1=Swap01-K0-Swap01
  hypB L.ax-K2=Swap12-Swap01-K0-Swap01-Swap12 = axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12

  hypB L.ax-CCX0-CCX0=ε = axiom ax-CCX0-CCX0=ε
  hypB L.ax-CCX1-CCX1=ε = axiom ax-CCX1-CCX1=ε
  hypB L.ax-CCX2-CCX2=ε = axiom ax-CCX2-CCX2=ε
  hypB L.ax-CX01-CX01=ε = axiom ax-CX01-CX01=ε
  hypB L.ax-CX10-CX10=ε = axiom ax-CX10-CX10=ε
  hypB L.ax-CX12-CX12=ε = axiom ax-CX12-CX12=ε
  hypB L.ax-CX21-CX21=ε = axiom ax-CX21-CX21=ε
  hypB L.ax-CX02-CX02=ε = axiom ax-CX02-CX02=ε
  hypB L.ax-CX20-CX20=ε = axiom ax-CX20-CX20=ε
  hypB L.ax-X0-X0=ε = axiom ax-X0-X0=ε
  hypB L.ax-X1-X1=ε = axiom ax-X1-X1=ε
  hypB L.ax-X2-X2=ε = axiom ax-X2-X2=ε
  hypB L.ax-Swap01-Swap01=ε = axiom ax-Swap01-Swap01=ε
  hypB L.ax-Swap12-Swap12=ε = axiom ax-Swap12-Swap12=ε
  hypB L.ax-S0-S0-S0-S0=ε = axiom ax-S0-S0-S0-S0=ε
  hypB L.ax-S1-S1-S1-S1=ε = axiom ax-S1-S1-S1-S1=ε
  hypB L.ax-S2-S2-S2-S2=ε = axiom ax-S2-S2-S2-S2=ε
  hypB L.ax-CS01-CS01-CS01-CS01=ε = axiom ax-CS01-CS01-CS01-CS01=ε
  hypB L.ax-CS12-CS12-CS12-CS12=ε = axiom ax-CS12-CS12-CS12-CS12=ε
  hypB L.ax-CS02-CS02-CS02-CS02=ε = axiom ax-CS02-CS02-CS02-CS02=ε
  hypB L.ax-CCZ-CCZ=ε = axiom ax-CCZ-CCZ=ε
  hypB L.ax-iI-iI-iI-iI=ε = axiom ax-iI-iI-iI-iI=ε
  hypB L.ax-CCK'-CCK'-CCK'=CS12-CS12 = axiom ax-CCK'-CCK'-CCK'=CS12-CS12
  hypB L.ax-CK10-CK10=S1-S1-S1 = axiom ax-CK10-CK10=S1-S1-S1
  hypB L.ax-CK20-CK20=S2-S2-S2 = axiom ax-CK20-CK20=S2-S2-S2
  hypB L.ax-K0-K0=iI-iI-iI = axiom ax-K0-K0=iI-iI-iI
  hypB L.ax-K1-K1=iI-iI-iI = lemma-K1-K1=iI-iI-iI
  hypB L.ax-K2-K2=iI-iI-iI = lemma-K2-K2=iI-iI-iI
  hypB L.ax-iI-CCX0=CCX0-iI = axiom ax-iI-CCX0=CCX0-iI
  hypB L.ax-iI-CCX1=CCX1-iI = axiom ax-iI-CCX1=CCX1-iI
  hypB L.ax-iI-CCX2=CCX2-iI = axiom ax-iI-CCX2=CCX2-iI
  hypB L.ax-iI-CX01=CX01-iI = axiom ax-iI-CX01=CX01-iI
  hypB L.ax-iI-CX10=CX10-iI = axiom ax-iI-CX10=CX10-iI
  hypB L.ax-iI-CX12=CX12-iI = axiom ax-iI-CX12=CX12-iI
  hypB L.ax-iI-CX21=CX21-iI = axiom ax-iI-CX21=CX21-iI
  hypB L.ax-iI-CX02=CX02-iI = axiom ax-iI-CX02=CX02-iI
  hypB L.ax-iI-CX20=CX20-iI = axiom ax-iI-CX20=CX20-iI
  hypB L.ax-iI-X0=X0-iI = axiom ax-iI-X0=X0-iI
  hypB L.ax-iI-X1=X1-iI = axiom ax-iI-X1=X1-iI
  hypB L.ax-iI-X2=X2-iI = axiom ax-iI-X2=X2-iI
  hypB L.ax-iI-Swap01=Swap01-iI = axiom ax-iI-Swap01=Swap01-iI
  hypB L.ax-iI-Swap12=Swap12-iI = axiom ax-iI-Swap12=Swap12-iI
  hypB L.ax-iI-S0=S0-iI = axiom ax-iI-S0=S0-iI
  hypB L.ax-iI-S1=S1-iI = axiom ax-iI-S1=S1-iI
  hypB L.ax-iI-S2=S2-iI = axiom ax-iI-S2=S2-iI
  hypB L.ax-iI-CS01=CS01-iI = axiom ax-iI-CS01=CS01-iI
  hypB L.ax-iI-CS12=CS12-iI = axiom ax-iI-CS12=CS12-iI
  hypB L.ax-iI-CS02=CS02-iI = axiom ax-iI-CS02=CS02-iI
  hypB L.ax-iI-CCZ=CCZ-iI = axiom ax-iI-CCZ=CCZ-iI
  hypB L.ax-iI-CCK'=CCK'-iI = axiom ax-iI-CCK'=CCK'-iI
  hypB L.ax-iI-CK10=CK10-iI = axiom ax-iI-CK10=CK10-iI
  hypB L.ax-iI-CK20=CK20-iI = axiom ax-iI-CK20=CK20-iI
  hypB L.ax-iI-K0=K0-iI = axiom ax-iI-K0=K0-iI
  hypB L.ax-iI-K1=K1-iI = lemma-iI-K1=K1-iI
  hypB L.ax-iI-K2=K2-iI = lemma-iI-K2=K2-iI

  hypB L.ax-CCX2-K0-CK10=K0-CK10-CCX2 = lemma-CCX2-K0-CK10=K0-CK10-CCX2
  hypB L.ax-CCX2-CK20-CCK'=CK20-CCK'-CCX2-CS01-CS01 = lemma-2'
  hypB L.ax-CCX1-CK10-CCK'=CK10-CCK'-CCX1-CS02-CS02 = lemma-3'
  hypB L.ax-CCX2-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCX2-CS01-CS01 = lemma-4'
  hypB L.ax-CCX1-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCX1-CS02-CS02 = lemma-5'
  hypB L.ax-CCX2-CX02-K0-CK10=CK10-CCX2-CX02-K0 = lemma-6'
  hypB L.ax-CCX1-CX01-CCK'=CCK'-CCX1-CX01 = lemma-7'
  hypB L.ax-CCX2-CCX1-CX02-CCK'=CCK'-CCX2-CCX1-CX02 = lemma-8'
  hypB L.ax-CCX2-Swap01-CK20-CCK'=Swap01-CK20-CCK'-CCX2-CS01-CS01 = lemma-9'
  hypB L.ax-CCX1-CX01-CK20=CK20-CCX1-CX01 = lemma-10'
  hypB L.ax-CCX2-K0-CCX2-K0=K0-CCX2-K0-CCX2-CX12 = lemma-CCX2-K0-CCX2-K0=K0-CCX2-K0-CCX2-CX12
  hypB L.ax-CCX2-CX02-K0-CCX2-CX02-K0=K0-CCX2-CX02-K0-CCX2-CX02-CX12-X2 = lemma-12'
  hypB L.ax-CCX2-CX02-CK10=CK10-CCX2-CX02 = lemma-13'
  hypB L.ax-CK10-CCK'-CCX1-CK20-CCK'=CCX1-CK20-CK10-CX20-CCX0-CS12-CS12-CS12 = lemma-14'
  hypB L.ax-K0-CK20-CK10-CCK'-CX01-CCX0-Swap01-CK20-CCK'=K0-CK10-CX01-CCX0-Swap01-S2-S2-S2-CS12-CS12 = lemma-15'


  hypB L.ax-S1-S0=S0-S1 = axiom ax-S1-S0=S0-S1
  hypB L.ax-S2-S0=S0-S2 = axiom ax-S2-S0=S0-S2
  hypB L.ax-S2-S1=S1-S2 = axiom ax-S2-S1=S1-S2
  hypB L.ax-CS01-S0=S0-CS01 = axiom ax-CS01-S0=S0-CS01
  hypB L.ax-CS01-S1=S1-CS01 = axiom ax-CS01-S1=S1-CS01
  hypB L.ax-CS01-S2=S2-CS01 = axiom ax-CS01-S2=S2-CS01
  hypB L.ax-CS12-S0=S0-CS12 = axiom ax-CS12-S0=S0-CS12
  hypB L.ax-CS12-S1=S1-CS12 = axiom ax-CS12-S1=S1-CS12
  hypB L.ax-CS12-S2=S2-CS12 = axiom ax-CS12-S2=S2-CS12
  hypB L.ax-CS12-CS01=CS01-CS12 = axiom ax-CS12-CS01=CS01-CS12
  hypB L.ax-CS12-CS02=CS02-CS12 = axiom ax-CS12-CS02=CS02-CS12
  hypB L.ax-CS02-S0=S0-CS02 = axiom ax-CS02-S0=S0-CS02
  hypB L.ax-CS02-S1=S1-CS02 = axiom ax-CS02-S1=S1-CS02
  hypB L.ax-CS02-S2=S2-CS02 = axiom ax-CS02-S2=S2-CS02
  hypB L.ax-CS02-CS01=CS01-CS02 = axiom ax-CS02-CS01=CS01-CS02
  hypB L.ax-CCZ-S0=S0-CCZ = axiom ax-CCZ-S0=S0-CCZ
  hypB L.ax-CCZ-S1=S1-CCZ = axiom ax-CCZ-S1=S1-CCZ
  hypB L.ax-CCZ-S2=S2-CCZ = axiom ax-CCZ-S2=S2-CCZ
  hypB L.ax-CCZ-CS01=CS01-CCZ = axiom ax-CCZ-CS01=CS01-CCZ
  hypB L.ax-CCZ-CS12=CS12-CCZ = axiom ax-CCZ-CS12=CS12-CCZ
  hypB L.ax-CCZ-CS02=CS02-CCZ = axiom ax-CCZ-CS02=CS02-CCZ
  hypB L.ax-Swap01-S0=S1-Swap01 = axiom ax-Swap01-S0=S1-Swap01
  hypB L.ax-Swap01-S1=S0-Swap01 = axiom ax-Swap01-S1=S0-Swap01
  hypB L.ax-Swap01-S2=S2-Swap01 = axiom ax-Swap01-S2=S2-Swap01
  hypB L.ax-Swap01-CS01=CS01-Swap01 = axiom ax-Swap01-CS01=CS01-Swap01
  hypB L.ax-Swap01-CS02=CS12-Swap01 = axiom ax-Swap01-CS02=CS12-Swap01
  hypB L.ax-Swap01-CS12=CS02-Swap01 = axiom ax-Swap01-CS12=CS02-Swap01
  hypB L.ax-Swap01-CCZ=CCZ-Swap01 = axiom ax-Swap01-CCZ=CCZ-Swap01
  hypB L.ax-Swap01-iI=iI-Swap01 = axiom ax-Swap01-iI=iI-Swap01
  hypB L.ax-CX01-S0=S0-CX01 = axiom ax-CX01-S0=S0-CX01
  hypB L.ax-CX01-S1=S0-S1-CS01-CS01-CX01 = axiom ax-CX01-S1=S0-S1-CS01-CS01-CX01
  hypB L.ax-CX01-S2=S2-CX01 = axiom ax-CX01-S2=S2-CX01
  hypB L.ax-CX01-CS01=S0-CS01-CS01-CS01-CX01 = axiom ax-CX01-CS01=S0-CS01-CS01-CS01-CX01
  hypB L.ax-CX01-CS02=CS02-CX01 = axiom ax-CX01-CS02=CS02-CX01
  hypB L.ax-CX01-CS12=CS02-CS12-CCZ-CX01 = axiom ax-CX01-CS12=CS02-CS12-CCZ-CX01
  hypB L.ax-CX01-CCZ=CS02-CS02-CCZ-CX01 = axiom ax-CX01-CCZ=CS02-CS02-CCZ-CX01
  hypB L.ax-CX01-iI=iI-CX01 = axiom ax-CX01-iI=iI-CX01
  hypB L.ax-CX02-S0=S0-CX02 = axiom ax-CX02-S0=S0-CX02
  hypB L.ax-CX02-S1=S1-CX02 = axiom ax-CX02-S1=S1-CX02
  hypB L.ax-CX02-S2=S0-S2-CS02-CS02-CX02 = axiom ax-CX02-S2=S0-S2-CS02-CS02-CX02
  hypB L.ax-CX02-CS01=CS01-CX02 = axiom ax-CX02-CS01=CS01-CX02
  hypB L.ax-CX02-CS02=S0-CS02-CS02-CS02-CX02 = axiom ax-CX02-CS02=S0-CS02-CS02-CS02-CX02
  hypB L.ax-CX02-CS12=CS01-CS12-CCZ-CX02 = axiom ax-CX02-CS12=CS01-CS12-CCZ-CX02
  hypB L.ax-CX02-CCZ=CS01-CS01-CCZ-CX02 = axiom ax-CX02-CCZ=CS01-CS01-CCZ-CX02
  hypB L.ax-CX02-iI=iI-CX02 = axiom ax-CX02-iI=iI-CX02
  hypB L.ax-CCX1-S0=S0-CCX1 = axiom ax-CCX1-S0=S0-CCX1
  hypB L.ax-CCX1-S1=S1-CS02-CCZ-CCX1 = axiom ax-CCX1-S1=S1-CS02-CCZ-CCX1
  hypB L.ax-CCX1-S2=S2-CCX1 = axiom ax-CCX1-S2=S2-CCX1
  hypB L.ax-CCX1-CS01=CS01-CS02-CCZ-CCX1 = axiom ax-CCX1-CS01=CS01-CS02-CCZ-CCX1
  hypB L.ax-CCX1-CS02=CS02-CCX1 = axiom ax-CCX1-CS02=CS02-CCX1
  hypB L.ax-CCX1-CS12=CS02-CS12-CCZ-CCX1 = axiom ax-CCX1-CS12=CS02-CS12-CCZ-CCX1
  hypB L.ax-CCX1-CCZ=CS02-CS02-CCZ-CCX1 = axiom ax-CCX1-CCZ=CS02-CS02-CCZ-CCX1
  hypB L.ax-CCX1-iI=iI-CCX1 = axiom ax-CCX1-iI=iI-CCX1
  hypB L.ax-CCX2-S0=S0-CCX2 = axiom ax-CCX2-S0=S0-CCX2
  hypB L.ax-CCX2-S1=S1-CCX2 = axiom ax-CCX2-S1=S1-CCX2
  hypB L.ax-CCX2-S2=S2-CS01-CCZ-CCX2 = axiom ax-CCX2-S2=S2-CS01-CCZ-CCX2
  hypB L.ax-CCX2-CS01=CS01-CCX2 = axiom ax-CCX2-CS01=CS01-CCX2
  hypB L.ax-CCX2-CS02=CS01-CS02-CCZ-CCX2 = axiom ax-CCX2-CS02=CS01-CS02-CCZ-CCX2
  hypB L.ax-CCX2-CS12=CS01-CS12-CCZ-CCX2 = axiom ax-CCX2-CS12=CS01-CS12-CCZ-CCX2
  hypB L.ax-CCX2-CCZ=CS01-CS01-CCZ-CCX2 = axiom ax-CCX2-CCZ=CS01-CS01-CCZ-CCX2
  hypB L.ax-CCX2-iI=iI-CCX2 = axiom ax-CCX2-iI=iI-CCX2
  hypB L.ax-X1-S0=S0-X1 = axiom ax-X1-S0=S0-X1
  hypB L.ax-X1-S1=S1-S1-S1-iI-X1 = axiom ax-X1-S1=S1-S1-S1-iI-X1
  hypB L.ax-X1-S2=S2-X1 = axiom ax-X1-S2=S2-X1
  hypB L.ax-X1-CS01=S0-CS01-CS01-CS01-X1 = axiom ax-X1-CS01=S0-CS01-CS01-CS01-X1
  hypB L.ax-X1-CS02=CS02-X1 = axiom ax-X1-CS02=CS02-X1
  hypB L.ax-X1-CS12=S2-CS12-CS12-CS12-X1 = axiom ax-X1-CS12=S2-CS12-CS12-CS12-X1
  hypB L.ax-X1-CCZ=CS02-CS02-CCZ-X1 = axiom ax-X1-CCZ=CS02-CS02-CCZ-X1
  hypB L.ax-X1-iI=iI-X1 = axiom ax-X1-iI=iI-X1
  hypB L.ax-X2-S0=S0-X2 = axiom ax-X2-S0=S0-X2
  hypB L.ax-X2-S1=S1-X2 = axiom ax-X2-S1=S1-X2
  hypB L.ax-X2-S2=S2-S2-S2-iI-X2 = axiom ax-X2-S2=S2-S2-S2-iI-X2
  hypB L.ax-X2-CS01=CS01-X2 = axiom ax-X2-CS01=CS01-X2
  hypB L.ax-X2-CS02=S0-CS02-CS02-CS02-X2 = axiom ax-X2-CS02=S0-CS02-CS02-CS02-X2
  hypB L.ax-X2-CS12=S1-CS12-CS12-CS12-X2 = axiom ax-X2-CS12=S1-CS12-CS12-CS12-X2
  hypB L.ax-X2-CCZ=CS01-CS01-CCZ-X2 = axiom ax-X2-CCZ=CS01-CS01-CCZ-X2
  hypB L.ax-X2-iI=iI-X2 = axiom ax-X2-iI=iI-X2
  hypB L.ax-CX12-S0=S0-CX12 = axiom ax-CX12-S0=S0-CX12
  hypB L.ax-CX12-S1=S1-CX12 = axiom ax-CX12-S1=S1-CX12
  hypB L.ax-CX12-S2=S1-S2-CS12-CS12-CX12 = axiom ax-CX12-S2=S1-S2-CS12-CS12-CX12
  hypB L.ax-CX12-CS01=CS01-CX12 = axiom ax-CX12-CS01=CS01-CX12
  hypB L.ax-CX12-CS02=CS01-CS02-CCZ-CX12 = axiom ax-CX12-CS02=CS01-CS02-CCZ-CX12
  hypB L.ax-CX12-CS12=S1-CS12-CS12-CS12-CX12 = axiom ax-CX12-CS12=S1-CS12-CS12-CS12-CX12
  hypB L.ax-CX12-CCZ=CS01-CS01-CCZ-CX12 = axiom ax-CX12-CCZ=CS01-CS01-CCZ-CX12
  hypB L.ax-CX12-iI=iI-CX12 = axiom ax-CX12-iI=iI-CX12
  hypB L.ax-CX21-S0=S0-CX21 = axiom ax-CX21-S0=S0-CX21
  hypB L.ax-CX21-S1=S1-S2-CS12-CS12-CX21 = axiom ax-CX21-S1=S1-S2-CS12-CS12-CX21
  hypB L.ax-CX21-S2=S2-CX21 = axiom ax-CX21-S2=S2-CX21
  hypB L.ax-CX21-CS01=CS01-CS02-CCZ-CX21 = axiom ax-CX21-CS01=CS01-CS02-CCZ-CX21
  hypB L.ax-CX21-CS02=CS02-CX21 = axiom ax-CX21-CS02=CS02-CX21
  hypB L.ax-CX21-CS12=S2-CS12-CS12-CS12-CX21 = axiom ax-CX21-CS12=S2-CS12-CS12-CS12-CX21
  hypB L.ax-CX21-CCZ=CS02-CS02-CCZ-CX21 = axiom ax-CX21-CCZ=CS02-CS02-CCZ-CX21
  hypB L.ax-CX21-iI=iI-CX21 = axiom ax-CX21-iI=iI-CX21
  hypB L.ax-Swap12-S0=S0-Swap12 = axiom ax-Swap12-S0=S0-Swap12
  hypB L.ax-Swap12-S1=S2-Swap12 = axiom ax-Swap12-S1=S2-Swap12
  hypB L.ax-Swap12-S2=S1-Swap12 = axiom ax-Swap12-S2=S1-Swap12
  hypB L.ax-Swap12-CS01=CS02-Swap12 = axiom ax-Swap12-CS01=CS02-Swap12
  hypB L.ax-Swap12-CS02=CS01-Swap12 = axiom ax-Swap12-CS02=CS01-Swap12
  hypB L.ax-Swap12-CS12=CS12-Swap12 = axiom ax-Swap12-CS12=CS12-Swap12
  hypB L.ax-Swap12-CCZ=CCZ-Swap12 = axiom ax-Swap12-CCZ=CCZ-Swap12
  hypB L.ax-Swap12-iI=iI-Swap12 = axiom ax-Swap12-iI=iI-Swap12
  hypB L.ax-X0-S0=S0-S0-S0-iI-X0 = axiom ax-X0-S0=S0-S0-S0-iI-X0
  hypB L.ax-X0-S1=S1-X0 = axiom ax-X0-S1=S1-X0
  hypB L.ax-X0-S2=S2-X0 = axiom ax-X0-S2=S2-X0
  hypB L.ax-X0-CS01=S1-CS01-CS01-CS01-X0 = axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0
  hypB L.ax-X0-CS02=S2-CS02-CS02-CS02-X0 = axiom ax-X0-CS02=S2-CS02-CS02-CS02-X0
  hypB L.ax-X0-CS12=CS12-X0 = axiom ax-X0-CS12=CS12-X0
  hypB L.ax-X0-CCZ=CS12-CS12-CCZ-X0 = axiom ax-X0-CCZ=CS12-CS12-CCZ-X0
  hypB L.ax-X0-iI=iI-X0 = axiom ax-X0-iI=iI-X0
  hypB L.ax-CX10-S0=S0-S1-CS01-CS01-CX10 = axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10
  hypB L.ax-CX10-S1=S1-CX10 = axiom ax-CX10-S1=S1-CX10
  hypB L.ax-CX10-S2=S2-CX10 = axiom ax-CX10-S2=S2-CX10
  hypB L.ax-CX10-CS01=S1-CS01-CS01-CS01-CX10 = axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10
  hypB L.ax-CX10-CS02=CS02-CS12-CCZ-CX10 = axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10
  hypB L.ax-CX10-CS12=CS12-CX10 = axiom ax-CX10-CS12=CS12-CX10
  hypB L.ax-CX10-CCZ=CS12-CS12-CCZ-CX10 = axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10
  hypB L.ax-CX10-iI=iI-CX10 = axiom ax-CX10-iI=iI-CX10
  hypB L.ax-CX20-S0=S0-S2-CS02-CS02-CX20 = axiom ax-CX20-S0=S0-S2-CS02-CS02-CX20
  hypB L.ax-CX20-S1=S1-CX20 = axiom ax-CX20-S1=S1-CX20
  hypB L.ax-CX20-S2=S2-CX20 = axiom ax-CX20-S2=S2-CX20
  hypB L.ax-CX20-CS01=CS01-CS12-CCZ-CX20 = axiom ax-CX20-CS01=CS01-CS12-CCZ-CX20
  hypB L.ax-CX20-CS02=S2-CS02-CS02-CS02-CX20 = axiom ax-CX20-CS02=S2-CS02-CS02-CS02-CX20
  hypB L.ax-CX20-CS12=CS12-CX20 = axiom ax-CX20-CS12=CS12-CX20
  hypB L.ax-CX20-CCZ=CS12-CS12-CCZ-CX20 = axiom ax-CX20-CCZ=CS12-CS12-CCZ-CX20
  hypB L.ax-CX20-iI=iI-CX20 = axiom ax-CX20-iI=iI-CX20
  hypB L.ax-CCX0-S0=S0-CS12-CCZ-CCX0 = axiom ax-CCX0-S0=S0-CS12-CCZ-CCX0
  hypB L.ax-CCX0-S1=S1-CCX0 = axiom ax-CCX0-S1=S1-CCX0
  hypB L.ax-CCX0-S2=S2-CCX0 = axiom ax-CCX0-S2=S2-CCX0
  hypB L.ax-CCX0-CS01=CS01-CS12-CCZ-CCX0 = axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0
  hypB L.ax-CCX0-CS02=CS02-CS12-CCZ-CCX0 = axiom ax-CCX0-CS02=CS02-CS12-CCZ-CCX0
  hypB L.ax-CCX0-CS12=CS12-CCX0 = axiom ax-CCX0-CS12=CS12-CCX0
  hypB L.ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0 = axiom ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0
  hypB L.ax-CCX0-iI=iI-CCX0 = axiom ax-CCX0-iI=iI-CCX0
  hypB L.ax-CCX1-CCX1-CCX2=CCX2 = axiom ax-CCX1-CCX1-CCX2=CCX2
  hypB L.ax-CCX2-CCX2-CX01=CX01 = axiom ax-CCX2-CCX2-CX01=CX01
  hypB L.ax-CCX1-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0 = axiom ax-CCX1-CCX0-CCX2-CX01=CCX0-CCX2-CX01-CCX0
  hypB L.ax-CCX0-CCX0-CCX2-CX01=CCX2-CX01 = axiom ax-CCX0-CCX0-CCX2-CX01=CCX2-CX01
  hypB L.ax-CCX0-CX10=CX10-CCX0 = axiom ax-CCX0-CX10=CX10-CCX0
  hypB L.ax-CCX0-CX20=CX20-CCX0 = axiom ax-CCX0-CX20=CX20-CCX0
  hypB L.ax-X1-X0=X0-X1 = axiom ax-X1-X0=X0-X1
  hypB L.ax-X2-X0=X0-X2 = axiom ax-X2-X0=X0-X2
  hypB L.ax-X2-X1=X1-X2 = axiom ax-X2-X1=X1-X2
  hypB L.ax-CX10-X0=X0-CX10 = axiom ax-CX10-X0=X0-CX10
  hypB L.ax-CX20-X0=X0-CX20 = axiom ax-CX20-X0=X0-CX20
  hypB L.ax-CX21-X0=X0-CX21 = axiom ax-CX21-X0=X0-CX21
  hypB L.ax-CX21-X1=X1-CX21 = axiom ax-CX21-X1=X1-CX21
  hypB L.ax-CX21-X2=X1-X2-CX21 = axiom ax-CX21-X2=X1-X2-CX21
  hypB L.ax-CCX0-X0=X0-CCX0 = axiom ax-CCX0-X0=X0-CCX0
  hypB L.ax-X0-CCK'=CCK'-X0-CCX0-CCZ = axiom ax-X0-CCK'=CCK'-X0-CCX0-CCZ
  hypB L.ax-X0-CCK'-CCK'=CCK'-CCK'-X0-CS12-CCZ = axiom ax-X0-CCK'-CCK'=CCK'-CCK'-X0-CS12-CCZ
  hypB L.ax-CX10-CCK'=CCK'-CX10-CCX0-CCZ = axiom ax-CX10-CCK'=CCK'-CX10-CCX0-CCZ
  hypB L.ax-CX10-CCK'-CCK'=CCK'-CCK'-CX10-CS12-CCZ = axiom ax-CX10-CCK'-CCK'=CCK'-CCK'-CX10-CS12-CCZ
  hypB L.ax-CX20-CCK'=CCK'-CX20-CCX0-CCZ = axiom ax-CX20-CCK'=CCK'-CX20-CCX0-CCZ
  hypB L.ax-CX20-CCK'-CCK'=CCK'-CCK'-CX20-CS12-CCZ = axiom ax-CX20-CCK'-CCK'=CCK'-CCK'-CX20-CS12-CCZ
  hypB L.ax-CCX0-CCK'=CCK'-CCZ = axiom ax-CCX0-CCK'=CCK'-CCZ
  hypB L.ax-CCX0-CCK'-CCK'=CCK'-CCK'-CCX0-CS12-CCZ = axiom ax-CCX0-CCK'-CCK'=CCK'-CCK'-CCX0-CS12-CCZ
  hypB L.ax-S0-CCK'=CCK'-CCK'-S0-CS12-CCZ = axiom ax-S0-CCK'=CCK'-CCK'-S0-CS12-CCZ
  hypB L.ax-S0-CCK'-CCK'=CCK'-CCX0-S0-CCZ = axiom ax-S0-CCK'-CCK'=CCK'-CCX0-S0-CCZ
  hypB L.ax-S1-CCK'=CCK'-S1 = axiom ax-S1-CCK'=CCK'-S1
  hypB L.ax-S1-CCK'-CCK'=CCK'-CCK'-S1 = axiom ax-S1-CCK'-CCK'=CCK'-CCK'-S1
  hypB L.ax-S2-CCK'=CCK'-S2 = axiom ax-S2-CCK'=CCK'-S2
  hypB L.ax-S2-CCK'-CCK'=CCK'-CCK'-S2 = axiom ax-S2-CCK'-CCK'=CCK'-CCK'-S2
  hypB L.ax-CS01-CCK'=CCK'-CCK'-CS01-CS12-CCZ = axiom ax-CS01-CCK'=CCK'-CCK'-CS01-CS12-CCZ
  hypB L.ax-CS01-CCK'-CCK'=CCK'-CCX0-CS01-CCZ = axiom ax-CS01-CCK'-CCK'=CCK'-CCX0-CS01-CCZ
  hypB L.ax-CS02-CCK'=CCK'-CCK'-CS02-CS12-CCZ = axiom ax-CS02-CCK'=CCK'-CCK'-CS02-CS12-CCZ
  hypB L.ax-CS02-CCK'-CCK'=CCK'-CCX0-CS02-CCZ = axiom ax-CS02-CCK'-CCK'=CCK'-CCX0-CS02-CCZ
  hypB L.ax-CS12-CCK'=CCK'-CS12 = axiom ax-CS12-CCK'=CCK'-CS12
  hypB L.ax-CS12-CCK'-CCK'=CCK'-CCK'-CS12 = axiom ax-CS12-CCK'-CCK'=CCK'-CCK'-CS12
  hypB L.ax-CCZ-CCK'=CCK'-CCX0-CS12-CCZ = axiom ax-CCZ-CCK'=CCK'-CCX0-CS12-CCZ
  hypB L.ax-CCZ-CCK'-CCK'=CCK'-CCK'-CCX0 = axiom ax-CCZ-CCK'-CCK'=CCK'-CCK'-CCX0
  hypB L.ax-iI-CCK'-CCK'=CCK'-CCK'-iI = axiom ax-iI-CCK'-CCK'=CCK'-CCK'-iI
  hypB L.ax-CK10-S0-CK10=S0-CK10-CX10-CS01-CS01-CS01 = axiom ax-CK10-S0-CK10=S0-CK10-CX10-CS01-CS01-CS01
  hypB L.ax-CCK'-CK10=CK10-CCK'-CCK'-CCX0-CS12 = axiom ax-CCK'-CK10=CK10-CCK'-CCK'-CCX0-CS12
  hypB L.ax-CCK'-S0-CK10=S0-CK10-CCK' = axiom ax-CCK'-S0-CK10=S0-CK10-CCK'
  hypB L.ax-X0-CK10=CK10-X0-CX10-CS01-CS01 = axiom ax-X0-CK10=CK10-X0-CX10-CS01-CS01
  hypB L.ax-X0-S0-CK10=S0-CK10-X0-S0-S0-S1-S1-iI-iI-iI = axiom ax-X0-S0-CK10=S0-CK10-X0-S0-S0-S1-S1-iI-iI-iI
  hypB L.ax-CX10-CK10=CK10-CS01-CS01 = axiom ax-CX10-CK10=CK10-CS01-CS01
  hypB L.ax-CX10-S0-CK10=S0-CK10-CX10-S1-CS01-CS01 = axiom ax-CX10-S0-CK10=S0-CK10-CX10-S1-CS01-CS01
  hypB L.ax-CX20-CK10=CK10-CX20-CCX0-CCZ = axiom ax-CX20-CK10=CK10-CX20-CCX0-CCZ
  hypB L.ax-CX20-S0-CK10=S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12 = axiom ax-CX20-S0-CK10=S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12
  hypB L.ax-CCX0-CK10=CK10-CCZ = axiom ax-CCX0-CK10=CK10-CCZ
  hypB L.ax-CCX0-S0-CK10=S0-CK10-CCX0-CS12-CCZ = axiom ax-CCX0-S0-CK10=S0-CK10-CCX0-CS12-CCZ
  hypB L.ax-S0-S0-CK10=CK10-CX10-S0-S0-CS01-CS01 = axiom ax-S0-S0-CK10=CK10-CX10-S0-S0-CS01-CS01
  hypB L.ax-S1-CK10=CK10-S1 = axiom ax-S1-CK10=CK10-S1
  hypB L.ax-S1-S0-CK10=S0-CK10-S1 = axiom ax-S1-S0-CK10=S0-CK10-S1
  hypB L.ax-S2-CK10=CK10-S2 = axiom ax-S2-CK10=CK10-S2
  hypB L.ax-S2-S0-CK10=S0-CK10-S2 = axiom ax-S2-S0-CK10=S0-CK10-S2
  hypB L.ax-CS01-CK10=S0-CK10-S0-S0-S0-CS01 = axiom ax-CS01-CK10=S0-CK10-S0-S0-S0-CS01
  hypB L.ax-CS01-S0-CK10=CK10-CX10-S0-CS01-CS01-CS01 = axiom ax-CS01-S0-CK10=CK10-CX10-S0-CS01-CS01-CS01
  hypB L.ax-CS12-CK10=CK10-CS12 = axiom ax-CS12-CK10=CK10-CS12
  hypB L.ax-CS12-S0-CK10=S0-CK10-CS12 = axiom ax-CS12-S0-CK10=S0-CK10-CS12
  hypB L.ax-CCZ-CK10=CK10-CCX0 = axiom ax-CCZ-CK10=CK10-CCX0
  hypB L.ax-CCZ-S0-CK10=S0-CK10-CCX0 = axiom ax-CCZ-S0-CK10=S0-CK10-CCX0
  hypB L.ax-iI-S0-CK10=S0-CK10-iI = axiom ax-iI-S0-CK10=S0-CK10-iI
  hypB L.ax-CK20-S0-CK20=S0-CK20-CX20-CS02-CS02-CS02 = axiom ax-CK20-S0-CK20=S0-CK20-CX20-CS02-CS02-CS02
  hypB L.ax-CK10-CK20=CK20-CK10 = axiom ax-CK10-CK20=CK20-CK10
  hypB L.ax-CK10-S0-CK20=S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS12-CCZ = axiom ax-CK10-S0-CK20=S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS12-CCZ
  hypB L.ax-CCK'-CK20=CK20-CCK'-CCK'-CCX0-CS12 = axiom ax-CCK'-CK20=CK20-CCK'-CCK'-CCX0-CS12
  hypB L.ax-CCK'-S0-CK20=S0-CK20-CCK' = axiom ax-CCK'-S0-CK20=S0-CK20-CCK'
  hypB L.ax-X0-CK20=CK20-X0-CX20-CS02-CS02 = axiom ax-X0-CK20=CK20-X0-CX20-CS02-CS02
  hypB L.ax-X0-S0-CK20=S0-CK20-X0-S0-S0-S2-S2-iI-iI-iI = axiom ax-X0-S0-CK20=S0-CK20-X0-S0-S0-S2-S2-iI-iI-iI
  hypB L.ax-CX10-CK20=CK20-CX10-CCX0-CCZ = axiom ax-CX10-CK20=CK20-CX10-CCX0-CCZ
  hypB L.ax-CX10-S0-CK20=S0-CK20-CX10-S1-S1-S1-CS01-CS01-CS12-CS12 = axiom ax-CX10-S0-CK20=S0-CK20-CX10-S1-S1-S1-CS01-CS01-CS12-CS12
  hypB L.ax-CX20-CK20=CK20-CS02-CS02 = axiom ax-CX20-CK20=CK20-CS02-CS02
  hypB L.ax-CX20-S0-CK20=S0-CK20-CX20-S2-CS02-CS02 = axiom ax-CX20-S0-CK20=S0-CK20-CX20-S2-CS02-CS02
  hypB L.ax-CCX0-CK20=CK20-CCZ = axiom ax-CCX0-CK20=CK20-CCZ
  hypB L.ax-CCX0-S0-CK20=S0-CK20-CCX0-CS12-CCZ = axiom ax-CCX0-S0-CK20=S0-CK20-CCX0-CS12-CCZ
  hypB L.ax-S0-S0-CK20=CK20-CX20-S0-S0-CS02-CS02 = axiom ax-S0-S0-CK20=CK20-CX20-S0-S0-CS02-CS02
  hypB L.ax-S1-CK20=CK20-S1 = axiom ax-S1-CK20=CK20-S1
  hypB L.ax-S1-S0-CK20=S0-CK20-S1 = axiom ax-S1-S0-CK20=S0-CK20-S1
  hypB L.ax-S2-CK20=CK20-S2 = axiom ax-S2-CK20=CK20-S2
  hypB L.ax-S2-S0-CK20=S0-CK20-S2 = axiom ax-S2-S0-CK20=S0-CK20-S2
  hypB L.ax-CS02-CK20=S0-CK20-S0-S0-S0-CS02 = axiom ax-CS02-CK20=S0-CK20-S0-S0-S0-CS02
  hypB L.ax-CS02-S0-CK20=CK20-CX20-S0-CS02-CS02-CS02 = axiom ax-CS02-S0-CK20=CK20-CX20-S0-CS02-CS02-CS02
  hypB L.ax-CS12-CK20=CK20-CS12 = axiom ax-CS12-CK20=CK20-CS12
  hypB L.ax-CS12-S0-CK20=S0-CK20-CS12 = axiom ax-CS12-S0-CK20=S0-CK20-CS12
  hypB L.ax-CCZ-CK20=CK20-CCX0 = axiom ax-CCZ-CK20=CK20-CCX0
  hypB L.ax-CCZ-S0-CK20=S0-CK20-CCX0 = axiom ax-CCZ-S0-CK20=S0-CK20-CCX0
  hypB L.ax-iI-S0-CK20=S0-CK20-iI = axiom ax-iI-S0-CK20=S0-CK20-iI
  hypB L.ax-K0-S0-K0=S0-K0-X0-S0-S0-S0 = axiom ax-K0-S0-K0=S0-K0-X0-S0-S0-S0
  hypB L.ax-CK20-K0=K0-CK20 = axiom ax-CK20-K0=K0-CK20
  hypB L.ax-CK20-S0-K0=S0-K0-CX20-CS02-CS02-CS02 = axiom ax-CK20-S0-K0=S0-K0-CX20-CS02-CS02-CS02
  hypB L.ax-CK10-K0=K0-CK10 = axiom ax-CK10-K0=K0-CK10
  hypB L.ax-CK10-S0-K0=S0-K0-CX10-CS01-CS01-CS01 = axiom ax-CK10-S0-K0=S0-K0-CX10-CS01-CS01-CS01
  hypB L.ax-CCK'-K0=K0-CCK'-CCK'-CCX0-CS12 = axiom ax-CCK'-K0=K0-CCK'-CCK'-CCX0-CS12
  hypB L.ax-CCK'-S0-K0=S0-K0-CCK' = axiom ax-CCK'-S0-K0=S0-K0-CCK'
  hypB L.ax-X0-K0=K0-S0-S0 = axiom ax-X0-K0=K0-S0-S0
  hypB L.ax-X0-S0-K0=S0-K0-X0-S0-S0-iI = axiom ax-X0-S0-K0=S0-K0-X0-S0-S0-iI
  hypB L.ax-CX10-K0=K0-CS01-CS01 = axiom ax-CX10-K0=K0-CS01-CS01
  hypB L.ax-CX10-S0-K0=S0-K0-CX10-S1-CS01-CS01 = axiom ax-CX10-S0-K0=S0-K0-CX10-S1-CS01-CS01
  hypB L.ax-CX20-K0=K0-CS02-CS02 = axiom ax-CX20-K0=K0-CS02-CS02
  hypB L.ax-CX20-S0-K0=S0-K0-CX20-S2-CS02-CS02 = axiom ax-CX20-S0-K0=S0-K0-CX20-S2-CS02-CS02
  hypB L.ax-CCX0-K0=K0-CCZ = axiom ax-CCX0-K0=K0-CCZ
  hypB L.ax-CCX0-S0-K0=S0-K0-CCX0-CS12-CCZ = axiom ax-CCX0-S0-K0=S0-K0-CCX0-CS12-CCZ
  hypB L.ax-S0-S0-K0=K0-X0 = axiom ax-S0-S0-K0=K0-X0
  hypB L.ax-S1-K0=K0-S1 = axiom ax-S1-K0=K0-S1
  hypB L.ax-S1-S0-K0=S0-K0-S1 = axiom ax-S1-S0-K0=S0-K0-S1
  hypB L.ax-S2-K0=K0-S2 = axiom ax-S2-K0=K0-S2
  hypB L.ax-S2-S0-K0=S0-K0-S2 = axiom ax-S2-S0-K0=S0-K0-S2
  hypB L.ax-CS01-K0=K0-S0-CK10-CX10-S0-S0-S0-S1 = axiom ax-CS01-K0=K0-S0-CK10-CX10-S0-S0-S0-S1
  hypB L.ax-CS01-S0-K0=S0-K0-S0-CK10-CX10-S0-S0-S0-S1 = axiom ax-CS01-S0-K0=S0-K0-S0-CK10-CX10-S0-S0-S0-S1
  hypB L.ax-CS02-K0=K0-S0-CK20-CX20-S0-S0-S0-S2 = axiom ax-CS02-K0=K0-S0-CK20-CX20-S0-S0-S0-S2
  hypB L.ax-CS02-S0-K0=S0-K0-S0-CK20-CX20-S0-S0-S0-S2 = axiom ax-CS02-S0-K0=S0-K0-S0-CK20-CX20-S0-S0-S0-S2
  hypB L.ax-CS12-K0=K0-CS12 = axiom ax-CS12-K0=K0-CS12
  hypB L.ax-CS12-S0-K0=S0-K0-CS12 = axiom ax-CS12-S0-K0=S0-K0-CS12
  hypB L.ax-CCZ-K0=K0-CCX0 = axiom ax-CCZ-K0=K0-CCX0
  hypB L.ax-CCZ-S0-K0=S0-K0-CCX0 = axiom ax-CCZ-S0-K0=S0-K0-CCX0
  hypB L.ax-iI-S0-K0=S0-K0-iI = axiom ax-iI-S0-K0=S0-K0-iI
  hypB L.ax-X1-K0=K0-X1 = axiom ax-X1-K0=K0-X1
  hypB L.ax-X1-CK20=CK20-X1 = axiom ax-X1-CK20=CK20-X1
  hypB L.ax-X1-CX10=X0-CX10-X1 = axiom ax-X1-CX10=X0-CX10-X1
  hypB L.ax-X1-CX20=CX20-X1 = axiom ax-X1-CX20=CX20-X1
  hypB L.ax-X1-CCX0=CX20-CCX0-X1 = axiom ax-X1-CCX0=CX20-CCX0-X1
  hypB L.ax-X2-K0=K0-X2 = axiom ax-X2-K0=K0-X2
  hypB L.ax-X2-CK10=CK10-X2 = axiom ax-X2-CK10=CK10-X2
  hypB L.ax-X2-CX10=CX10-X2 = axiom ax-X2-CX10=CX10-X2
  hypB L.ax-X2-CX20=X0-CX20-X2 = axiom ax-X2-CX20=X0-CX20-X2
  hypB L.ax-X2-CCX0=CX10-CCX0-X2 = axiom ax-X2-CCX0=CX10-CCX0-X2
  hypB L.ax-CX12-K0=K0-CX12 = axiom ax-CX12-K0=K0-CX12
  hypB L.ax-CX12-CK10=CK10-CX12 = axiom ax-CX12-CK10=CK10-CX12
  hypB L.ax-CX12-X0=X0-CX12 = axiom ax-CX12-X0=X0-CX12
  hypB L.ax-CX12-CX10=CX10-CX12 = axiom ax-CX12-CX10=CX10-CX12
  hypB L.ax-CX12-CX20=CX10-CX20-CX12 = axiom ax-CX12-CX20=CX10-CX20-CX12
  hypB L.ax-CX12-CCX0=CX10-CCX0-CX12 = axiom ax-CX12-CCX0=CX10-CCX0-CX12
  hypB L.ax-CX21-K0=K0-CX21 = axiom ax-CX21-K0=K0-CX21
  hypB L.ax-CX21-CK20=CK20-CX21 = axiom ax-CX21-CK20=CK20-CX21
  hypB L.ax-CX21-CX10=CX10-CX20-CX21 = axiom ax-CX21-CX10=CX10-CX20-CX21
  hypB L.ax-CX21-CX20=CX20-CX21 = axiom ax-CX21-CX20=CX20-CX21
  hypB L.ax-CX21-CCX0=CX20-CCX0-CX21 = axiom ax-CX21-CCX0=CX20-CCX0-CX21
  hypB L.ax-Swap12-K0=K0-Swap12 = axiom ax-Swap12-K0=K0-Swap12
  hypB L.ax-Swap12-CK20=CK10-Swap12 = axiom ax-Swap12-CK20=CK10-Swap12
  hypB L.ax-Swap12-CK10=CK20-Swap12 = axiom ax-Swap12-CK10=CK20-Swap12
  hypB L.ax-Swap12-CCK'=CCK'-Swap12 = axiom ax-Swap12-CCK'=CCK'-Swap12
  hypB L.ax-Swap12-X0=X0-Swap12 = axiom ax-Swap12-X0=X0-Swap12
  hypB L.ax-Swap12-CX10=CX20-Swap12 = axiom ax-Swap12-CX10=CX20-Swap12
  hypB L.ax-Swap12-CX20=CX10-Swap12 = axiom ax-Swap12-CX20=CX10-Swap12
  hypB L.ax-Swap12-CCX0=CCX0-Swap12 = axiom ax-Swap12-CCX0=CCX0-Swap12
  hypB L.ax-CX20-CX10=CX10-CX20 = axiom ax-CX20-CX10=CX10-CX20
  hypB L.ax-Swap12-X1=X2-Swap12 = axiom ax-Swap12-X1=X2-Swap12
  hypB L.ax-Swap12-X2=X1-Swap12 = axiom ax-Swap12-X2=X1-Swap12
  hypB L.ax-Swap12-CX12=CX21-Swap12 = axiom ax-Swap12-CX12=CX21-Swap12
  hypB L.ax-Swap12-CX21=CX12-Swap12 = axiom ax-Swap12-CX21=CX12-Swap12
  hypB L.ax-CX12-X2=X2-CX12 = axiom ax-CX12-X2=X2-CX12
  hypB L.ax-CX12-X1=X1-X2-CX12 = axiom ax-CX12-X1=X1-X2-CX12
  hypB L.ax-CX12-CX21-CX12=Swap12 = axiom ax-CX12-CX21-CX12=Swap12
  hypB L.ax-CX21-CX12-CX21=Swap12 = axiom ax-CX21-CX12-CX21=Swap12
  hypB L.ax-CX12-Swap12=CX21-CX12 = axiom ax-CX12-Swap12=CX21-CX12
  hypB L.ax-CX21-Swap12=CX12-CX21 = axiom ax-CX21-Swap12=CX12-CX21
  hypB L.ax-Swap01-CCX2-CCX1-CCX0-Swap12-Swap01=X1-CCX0-CCX2-CCX1-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-Swap01-X1-CCX0-CCX1-CCX2=X2-CCX0-CCX2-CCX1-X1-X2-CX21-X0-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-Swap01-X1-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-Swap01-X2-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-X2-CX21-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX01-CCX2-CCX0-CX02-CCX1=X2-CCX0-CCX2-CCX1-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX01-X1-CCX0-CCX1-CCX2=CCX0-CX21-CCX2-CX01-X1-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX01-X1-CCX0-CCX2-CCX1=CX21-CCX0-CCX2-CX01-X1-CX21-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX01-X2-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX01-CX21-CCX0-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX21-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX01-CCX0-CX21-CCX2-CX01=X1-CCX0-CCX1-CCX2-X1-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX02-CCX1-CCX0-CX01-CCX2=X1-CCX0-CCX1-CCX2-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX02-X1-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX02-X1-CCX0-CCX2-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-X2-Swap12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX02-X2-CCX0-CCX2-CCX1=CCX0-CX12-CCX1-CX02-X2-CX10-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX02-CCX0-CX12-CCX1-CX02=X2-CCX0-CCX2-CCX1-X2-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX02-CCX0-Swap12-CCX1-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-Swap12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX1-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX1-CCX2-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX1-CCX2-CCX0-CX02-CCX1=X2-CCX0-CCX2-CCX1-X2-CX12-CX10-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX1-X1-CCX0-CCX1-CCX2=CX01-CCX2-CCX0-CX01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX1-X1-CCX0-CCX2-CCX1=X1-CCX0-CCX2-CCX1-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX1-X2-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1-X2-CX12-CX10-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX2-CX02-CCX1-CCX0-CX02=X2-CCX0-CCX2-CCX1-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX2-CCX1-CCX0-CX01-CCX2=X1-CCX0-CCX1-CCX2-X1-CX21-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX2-X1-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2-X1-CX21-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX2-X1-CCX0-CCX2-CCX1=CCX0-Swap12-CCX2-Swap01-X2-CX21-CX12-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX2-X2-CCX0-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX2-CCX0-Swap12-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-CX12-CX21-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-Swap01=Swap01-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01=CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01-CCX2=CCX2-CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01-CCX2-CCX0-CX01=CCX2-CX10-CCX1-X1-CX21-X0-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01-CX20-CCX2=CX20-CX21-CCX2-CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01-CCX0-CX02=CX10-Swap12-CCX2-Swap01-X1-X2-CX12-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX01-CCX0-CCX2-CX01=CX10-CCX2-CCX1-X2-CX21-CX12-X0-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX02=CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX02-CX01=CX02-CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX02-CCX1=CX02-CCX1-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX02-CCX1-CCX0-CX02=CX20-CCX1-CCX2-CX01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX02-CX10-CCX1=CX02-CX10-CCX1-X1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX02-CCX0-CX01=CX02-CCX0-CX01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1=CCX1-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CX01=CCX1-CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CX01-CCX2=CCX1-CCX2-CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CX02=CCX1-CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX2=CCX1-CCX2-CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX2-CX01=CCX1-CX01-CCX2-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX2-CX02=CCX1-CCX2-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX2-CCX0-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CX12-Swap01=CCX1-CX12-Swap01-X2-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-CX12-Swap01-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CX20-CCX2-CX02=CX20-CCX2-CCX1-X1-CX21 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX0-CX01-CCX2=CCX0-CX21-CCX2-CX01-X1-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX0-CX02=CCX1-CCX0-Swap12-Swap01-X2-Swap12-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX0-CX12-Swap01=CCX1-CX12-CCX0-Swap01-X1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-CX02-X1-Swap12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2=CCX2-CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-Swap01=CCX2-Swap01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CX01=CX01-CCX2-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CX02=CCX2-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CX02-CCX1=CCX2-CCX1-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CCX1=CCX2-CX02-CCX1-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CCX1-CX01=CCX2-CCX1-CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CCX1-CX02=CCX2-CCX1-CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CCX1-CCX0-Swap12-Swap01=X2-CCX0-CCX2-CCX1-X1-CX21-CX12-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CX10-CCX1=CX01-CCX2-CCX0-CX01-X1-CX21-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CCX0-CX01=CCX0-CX01-CCX2-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CCX0-CX02-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-X2-Swap12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX2-CCX0-CX12-Swap01=CCX0-CCX2-CX01-X1-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-X1-CCX0-CCX1-CCX2=CCX0-CCX1-CCX2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-X1-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-X2-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-X2-CX12-CX21-X0-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX12-Swap01=CX12-Swap01-X2-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX12-CX01-CCX0-Swap01=CX10-CX12-CCX1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX12-CCX1=CX12-CCX1-CX01-X1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX12-CCX1-CX01=CX12-CCX1-X1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-CX21-CX12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX12-CCX2-Swap01=CX12-CCX2-Swap01-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX12-CCX2-CCX0-Swap01=CCX0-CX12-CCX2-Swap01-X2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX12-CCX0-Swap01=CCX0-CX12-Swap01-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX21-CCX2-CX01=CX12-CCX1-CX02-X1-X2-CX12-CX21 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-X0-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX21-CCX0-CCX2-CX01=CCX0-CX12-CCX1-CX02-X1-X2-CX12-CX21 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-Swap12-Swap01=Swap12-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX10-CX02-CCX1=CX10-CCX1-CX02-X1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX10-CCX1=CX10-CCX1-X1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX10-CCX1-CX02=CX10-CX02-CCX1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX10-CCX1-CCX2-CX01=CX10-CCX2-CCX1-CX01-X1-X2-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX10-CCX2-CCX1=CX01-CCX0-CCX2-CX01-X1-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX10-CCX2-CCX1-CX01=CX10-CCX1-CCX2-CX01-X2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX10-CX12-CCX1=CX12-CX01-CCX0-Swap01-X1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX10-Swap12-CCX2-Swap01=CX01-CCX0-CX02-X1-CX12-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CX01-CCX2=CX20-CCX2-CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX1-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX1-CCX2-CX01=CX02-CCX1-CCX0-CX02-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX1-CCX2-CX02=CX20-CCX1-CCX2-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX2=CX20-CCX2-CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX2-Swap01=CX20-CCX2-Swap01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX2-CX01=CX20-CX01-CCX2-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX2-CX02=CX20-CCX2-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CCX2-CCX1-CX02=CX20-CCX2-CCX1-CX01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CX20-CX21-CCX2-CX01=CX01-CX20-CCX2-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-Swap01=CCX0-Swap01-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CX01=CCX0-CX01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CX01-CCX2=CCX2-CCX0-CX01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CX02=CCX0-Swap12-Swap01-X2-Swap12-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CX02-CCX1=CCX0-Swap12-CCX2-Swap01-X2-CX21-CX12-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CCX1-CX02=CCX0-CCX1-CX12-Swap01-X2-Swap12-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX12-X0-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CCX1-CX12-Swap01=CCX0-CCX1-CX02-X1-Swap12-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CCX2-CX01=CCX2-CCX0-CX12-Swap01-X2-CX21-CX12-X0-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CX12-Swap01=CX12-CCX0-Swap01-X1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CX12-CCX1-CX02=CX21-CCX0-CCX2-CX01-X1-CX21-CX12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CX12-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-X1-X2-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-CX21-CCX2-CX01=CCX1-CCX0-CX01-CCX2-X1-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-Swap12-Swap01=CCX0-CX02-X1-Swap12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-X1-Swap12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X1-CCX0-Swap12-CCX2-Swap01=CCX0-CX02-CCX1-X1-CX12-CX21-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-Swap01=Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01=CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01-CCX2=CX01-CCX2-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-CX01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01-CCX2-CCX0-CX01=CX01-CCX2-CCX0-Swap01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01-CX20-CCX2=CX01-CX20-CCX2-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01-CCX0-Swap01=CX10-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01-CCX0-CX02=CX01-CCX0-CX02-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01-CCX0-CCX2-Swap01=CCX2-CX10-CCX1-X2-CX12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX01-CCX0-CCX2-CX01=CX10-CCX1-CCX2-CX01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX02=CX02-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX02-CX01=CX02-CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX02-CCX1=CCX1-CX02-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-X1-X2-CX21-CX12-X0-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX02-CX10-CCX1=CX20-CCX1-CCX2-Swap01-X1-Swap12-X0-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX02-CCX0-CX01=CX20-CCX2-Swap01-X1-X2-CX21-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1=CCX1-CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CX01=CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CX01-CCX2=CCX1-CCX2-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CX02=CX02-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX2=CCX1-CX01-CCX2-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX2-CX01=CCX1-CCX2-CX02-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX2-CX02=CCX1-CCX2-CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX2-CCX0-Swap01=X1-CCX0-CCX1-CCX2-X2-CX21-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CX12-Swap01=CCX1-CX12-Swap01-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX12-Swap01-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX0-CX02=CCX0-CX02-CCX1-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX02-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2=CCX2-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-Swap01=CCX2-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CX01=CCX2-CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CX02=CCX2-CX02-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CX02-CCX1=CCX2-CCX1-CX02-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CCX1=CCX2-CCX1-CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CCX1-CX01=CCX2-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CCX1-CX02=CCX2-CX02-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CCX1-CCX0-Swap12-Swap01=X1-CCX0-CCX2-CCX1-X1-CX21-CX12-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CX10-CCX1=CX01-CCX0-CCX2-Swap01-X2-CX12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CCX0-Swap01=CCX2-CCX0-CX01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CCX0-CX01=CCX2-CCX0-Swap01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CCX0-CX02-CCX1=CCX0-CX12-CCX1-CX02-X2-CX10-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX2-CCX0-CX12-Swap01=CX12-CCX2-CCX0-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-X1-CCX0-CCX1-CCX2=CCX1-CCX2-CCX0-Swap01-X1-X2-CX21-X0-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-X1-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-X2-CX12-CX21-X0-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-X2-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX12-Swap01=CX12-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX12-CX01-CCX0-Swap01=CX10-CX12-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX12-CCX1=CX12-CCX1-CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX12-CCX1-CX01=CX12-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-X2-CX21-CX12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX12-CCX2-Swap01=CX12-CCX2-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-CX12-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX12-CCX0-Swap01=CCX0-CX12-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX21-CCX2-CX01=CX12-CCX1-CX02-X2-CX12-CX21 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX21-CCX0-CCX2-Swap01=CCX0-CX21-CCX2-CX01-X1-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX1-CCX2-Swap01-CX12-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-Swap12-Swap01=Swap12-Swap01-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX10-CX02-CCX1=CX10-CCX1-CX02-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX10-CCX1=CX01-CCX0-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX10-CCX1-CX02=CX10-CX02-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX10-CCX1-CCX2-CX01=CX01-CCX0-CCX2-CX01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX10-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX10-CCX2-CCX1-CX01=CX10-CCX2-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX10-CX12-CCX1=CX12-CX01-CCX0-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CX01-CCX2=CX20-CCX2-CX01-X1-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX01-X2-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX1-CCX2-Swap01=CX02-CX10-CCX1-X2-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX1-CCX2-CX01=CCX1-CX20-CCX2-CX02-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX1-CCX2-CX02=CX20-CCX2-CCX1-CX02-X1-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX2=CX20-CCX2-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX2-Swap01=CX02-CCX0-CX01-X2-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX2-CX01=CX20-CX01-CCX2-X1-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX2-CX02=CX20-CCX2-CX02-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CX21-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-X1-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX02-X1-X2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-Swap01=CCX0-CX01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CX01=CCX0-Swap01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CX01-CCX2=CCX0-CCX2-Swap01-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CX02=CCX0-CX02-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CX02-CCX1=CCX1-CCX0-CX02-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CCX1-CX02=CCX1-CCX0-CX12-Swap01-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CCX1-CCX2=CCX1-CCX0-CCX2-Swap01-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CX01-CCX2-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CCX1-CX12-Swap01=CCX1-CX12-CCX0-Swap01-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CCX2-Swap01=CCX0-CX01-CCX2-X2-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CCX2-CX01=CCX0-CX12-CCX2-Swap01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CX12-Swap01=CX12-CCX0-Swap01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CX12-CCX1-CX02=CCX2-CCX0-CX02-CCX1-X2-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-CX01-X2-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-CX21-CCX2-CX01=CX21-CCX0-CCX2-Swap01-X1-CX12-X0-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-Swap12-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX12-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X2-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX12-CX02-CCX1-CCX0-CX02=X2-CCX0-CCX2-CCX1-X2-CX12-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX12-X1-CCX0-CCX1-CCX2=CX20-CCX2-CCX1-CX02-X1-X2-CX12-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX12-X1-CCX0-CCX2-CCX1=CX20-CCX1-CCX2-CX01-X1-X2-CX12-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX12-X2-CCX0-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX12-CX20-CCX1-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX12-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX12-CX20-CCX2-CCX1-CX02=X1-CCX0-CCX1-CCX2-X1-CX12-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX21-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX1-CCX2-X1-CX21-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX21-CX01-CCX0-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX21-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX21-X1-CCX0-CCX1-CCX2=CX01-CCX2-CCX0-CX01-X1-CX21-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX21-X1-CCX0-CCX2-CCX1=CX01-CCX0-CCX2-CX01-X1-CX21-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX21-X2-CCX0-CCX2-CCX1=CX10-CCX1-CCX2-CX01-X1-X2-CX21-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX21-CX10-CCX1-CCX2-CX01=X2-CCX0-CCX2-CCX1-X2-CX21-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-Swap12-CCX1-CCX0-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-CX12-CX21-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-Swap12-X1-CCX0-CCX1-CCX2=X2-CCX0-CCX2-CCX1-Swap12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-Swap12-X1-CCX0-CCX2-CCX1=CCX1-CCX0-CCX2-Swap01-X2-CX21-CX12-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-Swap12-X2-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-Swap12 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-Swap01=Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01=CX01-X1-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01-CCX2=CCX2-CX01-X1-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01-CCX2-CCX0-Swap01=CX10-CCX1-CCX2-CX01-X1-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01-CCX2-CCX0-CX01=CX01-CCX0-CCX2-CX01-X2-CX12-CX21-X0-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01-CX20-CCX2=CX20-CX21-CCX2-CX01-X1-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01-CCX0-Swap01=CX01-CCX0-Swap01-X1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01-CCX0-CX02=CX10-Swap12-CCX2-Swap01-X1-CX12-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01-CCX0-CCX2-Swap01=CX10-CCX2-CCX1-CX01-X1-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX01-CCX0-CCX2-CX01=CX01-CCX2-CCX0-CX01-X1-X2-CX21-CX12-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX02=CX02-X2-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX02-CX01=CX02-CX01-X1-X2-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX02-CCX1=CCX1-CX02-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX01-X1-CX21-CX12-X0-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX02-CX10-CCX1=CX20-CCX1-CCX2-Swap01-X1-CX21-CX12-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX02-CCX0-CX01=CX20-CCX2-Swap01-X1-CX21-CX12-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1=CCX1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CX01=CCX1-CX01-X1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CX01-CCX2=CCX2-CCX1-CX01-X1-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CX02=CX02-CCX1-X1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX2=CCX2-CCX1-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX2-CX01=CCX2-CCX1-CX02-X2-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX2-CX02=CCX2-CX02-CCX1-X1-X2-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX2-CCX0-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CX12-Swap01=Swap12-CCX2-Swap01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX02-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX0-CX01-CCX2=CX21-CCX0-CCX2-CX01-X1-CX12-X0-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX0-CX02=CCX1-CCX0-CX12-Swap01-X1-Swap12-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX0-CCX2-Swap01=X2-CCX0-CCX2-CCX1-X1-X2-CX21-X0-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX02-X2-Swap12-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX1-CCX0-Swap12-Swap01=CCX1-CX12-CCX0-Swap01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2=CCX2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-Swap01=CX12-CCX2-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CX01=CX01-CCX2-X1-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CX02=CCX2-CX02-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CX02-CCX1=CCX1-CCX2-CX02-X2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CCX1=CCX1-CCX2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CCX1-CX01=CCX1-CX01-CCX2-X1-X2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CCX1-CX02=CCX1-CCX2-CX01-X1-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX2-CCX0-Swap01-X1-CX21-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CX10-CCX1=CX10-CCX2-CCX1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CCX0-Swap01=CX12-CCX2-CCX0-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CCX0-CX01=CCX2-CCX0-CX12-Swap01-X1-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CCX0-CX02-CCX1=CX21-CCX0-CCX2-Swap01-X1-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX01-X1-X0-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-X1-CCX0-CCX1-CCX2=X1-CCX0-CCX2-CCX1-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-X1-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-X2-CCX0-CCX2-CCX1=CCX1-CCX0-CCX2-Swap01-X2-CX21-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX12-Swap01=CX12-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX12-CX01-CCX0-Swap01=CX12-CX01-CCX0-Swap01-X1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX12-CCX1=CX12-CCX1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX12-CCX1-CX01=CX12-CCX1-CX01-X1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-Swap12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX12-CCX2-Swap01=CCX2-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX12-CCX0-Swap01=CX12-CCX0-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX21-CCX2-CX01=CX12-CCX1-CX02-X2-Swap12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX21-CCX0-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-X1-X2-CX12-CX21-X0-CX10-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX21-CCX0-CCX2-CX01=CCX1-CCX0-CX01-CCX2-X1-X2-CX12-X0-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-Swap12-Swap01=Swap12-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-Swap12-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-Swap12-CCX2-Swap01=CCX1-CX12-Swap01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX10-CX02-CCX1=CX10-CCX1-CX02-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX10-CCX1=CX10-CCX1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX10-CCX1-CX02=CX10-CX02-CCX1-X1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX10-CCX1-CCX2-CX01=CX01-CCX2-CCX0-Swap01-X2-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX10-CCX2-CCX1=CCX2-CX10-CCX1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-Swap01-X1-X2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX10-CX12-CCX1=CX10-CX12-CCX1-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX10-Swap12-CCX2-Swap01=CX01-CCX0-CX02-X1-X2-CX12-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CX01-CCX2=CX20-CCX2-CX01-X1-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX1-CCX2-Swap01=CX02-CX10-CCX1-X1-X2-CX12-CX21-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX02-X2-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX1-CCX2-CX02=CCX1-CX20-CCX2-CX02-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX2=CX20-CCX2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX2-Swap01=CX02-CCX0-CX01-X1-X2-CX12-CX21-X0-CX10-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX2-CX01=CX20-CX01-CCX2-X1-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX2-CX02=CX20-CCX2-CX02-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX2-CCX1-CX01=CX02-CCX1-CCX0-CX02-X1-X2-CX12-CX21-CX10 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX01-X1-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CX20-CX21-CCX2-CX01=CX01-CX20-CCX2-X1-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-Swap01=CCX0-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CX01=CCX0-CX01-X1-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CX01-CCX2=CCX0-CCX2-CX01-X1-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CX02=CCX0-CX02-X2-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CX02-CCX1=CCX0-CCX1-CX02-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CCX1-CX02=CCX0-CX02-CCX1-X1-X2-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CCX1-CCX2=CCX0-CCX2-CCX1-CX21-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CCX1-CCX2-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CCX1-CX12-Swap01=CCX0-Swap12-CCX2-Swap01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CCX2-Swap01=CCX0-CX12-CCX2-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CCX2-CX01=CCX0-CX01-CCX2-X1-X2-CX12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CX12-Swap01=CCX0-CX12-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CX12-CCX1-CX02=CCX0-CX21-CCX2-CX01-X1-Swap12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-CX21-CCX2-CX01=CCX0-CX12-CCX1-CX02-X2-Swap12-X0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-Swap12-CCX1-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-X0-CCX0-Swap12-CCX2-Swap01=CCX0-CCX1-CX12-Swap01-X1-CX20 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX10-CCX1-CX20-CCX2-CX02=X1-CCX0-CCX2-CCX1-X1-CX21-CX10-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX10-X1-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX10-X1-CCX0-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX10-X2-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX01-X2-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX10-CX20-CCX1-CCX2-CX02=X1-CCX0-CCX1-CCX2-X1-CX10-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX10-CX20-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX20-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX2-CCX1-X1-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX20-CX01-CCX0-CCX2-CX01=X1-CCX0-CCX1-CCX2-X1-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX20-X1-CCX0-CCX1-CCX2=CX01-CCX0-CCX2-CX01-X1-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX20-X1-CCX0-CCX2-CCX1=CX01-CCX2-CCX0-CX01-X1-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX20-X2-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2-X0-CX10-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CX20-CX10-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2-CX20-CCX0 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX0-CCX1-CX20-CCX2-CX02=X1-CCX0-CCX2-CCX1-X1-CX21 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX0-X1-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX0-X1-CCX0-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX0-X2-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX0-CX10-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2 = ListNF.listnfeq' nf-p auto
  hypB L.ax-CCX0-CX20-CCX1-CCX2-CX02=X1-CCX0-CCX1-CCX2-X1 = ListNF.listnfeq' nf-p auto

  hypB L.ax-Swap01-CX01=CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX01-CCX2=CX01-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX01-CCX2-CCX0-Swap01=CX10-CCX2-CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX01-CCX2-CCX0-CX01=CX10-CCX2-CCX1-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX01-CX20-CCX2=CX01-CX20-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX01-CCX0-Swap01=CX10-CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX01-CCX0-CX02=CX01-CCX0-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX01-CCX0-CCX2-Swap01=CCX2-CX10-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX01-CCX0-CCX2-CX01=CX10-CCX1-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX02=CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX02-CX01=CX02-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX02-CCX1=CX12-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CX01-CCX2-CX12-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX02-CX10-CCX1=CX12-CX01-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX02-CCX0-CX01=CX12-CCX1-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1=CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX1-CX01=CCX0-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX1-CX01-CCX2=CCX0-CX01-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CX02=CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CCX2=CCX0-CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX1-CCX2-Swap01=CX20-CCX2-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CCX2-CX01=CCX0-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX1-CCX2-CX02=CCX0-CX12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CCX2-CCX0-Swap01=CCX0-CCX2-CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX1-CX12-Swap01=CCX0-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CX12-CCX0-Swap01=CCX0-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CCX0-CX01-CCX2=CX02-CCX1-CCX0-CX02-CX12-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CCX0-CX02=CCX0-CCX1-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX2=CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX2-Swap01=CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX2-CX01=CCX2-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX2-CX02=CX12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX2-CX02-CCX1=CX12-CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX2-CCX1=CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX2-CCX1-CX01=CCX2-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX2-CCX1-CX02=CCX2-CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX2-CX10-CCX1=CX01-CCX0-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX2-CCX0-Swap01=CCX2-CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX2-CCX0-CX01=CCX2-CCX1-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX2-CCX0-CX02-CCX1=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX2-CCX0-CX12-Swap01=CCX2-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX12-Swap01=CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX12-CX01-CCX0-Swap01=CX02-CX10-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX12-CCX1=CX20-CCX2-Swap01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX12-CCX1-CX01=CX02-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX12-CCX1-CX02=CX20-CX01-CCX2-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX12-CCX2-Swap01=CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX12-CCX2-CCX0-Swap01=CCX2-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX12-CCX0-Swap01=CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX21-CCX2-CX01=CX20-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX21-CCX0-CCX2-Swap01=CX20-CCX1-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX21-CCX0-CCX2-CX01=CX20-CCX1-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-Swap12-Swap01=Swap12-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-Swap12-CCX1-CCX2-Swap01=CX20-CCX2-CX02-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-Swap12-CCX2-Swap01=CCX0-Swap12-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX10-CX02-CCX1=CX10-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX10-CCX1=CX01-CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX10-CCX1-CX02=CX10-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX10-CCX1-CCX2-CX01=CX01-CCX0-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX10-CCX2-CCX1=CX01-CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX10-CCX2-CCX1-CX01=CX01-CCX2-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CX10-CX12-CCX1=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CX01-CCX2=CX12-CCX1-CX02-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX1-CCX2=CX21-CCX0-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX1-CCX2-Swap01=CX10-CX12-CCX1-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX1-CCX2-CX01=CX21-CCX0-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX1-CCX2-CX02=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX2=CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX2-Swap01=CX12-CCX1-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX2-CX01=CX21-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX2-CX02=Swap12-CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX2-CCX1=CCX0-CCX1-CCX2-Swap01-CX21-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX2-CCX1-CX01=CCX0-CX21-CCX2-CX01-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CCX2-CCX1-CX02=CCX0-CX12-CCX1-CX02-CX21-CX12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-Swap01=CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX0-CX01=CCX1-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX0-CX01-CCX2=CCX1-CX01-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CX02=CCX1-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CX02-CCX1=CCX1-CX12-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CCX1-CX02=CCX1-CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CCX1-CCX2=CCX1-CCX0-CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX0-CCX1-CCX2-Swap01=CX20-CCX2-CCX1-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CCX2-Swap01=CCX1-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX0-CCX2-CX01=CCX1-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX0-CCX2-CCX1=CCX1-CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-Swap01-CCX0-CX12-Swap01=CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CX12-CCX1-CX02=CX20-CCX2-CCX1-CX02-CX12-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CX12-CCX2-Swap01=CCX1-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-CX21-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-Swap12-Swap01=Swap12-CCX2-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap01-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-Swap01=Swap01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CX01-CCX2=CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CX01-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CX01-CCX2-CCX0-CX01=CCX2-CCX0-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CX01-CX20-CCX2=CX20-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX01-CCX0-Swap01=CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CX01-CCX0-CX02=CCX0-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX01-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CX01-CCX0-CCX2-CX01=CCX0-CCX2-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CX02=CX02-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX02-CX01=CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX02-CCX1=CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1=CCX1-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CCX1-CX01=CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CCX1-CX01-CCX2=CCX1-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CCX1-CX02=CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CCX2=CCX1-CX01-CCX2 = ListNF.listnfeq' nf-s6 auto


  hypB L.ax-CX01-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CCX2-CX01=CCX1-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CCX2-CX02=CCX1-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CCX2-CCX0-Swap01=CX21-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CCX1-CCX0-CX02=CCX0-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-Swap01=CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-CX01=CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-CX02=CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-CX02-CCX1=CCX2-CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-CCX1=CCX2-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-CCX1-CX01=CCX2-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-CCX1-CX02=CCX2-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX2-CX10-CCX1=CCX0-CX01-CCX2-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CCX2-CCX0-CX12-Swap01=CX10-CCX2-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX12-Swap01=CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX12-CX01-CCX0-Swap01=CX20-CCX2-CX01-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX12-CCX1=CX12-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX12-CCX1-CX01=CX21-CCX2-CX01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX12-CCX1-CX02=CX12-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX12-CCX2-CCX0-Swap01=CX10-CCX2-CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX12-CCX0-Swap01=CX10-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX21-CCX2-CX01=CX12-CCX1-CX01-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX21-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-Swap12-Swap01=Swap12-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX10-CX02-CCX1=CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX10-CCX1=CCX0-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CX10-CCX1-CX02=CX12-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX10-CCX1-CCX2-CX01=CCX0-CX12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX10-CCX2-CCX1=CCX2-CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX10-CCX2-CCX1-CX01=CX12-CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX10-CX12-CCX1=CX20-CX01-CCX2-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX10-Swap12-CCX2-Swap01=CCX0-Swap12-Swap01-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CX01-CCX2=CX10-CX12-CCX1-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX02-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX1-CCX2-Swap01=CX20-CCX2-Swap01-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX1-CCX2-CX01=CCX1-CX20-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX1-CCX2-CX02=CX20-CCX2-CCX1-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX2-CX01=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX2-CX02=CX20-CX21-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX2-CCX1=CX02-CCX1-CCX0-CX02-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX02-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CX20-CX21-CCX2-CX01=CX20-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-CX01=CX10-CCX1-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CCX0-CX01-CCX2=CCX2-CX10-CCX1-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CCX0-CX02-CCX1=CCX1-CCX0-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-CCX1-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX01-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-CCX2-CCX1=CCX0-CX12-CCX1-CX02-CX12-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-CX12-Swap01=CX10-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-CX12-CCX1-CX02=CCX0-CCX2-CCX1-CX12-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-CX12-CCX2-Swap01=CX10-CCX1-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-Swap12-Swap01=CX10-Swap12-CCX2-Swap01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX01-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-Swap01=Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX01-CCX2=CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX01-CCX2-CCX0-CX01=CCX2-CX10-CCX1-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX01-CX20-CCX2=CX01-CCX0-CX02-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX01-CCX0-Swap01=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX01-CCX0-CX02=CX01-CX20-CCX2-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX01-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX01-CCX0-CCX2-CX01=CX10-CCX2-CCX1-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX02-CX01=CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX02-CCX1=CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX02-CX10-CCX1=CX10-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX02-CCX0-CX01=CCX0-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CX01=CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CX01-CCX2=CCX1-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CX02=CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CCX2=CCX1-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CCX2-CX01=CCX1-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CCX2-CX02=CCX1-CX01-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CX12-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX2-Swap01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CCX0-CX12-Swap01=CX20-CCX1-CCX2-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX1-CCX0-Swap12-Swap01=CX20-CCX1-CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2=CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-Swap01=CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CX01=CX01-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CX02=CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CX02-CCX1=CCX2-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CCX1=CCX2-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CCX1-CX01=CCX2-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CCX1-CX02=CCX2-CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CCX1-CCX0-Swap12-Swap01=CX21-CCX0-CCX2-CX01-CX12-CX21-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CX10-CCX1=CX01-CCX2-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CCX0-CX01=CCX0-CX01-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CCX0-CX02-CCX1=CCX0-CCX2-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX2-CCX0-CX12-Swap01=CCX0-CX12-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX12-Swap01=CX12-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX12-CX01-CCX0-Swap01=CX10-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX12-CCX1=CX21-CCX2-CX01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX12-CCX1-CX01=CX12-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX12-CCX1-CX02=CX12-CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX12-CCX2-CCX0-Swap01=CCX0-CCX2-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX12-CCX0-Swap01=CX20-CCX2-CX01-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto

  hypB L.ax-CX02-CX21-CCX2-CX01=CX12-CCX1-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX21-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX21-CCX0-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX21-CX12-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-Swap12-Swap01=Swap12-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX10-CX02-CCX1=CX10-CX12-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX10-CCX1-CX02=CX12-CX01-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX10-CCX1-CCX2-CX01=CX10-CCX2-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX10-CCX2-CCX1=CX10-CCX1-CCX2-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX10-CX12-CCX1=CX10-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX10-Swap12-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CX01-CCX2=CCX0-CX12-Swap01-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX1-CCX2=CCX1-CCX0-CX12-Swap01-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX1-CCX2-Swap01=CX01-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX1-CCX2-CX01=CCX1-CCX0-Swap12-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX1-CCX2-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX2=CCX0-CX02-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX2-Swap01=CCX0-Swap01-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX2-CX01=CX12-CCX0-Swap01-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX2-CX02=CCX0-Swap12-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX2-CCX1=CCX0-CX02-CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX2-CCX1-CX01=CCX0-CCX1-CX02-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CCX2-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CX20-CX21-CCX2-CX01=CX10-Swap12-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-Swap01=CX20-CCX2-Swap01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CX01-CCX2=CCX2-CCX0-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CX02=CX20-CCX2-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CX02-CCX1=CX20-CCX2-CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CCX1-CX02=CX20-CCX2-CCX1-CX01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CCX1-CCX2=CCX0-CX21-CCX2-CX01-CX21-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CCX1-CX12-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CCX2-CX01=CX12-CCX2-CCX0-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CX12-Swap01=CX20-CX01-CCX2-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CX12-CCX2-Swap01=CCX2-CCX0-CX12-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-CX21-CCX2-CX01=CCX0-CCX1-CCX2-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-Swap12-Swap01=CX20-CCX2-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX02-CCX0-Swap12-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-Swap01=Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX01-CCX2-CCX0-Swap01=CX21-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX01-CX20-CCX2=CX02-CCX1-CCX0-CX02-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX01-CCX0-Swap01=CCX0-Swap01-CX10-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CX01-CCX0-CX02=CCX0-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX01-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX01-CCX0-CCX2-CX01=CX01-CCX0-CCX2-CX01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CX02-CX01=CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX02-CCX1=CX02-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX02-CCX1-CCX0-CX02=CX01-CX20-CCX2-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX1-CX01=CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX1-CX01-CCX2=CX01-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX1-CX02=CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX1-CCX2-Swap01=CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX1-CCX2-CX01=CCX2-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX1-CCX2-CX02=CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX1-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX1-CX12-Swap01=CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX1-CX12-CCX0-Swap01=CX12-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX1-CX20-CCX2-CX02=CX20-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX1-CCX0-CX01-CCX2=CCX0-CX01-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX1-CCX0-CX02=CCX0-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX1-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX1-CCX0-CX12-Swap01=CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX2-CX02-CCX1=CX12-CCX1-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX2-CCX1=CX12-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX2-CCX1-CX01=CX21-CCX2-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX2-CCX1-CX02=CX12-CCX1-CX02-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX2-CX10-CCX1=CCX0-CCX1-CCX2-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX2-CCX0-CX01=CCX0-CX21-CCX2-CX01-CX21-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX12-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX12-CX01-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX12-CCX1=CCX2-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX12-CCX1-CX01=CCX2-CX02-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX12-CCX1-CX02=CCX2-CCX1-CX02-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX12-CCX2-CCX0-Swap01=CX10-CCX2-CCX1-CX01-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX21-CCX2-CX01=CCX2-CCX1-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX21-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX21-CCX0-CCX2-CX01=CX21-CCX0-CCX2-CX01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-Swap12-Swap01=Swap12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-Swap12-CCX2-Swap01=Swap12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX10-CX02-CCX1=CCX0-CCX1-CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX10-CCX1=CX10-CCX1-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CX10-CCX1-CX02=CCX0-CCX1-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX10-CCX1-CCX2-CX01=CCX0-CX12-CCX2-Swap01-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX10-CCX2-CCX1=CX10-CCX2-CCX1-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CX10-CCX2-CCX1-CX01=CX12-CCX2-CCX0-Swap01-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX10-CX12-CCX1=CX20-CCX1-CCX2-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX10-Swap12-CCX2-Swap01=CCX0-Swap12-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CX01-CCX2=CX20-CCX2-CCX1-CX02-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX1-CCX2=CX10-CX12-CCX1-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX1-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX1-CCX2-CX01=CX20-CX21-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX1-CCX2-CX02=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX2=CX20-CCX2-CCX1-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX2-Swap01=CX20-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX2-CCX1=CX20-CCX2-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CCX2-CCX1-CX01=CX20-CCX2-CX01-CX21 = ListNF.listnfeq' nf-s7 auto

  hypB L.ax-CCX1-CX20-CCX2-CCX1-CX02=CX20-CX01-CCX2-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CX20-CX21-CCX2-CX01=CX20-CCX1-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-Swap01=CX01-CCX0-Swap01-CX10-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX0-CX01=CCX0-CX01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX0-CX02-CCX1=CX01-CCX0-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-CCX1-CX02=CX10-CCX1-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-CCX1-CCX2=CCX2-CX10-CCX1-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX0-CCX1-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-CCX1-CX12-Swap01=CX10-CX02-CCX1-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX1-CCX0-CX12-CCX1-CX02=CCX0-CX12-CCX1-CX02-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-CX12-CCX2-Swap01=CX10-CCX1-CCX2-CX01-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX1-CCX0-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX01-CCX2=CX02-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX01-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX01-CCX2-CCX0-CX01=CX02-CX10-CCX1-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX01-CX20-CCX2=CX01-CCX0-CX02-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX01-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX01-CCX0-CX02=CX01-CX20-CCX2-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX01-CCX0-CCX2-Swap01=CX01-CCX0-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX01-CCX0-CCX2-CX01=CX10-CCX1-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX02-CX01=CX01-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX02-CX10-CCX1=CX01-CCX2-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX02-CCX0-CX01=CCX0-CX01-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CX01-CCX2=CX12-CCX1-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CCX2=CX12-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX1-CCX2-CX01=CX21-CCX2-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CCX2-CX02=CX12-CCX1-CX02-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CX12-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX1-CCX2-Swap01-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CCX0-CX02=CCX0-CX12-CCX1-CX02-CX12-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX1-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX2-Swap01=Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX2-CX02=CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX2-CX02-CCX1=CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX2-CCX1=CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX2-CCX1-CX01=CCX1-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX2-CCX1-CX02=CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-Swap12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX2-CX10-CCX1=CX10-CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX2-CCX0-Swap01=CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX2-CCX0-CX01=CCX0-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX2-CCX0-CX02-CCX1=CCX0-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX2-CCX0-CX12-Swap01=CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX12-Swap01=CX12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX12-CX01-CCX0-Swap01=CX10-CCX2-CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX12-CCX1=CCX1-CCX2-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX12-CCX1-CX01=CCX1-CX01-CCX2-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX12-CCX1-CX02=CCX1-CCX2-CX02-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX12-CCX2-Swap01=CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX12-CCX2-CCX0-Swap01=CX12-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX12-CCX0-Swap01=CX12-CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX21-CCX2-CX01=CCX1-CCX2-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX21-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX21-CCX0-CCX2-CX01=CX20-CCX1-CCX2-CX01-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-Swap12-Swap01=Swap12-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-Swap12-CCX1-CCX2-Swap01=Swap12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-Swap12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX10-CX02-CCX1=CX10-CCX1-CCX2-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX10-CCX1-CX02=CX01-CCX0-CCX2-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX10-CCX1-CCX2-CX01=CX10-CX02-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX10-CCX2-CCX1=CX10-CX12-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX10-CCX2-CCX1-CX01=CX12-CX01-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX10-CX12-CCX1=CX10-CCX2-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CX01-CCX2=CCX0-CX12-CCX2-Swap01-CX21-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX1-CCX2=CX20-CCX1-CCX2-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX1-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX1-CCX2-CX01=CX21-CCX0-CCX2-CX01-CX21-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX1-CCX2-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX2=CX20-CCX2-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX2-Swap01=CCX0-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX2-CX01=CCX0-CCX2-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX2-CX02=CCX0-Swap12-Swap01-Swap12-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX2-CCX1=CCX0-CCX2-CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CCX2-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CX01-CCX2=CX02-CCX0-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CX02=CCX0-CX02-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CCX1-CX02=CCX0-CCX1-CX02-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CCX1-CCX2=CCX0-CCX1-CCX2-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX2-CCX0-CCX1-CX12-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CCX2-Swap01=CX20-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CCX2-CX01=CX20-CCX2-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CX12-CCX2-Swap01=CX20-CX01-CCX2-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-CX21-CCX2-CX01=CCX0-CX21-CCX2-CX01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-Swap12-Swap01=CX20-CCX2-CX02-Swap12-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX2-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CX20-CCX2-CX02-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX01=CX02-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX01-CCX2=CCX2-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX01-CCX2-CCX0-CX01=CX10-CCX1-CCX2-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX01-CX20-CCX2=CX01-CCX0-CX02-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX01-CCX0-CX02=CX01-CX20-CCX2-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX01-CCX0-CCX2-Swap01=CX10-CCX2-CCX1-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX01-CCX0-CCX2-CX01=CX01-CCX2-CCX0-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto

  hypB L.ax-CX12-CX02=CX02-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX02-CX01=CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX02-CCX1=CX21-CCX2-CX01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX02-CX10-CCX1=CX10-CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX02-CCX0-CX01=CX20-CX01-CCX2-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CX01-CCX2=CCX2-CCX1-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX2=CCX2-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX2-Swap01=CCX1-CX12-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX2-CX01=CCX2-CX02-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX2-CX02=CCX2-CCX1-CX02-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CX12-Swap01=CCX1-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CX20-CCX2-CX02=CCX2-CCX1-CCX0-Swap12-Swap01-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CX12-Swap01-CX12-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX0-CX02=CCX0-CX12-CCX1-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX0-CCX2-Swap01=CX20-CCX2-CCX1-CX01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX0-CX12-Swap01=CCX0-CX21-CCX2-CX01-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2=CCX2-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CX01=CX01-CCX2-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CX02=CCX2-CX02-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CX02-CCX1=CCX1-CCX2-CX01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CCX1=CCX1-CCX2-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CCX1-CX01=CCX1-CX01-CCX2-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CCX1-CX02=CCX1-CCX2-CX02-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CX20-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CX10-CCX1=CX10-CCX2-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CCX0-CX01=CCX2-CCX0-CX12-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CCX0-CX02-CCX1=CCX0-CX02-CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX12-Swap01=Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX12-CX01-CCX0-Swap01=CX01-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX12-CCX1=CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX12-CCX1-CX01=CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX12-CCX1-CX02=CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX12-CCX2-Swap01=CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX12-CCX0-Swap01=CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX21-CCX2-CX01=CX02-CCX1-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CX02-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-Swap12-Swap01=Swap12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-Swap12-CCX1-CCX2-Swap01=Swap12-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-Swap12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX10-CX02-CCX1=CX02-CX10-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX10-CCX1=CX10-CX12-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX10-CCX1-CX02=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX10-CCX1-CCX2-CX01=CX01-CCX2-CCX0-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX10-CCX2-CCX1=CCX2-CX10-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-Swap01-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX10-CX12-CCX1=CX10-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX10-Swap12-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CX01-CCX2=CX02-CCX0-CX01-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX1-CCX2=CCX0-CCX1-CCX2-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX1-CCX2-Swap01=CX10-CCX1-CX02-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX1-CCX2-CX02=CCX1-CCX2-CCX0-Swap01-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX2=CX20-CCX2-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX2-Swap01=CX20-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX2-CX01=CX20-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX2-CX02=CX20-CCX2-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX2-CCX1=CCX0-CCX2-CCX1-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CCX2-CCX1-CX01=CCX1-CCX0-CCX2-Swap01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CX20-CX21-CCX2-CX01=CX10-Swap12-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CX01=CCX0-CX12-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CX01-CCX2=CCX0-CX12-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CX02=CCX0-CX02-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CX02-CCX1=CCX2-CCX0-CX02-CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CCX1-CX02=CX21-CCX0-CCX2-Swap01-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CCX1-CCX2-Swap01=CCX1-CX12-CCX0-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX01-CCX2-CX12-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CCX2-Swap01=CCX0-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CCX2-CX01=CCX0-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CX12-Swap01=CCX0-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CX12-CCX2-Swap01=CCX0-CX01-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-CX21-CCX2-CX01=CCX1-CCX0-CX12-Swap01-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX12-CCX0-Swap12-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-Swap01=Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX01=CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX01-CCX2=CX12-CCX1-CX02-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX01-CCX2-CCX0-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX01-CX20-CCX2=CX20-CX01-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX01-CCX0-CX02=CX10-CX02-CCX1-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX01-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX02=CX02-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX02-CX01=CX02-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX02-CCX1=CCX1-CX02-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX02-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1=CCX1-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CX01=CCX1-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CX01-CCX2=CCX2-CCX1-CX02-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CX02=CX02-CCX1-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX2=CCX2-CCX1-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX2-Swap01=CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX2-CX01=CCX2-CCX1-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX2-CX02=CCX2-CX02-CCX1-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CX12-Swap01=Swap12-CCX2-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto

  hypB L.ax-CX21-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX0-CX01-CCX2=CCX0-CX01-CCX2-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX0-CX02=CCX1-CCX0-CX12-Swap01-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX02-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX1-CCX0-Swap12-Swap01=CCX1-CX12-CCX0-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2=CX12-CCX1-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-Swap01=CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CX02=CX12-CCX1-CX01-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CX02-CCX1=CCX1-CCX2-CX02-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CCX1=CCX1-CCX2-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CCX1-CX01=CCX1-CCX2-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CCX1-CX02=CCX1-CX01-CCX2-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CCX1-CCX0-Swap12-Swap01=CX10-CCX2-CCX1-CX01-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CX10-CCX1=CCX0-CCX1-CCX2-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CX21-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CCX0-CX01=CCX0-CX21-CCX2-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CCX0-CX02-CCX1=CCX0-CX12-CCX2-Swap01-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX2-CCX0-CX12-Swap01=CCX0-CX12-CCX1-CX02-CX21-CX12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX12-Swap01=Swap12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX12-CX01-CCX0-Swap01=CX20-CCX2-CX02-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX12-CCX1=CCX2-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX12-CCX1-CX01=CCX2-CX02-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX12-CCX1-CX02=CX01-CCX2-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX12-CCX2-CCX0-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX12-CCX0-Swap01=CCX0-Swap12-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX21-CCX2-CX01=CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX21-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX21-CCX0-CCX2-CX01=CCX0-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-Swap12-Swap01=CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-Swap12-CCX1-CCX2-Swap01=CX12-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-Swap12-CCX2-Swap01=CCX1-CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX10-CX02-CCX1=CX01-CCX0-CX02-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX10-CCX1=CX10-CCX1-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX10-CCX1-CX02=CX10-Swap12-CCX2-Swap01-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX10-CCX2-CCX1=CCX0-CCX2-CCX1-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX10-CCX2-CCX1-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX10-CX12-CCX1=CX20-CCX2-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX10-Swap12-CCX2-Swap01=CX10-CCX1-CX02-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CX01-CCX2=CX01-CX20-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX1-CCX2-Swap01=CX20-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX1-CCX2-CX02=CCX1-CX20-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX2=CX10-CX12-CCX1-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX2-CX01=CX20-CX21-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX2-CX02=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX2-CCX1=CX20-CCX1-CCX2-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CCX2-CCX1-CX02=CX02-CCX1-CCX0-CX02-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CX20-CX21-CCX2-CX01=CX20-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-Swap01=CCX0-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CX01=CCX0-CX01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CX01-CCX2=CCX1-CCX0-CX01-CCX2-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CX02=CCX0-CX12-Swap01-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CX02-CCX1=CCX0-CCX1-CX12-Swap01-CX21-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CCX1-CX02=CCX0-Swap12-CCX2-Swap01-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CCX1-CCX2=CCX2-CX10-CCX1-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CCX1-CCX2-Swap01=CCX2-CCX0-Swap01-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CCX1-CX12-Swap01=CCX0-CX02-CCX1-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CX12-Swap01=CCX0-CX02-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CX12-CCX1-CX02=CCX2-CCX0-CX12-Swap01-CX12-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CX12-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-Swap12-Swap01=CX12-CCX0-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-Swap12-CCX1-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX21-CCX0-Swap12-CCX2-Swap01=CCX0-CCX1-CX02-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01=CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01-CCX2=CX02-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01-CCX2-CCX0-CX01=CX02-CCX1-CCX0-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01-CX20-CCX2=CX02-CX10-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01-CCX0-Swap01=CX20-CCX2-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01-CCX0-CX02=CX02-CCX0-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01-CCX0-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX01-CCX0-CCX2-CX01=CX20-CCX2-CCX1-CX01-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX02=CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX02-CX01=CX02-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX02-CCX1=CX01-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX02-CCX1-CCX0-CX02=CX01-CCX2-CCX0-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX02-CX10-CCX1=CX01-CX20-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX02-CCX0-CX01=CX01-CCX0-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1=CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CX01=CCX2-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CX01-CCX2=CCX2-CX02-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CX02=CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CCX2=CCX2-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CCX2-CX01=CCX2-CCX1-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CCX2-CX02=CCX2-CCX1-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CCX2-CCX0-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CX12-Swap01=CX12-CCX2-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CX12-CCX0-Swap01=CX12-CCX2-CCX0-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CX20-CCX2-CX02=CX01-CCX0-CCX2-Swap01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CCX0-CX01-CCX2=CCX2-CCX0-CX02-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CCX0-CX02=CCX2-CCX0-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CCX0-CX12-Swap01=CCX2-CCX0-CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX1-CCX0-Swap12-Swap01=CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2=CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CX01=CCX1-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CX02=CCX1-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CX02-CCX1=CCX1-CX01-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CCX1=CCX1-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CCX1-CX01=CCX1-CCX2-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CCX1-CX02=CCX1-CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CX10-CCX1=CX20-CCX2-CCX1-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CCX0-CX01=CCX1-CCX0-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CCX0-CX02-CCX1=CCX1-CCX0-CX01-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX2-CCX0-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX12-Swap01=CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX12-CX01-CCX0-Swap01=CX12-CX01-CCX0-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX12-CCX1=CX12-CCX1-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX12-CCX1-CX01=CX12-CCX1-CX01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX12-CCX1-CX02=CX21-CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX12-CCX2-Swap01=CCX1-CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX12-CCX2-CCX0-Swap01=CCX1-CX12-CCX0-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX12-CCX0-Swap01=CX12-CCX0-Swap01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX21-CCX2-CX01=CX12-CCX1-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX21-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX21-CCX0-CCX2-CX01=CX21-CCX0-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-Swap12-Swap01=Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-Swap12-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-Swap12-CCX2-Swap01=CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX10-CX02-CCX1=CX20-CX01-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX10-CCX1=CX20-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX10-CCX1-CX02=CX20-CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX10-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX10-CCX2-CCX1=CX20-CCX1-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX10-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX10-CX12-CCX1=CX10-CX12-CCX1-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX10-Swap12-CCX2-Swap01=CX20-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CX01-CCX2=CX10-CX02-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX1-CCX2=CX10-CCX2-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX1-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX1-CCX2-CX01=CX01-CCX2-CCX0-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX1-CCX2-CX02=CX10-CCX2-CCX1-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX2=CX10-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX2-Swap01=CX10-Swap12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX2-CX01=CX10-CCX1-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX2-CX02=CX01-CCX0-Swap01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX2-CCX1-CX01=CX01-CCX0-CCX2-CX01-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CCX2-CCX1-CX02=CX10-CCX1-CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CX20-CX21-CCX2-CX01=CX20-CCX1-CCX2-Swap01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-Swap01=CCX0-Swap12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CX01=CCX0-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CX01-CCX2=CCX0-CX02-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CX02=CCX0-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CX02-CCX1=CCX0-CX01-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CCX1-CX02=CCX0-CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CCX1-CCX2=CCX0-CCX2-CCX1-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CCX1-CCX2-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CCX1-CX12-Swap01=CCX0-CX12-CCX2-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CCX2-Swap01=CCX0-Swap12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CCX2-CX01=CCX0-CCX1-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CCX2-CCX1=CCX0-CCX1-CCX2-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CX12-Swap01=CCX0-CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CX12-CCX1-CX02=CCX0-CX21-CCX2-CX01-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CX12-CCX2-Swap01=CCX0-CCX1-CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-CX21-CCX2-CX01=CCX0-CX12-CCX1-CX02-Swap12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-Swap12-Swap01=CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-Swap12-CCX1-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-Swap12-CCX0-Swap12-CCX2-Swap01=CCX0-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  
  hypB L.ax-CX10-Swap01=CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CX01=Swap01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CX01-CCX2=CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX01-CCX2-CCX0-Swap01=CCX2-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX01-CCX2-CCX0-CX01=CCX2-CX02-CCX1-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX01-CX20-CCX2=CCX1-CCX2-Swap01-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX01-CCX0-Swap01=CCX1-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CX01-CCX0-CX02=CCX1-CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX01-CCX0-CCX2-Swap01=CCX1-CX01-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CX01-CCX0-CCX2-CX01=CCX1-CCX2-CX02-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX02=CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX02-CX01=CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CCX2-Swap01-CX12-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX02-CX10-CCX1=CX21-CCX2-CX01-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX02-CCX0-CX01=CX20-CCX2-CX01-CX21-CX12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CX01=CX01-CCX0-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CCX1-CX01-CCX2=CX01-CCX0-CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CCX1-CCX2=CCX2-CX10-CCX1-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CCX2-Swap01=CX01-CX20-CCX2-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CCX2-CX02=CX01-CCX0-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CCX2-CCX0-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CX12-Swap01=CX01-CCX0-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CCX0-CX02=CCX0-CCX1-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CCX0-CCX2-Swap01=CX02-CCX1-CCX0-CX02-CX12-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CCX0-CX12-Swap01=CCX0-CX02-CCX1-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2=CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-Swap01=CX01-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CX01=CX12-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CX02=CCX2-CX02-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CX02-CCX1=CX01-CCX2-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CCX1-CX02=CX01-CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CCX1-CCX0-Swap12-Swap01=CX20-CCX1-CCX2-CX01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CX10-CCX1=CCX1-CCX2-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CCX0-Swap01=CCX2-CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CCX0-CX01=CX12-CCX2-CCX0-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CCX0-CX02-CCX1=CCX0-CX21-CCX2-CX01-CX21-CX12-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX12-Swap01=CX02-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX12-CCX1-CX02=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX12-CCX2-Swap01=CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX12-CCX0-Swap01=CCX0-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX21-CCX2-CX01=CX02-CX10-CCX1-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX21-CCX0-CCX2-Swap01=CCX0-CX12-CCX1-CX02-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX1-CCX2-Swap01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-Swap12-Swap01=Swap12-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-Swap12-CCX1-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX10-CX02-CCX1=CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX10-CCX1=CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CX10-CCX1-CX02=CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX10-CCX1-CCX2-CX01=CCX1-CCX2-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CX10-CCX2-CCX1=CCX2-CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CX10-CCX2-CCX1-CX01=CCX2-CCX1-CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CX10-CX12-CCX1=CX12-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX10-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CX01-CCX2=CX20-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX1-CCX2=CCX0-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX1-CCX2-Swap01=CX12-CCX1-CX02-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX1-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX2=CX20-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX2-Swap01=CX20-CX01-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX2-CX01=CX02-CCX0-CX01-CX12-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX2-CX02=CX20-CCX2-CX02-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CCX2-CCX1-CX02=CCX1-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CX20-CX21-CCX2-CX01=Swap12-CCX1-CCX2-Swap01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-Swap01=CCX0-CX01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CCX0-CX01=CCX0-Swap01-CX10 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CX10-CCX0-CX01-CCX2=CCX0-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CX02=CCX0-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CX02-CCX1=CCX1-CCX0-CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CCX1-CCX2=CX20-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CX01-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CCX1-CX12-Swap01=CCX1-CX12-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CCX2-Swap01=CCX0-CX01-CCX2-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CCX2-CX01=CCX0-CX12-CCX2-Swap01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CX12-Swap01=CX12-CCX0-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CX12-CCX1-CX02=CX21-CCX0-CCX2-Swap01-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-CX01-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-Swap12-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX10-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-Swap01=Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX01=CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX01-CCX2-CCX0-Swap01=CCX1-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX01-CX20-CCX2=CX12-CCX1-CX02-CX12-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto

  hypB L.ax-CX20-CX01-CCX0-CX02=CX10-CCX1-CX02-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX01-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX02=Swap12-Swap01-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX02-CX01=CX12-Swap01-CX21-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX02-CCX1=Swap12-CCX2-Swap01-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX02-CCX1-CCX0-CX02=CCX1-CX01-CCX2-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX02-CX10-CCX1=Swap12-CCX1-CCX2-Swap01-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX02-CCX0-CX01=CX12-CCX2-Swap01-CX21-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1=CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CX01=CCX1-CX01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CX01-CCX2=CX02-CCX1-CCX0-CX02-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CX02=CCX1-CX12-Swap01-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CX12-Swap01=CCX1-CX02-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-CX02-CX21-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CX20-CCX2-CX02=CCX2-CX02-CCX1-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CCX0-CX01-CCX2=CCX0-CX12-CCX1-CX02-CX12-CX21-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CCX0-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CCX0-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-Swap12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-CX12-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX2-CX02-CCX1=CCX1-CX20-CCX2-CX02-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX2-CCX1-CCX0-Swap12-Swap01=CX10-CCX1-CCX2-CX01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX2-CX10-CCX1=CCX0-CCX2-CCX1-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX2-CCX0-CX01=CCX0-CCX2-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX2-CCX0-CX02-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX2-CCX0-CX12-Swap01=CCX0-CX01-CCX2-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX12-Swap01=CX02-CX01-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX12-CCX1=CX10-CX12-CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX12-CCX1-CX02=CX01-CX20-CCX2-CX21-CX12 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX12-CCX2-Swap01=CX02-CCX0-CX01-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX12-CCX2-CCX0-Swap01=CCX0-CX12-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX12-CCX0-Swap01=CCX0-CX12-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX21-CCX0-CCX2-CX01=CCX0-CX21-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-Swap12-Swap01=CX02-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-Swap12-CCX1-CCX2-Swap01=CX02-CX10-CCX1-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-Swap12-CCX2-Swap01=CX02-CCX1-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX10-CX02-CCX1=CX10-Swap12-CCX2-Swap01-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX10-CCX1=CX10-CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX10-CCX1-CX02=CX01-CCX0-CX02-CX21-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX10-CCX1-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX10-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX10-CX12-CCX1=CX12-CCX1-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX10-Swap12-CCX2-Swap01=CX10-CX02-CCX1-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CX01-CCX2=CX01-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX1-CCX2=CCX1-CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX1-CCX2-CX01=CCX1-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX1-CCX2-CX02=CCX1-CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX2=CCX2 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX2-Swap01=CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX2-CX01=CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX2-CX02=CCX2-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX2-CCX1=CCX2-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX2-CCX1-CX01=CCX2-CCX1-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CCX2-CCX1-CX02=CCX2-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CX20-CX21-CCX2-CX01=CX21-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-Swap01=CCX0-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CX01=CCX0-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CX01-CCX2=CCX2-CCX0-CX12-Swap01-CX21-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CX02=CCX0-Swap12-Swap01-Swap12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CX02-CCX1=CCX0-Swap12-CCX2-Swap01-CX21-CX12-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CCX1-CCX2=CX10-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CCX1-CX12-Swap01=CCX0-CCX1-CX02-Swap12-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CX12-Swap01=CX12-CCX0-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX01-CCX2-CX21-CX12-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CX12-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-CX21-CCX2-CX01=CX21-CCX0-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-Swap12-Swap01=CCX0-CX02-Swap12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CX20-CCX0-Swap12-CCX2-Swap01=CCX0-CX02-CCX1-CX12-CX21-CX10 = ListNF.listnfeq' nf-s7 auto
  
  hypB L.ax-CCX0-CX01-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-Swap01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CX01-CCX2-CCX0-CX01=CCX2-CX02-CCX1-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX01-CX20-CCX2=CCX1-CCX0-CX01-CCX2-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CX01-CCX0-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX01-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX01-CCX0-CCX2-CX01=CCX1-CCX2-CX02-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX02-CX01=CX12-CCX0-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX02-CCX1-CCX0-CX02=CCX1-CX01-CCX2-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX02-CX10-CCX1=CCX2-CCX0-CX02-CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX02-CCX0-CX01=CX12-CCX2-CCX0-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX1=CX10-CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX1-CX01=CCX1-CX01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX1-CX01-CCX2=CX02-CCX1-CCX0-CX02-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX1-CCX2-CX01=CCX1-CCX2-CX01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX1-CCX2-CX02=CX01-CCX0-CCX2-CX01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX1-CCX2-CCX0-Swap01=CCX1-CCX2-CCX0-Swap01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX1-CX12-CCX0-Swap01=CX01-CCX0-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX1-CCX0-CX01-CCX2=CX01-CX20-CCX2-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX1-CCX0-CX02=CX10-CCX1-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX1-CCX0-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX1-CCX0-CX12-Swap01=CX10-CX02-CCX1-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX1-CCX0-Swap12-Swap01=CX10-Swap12-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2=CX20-CCX2-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CX02=CCX2-CX02-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CX02-CCX1=CX01-CCX2-CCX0-CX01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CCX1-CX02=CCX2-CCX1-CX02-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CCX1-CCX0-Swap12-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CX10-CCX1=CX20-CCX2-CCX1-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CCX0-Swap01=CX20-CCX2-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CCX0-CX01=CX20-CCX2-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CCX0-CX02-CCX1=CX02-CX10-CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX2-CCX0-CX12-Swap01=CX20-CX01-CCX2-CX12-CX21-CX10-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX12-CCX1=CX12-CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX12-CCX2-CCX0-Swap01=CX02-CCX0-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX12-CCX0-Swap01=CX02-CX01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX21-CCX0-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX21-CCX0-CCX2-CX01=CX20-CX21-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX10-CX02-CCX1=CCX1-CCX0-CX12-Swap01-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX10-CCX1=CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CX10-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX10-CCX1-CCX2-CX01=CX10-CCX1-CCX2-CX01-CCX0 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CX10-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX10-CX12-CCX1=CX10-CX12-CCX1-CX10-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX10-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CX01-CCX2=CCX2-CCX0-CX12-Swap01-CX21-CX12-CX10 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX1-CCX2=CX10-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX1-CCX2-CX01=CX20-CCX1-CCX2-CX01-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX2=CCX2-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX2-Swap01=CCX2-CCX0-Swap01-CX21 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX2-CX02=CX20-CCX2-CX02-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX10-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX2-CCX1-CX01=CCX2-CCX1-CX01-CX20-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CCX2-CCX1-CX02=CX20-CCX2-CCX1-CX02-CCX0 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CX20-CX21-CCX2-CX01=CX21-CCX0-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-Swap01=Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX0-CX01=CX01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX0-CX01-CCX2=CX01-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX0-CX02=CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-CX02-CCX1=CX02-CCX1 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-CCX1-CX02=CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-CCX1-CCX2=CCX1-CCX2 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX0-CCX1-CX12-Swap01=CCX1-CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-CCX2-Swap01=CCX2-Swap01 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX0-CCX2-CCX1=CCX2-CCX1 = ListNF.listnfeq' nf-s6 auto
  hypB L.ax-CCX0-CCX0-CX12-Swap01=CX12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-CX12-CCX1-CX02=CX12-CCX1-CX02 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-CX12-CCX2-Swap01=CX12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-CX21-CCX2-CX01=CX21-CCX2-CX01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-Swap12-Swap01=Swap12-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto
  hypB L.ax-CCX0-CCX0-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01 = ListNF.listnfeq' nf-s7 auto

  hypB L.ax-iI-S0-K0-S0-CK10=S0-K0-S0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20=S0-K0-S0-CK20-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK10=S0-K0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20=S0-K0-CK20-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20-CK10=S0-K0-CK20-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CCK'=S0-K0-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK10-CCK'=S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK20-S0-CK10=S0-CK20-S0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK20-CK10=S0-CK20-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK20-CCK'=S0-CK20-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK10=K0-S0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20=K0-S0-CK20-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20-CK10=K0-S0-CK20-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK10=K0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK10-CCK'=K0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20=K0-CK20-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20-S0-CK10=K0-CK20-S0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20-CK10=K0-CK20-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20-CCK'=K0-CK20-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CCK'=K0-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-K0-CCK'-CCK'=K0-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK10-CCK'=CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK10-CCK'-CCK'=CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK20-S0-CK10=CK20-S0-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK20-CK10=CK20-CK10-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK20-CK10-CCK'=CK20-CK10-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK20-CCK'=CK20-CCK'-iI = mvI.general-rewrite 20 auto
  hypB L.ax-iI-CK20-CCK'-CCK'=CK20-CCK'-CCK'-iI = mvI.general-rewrite 20 auto

  hypB L.ax-S0-S0-K0-S0-CK10=K0-S0-CK10-X0-S0-S0-S1-S1-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20=K0-S0-CK20-X0-S0-S0-S2-S2-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK10=K0-CK10-X0-CX10-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK10-CCK'=K0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20=K0-CK20-X0-CX20-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20-CK10=K0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20-CCK'=K0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CCK'=K0-CCK'-X0-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-K0-CCK'-CCK'=K0-CCK'-CCK'-X0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-S0-S0-CK10-CCK'=CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK20-S0-CK10=CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK20-CK10=CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK20-CK10-CCK'=CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK20-CCK'=CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-S0-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto

  hypB L.ax-S1-S0-K0-S0-CK10=S0-K0-S0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20=S0-K0-S0-CK20-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK10=S0-K0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20=S0-K0-CK20-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20-CK10=S0-K0-CK20-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CCK'=S0-K0-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  
  hypB L.ax-S1-S0-CK10-CCK'=S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK20-CK10=S0-CK20-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK20-CCK'=S0-CK20-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK10=K0-S0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20=K0-S0-CK20-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20-CK10=K0-S0-CK20-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK10=K0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK10-CCK'=K0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20=K0-CK20-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20-S0-CK10=K0-CK20-S0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20-CK10=K0-CK20-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20-CCK'=K0-CK20-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CCK'=K0-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-K0-CCK'-CCK'=K0-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK10-CCK'=CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK20-S0-CK10=CK20-S0-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK20-CK10=CK20-CK10-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK20-CK10-CCK'=CK20-CK10-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK20-CCK'=CK20-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S1-CK20-CCK'-CCK'=CK20-CCK'-CCK'-S1 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK10=S0-K0-S0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20=S0-K0-S0-CK20-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK10=S0-K0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20=S0-K0-CK20-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20-CK10=S0-K0-CK20-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CCK'=S0-K0-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK10-CCK'=S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK20-CK10=S0-CK20-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK20-CCK'=S0-CK20-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK10=K0-S0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20=K0-S0-CK20-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20-CK10=K0-S0-CK20-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK10=K0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK10-CCK'=K0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20=K0-CK20-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20-S0-CK10=K0-CK20-S0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20-CK10=K0-CK20-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20-CCK'=K0-CK20-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CCK'=K0-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-K0-CCK'-CCK'=K0-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK10-CCK'=CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK20-S0-CK10=CK20-S0-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK20-CK10=CK20-CK10-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK20-CK10-CCK'=CK20-CK10-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK20-CCK'=CK20-CCK'-S2 = mvD3.general-rewrite 50 auto
  hypB L.ax-S2-CK20-CCK'-CCK'=CK20-CCK'-CCK'-S2 = mvD3.general-rewrite 50 auto

  hypB L.ax-CS01-S0-K0-S0-CK10=S0-K0-S0-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-CCX0-S0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CCK'-S0-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20=S0-K0-S0-CK20-CK10-CX10-CCX0-S1-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S1-CS01-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S1-CS01-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCX0-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CCK'-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX10-S1-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX10-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK10=S0-K0-CK10-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCK'-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCX0-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20=S0-K0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20-S0-CK10=S0-K0-CK20-CCK'-CCX0-S0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S0-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20-CCK'=S0-K0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-S0-CK10-CCK'=CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX10-S0-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20=S0-CK20-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20-S0-CK10=S0-CK20-CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CX10-CCX0-S0-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20-CK10=S0-CK20-S0-CK10-CCK'-CCK'-S0-S0-S0-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20-CK10-CCK'=S0-CK20-S0-CK10-CCX0-S0-S0-S0-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-S0-S0-S0-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20-CCK'=S0-CK20-CCK'-CS01 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-S0-CK20-CCK'-CCK'=S0-CK20-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-K0-S0-CK10=K0-S0-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK10-CCK'=K0-CCK'-CCK'-CCX0-S0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK10-CCK'-CCK'=K0-CCK'-S0-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20=K0-S0-CK20-CK10-CX10-CCX0-S1-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S1-CS01-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S1-CS01-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20-CK10=K0-S0-CK20-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CCK'-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20-CCK'=K0-S0-CK20-CK10-CCK'-CX10-S1-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK10=K0-CK10-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK10-CCK'=K0-CK10-CCK'-CCK'-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCX0-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20=K0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20-S0-CK10=K0-CK20-CCK'-CCX0-S0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-S0-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20-CCK'=K0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-K0-CCK'-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS01-CK10-CCK'=S0-CK10-CCK'-S0-S0-S0-CS01 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S0-S0-S0-CS01 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20=CK20-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20-S0-CK10=CK20-CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CX10-CCX0-S0-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20-CK10=CK20-S0-CK10-CCK'-CCK'-S0-S0-S0-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20-CK10-CCK'=CK20-S0-CK10-CCX0-S0-S0-S0-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCX0-S0-S0-S0-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20-CCK'=CK20-CCK'-CS01 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS01-CK20-CCK'-CCK'=CK20-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-K0-S0-CK10=S0-K0-S0-CK20-CK10-CX20-CCX0-S2-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX20-S2-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX20-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20=S0-K0-S0-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20-S0-CK10=S0-K0-CK10-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20-CK10=S0-K0-S0-CK10-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK10-CCK'-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-CCX0-S0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CCK'-S0-CS02-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK10=S0-K0-S0-CK20-S0-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20=S0-K0-CK20-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCK'-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCX0-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX20-CCX0-S0-S0-S0-S2-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-S0-S2-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto

  hypB L.ax-CS02-S0-CK10=S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK10-CCK'=S0-CK10-CCK'-CS02 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK10-CCK'-CCK'=S0-CK10-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK20-S0-CK10=CK20-CK10-CCK'-CCK'-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK20-CK10=CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK20-CK10-CCK'=CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK20-CCK'=CK20-CCK'-CX20-CCX0-S0-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX20-S0-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-K0-S0-CK10=K0-S0-CK20-CK10-CX20-CCX0-S2-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-S2-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX20-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20=K0-S0-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20-S0-CK10=K0-CK10-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20-S0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20-CK10=K0-S0-CK10-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20-CK10-CCK'=K0-S0-CK10-CCK'-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20-CCK'=K0-CCK'-CCK'-CCX0-S0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-S0-CK20-CCK'-CCK'=K0-CCK'-S0-CS02-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK10=K0-S0-CK20-S0-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20=K0-CK20-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20-CCK'=K0-CK20-CCK'-CCK'-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCX0-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CCX0-S0-S0-S0-S2-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-K0-CCK'-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-S0-S2-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CS02-CK10=CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CS02-CK10-CCK'=CK10-CCK'-CS02 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK10-CCK'-CCK'=CK10-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK20-S0-CK10=S0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CS02 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK20-CK10=S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK20-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX10-S0-S0-CS01-CS01-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK20-CCK'=S0-CK20-CCK'-S0-S0-S0-CS02 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CS02-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S0-S0-S0-CS02 = ListNF.listnfeq' nf-e3 auto

  hypB L.ax-CS12-S0-K0-S0-CK10=S0-K0-S0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20=S0-K0-S0-CK20-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK10=S0-K0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20=S0-K0-CK20-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CCK'=S0-K0-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK10-CCK'=S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK20-CK10=S0-CK20-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK20-CCK'=S0-CK20-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK10=K0-S0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20=K0-S0-CK20-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK10=K0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK10-CCK'=K0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20=K0-CK20-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20-CK10=K0-CK20-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20-CCK'=K0-CK20-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CCK'=K0-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-K0-CCK'-CCK'=K0-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK10-CCK'=CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK20-S0-CK10=CK20-S0-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK20-CK10=CK20-CK10-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK20-CK10-CCK'=CK20-CK10-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK20-CCK'=CK20-CCK'-CS12 = mvD3.general-rewrite 50 auto
  hypB L.ax-CS12-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CS12 = mvD3.general-rewrite 50 auto

  hypB L.ax-CCZ-S0-K0-S0-CK10=S0-K0-S0-CK10-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20=S0-K0-S0-CK20-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCX0-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK10=S0-K0-CK10-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20=S0-K0-CK20-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CCK'=S0-K0-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-S0-CK10-CCK'=S0-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK20-CK10=S0-CK20-CK10-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK20-CCK'=S0-CK20-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto

  hypB L.ax-CCZ-K0-S0-CK10=K0-S0-CK10-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20=K0-S0-CK20-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCX0-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK10=K0-CK10-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK10-CCK'=K0-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20=K0-CK20-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20-CK10=K0-CK20-CK10-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20-CCK'=K0-CK20-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CCK'=K0-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCZ-CK10-CCK'=CK10-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK20-S0-CK10=CK20-S0-CK10-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK20-CK10=CK20-CK10-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK20-CK10-CCK'=CK20-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK20-CCK'=CK20-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCZ-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-K0-S0-K0-S0-CK10=S0-K0-CK10-X0-CX10-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK10-CCK'=S0-K0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20=S0-K0-CK20-X0-CX20-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20-CK10=S0-K0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20-CCK'=S0-K0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK10=S0-K0-S0-CK10-X0-CX10-CS01-CS01-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK10-CCK'=S0-K0-S0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20=S0-K0-S0-CK20-X0-CX20-CS02-CS02-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20-CK10=S0-K0-S0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20-CCK'=S0-K0-S0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CCK'=S0-K0-CCK'-CCK'-X0-CCX0-S0-S0-S0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-S0-K0-CCK'-CCK'=S0-K0-CCK'-X0-CCX0-S0-S0-S0-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK10=S0-CK10-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK10-CCK'=S0-CK10-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20=S0-CK20-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20-CK10=S0-CK20-CK10-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20-CCK'=S0-CK20-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK10=CK10-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK10-CCK'=CK10-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20=CK20-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20-S0-CK10=CK20-S0-CK10-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20-CK10=CK20-CK10-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20-CK10-CCK'=CK20-CK10-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20-CCK'=CK20-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CCK'=CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-K0-K0-CCK'-CCK'=CCK'-CCK'-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK10=S0-K0-S0-CK10-X0-CX10-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20=S0-K0-S0-CK20-X0-CX20-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK10=S0-K0-CK10-X0-S0-S0-S1-S1-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20=S0-K0-CK20-X0-S0-S0-S2-S2-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20-CK10=S0-K0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CCK'=S0-K0-CCK'-X0-S0-S0-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-X0-CCX0-S0-S0-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-e4 auto

  hypB L.ax-X0-S0-CK10-CCK'=S0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK20-CK10=S0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK20-CCK'=S0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-K0-S0-CK10=K0-S0-CK10-CX10-S0-S0-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20=K0-S0-CK20-CX20-S0-S0-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK10=K0-CK10-CX10-S0-S0-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20=K0-CK20-CX20-S0-S0-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20-CK10=K0-CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20-CCK'=K0-CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CCK'=K0-CCK'-CCX0-S0-S0-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-S0-S0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-X0-CK10-CCK'=CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK20-S0-CK10=CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK20-CK10=CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK20-CK10-CCK'=CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK20-CCK'=CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-X1-S0-K0=S0-K0-X1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK10=K0-S0-CK10-X1-X0-CX10-S1-S1-S1-CS01-CS01-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-X1-X0-CX10-CCX0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK20=S0-K0-S0-CK20-X1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK20-S0-CK10=S0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X1-X0-CX10-CX20-S1-S1-S1-CS01-CS01-CS02-CS02-iI = ListNF.listnfeq' nf-p24k0d auto

  hypB L.ax-X1-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK10=S0-CK10-X1-S1-S1-S1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK10-CCK'=S0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK10-CCK'-CCK'=CK20-S0-CK10-X1-CX20-S1-S1-S1-S2-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK20=S0-K0-CK20-X1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK20-S0-CK10=K0-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X1-X0-CX10-CCX0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK20-CK10=S0-CK20-CK10-X1-S1-S1-S1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK20-CK10-CCK'=S0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X1-S1-S1-S1-S2-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CK20-CCK'=S0-K0-CCK'-X1-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto

  hypB L.ax-X1-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CCK'=S0-K0-CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK10=S0-K0-CK10-X1-S1-S1-S1-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20=S0-CK20-X1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20-S0-CK10=K0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-X1-X0-S0-S0-S1-S2-CS02-CS02-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20-CK10=S0-K0-CK20-CK10-X1-S1-S1-S1-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20-CK10-CCK'=S0-K0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20-CCK'=CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK10=S0-K0-S0-CK10-X1-CX10-S0-S0-S1-S1-S1-CS01-CS01 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20=K0-S0-CK20-X1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20-S0-CK10=CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-X1-X0-S0-S0-S1-S2-CS02-CS02 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X1-CX10-CX20-S0-S0-S1-S1-S1-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK10-CCK'-X1-CX10-CX20-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X1-CX10-CX20-CCX0-S0-S0-S1-S1-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20-CCK'=K0-CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-S0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK10=CK10-X1-S1-S1-S1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK10-CCK'=CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20=K0-CK20-X1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20-S0-CK10=S0-K0-S0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20-CK10=CK20-CK10-X1-S1-S1-S1 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20-CK10-CCK'=CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20-CCK'=K0-CCK'-X1-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CCK'=K0-CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-K0-CCK'-CCK'=K0-S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK10=K0-CK10-X1-S1-S1-S1-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK10-CCK'=K0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK20-S0-CK10=S0-K0-CK10-CCK'-CCK'-X1-CX20-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X1-S1-S1-S1-S2-CS02-CS02-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK20-CK10=K0-CK20-CK10-X1-S1-S1-S1-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK20-CK10-CCK'=K0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK20-CCK'=CCK'-X1-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CCK'=CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X1-CCK'-CCK'=S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto

  hypB L.ax-X2-S0-K0=S0-K0-X2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK10=S0-K0-S0-CK10-X2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20=K0-S0-CK20-X2-X0-CX20-S2-S2-S2-CS02-CS02-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-X2-X0-CX20-CCX0-S0-S0-S1-S1-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CCK'-CCK'-X2-X0-CX20-S0-S1-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X2-X0-CX10-CX20-S0-S1-S1-S2-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X2-X0-CX10-CX20-S2-S2-S2-CS01-CS01-CS02-CS02-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CCK'-X2-X0-CX10-CX20-CCX0-S2-S2-S2-CS01-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X2-X0-CX10-CX20-CCX0-S0-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20-CCK'=K0-S0-CK20-CK10-CCK'-X2-X0-CX20-CCX0-S1-S1-S2-S2-S2-CS01-CS01-CS01-CS02-CS02-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-X2-X0-CX20-CCX0-S0-S1-S1-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK10=S0-K0-CK10-X2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK10-CCK'=S0-K0-CCK'-X2-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20=S0-CK20-X2-S2-S2-S2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20-S0-CK10=S0-CK20-S0-CK10-X2-S2-S2-S2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20-S0-CK10-CCK'=S0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20-CK10=S0-CK20-CK10-X2-S2-S2-S2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20-CK10-CCK'=S0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20-CCK'=S0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CCK'=S0-K0-CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK10=S0-CK10-X2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK10-CCK'=CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20=S0-K0-CK20-X2-S2-S2-S2-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X2-S2-S2-S2-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20-CK10=S0-K0-CK20-CK10-X2-S2-S2-S2-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20-CK10-CCK'=S0-K0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20-CCK'=S0-K0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-S0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK10=K0-S0-CK10-X2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK10-CCK'=K0-CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20=S0-K0-S0-CK20-X2-CX20-S0-S0-S2-S2-S2-CS02-CS02 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X2-CX10-CX20-CCX0-S0-S0-S2-S2-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X2-CX10-CX20-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X2-CX20-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X2-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CCK'-X2-CX10-CX20-CCX0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X2-CX10-CX20-S0-S1-S1-S2-S2-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CK10-CCK'-X2-CX20-CCX0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X2-CX20-S0-S1-S2-S2-CS01 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK10=K0-CK10-X2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK10-CCK'=K0-CCK'-X2-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20=CK20-X2-S2-S2-S2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20-S0-CK10=CK20-S0-CK10-X2-S2-S2-S2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20-S0-CK10-CCK'=CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20-CK10=CK20-CK10-X2-S2-S2-S2 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20-CK10-CCK'=CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20-CCK'=CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CK20-CCK'-CCK'=CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CCK'=K0-CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-K0-CCK'-CCK'=K0-S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK10-CCK'=CCK'-X2-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20=K0-CK20-X2-S2-S2-S2-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20-S0-CK10=K0-CK20-S0-CK10-X2-S2-S2-S2-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20-S0-CK10-CCK'=K0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20-CK10=K0-CK20-CK10-X2-S2-S2-S2-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20-CK10-CCK'=K0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20-CCK'=K0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12-iI = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CCK'=CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-X2-CCK'-CCK'=S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  
  hypB L.ax-CX10-S0-K0-S0-CK10=S0-K0-S0-CK10-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20=S0-K0-S0-CK20-CX10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S1-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX10-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK10=S0-K0-CK10-CX10-S1-S1-S1-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20=S0-K0-CK20-CX10-S1-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCX0-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CX10-S1-S1-S1-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX10-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CCK'=S0-K0-CCK'-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-S0-CK10-CCK'=S0-CK10-CCK'-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S1-S1-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-S1-S1-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCX0-S1-S1-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK20-CK10=S0-CK20-CK10-CX10-S1-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX10-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK20-CCK'=S0-CK20-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-K0-S0-CK10=K0-S0-CK10-CX10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20=K0-S0-CK20-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX10-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK10=K0-CK10-CX10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20=K0-CK20-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20-CK10=K0-CK20-CK10-CX10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX10-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20-CCK'=K0-CK20-CCK'-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CCK'=K0-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX10-CK10-CCK'=CK10-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK20-S0-CK10=CK20-S0-CK10-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-S1-CS01-CS01 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK20-CK10=CK20-CK10-CCX0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK20-CK10-CCK'=CK20-CK10-CCK'-CS01-CS01 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK20-CCK'=CK20-CCK'-CX10-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX10-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX10 = ListNF.listnfeq' nf-e3 auto
  
  hypB L.ax-CX12-S0-K0=S0-K0-CX12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK10=S0-K0-S0-CK10-CX12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20=S0-K0-S0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CX12-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK10=S0-K0-CK10-CX12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK10-CCK'=S0-K0-CCK'-CX12-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20=S0-K0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20-CK10=S0-K0-CK20-CX12-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CCK'=S0-K0-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK10=S0-CK10-CX12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK10-CCK'=CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20=S0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20-CK10=S0-CK20-CX12-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20-CCK'=S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-S0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK10=K0-S0-CK10-CX12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK10-CCK'=K0-CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20=K0-S0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20-CK10=K0-S0-CK20-CX12-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK10=K0-CK10-CX12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK10-CCK'=K0-CCK'-CX12-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20=K0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20-S0-CK10-CCK'=K0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20-CK10=K0-CK20-CX12-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20-CCK'=K0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CCK'=K0-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-K0-CCK'-CCK'=K0-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK10-CCK'=CCK'-CX12-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20=CK20-CK10-CX12-S1-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20-S0-CK10=CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20-S0-CK10-CCK'-CCK'=CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20-CK10=CK20-CX12-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20-CK10-CCK'=CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20-CCK'=CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CK20-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CCK'=CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX12-CCK'-CCK'=S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  
  hypB L.ax-CX20-S0-K0-S0-CK10=S0-K0-S0-CK10-CX20-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX20-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX20 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20=S0-K0-S0-CK20-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK10=S0-K0-CK10-CX20-S2-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX20-S2-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20=S0-K0-CK20-CX20-S2-S2-S2-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CX20-CCX0-S2-S2-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX20-S2-S2-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX20-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CCK'=S0-K0-CCK'-CX20-S2-CS02-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-S0-CK10-CCK'=S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CX20-CCX0-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX20-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX20 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK20-CK10=S0-CK20-CK10-CX20-S2-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX20-S2-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK20-CCK'=S0-CK20-CCK'-CX20-S2-CS02-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-K0-S0-CK10=K0-S0-CK10-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20=K0-S0-CK20-CX20 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX20-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX20 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK10=K0-CK10-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK10-CCK'=K0-CK10-CCK'-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20=K0-CK20-CX20 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20-CK10=K0-CK20-CK10-CX20-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX20-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX20 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20-CCK'=K0-CK20-CCK'-CX20-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX20-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CCK'=K0-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CX20-CK10-CCK'=CK10-CCK'-CX20-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX20 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK20-S0-CK10=CK20-S0-CK10-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CS02-CS02 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK20-CK10=CK20-CK10-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK20-CK10-CCK'=CK20-CK10-CCK'-CS02-CS02 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK20-CCK'=CK20-CCK'-CCX0-CS02-CS02-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX20-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CX21-S0-K0=S0-K0-CX21 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK10=S0-K0-S0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20=S0-K0-S0-CK20-CX21 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20-CK10=S0-K0-S0-CK10-CX21-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK10=S0-K0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20=S0-K0-CK20-CX21 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20-CK10=S0-K0-CK10-CX21-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20-CCK'=S0-K0-CCK'-CX21-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CCK'=S0-K0-CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK10=S0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK10-CCK'=S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20=S0-CK20-CX21 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20-S0-CK10=CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20-CK10=S0-CK10-CX21-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20-CCK'=CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK10=K0-S0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20=K0-S0-CK20-CX21 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20-S0-CK10=K0-CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20-CK10=K0-S0-CK10-CX21-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20-CCK'=K0-CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-S0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK10=K0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK10-CCK'=K0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20=K0-CK20-CX21 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20-S0-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20-CK10=K0-CK10-CX21-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20-CCK'=K0-CCK'-CX21-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CCK'=K0-CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-K0-CCK'-CCK'=K0-S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK10=CK20-CK10-CX21-S2-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK10-CCK'=CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK20-S0-CK10=S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK20-CK10=CK10-CX21-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK20-CK10-CCK'=CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK20-CCK'=CCK'-CX21-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CCK'=CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CX21-CCK'-CCK'=S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-CCX0-S0-K0-S0-CK10=S0-K0-S0-CK10-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20=S0-K0-S0-CK20-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK10=S0-K0-CK10-CCX0-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20=S0-K0-CK20-CCX0-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCX0-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CCK'=S0-K0-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-S0-CK10-CCK'=S0-CK10-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK20-CK10=S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CCX0-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK20-CCK'=S0-CK20-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-K0-S0-CK10=K0-S0-CK10-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20=K0-S0-CK20-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK10=K0-CK10-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK10-CCK'=K0-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20=K0-CK20-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20-CK10=K0-CK20-CK10-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20-CCK'=K0-CK20-CCK'-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CCK'=K0-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCX0-CK10-CCK'=CK10-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK20-S0-CK10=CK20-S0-CK10-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK20-CK10=CK20-CK10-CCX0 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK20-CK10-CCK'=CK20-CK10-CCK'-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK20-CCK'=CK20-CCK'-CCX0-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCX0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0 = ListNF.listnfeq' nf-e3 auto

  hypB L.ax-Swap12-S0-K0=S0-K0-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK10=S0-K0-S0-CK20-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK20=S0-K0-S0-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK10=S0-K0-CK20-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK10-CCK'=S0-K0-CK20-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK20=S0-K0-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-K0-CK20-CK10=S0-K0-CK20-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK20-CCK'=S0-K0-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CCK'=S0-K0-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK10=S0-CK20-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK10-CCK'=S0-CK20-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK20=S0-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK20-S0-CK10=CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-S0-CK20-CK10=S0-CK20-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK20-CCK'=S0-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-S0-CK20-CCK'-CCK'=S0-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK10=K0-S0-CK20-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK10-CCK'=K0-S0-CK20-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK20=K0-S0-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-K0-S0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-K0-S0-CK20-CK10=K0-S0-CK20-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK20-CCK'=K0-S0-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK10=K0-CK20-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK10-CCK'=K0-CK20-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK20=K0-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-K0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-K0-CK20-CK10=K0-CK20-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK20-CCK'=K0-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CK20-CCK'-CCK'=K0-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CCK'=K0-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-K0-CCK'-CCK'=K0-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-CK10-CCK'=CK20-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-CK10-CCK'-CCK'=CK20-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-CK20-S0-CK10=S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ = ListNF.listnfeq' nf-p24k0d auto
  hypB L.ax-Swap12-CK20-CK10=CK20-CK10-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-CK20-CK10-CCK'=CK20-CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-CK20-CCK'=CK10-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-CK20-CCK'-CCK'=CK10-CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto
  hypB L.ax-Swap12-CCK'-CCK'=CCK'-CCK'-Swap12 = mvD3.general-rewrite 50 auto

  hypB L.ax-CK10-S0-K0-S0-CK10=S0-K0-CK10-S0-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-S0-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CCX0-S0-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20=S0-K0-S0-CK20-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CX10-CCX0-S0-S1-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX10-S0-S1-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CX10-S0-S1-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX10-S1-S1-S1-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CX10-CCX0-S1-S1-S1-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK10=S0-K0-S0-CK10-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20=S0-K0-CK20-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCX0-S0-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S0-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCX0-S0-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-S0-CK10-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CCK'=S0-K0-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-K0-CCK'-CCK'=S0-K0-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-S0-CK10-CCK'=S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK20-S0-CK10=S0-CK20-CCK'-CX10-CCX0-S0-S1-S1-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK20-S0-CK10-CCK'=S0-CK20-CX10-S0-S1-S1-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX10-CCX0-S0-S1-S1-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK20-CCK'=S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-S0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-K0-S0-CK10=K0-S0-CK10-CX10-CS01-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20=K0-S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20-S0-CK10=K0-S0-CK20-CCK'-CX10-CCX0-S0-S1-S1-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CX10-S0-S1-S1-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX10-CCX0-S0-S1-S1-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CX10-CS01-CS01-CS01-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20-CCK'=K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK10=K0-S1-S1-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK10-CCK'=K0-CCK'-S1-S1-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK10-CCK'-CCK'=K0-CCK'-CCK'-S1-S1-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20=K0-CK20-CK10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CS01-CS01-CS01 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20-CK10=K0-CK20-S1-S1-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20-CK10-CCK'=K0-CK20-CCK'-S1-S1-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-S1-S1-S1 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20-CCK'=K0-CK20-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CK20-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CCK'=K0-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-K0-CCK'-CCK'=K0-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK10-CK10-CCK'=CCK'-S1-S1-S1 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK10-CCK'-CCK'=CCK'-CCK'-S1-S1-S1 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK20-S0-CK10=CK20-S0-CK10-CX10-CS01-CS01-CS01 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK20-CK10=CK20-S1-S1-S1 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK20-CK10-CCK'=CK20-CCK'-S1-S1-S1 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK20-CK10-CCK'-CCK'=CK20-CCK'-CCK'-S1-S1-S1 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK20-CCK'=CK20-CK10-CCK' = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK10-CK20-CCK'-CCK'=CK20-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-S0-K0-S0-CK10=S0-K0-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20=S0-K0-CK20-S0-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CX10-S0-S0-CS01-CS01-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-S0-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CCX0-S0-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK10=S0-K0-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20=S0-K0-S0-CK20-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-S2-S2-S2-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S2-S2-S2-CS02-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCX0-S2-S2-S2-CS02-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CCK'=S0-K0-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-K0-CCK'-CCK'=S0-K0-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-S0-CK20-CCK'=S0-CK20-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-K0-S0-CK10=K0-CK20-S0-CK10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20=K0-S0-CK20-CX20-CS02-CS02-CS02 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CX20-CS02-CS02-CS02-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK10=K0-CK20-CK10 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK10-CCK'=K0-CK20-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20=K0-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20-S0-CK10=K0-S0-CK10-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20-S0-CK10-CCK'=K0-S0-CK10-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20-CK10=K0-CK10-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20-CK10-CCK'=K0-CK10-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20-CCK'=K0-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CK20-CCK'-CCK'=K0-CCK'-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CCK'=K0-CK20-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-K0-CCK'-CCK'=K0-CK20-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CK20-CK20-S0-CK10=S0-CK10-S2-S2-S2 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-CK20-S0-CK10-CCK'=S0-CK10-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-CK20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-CK20-CK10=CK10-S2-S2-S2 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-CK20-CK10-CCK'=CK10-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-CK20-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-CK20-CCK'=CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CK20-CK20-CCK'-CCK'=CCK'-CCK'-S2-S2-S2 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-K0-S0-CK10=S0-K0-S0-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20=S0-K0-S0-CK20-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK10=S0-K0-CK10-CCK'-CCK'-CCX0-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK10-CCK'=S0-K0-CK10-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20=S0-K0-CK20-CCK'-CCK'-CCX0-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCX0-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20-CCK'=S0-K0-CK20-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CCK'=S0-K0-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-K0-CCK'-CCK'=S0-K0-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-S0-CK10-CCK'=S0-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK10-CCK'-CCK'=S0-CK10-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCK' = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CCX0-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK20-CK10-CCK'=S0-CK20-CK10-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCX0-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK20-CCK'=S0-CK20-CCK'-CCK' = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-S0-CK20-CCK'-CCK'=S0-CK20-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-K0-S0-CK10=K0-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK10-CCK'=K0-S0-CK10-CCX0-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20=K0-S0-CK20-CCK'-CCK'-CCX0-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCX0-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20-CCK'=K0-S0-CK20-CCX0-CS12-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK10=K0-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK10-CCK'=K0-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK10-CCK'-CCK'=K0-CK10-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20=K0-CK20-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20-CK10-CCK'=K0-CK20-CK10-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20-CCK'=K0-CK20-CCK'-CCK' = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CK20-CCK'-CCK'=K0-CK20-CS12-CS12 = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CCK'=K0-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-K0-CCK'-CCK'=K0-CCK'-CCX0-CCZ = ListNF.listnfeq' nf-e4 auto
  hypB L.ax-CCK'-CK10-CCK'=CK10-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK10-CCK'-CCK'=CK10-CCK'-CCX0-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK20-S0-CK10=CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCX0-CS12-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK20-CK10=CK20-CK10-CCK' = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK20-CK10-CCK'=CK20-CK10-CCK'-CCK' = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK20-CK10-CCK'-CCK'=CK20-CK10-CS12-CS12 = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK20-CCK'=CK20-CS12-CS12-CS12-CCZ = ListNF.listnfeq' nf-e3 auto
  hypB L.ax-CCK'-CK20-CCK'-CCK'=CK20-CCK'-CCX0-CCZ = ListNF.listnfeq' nf-e3 auto


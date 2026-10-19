------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
--
-- The original was checked with --call-by-name, which saved memory
-- while the coset normal forms of CosetNF renormalised the whole
-- tail of a word at every letter.  They now act incrementally
-- (CosetNF.CosIns), and the default call-by-need checks this module
-- in under a minute and 1.4 GB.
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

import Examples.Groups.Clifford+CS-3qubit.Step4.HypB1 as HB1
import Examples.Groups.Clifford+CS-3qubit.Step4.HypB2 as HB2
import Examples.Groups.Clifford+CS-3qubit.Step4.HypB3 as HB3
import Examples.Groups.Clifford+CS-3qubit.Step4.HypB4 as HB4
import Examples.Groups.Clifford+CS-3qubit.Step4.HypB5 as HB5

module Examples.Groups.Clifford+CS-3qubit.Step4.Main where

  -- The translations, and Goal, now in Step4.Simple; the normal-form
  -- proofs of hypB in Step4.HypB1 ...
  open import Examples.Groups.Clifford+CS-3qubit.Step4.Simple public

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
  hypB L.ax-Swap01-CCX2-CCX1-CCX0-Swap12-Swap01=X1-CCX0-CCX2-CCX1-X1-CX21-CX20 = HB1.hb1
  hypB L.ax-Swap01-X1-CCX0-CCX1-CCX2=X2-CCX0-CCX2-CCX1-X1-X2-CX21-X0-CX10 = HB1.hb2
  hypB L.ax-Swap01-X1-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20 = HB1.hb3
  hypB L.ax-Swap01-X2-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-X2-CX21-X0-CX10-CX20 = HB1.hb4
  hypB L.ax-CX01-CCX2-CCX0-CX02-CCX1=X2-CCX0-CCX2-CCX1-X2-CX12-CX10 = HB1.hb5
  hypB L.ax-CX01-X1-CCX0-CCX1-CCX2=CCX0-CX21-CCX2-CX01-X1-CX20-CCX0 = HB1.hb6
  hypB L.ax-CX01-X1-CCX0-CCX2-CCX1=CX21-CCX0-CCX2-CX01-X1-CX21-CCX0 = HB1.hb7
  hypB L.ax-CX01-X2-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1-X2-CX12-CX10 = HB1.hb8
  hypB L.ax-CX01-CX21-CCX0-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX21-CCX0 = HB1.hb9
  hypB L.ax-CX01-CCX0-CX21-CCX2-CX01=X1-CCX0-CCX1-CCX2-X1-CCX0 = HB1.hb10
  hypB L.ax-CX02-CCX1-CCX0-CX01-CCX2=X1-CCX0-CCX1-CCX2-X1-CX21-CX20 = HB1.hb11
  hypB L.ax-CX02-X1-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2-X1-CX21-CX20 = HB1.hb12
  hypB L.ax-CX02-X1-CCX0-CCX2-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-X2-Swap12 = HB1.hb13
  hypB L.ax-CX02-X2-CCX0-CCX2-CCX1=CCX0-CX12-CCX1-CX02-X2-CX10-CCX0 = HB1.hb14
  hypB L.ax-CX02-CCX0-CX12-CCX1-CX02=X2-CCX0-CCX2-CCX1-X2-CCX0 = HB1.hb15
  hypB L.ax-CX02-CCX0-Swap12-CCX1-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-Swap12 = HB1.hb16
  hypB L.ax-CCX1-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX1-CCX2-X1-CX21-CX20 = HB1.hb17
  hypB L.ax-CCX1-CCX2-CCX0-CX02-CCX1=X2-CCX0-CCX2-CCX1-X2-CX12-CX10-CCX0 = HB1.hb18
  hypB L.ax-CCX1-X1-CCX0-CCX1-CCX2=CX01-CCX2-CCX0-CX01-X1-CX21-CX20 = HB1.hb19
  hypB L.ax-CCX1-X1-CCX0-CCX2-CCX1=X1-CCX0-CCX2-CCX1-CCX0 = HB1.hb20
  hypB L.ax-CCX1-X2-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1-X2-CX12-CX10-CCX0 = HB1.hb21
  hypB L.ax-CCX2-CX02-CCX1-CCX0-CX02=X2-CCX0-CCX2-CCX1-X2-CX12-CX10 = HB1.hb22
  hypB L.ax-CCX2-CCX1-CCX0-CX01-CCX2=X1-CCX0-CCX1-CCX2-X1-CX21-CX20-CCX0 = HB1.hb23
  hypB L.ax-CCX2-X1-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2-X1-CX21-CX20-CCX0 = HB1.hb24
  hypB L.ax-CCX2-X1-CCX0-CCX2-CCX1=CCX0-Swap12-CCX2-Swap01-X2-CX21-CX12-CX20 = HB1.hb25
  hypB L.ax-CCX2-X2-CCX0-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CX10 = HB1.hb26
  hypB L.ax-CCX2-CCX0-Swap12-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-CX12-CX21-CX10 = HB1.hb27
  hypB L.ax-X1-Swap01=Swap01-X0 = HB1.hb28
  hypB L.ax-X1-CX01=CX01-X1 = HB1.hb29
  hypB L.ax-X1-CX01-CCX2=CCX2-CX01-X1 = HB1.hb30
  hypB L.ax-X1-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX21-X0 = HB1.hb31
  hypB L.ax-X1-CX01-CCX2-CCX0-CX01=CCX2-CX10-CCX1-X1-CX21-X0-CX10 = HB1.hb32
  hypB L.ax-X1-CX01-CX20-CCX2=CX20-CX21-CCX2-CX01-X1 = HB1.hb33
  hypB L.ax-X1-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX21-X0 = HB1.hb34
  hypB L.ax-X1-CX01-CCX0-CX02=CX10-Swap12-CCX2-Swap01-X1-X2-CX12-CX20 = HB1.hb35
  hypB L.ax-X1-CX01-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-X0 = HB1.hb36
  hypB L.ax-X1-CX01-CCX0-CCX2-CX01=CX10-CCX2-CCX1-X2-CX21-CX12-X0-CX10 = HB1.hb37
  hypB L.ax-X1-CX02=CX02-X1 = HB1.hb38
  hypB L.ax-X1-CX02-CX01=CX02-CX01-X1 = HB1.hb39
  hypB L.ax-X1-CX02-CCX1=CX02-CCX1-X1 = HB1.hb40
  hypB L.ax-X1-CX02-CCX1-CCX0-CX02=CX20-CCX1-CCX2-CX01-X1-CX20 = HB1.hb41
  hypB L.ax-X1-CX02-CX10-CCX1=CX02-CX10-CCX1-X1-CX21-X0 = HB1.hb42
  hypB L.ax-X1-CX02-CCX0-CX01=CX02-CCX0-CX01-X1-CX21-CX20 = HB1.hb43
  hypB L.ax-X1-CCX1=CCX1-X1 = HB1.hb44
  hypB L.ax-X1-CCX1-CX01=CCX1-CX01-X1 = HB1.hb45
  hypB L.ax-X1-CCX1-CX01-CCX2=CCX1-CCX2-CX01-X1 = HB1.hb46
  hypB L.ax-X1-CCX1-CX02=CCX1-CX02-X1 = HB1.hb47
  hypB L.ax-X1-CCX1-CCX2=CCX1-CCX2-CX02-X1 = HB1.hb48
  hypB L.ax-X1-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX12-X0 = HB1.hb49
  hypB L.ax-X1-CCX1-CCX2-CX01=CCX1-CX01-CCX2-X1 = HB1.hb50
  hypB L.ax-X1-CCX1-CCX2-CX02=CCX1-CCX2-X1 = HB1.hb51
  hypB L.ax-X1-CCX1-CCX2-CCX0-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX21-X0 = HB1.hb52
  hypB L.ax-X1-CCX1-CX12-Swap01=CCX1-CX12-Swap01-X2-X0 = HB1.hb53
  hypB L.ax-X1-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-CX12-Swap01-X2-CX21-X0 = HB1.hb54
  hypB L.ax-X1-CCX1-CX20-CCX2-CX02=CX20-CCX2-CCX1-X1-CX21 = HB1.hb55
  hypB L.ax-X1-CCX1-CCX0-CX01-CCX2=CCX0-CX21-CCX2-CX01-X1-CX20-CCX0 = HB1.hb56
  hypB L.ax-X1-CCX1-CCX0-CX02=CCX1-CCX0-Swap12-Swap01-X2-Swap12-CX20 = HB1.hb57
  hypB L.ax-X1-CCX1-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-X0 = HB1.hb58
  hypB L.ax-X1-CCX1-CCX0-CX12-Swap01=CCX1-CX12-CCX0-Swap01-X1-X2-CX21-X0 = HB1.hb59
  hypB L.ax-X1-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-CX02-X1-Swap12-CX10 = HB1.hb60
  hypB L.ax-X1-CCX2=CCX2-CX02-X1 = HB1.hb61
  hypB L.ax-X1-CCX2-Swap01=CCX2-Swap01-CX12-X0 = HB1.hb62
  hypB L.ax-X1-CCX2-CX01=CX01-CCX2-X1 = HB1.hb63
  hypB L.ax-X1-CCX2-CX02=CCX2-X1 = HB1.hb64
  hypB L.ax-X1-CCX2-CX02-CCX1=CCX2-CCX1-X1 = HB1.hb65
  hypB L.ax-X1-CCX2-CCX1=CCX2-CX02-CCX1-X1 = HB1.hb66
  hypB L.ax-X1-CCX2-CCX1-CX01=CCX2-CCX1-CX02-X1 = HB1.hb67
  hypB L.ax-X1-CCX2-CCX1-CX02=CCX2-CCX1-CX01-X1 = HB1.hb68
  hypB L.ax-X1-CCX2-CCX1-CCX0-Swap12-Swap01=X2-CCX0-CCX2-CCX1-X1-CX21-CX12-X0-CX10-CX20 = HB1.hb69
  hypB L.ax-X1-CCX2-CX10-CCX1=CX01-CCX2-CCX0-CX01-X1-CX21-CX10-CX20 = HB1.hb70
  hypB L.ax-X1-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX12-CX21-X0 = HB1.hb71
  hypB L.ax-X1-CCX2-CCX0-CX01=CCX0-CX01-CCX2-X1-CX21-CX20 = HB1.hb72
  hypB L.ax-X1-CCX2-CCX0-CX02-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-X2-Swap12 = HB1.hb73
  hypB L.ax-X1-CCX2-CCX0-CX12-Swap01=CCX0-CCX2-CX01-X1-CX12-CX21-CX10-CX20 = HB1.hb74
  hypB L.ax-X1-X1-CCX0-CCX1-CCX2=CCX0-CCX1-CCX2 = HB1.hb75
  hypB L.ax-X1-X1-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1 = HB1.hb76
  hypB L.ax-X1-X2-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-X2-CX12-CX21-X0-CX20 = HB1.hb77
  hypB L.ax-X1-CX12-Swap01=CX12-Swap01-X2-X0 = HB1.hb78
  hypB L.ax-X1-CX12-CX01-CCX0-Swap01=CX10-CX12-CCX1-X2-CX21-X0 = HB1.hb79
  hypB L.ax-X1-CX12-CCX1=CX12-CCX1-CX01-X1-X2 = HB1.hb80
  hypB L.ax-X1-CX12-CCX1-CX01=CX12-CCX1-X1-X2 = HB1.hb81
  hypB L.ax-X1-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-CX21-CX12 = HB1.hb82
  hypB L.ax-X1-CX12-CCX2-Swap01=CX12-CCX2-Swap01-X2-CX12-X0 = HB1.hb83
  hypB L.ax-X1-CX12-CCX2-CCX0-Swap01=CCX0-CX12-CCX2-Swap01-X2-CX12-CX21-X0 = HB1.hb84
  hypB L.ax-X1-CX12-CCX0-Swap01=CCX0-CX12-Swap01-X2-CX21-X0 = HB1.hb85
  hypB L.ax-X1-CX21-CCX2-CX01=CX12-CCX1-CX02-X1-X2-CX12-CX21 = HB1.hb86
  hypB L.ax-X1-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-X0-CX20-CCX0 = HB1.hb87
  hypB L.ax-X1-CX21-CCX0-CCX2-CX01=CCX0-CX12-CCX1-CX02-X1-X2-CX12-CX21 = HB1.hb88
  hypB L.ax-X1-Swap12-Swap01=Swap12-Swap01-X2 = HB1.hb89
  hypB L.ax-X1-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-X2-CX12-CX10 = HB1.hb90
  hypB L.ax-X1-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-X2 = HB1.hb91
  hypB L.ax-X1-CX10-CX02-CCX1=CX10-CCX1-CX02-X1-X2-CX21-X0 = HB1.hb92
  hypB L.ax-X1-CX10-CCX1=CX10-CCX1-X1-CX21-X0 = HB1.hb93
  hypB L.ax-X1-CX10-CCX1-CX02=CX10-CX02-CCX1-X2-CX21-X0 = HB1.hb94
  hypB L.ax-X1-CX10-CCX1-CCX2-CX01=CX10-CCX2-CCX1-CX01-X1-X2-CX21-CX12-X0 = HB1.hb95
  hypB L.ax-X1-CX10-CCX2-CCX1=CX01-CCX0-CCX2-CX01-X1-CX12-CX21-CX10-CX20 = HB1.hb96
  hypB L.ax-X1-CX10-CCX2-CCX1-CX01=CX10-CCX1-CCX2-CX01-X2-CX12-CX21-X0 = HB1.hb97
  hypB L.ax-X1-CX10-CX12-CCX1=CX12-CX01-CCX0-Swap01-X1-X2-CX21-X0 = HB1.hb98
  hypB L.ax-X1-CX10-Swap12-CCX2-Swap01=CX01-CCX0-CX02-X1-CX12-CX10-CX20 = HB1.hb99
  hypB L.ax-X1-CX20-CX01-CCX2=CX20-CCX2-CX01-X1 = HB1.hb100
  hypB L.ax-X1-CX20-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1 = HB1.hb101
  hypB L.ax-X1-CX20-CCX1-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX12-X0 = HB1.hb102
  hypB L.ax-X1-CX20-CCX1-CCX2-CX01=CX02-CCX1-CCX0-CX02-X1-CX20 = HB1.hb103
  hypB L.ax-X1-CX20-CCX1-CCX2-CX02=CX20-CCX1-CCX2-X1 = HB1.hb104
  hypB L.ax-X1-CX20-CCX2=CX20-CCX2-CX02-X1 = HB1.hb105
  hypB L.ax-X1-CX20-CCX2-Swap01=CX20-CCX2-Swap01-CX12-X0 = HB1.hb106
  hypB L.ax-X1-CX20-CCX2-CX01=CX20-CX01-CCX2-X1 = HB1.hb107
  hypB L.ax-X1-CX20-CCX2-CX02=CX20-CCX2-X1 = HB1.hb108
  hypB L.ax-X1-CX20-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21 = HB1.hb109
  hypB L.ax-X1-CX20-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX02-X1 = HB1.hb110
  hypB L.ax-X1-CX20-CCX2-CCX1-CX02=CX20-CCX2-CCX1-CX01-X1 = HB1.hb111
  hypB L.ax-X1-CX20-CX21-CCX2-CX01=CX01-CX20-CCX2-X1 = HB1.hb112
  hypB L.ax-X1-CCX0-Swap01=CCX0-Swap01-CX21-X0 = HB1.hb113
  hypB L.ax-X1-CCX0-CX01=CCX0-CX01-X1-CX21-CX20 = HB1.hb114
  hypB L.ax-X1-CCX0-CX01-CCX2=CCX2-CCX0-CX01-X1-CX21-CX20 = HB1.hb115
  hypB L.ax-X1-CCX0-CX02=CCX0-Swap12-Swap01-X2-Swap12-CX20 = HB1.hb116
  hypB L.ax-X1-CCX0-CX02-CCX1=CCX0-Swap12-CCX2-Swap01-X2-CX21-CX12-CX20 = HB1.hb117
  hypB L.ax-X1-CCX0-CCX1-CX02=CCX0-CCX1-CX12-Swap01-X2-Swap12-X0-CX10-CX20 = HB1.hb118
  hypB L.ax-X1-CCX0-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX12-X0-CX20-CCX0 = HB1.hb119
  hypB L.ax-X1-CCX0-CCX1-CX12-Swap01=CCX0-CCX1-CX02-X1-Swap12-CX10-CX20 = HB1.hb120
  hypB L.ax-X1-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX21-CX12-X0 = HB1.hb121
  hypB L.ax-X1-CCX0-CCX2-CX01=CCX2-CCX0-CX12-Swap01-X2-CX21-CX12-X0-CX10 = HB1.hb122
  hypB L.ax-X1-CCX0-CX12-Swap01=CX12-CCX0-Swap01-X1-X2-CX21-X0 = HB1.hb123
  hypB L.ax-X1-CCX0-CX12-CCX1-CX02=CX21-CCX0-CCX2-CX01-X1-CX21-CX12 = HB1.hb124
  hypB L.ax-X1-CCX0-CX12-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-X1-X2-CX21-CX12-X0 = HB1.hb125
  hypB L.ax-X1-CCX0-CX21-CCX2-CX01=CCX1-CCX0-CX01-CCX2-X1-CCX0 = HB1.hb126
  hypB L.ax-X1-CCX0-Swap12-Swap01=CCX0-CX02-X1-Swap12-CX10 = HB1.hb127
  hypB L.ax-X1-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-X1-Swap12 = HB1.hb128
  hypB L.ax-X1-CCX0-Swap12-CCX2-Swap01=CCX0-CX02-CCX1-X1-CX12-CX21-CX10 = HB1.hb129
  hypB L.ax-X2-Swap01=Swap01-X2 = HB1.hb130
  hypB L.ax-X2-CX01=CX01-X2 = HB1.hb131
  hypB L.ax-X2-CX01-CCX2=CX01-CCX2-X2 = HB1.hb132
  hypB L.ax-X2-CX01-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-CX01-X2-CX10 = HB1.hb133
  hypB L.ax-X2-CX01-CCX2-CCX0-CX01=CX01-CCX2-CCX0-Swap01-X2-CX10 = HB1.hb134
  hypB L.ax-X2-CX01-CX20-CCX2=CX01-CX20-CCX2-X2-CX12-X0 = HB1.hb135
  hypB L.ax-X2-CX01-CCX0-Swap01=CX10-CCX1-X2 = HB1.hb136
  hypB L.ax-X2-CX01-CCX0-CX02=CX01-CCX0-CX02-X2-CX12-CX10 = HB1.hb137
  hypB L.ax-X2-CX01-CCX0-CCX2-Swap01=CCX2-CX10-CCX1-X2-CX12 = HB1.hb138
  hypB L.ax-X2-CX01-CCX0-CCX2-CX01=CX10-CCX1-CCX2-CX01-X2-CX10 = HB1.hb139
  hypB L.ax-X2-CX02=CX02-X2 = HB1.hb140
  hypB L.ax-X2-CX02-CX01=CX02-CX01-X2 = HB1.hb141
  hypB L.ax-X2-CX02-CCX1=CCX1-CX02-X2 = HB1.hb142
  hypB L.ax-X2-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-X1-X2-CX21-CX12-X0-CX20 = HB1.hb143
  hypB L.ax-X2-CX02-CX10-CCX1=CX20-CCX1-CCX2-Swap01-X1-Swap12-X0-CX20-CCX0 = HB1.hb144
  hypB L.ax-X2-CX02-CCX0-CX01=CX20-CCX2-Swap01-X1-X2-CX21-CX12-CX10 = HB1.hb145
  hypB L.ax-X2-CCX1=CCX1-CX01-X2 = HB1.hb146
  hypB L.ax-X2-CCX1-CX01=CCX1-X2 = HB1.hb147
  hypB L.ax-X2-CCX1-CX01-CCX2=CCX1-CCX2-X2 = HB1.hb148
  hypB L.ax-X2-CCX1-CX02=CX02-CCX1-X2 = HB1.hb149
  hypB L.ax-X2-CCX1-CCX2=CCX1-CX01-CCX2-X2 = HB1.hb150
  hypB L.ax-X2-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-X2-CX12-CX10 = HB1.hb151
  hypB L.ax-X2-CCX1-CCX2-CX01=CCX1-CCX2-CX02-X2 = HB1.hb152
  hypB L.ax-X2-CCX1-CCX2-CX02=CCX1-CCX2-CX01-X2 = HB1.hb153
  hypB L.ax-X2-CCX1-CCX2-CCX0-Swap01=X1-CCX0-CCX1-CCX2-X2-CX21-X0-CX10-CX20 = HB1.hb154
  hypB L.ax-X2-CCX1-CX12-Swap01=CCX1-CX12-Swap01-X2-CX12-CX10 = HB1.hb155
  hypB L.ax-X2-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX12-Swap01-X2-CX12-CX10 = HB1.hb156
  hypB L.ax-X2-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX01-CX12-X0 = HB1.hb157
  hypB L.ax-X2-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2-Swap01-X2 = HB1.hb158
  hypB L.ax-X2-CCX1-CCX0-CX02=CCX0-CX02-CCX1-X2-CX12-CX10 = HB1.hb159
  hypB L.ax-X2-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-X2-CX12-CX10 = HB1.hb160
  hypB L.ax-X2-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX02-X2-CX12-CX10 = HB1.hb161
  hypB L.ax-X2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX12-CX21-X0 = HB1.hb162
  hypB L.ax-X2-CCX2=CCX2-X2 = HB1.hb163
  hypB L.ax-X2-CCX2-Swap01=CCX2-Swap01-X2 = HB1.hb164
  hypB L.ax-X2-CCX2-CX01=CCX2-CX01-X2 = HB1.hb165
  hypB L.ax-X2-CCX2-CX02=CCX2-CX02-X2 = HB1.hb166
  hypB L.ax-X2-CCX2-CX02-CCX1=CCX2-CCX1-CX02-X2 = HB1.hb167
  hypB L.ax-X2-CCX2-CCX1=CCX2-CCX1-CX01-X2 = HB1.hb168
  hypB L.ax-X2-CCX2-CCX1-CX01=CCX2-CCX1-X2 = HB1.hb169
  hypB L.ax-X2-CCX2-CCX1-CX02=CCX2-CX02-CCX1-X2 = HB1.hb170
  hypB L.ax-X2-CCX2-CCX1-CCX0-Swap12-Swap01=X1-CCX0-CCX2-CCX1-X1-CX21-CX12-X0-CX10-CX20 = HB1.hb171
  hypB L.ax-X2-CCX2-CX10-CCX1=CX01-CCX0-CCX2-Swap01-X2-CX12 = HB1.hb172
  hypB L.ax-X2-CCX2-CCX0-Swap01=CCX2-CCX0-CX01-X2-CX10 = HB1.hb173
  hypB L.ax-X2-CCX2-CCX0-CX01=CCX2-CCX0-Swap01-X2-CX10 = HB1.hb174
  hypB L.ax-X2-CCX2-CCX0-CX02-CCX1=CCX0-CX12-CCX1-CX02-X2-CX10-CCX0 = HB1.hb175
  hypB L.ax-X2-CCX2-CCX0-CX12-Swap01=CX12-CCX2-CCX0-Swap01-X2 = HB1.hb176
  hypB L.ax-X2-X1-CCX0-CCX1-CCX2=CCX1-CCX2-CCX0-Swap01-X1-X2-CX21-X0-CX10 = HB1.hb177
  hypB L.ax-X2-X1-CCX0-CCX2-CCX1=CCX2-CCX1-CCX0-Swap12-Swap01-X1-X2-CX12-CX21-X0-CX20 = HB1.hb178
  hypB L.ax-X2-X2-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1 = HB1.hb179
  hypB L.ax-X2-CX12-Swap01=CX12-Swap01-X2 = HB1.hb180
  hypB L.ax-X2-CX12-CX01-CCX0-Swap01=CX10-CX12-CCX1-X2 = HB1.hb181
  hypB L.ax-X2-CX12-CCX1=CX12-CCX1-CX01-X2 = HB1.hb182
  hypB L.ax-X2-CX12-CCX1-CX01=CX12-CCX1-X2 = HB1.hb183
  hypB L.ax-X2-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-X2-CX21-CX12 = HB1.hb184
  hypB L.ax-X2-CX12-CCX2-Swap01=CX12-CCX2-Swap01-X2 = HB1.hb185
  hypB L.ax-X2-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-CX12-Swap01-X2 = HB1.hb186
  hypB L.ax-X2-CX12-CCX0-Swap01=CCX0-CX12-Swap01-X2 = HB1.hb187
  hypB L.ax-X2-CX21-CCX2-CX01=CX12-CCX1-CX02-X2-CX12-CX21 = HB1.hb188
  hypB L.ax-X2-CX21-CCX0-CCX2-Swap01=CCX0-CX21-CCX2-CX01-X1-X2-CX12-CX10 = HB1.hb189
  hypB L.ax-X2-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX1-CCX2-Swap01-CX12-X0-CX10-CX20-CCX0 = HB1.hb190
  hypB L.ax-X2-Swap12-Swap01=Swap12-Swap01-X0 = HB1.hb191
  hypB L.ax-X2-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX12-X0 = HB1.hb192
  hypB L.ax-X2-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12-X0 = HB1.hb193
  hypB L.ax-X2-CX10-CX02-CCX1=CX10-CCX1-CX02-X2 = HB1.hb194
  hypB L.ax-X2-CX10-CCX1=CX01-CCX0-Swap01-X2 = HB1.hb195
  hypB L.ax-X2-CX10-CCX1-CX02=CX10-CX02-CCX1-X2 = HB1.hb196
  hypB L.ax-X2-CX10-CCX1-CCX2-CX01=CX01-CCX0-CCX2-CX01-X2-CX10 = HB1.hb197
  hypB L.ax-X2-CX10-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2 = HB1.hb198
  hypB L.ax-X2-CX10-CCX2-CCX1-CX01=CX10-CCX2-CCX1-X2 = HB1.hb199
  hypB L.ax-X2-CX10-CX12-CCX1=CX12-CX01-CCX0-Swap01-X2 = HB1.hb200
  hypB L.ax-X2-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX12-X0 = HB1.hb201
  hypB L.ax-X2-CX20-CX01-CCX2=CX20-CCX2-CX01-X1-X2-CX12-X0 = HB1.hb202
  hypB L.ax-X2-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX01-X2-CX21-CX12-X0 = HB1.hb203
  hypB L.ax-X2-CX20-CCX1-CCX2-Swap01=CX02-CX10-CCX1-X2-Swap12-CX10-CX20-CCX0 = HB1.hb204
  hypB L.ax-X2-CX20-CCX1-CCX2-CX01=CCX1-CX20-CCX2-CX02-CX12-X0 = HB1.hb205
  hypB L.ax-X2-CX20-CCX1-CCX2-CX02=CX20-CCX2-CCX1-CX02-X1-CX21-CX12-X0 = HB1.hb206
  hypB L.ax-X2-CX20-CCX2=CX20-CCX2-X2-CX12-X0 = HB1.hb207
  hypB L.ax-X2-CX20-CCX2-Swap01=CX02-CCX0-CX01-X2-CX12-CX21-CX10-CX20 = HB1.hb208
  hypB L.ax-X2-CX20-CCX2-CX01=CX20-CX01-CCX2-X1-CX12-X0 = HB1.hb209
  hypB L.ax-X2-CX20-CCX2-CX02=CX20-CCX2-CX02-CX12-X0 = HB1.hb210
  hypB L.ax-X2-CX20-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CX21-CX10 = HB1.hb211
  hypB L.ax-X2-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-X1-CX12-CX21-X0 = HB1.hb212
  hypB L.ax-X2-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX02-X1-X2-CX12-CX21-X0 = HB1.hb213
  hypB L.ax-X2-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX12-X0 = HB1.hb214
  hypB L.ax-X2-CCX0-Swap01=CCX0-CX01-X2-CX10 = HB1.hb215
  hypB L.ax-X2-CCX0-CX01=CCX0-Swap01-X2-CX10 = HB1.hb216
  hypB L.ax-X2-CCX0-CX01-CCX2=CCX0-CCX2-Swap01-X2-CX12-CX10 = HB1.hb217
  hypB L.ax-X2-CCX0-CX02=CCX0-CX02-X2-CX12-CX10 = HB1.hb218
  hypB L.ax-X2-CCX0-CX02-CCX1=CCX1-CCX0-CX02-X2-CX12-CX10 = HB1.hb219
  hypB L.ax-X2-CCX0-CCX1-CX02=CCX1-CCX0-CX12-Swap01-X2-CX12-CX10 = HB1.hb220
  hypB L.ax-X2-CCX0-CCX1-CCX2=CCX1-CCX0-CCX2-Swap01-X2-CX12-CX10 = HB1.hb221
  hypB L.ax-X2-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CX01-CCX2-X2 = HB1.hb222
  hypB L.ax-X2-CCX0-CCX1-CX12-Swap01=CCX1-CX12-CCX0-Swap01-X2-CX12-CX10 = HB1.hb223
  hypB L.ax-X2-CCX0-CCX2-Swap01=CCX0-CX01-CCX2-X2-CX12-CX10 = HB1.hb224
  hypB L.ax-X2-CCX0-CCX2-CX01=CCX0-CX12-CCX2-Swap01-X2-CX10 = HB1.hb225
  hypB L.ax-X2-CCX0-CX12-Swap01=CX12-CCX0-Swap01-X2 = HB1.hb226
  hypB L.ax-X2-CCX0-CX12-CCX1-CX02=CCX2-CCX0-CX02-CCX1-X2-CCX0 = HB1.hb227
  hypB L.ax-X2-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-CX01-X2-CX10 = HB1.hb228
  hypB L.ax-X2-CCX0-CX21-CCX2-CX01=CX21-CCX0-CCX2-Swap01-X1-CX12-X0-CX10 = HB1.hb229
  hypB L.ax-X2-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21-X0 = HB1.hb230
  hypB L.ax-X2-CCX0-Swap12-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX12-X0-CX10-CX20-CCX0 = HB1.hb231
  hypB L.ax-X2-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX12-X0 = HB1.hb232
  hypB L.ax-CX12-CX02-CCX1-CCX0-CX02=X2-CCX0-CCX2-CCX1-X2-CX12-CCX0 = HB1.hb233
  hypB L.ax-CX12-X1-CCX0-CCX1-CCX2=CX20-CCX2-CCX1-CX02-X1-X2-CX12-X0-CX10-CX20-CCX0 = HB1.hb234
  hypB L.ax-CX12-X1-CCX0-CCX2-CCX1=CX20-CCX1-CCX2-CX01-X1-X2-CX12-X0-CX10-CX20-CCX0 = HB1.hb235
  hypB L.ax-CX12-X2-CCX0-CCX2-CCX1=CX02-CCX1-CCX0-CX02-X2-CX12-CCX0 = HB1.hb236
  hypB L.ax-CX12-CX20-CCX1-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX12-CCX0 = HB1.hb237
  hypB L.ax-CX12-CX20-CCX2-CCX1-CX02=X1-CCX0-CCX1-CCX2-X1-CX12-CCX0 = HB1.hb238
  hypB L.ax-CX21-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX1-CCX2-X1-CX21-CCX0 = HB1.hb239
  hypB L.ax-CX21-CX01-CCX0-CCX2-CX01=X1-CCX0-CCX2-CCX1-X1-CX21-CCX0 = HB1.hb240
  hypB L.ax-CX21-X1-CCX0-CCX1-CCX2=CX01-CCX2-CCX0-CX01-X1-CX21-CCX0 = HB1.hb241
  hypB L.ax-CX21-X1-CCX0-CCX2-CCX1=CX01-CCX0-CCX2-CX01-X1-CX21-CCX0 = HB1.hb242
  hypB L.ax-CX21-X2-CCX0-CCX2-CCX1=CX10-CCX1-CCX2-CX01-X1-X2-CX21-X0-CX10-CX20-CCX0 = HB1.hb243
  hypB L.ax-CX21-CX10-CCX1-CCX2-CX01=X2-CCX0-CCX2-CCX1-X2-CX21-CCX0 = HB1.hb244
  hypB L.ax-Swap12-CCX1-CCX0-CCX2-Swap01=X1-CCX0-CCX2-CCX1-X1-CX12-CX21-CX10 = HB1.hb245
  hypB L.ax-Swap12-X1-CCX0-CCX1-CCX2=X2-CCX0-CCX2-CCX1-Swap12 = HB1.hb246
  hypB L.ax-Swap12-X1-CCX0-CCX2-CCX1=CCX1-CCX0-CCX2-Swap01-X2-CX21-CX12-CX20 = HB1.hb247
  hypB L.ax-Swap12-X2-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-Swap12 = HB1.hb248
  hypB L.ax-X0-Swap01=Swap01-X1 = HB1.hb249
  hypB L.ax-X0-CX01=CX01-X1-X0 = HB1.hb250
  hypB L.ax-X0-CX01-CCX2=CCX2-CX01-X1-CX12-X0 = HB1.hb251
  hypB L.ax-X0-CX01-CCX2-CCX0-Swap01=CX10-CCX1-CCX2-CX01-X1-CX12-CX21-X0 = HB1.hb252
  hypB L.ax-X0-CX01-CCX2-CCX0-CX01=CX01-CCX0-CCX2-CX01-X2-CX12-CX21-X0-CX20 = HB1.hb253
  hypB L.ax-X0-CX01-CX20-CCX2=CX20-CX21-CCX2-CX01-X1-CX12-X0 = HB1.hb254
  hypB L.ax-X0-CX01-CCX0-Swap01=CX01-CCX0-Swap01-X1-CX21-X0 = HB1.hb255
  hypB L.ax-X0-CX01-CCX0-CX02=CX10-Swap12-CCX2-Swap01-X1-CX12-CX20 = HB1.hb256
  hypB L.ax-X0-CX01-CCX0-CCX2-Swap01=CX10-CCX2-CCX1-CX01-X1-CX21-CX12-X0 = HB1.hb257
  hypB L.ax-X0-CX01-CCX0-CCX2-CX01=CX01-CCX2-CCX0-CX01-X1-X2-CX21-CX12-CX10-CX20 = HB1.hb258
  hypB L.ax-X0-CX02=CX02-X2-X0 = HB1.hb259
  hypB L.ax-X0-CX02-CX01=CX02-CX01-X1-X2-X0 = HB1.hb260
  hypB L.ax-X0-CX02-CCX1=CCX1-CX02-X2-CX21-X0 = HB1.hb261
  hypB L.ax-X0-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX01-X1-CX21-CX12-X0-CX20 = HB1.hb262
  hypB L.ax-X0-CX02-CX10-CCX1=CX20-CCX1-CCX2-Swap01-X1-CX21-CX12-CCX0 = HB1.hb263
  hypB L.ax-X0-CX02-CCX0-CX01=CX20-CCX2-Swap01-X1-CX21-CX12-CX10 = HB1.hb264
  hypB L.ax-X0-CCX1=CCX1-CX21-X0 = HB1.hb265
  hypB L.ax-X0-CCX1-CX01=CCX1-CX01-X1-CX21-X0 = HB1.hb266
  hypB L.ax-X0-CCX1-CX01-CCX2=CCX2-CCX1-CX01-X1-CX21-CX12-X0 = HB1.hb267
  hypB L.ax-X0-CCX1-CX02=CX02-CCX1-X1-X2-CX21-X0 = HB1.hb268
  hypB L.ax-X0-CCX1-CCX2=CCX2-CCX1-CX21-CX12-X0 = HB1.hb269
  hypB L.ax-X0-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-X1-CX20 = HB1.hb270
  hypB L.ax-X0-CCX1-CCX2-CX01=CCX2-CCX1-CX02-X2-CX21-CX12-X0 = HB1.hb271
  hypB L.ax-X0-CCX1-CCX2-CX02=CCX2-CX02-CCX1-X1-X2-CX21-CX12-X0 = HB1.hb272
  hypB L.ax-X0-CCX1-CCX2-CCX0-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20 = HB1.hb273
  hypB L.ax-X0-CCX1-CX12-Swap01=Swap12-CCX2-Swap01-X1-CX20 = HB1.hb274
  hypB L.ax-X0-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01-X1-CX21-CX20 = HB1.hb275
  hypB L.ax-X0-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX02-X2-CX12-X0 = HB1.hb276
  hypB L.ax-X0-CCX1-CCX0-CX01-CCX2=CX21-CCX0-CCX2-CX01-X1-CX12-X0-CX20-CCX0 = HB1.hb277
  hypB L.ax-X0-CCX1-CCX0-CX02=CCX1-CCX0-CX12-Swap01-X1-Swap12-CX10-CX20 = HB1.hb278
  hypB L.ax-X0-CCX1-CCX0-CCX2-Swap01=X2-CCX0-CCX2-CCX1-X1-X2-CX21-X0-CX10 = HB1.hb279
  hypB L.ax-X0-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX02-X2-Swap12-X0-CX10-CX20 = HB1.hb280
  hypB L.ax-X0-CCX1-CCX0-Swap12-Swap01=CCX1-CX12-CCX0-Swap01-X1-CX21-CX20 = HB1.hb281
  hypB L.ax-X0-CCX2=CCX2-CX12-X0 = HB1.hb282
  hypB L.ax-X0-CCX2-Swap01=CX12-CCX2-Swap01-X1 = HB1.hb283
  hypB L.ax-X0-CCX2-CX01=CX01-CCX2-X1-X2-CX12-X0 = HB1.hb284
  hypB L.ax-X0-CCX2-CX02=CCX2-CX02-X2-CX12-X0 = HB1.hb285
  hypB L.ax-X0-CCX2-CX02-CCX1=CCX1-CCX2-CX02-X2-CX12-CX21-X0 = HB1.hb286
  hypB L.ax-X0-CCX2-CCX1=CCX1-CCX2-CX12-CX21-X0 = HB1.hb287
  hypB L.ax-X0-CCX2-CCX1-CX01=CCX1-CX01-CCX2-X1-X2-CX12-CX21-X0 = HB1.hb288
  hypB L.ax-X0-CCX2-CCX1-CX02=CCX1-CCX2-CX01-X1-CX12-CX21-X0 = HB1.hb289
  hypB L.ax-X0-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX2-CCX0-Swap01-X1-CX21-CX20 = HB1.hb290
  hypB L.ax-X0-CCX2-CX10-CCX1=CX10-CCX2-CCX1-CX21-X0 = HB1.hb291
  hypB L.ax-X0-CCX2-CCX0-Swap01=CX12-CCX2-CCX0-Swap01-X1 = HB1.hb292
  hypB L.ax-X0-CCX2-CCX0-CX01=CCX2-CCX0-CX12-Swap01-X1-CX10 = HB1.hb293
  hypB L.ax-X0-CCX2-CCX0-CX02-CCX1=CX21-CCX0-CCX2-Swap01-X1-CX21-CX12-CX10-CX20-CCX0 = HB1.hb294
  hypB L.ax-X0-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX01-X1-X0-CX10 = HB1.hb295
  hypB L.ax-X0-X1-CCX0-CCX1-CCX2=X1-CCX0-CCX2-CCX1-CX21-CX12-X0 = HB1.hb296
  hypB L.ax-X0-X1-CCX0-CCX2-CCX1=X1-CCX0-CCX1-CCX2-CX12-CX21-X0 = HB1.hb297
  hypB L.ax-X0-X2-CCX0-CCX2-CCX1=CCX1-CCX0-CCX2-Swap01-X2-CX21-X0-CX10-CX20 = HB1.hb298
  hypB L.ax-X0-CX12-Swap01=CX12-Swap01-X1 = HB1.hb299
  hypB L.ax-X0-CX12-CX01-CCX0-Swap01=CX12-CX01-CCX0-Swap01-X1-CX21-X0 = HB1.hb300
  hypB L.ax-X0-CX12-CCX1=CX12-CCX1-CX21-X0 = HB1.hb301
  hypB L.ax-X0-CX12-CCX1-CX01=CX12-CCX1-CX01-X1-CX21-X0 = HB1.hb302
  hypB L.ax-X0-CX12-CCX1-CX02=CX21-CCX2-CX01-X1-Swap12-X0 = HB1.hb303
  hypB L.ax-X0-CX12-CCX2-Swap01=CCX2-Swap01-X1 = HB1.hb304
  hypB L.ax-X0-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01-X1 = HB1.hb305
  hypB L.ax-X0-CX12-CCX0-Swap01=CX12-CCX0-Swap01-X1 = HB1.hb306
  hypB L.ax-X0-CX21-CCX2-CX01=CX12-CCX1-CX02-X2-Swap12-X0 = HB1.hb307
  hypB L.ax-X0-CX21-CCX0-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-X1-X2-CX12-CX21-X0-CX10-CCX0 = HB1.hb308
  hypB L.ax-X0-CX21-CCX0-CCX2-CX01=CCX1-CCX0-CX01-CCX2-X1-X2-CX12-X0-CCX0 = HB1.hb309
  hypB L.ax-X0-Swap12-Swap01=Swap12-Swap01-X1 = HB1.hb310
  hypB L.ax-X0-Swap12-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-X1-CX20 = HB1.hb311
  hypB L.ax-X0-Swap12-CCX2-Swap01=CCX1-CX12-Swap01-X1-CX20 = HB1.hb312
  hypB L.ax-X0-CX10-CX02-CCX1=CX10-CCX1-CX02-X2-CX21-X0 = HB1.hb313
  hypB L.ax-X0-CX10-CCX1=CX10-CCX1-CX21-X0 = HB1.hb314
  hypB L.ax-X0-CX10-CCX1-CX02=CX10-CX02-CCX1-X1-X2-CX21-X0 = HB1.hb315
  hypB L.ax-X0-CX10-CCX1-CCX2-CX01=CX01-CCX2-CCX0-Swap01-X2-CX21-CX12-X0 = HB1.hb316
  hypB L.ax-X0-CX10-CCX2-CCX1=CCX2-CX10-CCX1-CX21-X0 = HB1.hb317
  hypB L.ax-X0-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-Swap01-X1-X2-CX12-CX21-X0 = HB1.hb318
  hypB L.ax-X0-CX10-CX12-CCX1=CX10-CX12-CCX1-CX21-X0 = HB1.hb319
  hypB L.ax-X0-CX10-Swap12-CCX2-Swap01=CX01-CCX0-CX02-X1-X2-CX12-X0-CX10-CX20 = HB1.hb320
  hypB L.ax-X0-CX20-CX01-CCX2=CX20-CCX2-CX01-X1-CX12-X0 = HB1.hb321
  hypB L.ax-X0-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX21-CX12-X0 = HB1.hb322
  hypB L.ax-X0-CX20-CCX1-CCX2-Swap01=CX02-CX10-CCX1-X1-X2-CX12-CX21-X0-CX10-CX20-CCX0 = HB1.hb323
  hypB L.ax-X0-CX20-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX02-X2-CX21-CX12-X0 = HB1.hb324
  hypB L.ax-X0-CX20-CCX1-CCX2-CX02=CCX1-CX20-CCX2-CX02-X2-CX12-X0 = HB1.hb325
  hypB L.ax-X0-CX20-CCX2=CX20-CCX2-CX12-X0 = HB1.hb326
  hypB L.ax-X0-CX20-CCX2-Swap01=CX02-CCX0-CX01-X1-X2-CX12-CX21-X0-CX10-CX20 = HB1.hb327
  hypB L.ax-X0-CX20-CCX2-CX01=CX20-CX01-CCX2-X1-X2-CX12-X0 = HB1.hb328
  hypB L.ax-X0-CX20-CCX2-CX02=CX20-CCX2-CX02-X2-CX12-X0 = HB1.hb329
  hypB L.ax-X0-CX20-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-X0 = HB1.hb330
  hypB L.ax-X0-CX20-CCX2-CCX1-CX01=CX02-CCX1-CCX0-CX02-X1-X2-CX12-CX21-CX10 = HB1.hb331
  hypB L.ax-X0-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX01-X1-CX12-CX21-X0 = HB1.hb332
  hypB L.ax-X0-CX20-CX21-CCX2-CX01=CX01-CX20-CCX2-X1-X2-CX12-X0 = HB1.hb333
  hypB L.ax-X0-CCX0-Swap01=CCX0-Swap01-X1 = HB1.hb334
  hypB L.ax-X0-CCX0-CX01=CCX0-CX01-X1-X0 = HB1.hb335
  hypB L.ax-X0-CCX0-CX01-CCX2=CCX0-CCX2-CX01-X1-CX12-X0 = HB1.hb336
  hypB L.ax-X0-CCX0-CX02=CCX0-CX02-X2-X0 = HB1.hb337
  hypB L.ax-X0-CCX0-CX02-CCX1=CCX0-CCX1-CX02-X2-CX21-X0 = HB1.hb338
  hypB L.ax-X0-CCX0-CCX1-CX02=CCX0-CX02-CCX1-X1-X2-CX21-X0 = HB1.hb339
  hypB L.ax-X0-CCX0-CCX1-CCX2=CCX0-CCX2-CCX1-CX21-CX12-X0 = HB1.hb340
  hypB L.ax-X0-CCX0-CCX1-CCX2-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-X1-CX20 = HB1.hb341
  hypB L.ax-X0-CCX0-CCX1-CX12-Swap01=CCX0-Swap12-CCX2-Swap01-X1-CX20 = HB1.hb342
  hypB L.ax-X0-CCX0-CCX2-Swap01=CCX0-CX12-CCX2-Swap01-X1 = HB1.hb343
  hypB L.ax-X0-CCX0-CCX2-CX01=CCX0-CX01-CCX2-X1-X2-CX12-X0 = HB1.hb344
  hypB L.ax-X0-CCX0-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-X0 = HB1.hb345
  hypB L.ax-X0-CCX0-CX12-Swap01=CCX0-CX12-Swap01-X1 = HB1.hb346
  hypB L.ax-X0-CCX0-CX12-CCX1-CX02=CCX0-CX21-CCX2-CX01-X1-Swap12-X0 = HB1.hb347
  hypB L.ax-X0-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-Swap01-X1 = HB1.hb348
  hypB L.ax-X0-CCX0-CX21-CCX2-CX01=CCX0-CX12-CCX1-CX02-X2-Swap12-X0 = HB1.hb349
  hypB L.ax-X0-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-X1 = HB1.hb350
  hypB L.ax-X0-CCX0-Swap12-CCX1-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-X1-CX20 = HB1.hb351
  hypB L.ax-X0-CCX0-Swap12-CCX2-Swap01=CCX0-CCX1-CX12-Swap01-X1-CX20 = HB1.hb352
  hypB L.ax-CX10-CCX1-CX20-CCX2-CX02=X1-CCX0-CCX2-CCX1-X1-CX21-CX10-CCX0 = HB1.hb353
  hypB L.ax-CX10-X1-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1-X0-CX10-CX20-CCX0 = HB1.hb354
  hypB L.ax-CX10-X1-CCX0-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21-X0-CX10-CX20-CCX0 = HB1.hb355
  hypB L.ax-CX10-X2-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX01-X2-X0-CX10-CX20-CCX0 = HB1.hb356
  hypB L.ax-CX10-CX20-CCX1-CCX2-CX02=X1-CCX0-CCX1-CCX2-X1-CX10-CCX0 = HB1.hb357
  hypB L.ax-CX10-CX20-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2-CX20-CCX0 = HB1.hb358
  hypB L.ax-CX20-CX01-CCX2-CCX0-CX01=X1-CCX0-CCX2-CCX1-X1-CCX0 = HB1.hb359
  hypB L.ax-CX20-CX01-CCX0-CCX2-CX01=X1-CCX0-CCX1-CCX2-X1-CCX0 = HB1.hb360
  hypB L.ax-CX20-X1-CCX0-CCX1-CCX2=CX01-CCX0-CCX2-CX01-X1-CX20-CCX0 = HB1.hb361
  hypB L.ax-CX20-X1-CCX0-CCX2-CCX1=CX01-CCX2-CCX0-CX01-X1-CX20-CCX0 = HB1.hb362
  hypB L.ax-CX20-X2-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2-X0-CX10-CX20-CCX0 = HB1.hb363
  hypB L.ax-CX20-CX10-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2-CX20-CCX0 = HB1.hb364
  hypB L.ax-CCX0-CCX1-CX20-CCX2-CX02=X1-CCX0-CCX2-CCX1-X1-CX21 = HB1.hb365
  hypB L.ax-CCX0-X1-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-CX02-X1 = HB1.hb366
  hypB L.ax-CCX0-X1-CCX0-CCX2-CCX1=CCX1-CX20-CCX2-CX02-X1-CX21 = HB1.hb367
  hypB L.ax-CCX0-X2-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-CX01-X2 = HB1.hb368
  hypB L.ax-CCX0-CX10-CCX2-CCX1-CX01=X2-CCX0-CCX2-CCX1-X2 = HB1.hb369
  hypB L.ax-CCX0-CX20-CCX1-CCX2-CX02=X1-CCX0-CCX1-CCX2-X1 = HB1.hb370

  hypB L.ax-Swap01-CX01=CX01-CX10 = HB1.hb371
  hypB L.ax-Swap01-CX01-CCX2=CX01-CCX2-CX12-CX10 = HB1.hb372
  hypB L.ax-Swap01-CX01-CCX2-CCX0-Swap01=CX10-CCX2-CCX1 = HB1.hb373
  hypB L.ax-Swap01-CX01-CCX2-CCX0-CX01=CX10-CCX2-CCX1-CX01-CX10 = HB1.hb374
  hypB L.ax-Swap01-CX01-CX20-CCX2=CX01-CX20-CCX2-CX12-CX10 = HB1.hb375
  hypB L.ax-Swap01-CX01-CCX0-Swap01=CX10-CCX1 = HB1.hb376
  hypB L.ax-Swap01-CX01-CCX0-CX02=CX01-CCX0-CX02-CX12-CX10 = HB1.hb377
  hypB L.ax-Swap01-CX01-CCX0-CCX2-Swap01=CCX2-CX10-CCX1-CX12 = HB1.hb378
  hypB L.ax-Swap01-CX01-CCX0-CCX2-CX01=CX10-CCX1-CCX2-CX01-CX10 = HB1.hb379
  hypB L.ax-Swap01-CX02=CX12-Swap01 = HB1.hb380
  hypB L.ax-Swap01-CX02-CX01=CX02-CX01-CX12-CX10 = HB1.hb381
  hypB L.ax-Swap01-CX02-CCX1=CX12-CCX0-Swap01 = HB1.hb382
  hypB L.ax-Swap01-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CX01-CCX2-CX12-CX10-CCX0 = HB1.hb383
  hypB L.ax-Swap01-CX02-CX10-CCX1=CX12-CX01-CCX0-Swap01 = HB1.hb384
  hypB L.ax-Swap01-CX02-CCX0-CX01=CX12-CCX1-CX01-CX10 = HB1.hb385
  hypB L.ax-Swap01-CCX1=CCX0-Swap01 = HB1.hb386
  hypB L.ax-Swap01-CCX1-CX01=CCX0-CX01-CX10 = HB1.hb387
  hypB L.ax-Swap01-CCX1-CX01-CCX2=CCX0-CX01-CCX2-CX12-CX10 = HB1.hb388
  hypB L.ax-Swap01-CCX1-CX02=CCX0-CX12-Swap01 = HB1.hb389
  hypB L.ax-Swap01-CCX1-CCX2=CCX0-CCX2-Swap01 = HB1.hb390
  hypB L.ax-Swap01-CCX1-CCX2-Swap01=CX20-CCX2-CX20-CCX0 = HB1.hb391
  hypB L.ax-Swap01-CCX1-CCX2-CX01=CCX0-CCX2-CX01-CX10 = HB1.hb392
  hypB L.ax-Swap01-CCX1-CCX2-CX02=CCX0-CX12-CCX2-Swap01 = HB1.hb393
  hypB L.ax-Swap01-CCX1-CCX2-CCX0-Swap01=CCX0-CCX2-CCX1 = HB1.hb394
  hypB L.ax-Swap01-CCX1-CX12-Swap01=CCX0-CX02 = HB1.hb395
  hypB L.ax-Swap01-CCX1-CX12-CCX0-Swap01=CCX0-CX02-CCX1 = HB1.hb396
  hypB L.ax-Swap01-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb397
  hypB L.ax-Swap01-CCX1-CCX0-CX01-CCX2=CX02-CCX1-CCX0-CX02-CX12-CCX0 = HB1.hb398
  hypB L.ax-Swap01-CCX1-CCX0-CX02=CCX0-CCX1-CX12-Swap01 = HB1.hb399
  hypB L.ax-Swap01-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2 = HB1.hb400
  hypB L.ax-Swap01-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX02 = HB1.hb401
  hypB L.ax-Swap01-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-Swap12 = HB1.hb402
  hypB L.ax-Swap01-CCX2=CCX2-Swap01 = HB1.hb403
  hypB L.ax-Swap01-CCX2-Swap01=CCX2 = HB1.hb404
  hypB L.ax-Swap01-CCX2-CX01=CCX2-CX01-CX10 = HB1.hb405
  hypB L.ax-Swap01-CCX2-CX02=CX12-CCX2-Swap01 = HB1.hb406
  hypB L.ax-Swap01-CCX2-CX02-CCX1=CX12-CCX2-CCX0-Swap01 = HB1.hb407
  hypB L.ax-Swap01-CCX2-CCX1=CCX2-CCX0-Swap01 = HB1.hb408
  hypB L.ax-Swap01-CCX2-CCX1-CX01=CCX2-CCX0-CX01-CX10 = HB1.hb409
  hypB L.ax-Swap01-CCX2-CCX1-CX02=CCX2-CCX0-CX12-Swap01 = HB1.hb410
  hypB L.ax-Swap01-CCX2-CX10-CCX1=CX01-CCX0-CCX2-Swap01-CX12 = HB1.hb411
  hypB L.ax-Swap01-CCX2-CCX0-Swap01=CCX2-CCX1 = HB1.hb412
  hypB L.ax-Swap01-CCX2-CCX0-CX01=CCX2-CCX1-CX01-CX10 = HB1.hb413
  hypB L.ax-Swap01-CCX2-CCX0-CX02-CCX1=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0 = HB1.hb414
  hypB L.ax-Swap01-CCX2-CCX0-CX12-Swap01=CCX2-CCX1-CX02 = HB1.hb415
  hypB L.ax-Swap01-CX12-Swap01=CX02 = HB1.hb416
  hypB L.ax-Swap01-CX12-CX01-CCX0-Swap01=CX02-CX10-CCX1 = HB1.hb417
  hypB L.ax-Swap01-CX12-CCX1=CX20-CCX2-Swap01-CX21-CX12 = HB1.hb418
  hypB L.ax-Swap01-CX12-CCX1-CX01=CX02-CCX0-CX01-CX10 = HB1.hb419
  hypB L.ax-Swap01-CX12-CCX1-CX02=CX20-CX01-CCX2-Swap12-CX20 = HB1.hb420
  hypB L.ax-Swap01-CX12-CCX2-Swap01=CCX2-CX02 = HB1.hb421
  hypB L.ax-Swap01-CX12-CCX2-CCX0-Swap01=CCX2-CX02-CCX1 = HB1.hb422
  hypB L.ax-Swap01-CX12-CCX0-Swap01=CX02-CCX1 = HB1.hb423
  hypB L.ax-Swap01-CX21-CCX2-CX01=CX20-CCX2-CX01-CX10 = HB1.hb424
  hypB L.ax-Swap01-CX21-CCX0-CCX2-Swap01=CX20-CCX1-CCX2 = HB1.hb425
  hypB L.ax-Swap01-CX21-CCX0-CCX2-CX01=CX20-CCX1-CCX2-CX01-CX10 = HB1.hb426
  hypB L.ax-Swap01-Swap12-Swap01=Swap12-Swap01-Swap12 = HB1.hb427
  hypB L.ax-Swap01-Swap12-CCX1-CCX2-Swap01=CX20-CCX2-CX02-CX20-CCX0 = HB1.hb428
  hypB L.ax-Swap01-Swap12-CCX2-Swap01=CCX0-Swap12-Swap01-Swap12 = HB1.hb429
  hypB L.ax-Swap01-CX10-CX02-CCX1=CX10-CCX1-CX02 = HB1.hb430
  hypB L.ax-Swap01-CX10-CCX1=CX01-CCX0-Swap01 = HB1.hb431
  hypB L.ax-Swap01-CX10-CCX1-CX02=CX10-CX02-CCX1 = HB1.hb432
  hypB L.ax-Swap01-CX10-CCX1-CCX2-CX01=CX01-CCX0-CCX2-CX01-CX10 = HB1.hb433
  hypB L.ax-Swap01-CX10-CCX2-CCX1=CX01-CCX2-CCX0-Swap01 = HB1.hb434
  hypB L.ax-Swap01-CX10-CCX2-CCX1-CX01=CX01-CCX2-CCX0-CX01-CX10 = HB1.hb435
  hypB L.ax-Swap01-CX10-CX12-CCX1=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb436
  hypB L.ax-Swap01-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX12 = HB1.hb437
  hypB L.ax-Swap01-CX20-CX01-CCX2=CX12-CCX1-CX02-Swap12-CX10 = HB1.hb438
  hypB L.ax-Swap01-CX20-CCX1-CCX2=CX21-CCX0-CCX2-Swap01 = HB1.hb439
  hypB L.ax-Swap01-CX20-CCX1-CCX2-Swap01=CX10-CX12-CCX1-Swap12-CX10-CX20-CCX0 = HB1.hb440
  hypB L.ax-Swap01-CX20-CCX1-CCX2-CX01=CX21-CCX0-CCX2-CX01-CX10 = HB1.hb441
  hypB L.ax-Swap01-CX20-CCX1-CCX2-CX02=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10-CX20-CCX0 = HB1.hb442
  hypB L.ax-Swap01-CX20-CCX2=CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb443
  hypB L.ax-Swap01-CX20-CCX2-Swap01=CX12-CCX1-CX12-CX21 = HB1.hb444
  hypB L.ax-Swap01-CX20-CCX2-CX01=CX21-CCX2-CX01-CX10 = HB1.hb445
  hypB L.ax-Swap01-CX20-CCX2-CX02=Swap12-CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb446
  hypB L.ax-Swap01-CX20-CCX2-CCX1=CCX0-CCX1-CCX2-Swap01-CX21-CCX0 = HB1.hb447
  hypB L.ax-Swap01-CX20-CCX2-CCX1-CX01=CCX0-CX21-CCX2-CX01-CX21-CX10-CX20 = HB1.hb448
  hypB L.ax-Swap01-CX20-CCX2-CCX1-CX02=CCX0-CX12-CCX1-CX02-CX21-CX12-CX10-CX20 = HB1.hb449
  hypB L.ax-Swap01-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX10 = HB1.hb450
  hypB L.ax-Swap01-CCX0-Swap01=CCX1 = HB1.hb451
  hypB L.ax-Swap01-CCX0-CX01=CCX1-CX01-CX10 = HB1.hb452
  hypB L.ax-Swap01-CCX0-CX01-CCX2=CCX1-CX01-CCX2-CX12-CX10 = HB1.hb453
  hypB L.ax-Swap01-CCX0-CX02=CCX1-CX12-Swap01 = HB1.hb454
  hypB L.ax-Swap01-CCX0-CX02-CCX1=CCX1-CX12-CCX0-Swap01 = HB1.hb455
  hypB L.ax-Swap01-CCX0-CCX1-CX02=CCX1-CCX0-CX12-Swap01 = HB1.hb456
  hypB L.ax-Swap01-CCX0-CCX1-CCX2=CCX1-CCX0-CCX2-Swap01 = HB1.hb457
  hypB L.ax-Swap01-CCX0-CCX1-CCX2-Swap01=CX20-CCX2-CCX1-CX21-CX20-CCX0 = HB1.hb458
  hypB L.ax-Swap01-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX02 = HB1.hb459
  hypB L.ax-Swap01-CCX0-CCX2-Swap01=CCX1-CCX2 = HB1.hb460
  hypB L.ax-Swap01-CCX0-CCX2-CX01=CCX1-CCX2-CX01-CX10 = HB1.hb461
  hypB L.ax-Swap01-CCX0-CCX2-CCX1=CCX1-CCX2-CCX0-Swap01 = HB1.hb462
  hypB L.ax-Swap01-CCX0-CX12-Swap01=CCX1-CX02 = HB1.hb463
  hypB L.ax-Swap01-CCX0-CX12-CCX1-CX02=CX20-CCX2-CCX1-CX02-CX12-CX21-CX20 = HB1.hb464
  hypB L.ax-Swap01-CCX0-CX12-CCX2-Swap01=CCX1-CCX2-CX02 = HB1.hb465
  hypB L.ax-Swap01-CCX0-CX21-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21-CX10 = HB1.hb466
  hypB L.ax-Swap01-CCX0-Swap12-Swap01=Swap12-CCX2-Swap01-Swap12 = HB1.hb467
  hypB L.ax-Swap01-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX20-CCX0 = HB1.hb468
  hypB L.ax-Swap01-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-Swap12 = HB1.hb469
  hypB L.ax-CX01-Swap01=Swap01-CX10 = HB1.hb470
  hypB L.ax-CX01-CX01-CCX2=CCX2 = HB1.hb471
  hypB L.ax-CX01-CX01-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01 = HB1.hb472
  hypB L.ax-CX01-CX01-CCX2-CCX0-CX01=CCX2-CCX0-CX01 = HB1.hb473
  hypB L.ax-CX01-CX01-CX20-CCX2=CX20-CCX2 = HB1.hb474
  hypB L.ax-CX01-CX01-CCX0-Swap01=CCX0-Swap01 = HB1.hb475
  hypB L.ax-CX01-CX01-CCX0-CX02=CCX0-CX02 = HB1.hb476
  hypB L.ax-CX01-CX01-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01 = HB1.hb477
  hypB L.ax-CX01-CX01-CCX0-CCX2-CX01=CCX0-CCX2-CX01 = HB1.hb478
  hypB L.ax-CX01-CX02=CX02-CX01 = HB1.hb479
  hypB L.ax-CX01-CX02-CX01=CX02 = HB1.hb480
  hypB L.ax-CX01-CX02-CCX1=CCX1-CX02 = HB1.hb481
  hypB L.ax-CX01-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX21-CX20 = HB1.hb482
  hypB L.ax-CX01-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10 = HB1.hb483
  hypB L.ax-CX01-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10 = HB1.hb484
  hypB L.ax-CX01-CCX1=CCX1-CX01 = HB1.hb485
  hypB L.ax-CX01-CCX1-CX01=CCX1 = HB1.hb486
  hypB L.ax-CX01-CCX1-CX01-CCX2=CCX1-CCX2 = HB1.hb487
  hypB L.ax-CX01-CCX1-CX02=CX02-CCX1 = HB1.hb488
  hypB L.ax-CX01-CCX1-CCX2=CCX1-CX01-CCX2 = HB1.hb489


  hypB L.ax-CX01-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX12-CX10 = HB1.hb490
  hypB L.ax-CX01-CCX1-CCX2-CX01=CCX1-CCX2-CX02 = HB1.hb491
  hypB L.ax-CX01-CCX1-CCX2-CX02=CCX1-CCX2-CX01 = HB1.hb492
  hypB L.ax-CX01-CCX1-CCX2-CCX0-Swap01=CX21-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0 = HB1.hb493
  hypB L.ax-CX01-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CX12-CX10 = HB1.hb494
  hypB L.ax-CX01-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX02-CX12-CX10 = HB1.hb495
  hypB L.ax-CX01-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX01 = HB1.hb496
  hypB L.ax-CX01-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2 = HB1.hb497
  hypB L.ax-CX01-CCX1-CCX0-CX02=CCX0-CX02-CCX1 = HB1.hb498
  hypB L.ax-CX01-CCX1-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-CX10 = HB1.hb499
  hypB L.ax-CX01-CCX1-CCX0-CX12-Swap01=CCX0-CCX1-CX12-Swap01-CX12-CX10 = HB1.hb500
  hypB L.ax-CX01-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX12 = HB1.hb501
  hypB L.ax-CX01-CCX2-Swap01=CCX2-Swap01-CX12-CX10 = HB1.hb502
  hypB L.ax-CX01-CCX2-CX01=CCX2-CX02 = HB1.hb503
  hypB L.ax-CX01-CCX2-CX02=CCX2-CX01 = HB1.hb504
  hypB L.ax-CX01-CCX2-CX02-CCX1=CCX2-CCX1-CX01 = HB1.hb505
  hypB L.ax-CX01-CCX2-CCX1=CCX2-CCX1-CX02 = HB1.hb506
  hypB L.ax-CX01-CCX2-CCX1-CX01=CCX2-CX02-CCX1 = HB1.hb507
  hypB L.ax-CX01-CCX2-CCX1-CX02=CCX2-CCX1 = HB1.hb508
  hypB L.ax-CX01-CCX2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX10 = HB1.hb509
  hypB L.ax-CX01-CCX2-CX10-CCX1=CCX0-CX01-CCX2-CX10 = HB1.hb510
  hypB L.ax-CX01-CCX2-CCX0-CX12-Swap01=CX10-CCX2-CCX1 = HB1.hb511
  hypB L.ax-CX01-CX12-Swap01=CX12-Swap01-CX12-CX10 = HB1.hb512
  hypB L.ax-CX01-CX12-CX01-CCX0-Swap01=CX20-CCX2-CX01-CX21-CX12-CX20 = HB1.hb513
  hypB L.ax-CX01-CX12-CCX1=CX12-CCX1-CX02 = HB1.hb514
  hypB L.ax-CX01-CX12-CCX1-CX01=CX21-CCX2-CX01-CX21-CX12 = HB1.hb515
  hypB L.ax-CX01-CX12-CCX1-CX02=CX12-CCX1 = HB1.hb516
  hypB L.ax-CX01-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CX10 = HB1.hb517
  hypB L.ax-CX01-CX12-CCX2-CCX0-Swap01=CX10-CCX2-CCX1-CX01 = HB1.hb518
  hypB L.ax-CX01-CX12-CCX0-Swap01=CX10-CCX1-CX02 = HB1.hb519
  hypB L.ax-CX01-CX21-CCX2-CX01=CX12-CCX1-CX01-CX12-CX21 = HB1.hb520
  hypB L.ax-CX01-CX21-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0 = HB1.hb521
  hypB L.ax-CX01-Swap12-Swap01=Swap12-Swap01-CX12 = HB1.hb522
  hypB L.ax-CX01-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX10 = HB1.hb523
  hypB L.ax-CX01-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12 = HB1.hb524
  hypB L.ax-CX01-CX10-CX02-CCX1=CCX0-CX12-Swap01 = HB1.hb525
  hypB L.ax-CX01-CX10-CCX1=CCX0-CX01-CX10 = HB1.hb526
  hypB L.ax-CX01-CX10-CCX1-CX02=CX12-CCX0-Swap01 = HB1.hb527
  hypB L.ax-CX01-CX10-CCX1-CCX2-CX01=CCX0-CX12-CCX2-Swap01 = HB1.hb528
  hypB L.ax-CX01-CX10-CCX2-CCX1=CCX2-CCX0-CX12-Swap01 = HB1.hb529
  hypB L.ax-CX01-CX10-CCX2-CCX1-CX01=CX12-CCX2-CCX0-Swap01 = HB1.hb530
  hypB L.ax-CX01-CX10-CX12-CCX1=CX20-CX01-CCX2-Swap12-CX20 = HB1.hb531
  hypB L.ax-CX01-CX10-Swap12-CCX2-Swap01=CCX0-Swap12-Swap01-CX12-CX21 = HB1.hb532
  hypB L.ax-CX01-CX20-CX01-CCX2=CX10-CX12-CCX1-Swap12-CX10 = HB1.hb533
  hypB L.ax-CX01-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX02-CX21 = HB1.hb534
  hypB L.ax-CX01-CX20-CCX1-CCX2-Swap01=CX20-CCX2-Swap01-CX12-CX10-CX20-CCX0 = HB1.hb535
  hypB L.ax-CX01-CX20-CCX1-CCX2-CX01=CCX1-CX20-CCX2-CX02 = HB1.hb536
  hypB L.ax-CX01-CX20-CCX1-CCX2-CX02=CX20-CCX2-CCX1-CX01-CX21 = HB1.hb537
  hypB L.ax-CX01-CX20-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX12-CX10-CX20-CCX0 = HB1.hb538
  hypB L.ax-CX01-CX20-CCX2-CX01=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10 = HB1.hb539
  hypB L.ax-CX01-CX20-CCX2-CX02=CX20-CX21-CCX2-CX01 = HB1.hb540
  hypB L.ax-CX01-CX20-CCX2-CCX1=CX02-CCX1-CCX0-CX02-CX21-CX20 = HB1.hb541
  hypB L.ax-CX01-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX02-CX21 = HB1.hb542
  hypB L.ax-CX01-CX20-CCX2-CCX1-CX02=CX20-CCX1-CCX2-CX21 = HB1.hb543
  hypB L.ax-CX01-CX20-CX21-CCX2-CX01=CX20-CCX2-CX02 = HB1.hb544
  hypB L.ax-CX01-CCX0-CX01=CX10-CCX1-CX10 = HB1.hb545
  hypB L.ax-CX01-CCX0-CX01-CCX2=CCX2-CX10-CCX1-CX10 = HB1.hb546
  hypB L.ax-CX01-CCX0-CX02-CCX1=CCX1-CCX0-CX02 = HB1.hb547
  hypB L.ax-CX01-CCX0-CCX1-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX10 = HB1.hb548
  hypB L.ax-CX01-CCX0-CCX1-CCX2=CCX1-CCX0-CX01-CCX2 = HB1.hb549
  hypB L.ax-CX01-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10 = HB1.hb550
  hypB L.ax-CX01-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CX12-CX10 = HB1.hb551
  hypB L.ax-CX01-CCX0-CCX2-CCX1=CCX0-CX12-CCX1-CX02-CX12-CCX0 = HB1.hb552
  hypB L.ax-CX01-CCX0-CX12-Swap01=CX10-CX02-CCX1 = HB1.hb553
  hypB L.ax-CX01-CCX0-CX12-CCX1-CX02=CCX0-CCX2-CCX1-CX12-CX10-CCX0 = HB1.hb554
  hypB L.ax-CX01-CCX0-CX12-CCX2-Swap01=CX10-CCX1-CCX2-CX01 = HB1.hb555
  hypB L.ax-CX01-CCX0-Swap12-Swap01=CX10-Swap12-CCX2-Swap01-CX21-CX12 = HB1.hb556
  hypB L.ax-CX01-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10 = HB1.hb557
  hypB L.ax-CX01-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX12 = HB1.hb558
  hypB L.ax-CX02-Swap01=Swap01-CX12 = HB1.hb559
  hypB L.ax-CX02-CX01-CCX2=CCX2-CX01 = HB1.hb560
  hypB L.ax-CX02-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12 = HB1.hb561
  hypB L.ax-CX02-CX01-CCX2-CCX0-CX01=CCX2-CX10-CCX1-CX10 = HB1.hb562
  hypB L.ax-CX02-CX01-CX20-CCX2=CX01-CCX0-CX02-CX20 = HB1.hb563
  hypB L.ax-CX02-CX01-CCX0-Swap01=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb564
  hypB L.ax-CX02-CX01-CCX0-CX02=CX01-CX20-CCX2-CX20 = HB1.hb565
  hypB L.ax-CX02-CX01-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX12 = HB1.hb566
  hypB L.ax-CX02-CX01-CCX0-CCX2-CX01=CX10-CCX2-CCX1-CX01-CX12-CX10 = HB1.hb567
  hypB L.ax-CX02-CX02-CX01=CX01 = HB1.hb568
  hypB L.ax-CX02-CX02-CCX1=CCX1 = HB1.hb569
  hypB L.ax-CX02-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CX02 = HB1.hb570
  hypB L.ax-CX02-CX02-CX10-CCX1=CX10-CCX1 = HB1.hb571
  hypB L.ax-CX02-CX02-CCX0-CX01=CCX0-CX01 = HB1.hb572
  hypB L.ax-CX02-CCX1-CX01=CCX1-CX02 = HB1.hb573
  hypB L.ax-CX02-CCX1-CX01-CCX2=CCX1-CCX2-CX02 = HB1.hb574
  hypB L.ax-CX02-CCX1-CX02=CCX1-CX01 = HB1.hb575
  hypB L.ax-CX02-CCX1-CCX2=CCX1-CCX2-CX01 = HB1.hb576
  hypB L.ax-CX02-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CX10 = HB1.hb577
  hypB L.ax-CX02-CCX1-CCX2-CX01=CCX1-CCX2 = HB1.hb578
  hypB L.ax-CX02-CCX1-CCX2-CX02=CCX1-CX01-CCX2 = HB1.hb579
  hypB L.ax-CX02-CCX1-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CX10 = HB1.hb580
  hypB L.ax-CX02-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CX10 = HB1.hb581
  hypB L.ax-CX02-CCX1-CX12-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX20 = HB1.hb582
  hypB L.ax-CX02-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX2-Swap01-CX21-CX12 = HB1.hb583
  hypB L.ax-CX02-CCX1-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb584
  hypB L.ax-CX02-CCX1-CCX0-CX12-Swap01=CX20-CCX1-CCX2-Swap12-CX20 = HB1.hb585
  hypB L.ax-CX02-CCX1-CCX0-Swap12-Swap01=CX20-CCX1-CCX2-CX01-Swap12 = HB1.hb586
  hypB L.ax-CX02-CCX2=CCX2-CX02 = HB1.hb587
  hypB L.ax-CX02-CCX2-Swap01=CCX2-Swap01-CX12 = HB1.hb588
  hypB L.ax-CX02-CCX2-CX01=CX01-CCX2 = HB1.hb589
  hypB L.ax-CX02-CCX2-CX02=CCX2 = HB1.hb590
  hypB L.ax-CX02-CCX2-CX02-CCX1=CCX2-CCX1 = HB1.hb591
  hypB L.ax-CX02-CCX2-CCX1=CCX2-CX02-CCX1 = HB1.hb592
  hypB L.ax-CX02-CCX2-CCX1-CX01=CCX2-CCX1-CX02 = HB1.hb593
  hypB L.ax-CX02-CCX2-CCX1-CX02=CCX2-CCX1-CX01 = HB1.hb594
  hypB L.ax-CX02-CCX2-CCX1-CCX0-Swap12-Swap01=CX21-CCX0-CCX2-CX01-CX12-CX21-CCX0 = HB1.hb595
  hypB L.ax-CX02-CCX2-CX10-CCX1=CX01-CCX2-CCX0-CX01-CX10 = HB1.hb596
  hypB L.ax-CX02-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX12 = HB1.hb597
  hypB L.ax-CX02-CCX2-CCX0-CX01=CCX0-CX01-CCX2 = HB1.hb598
  hypB L.ax-CX02-CCX2-CCX0-CX02-CCX1=CCX0-CCX2-CCX1 = HB1.hb599
  hypB L.ax-CX02-CCX2-CCX0-CX12-Swap01=CCX0-CX12-CCX2-Swap01-CX12 = HB1.hb600
  hypB L.ax-CX02-CX12-Swap01=CX12-Swap01-CX12 = HB1.hb601
  hypB L.ax-CX02-CX12-CX01-CCX0-Swap01=CX10-CCX1-CX02 = HB1.hb602
  hypB L.ax-CX02-CX12-CCX1=CX21-CCX2-CX01-CX21-CX12 = HB1.hb603
  hypB L.ax-CX02-CX12-CCX1-CX01=CX12-CCX1-CX02 = HB1.hb604
  hypB L.ax-CX02-CX12-CCX1-CX02=CX12-CCX1-CX01 = HB1.hb605
  hypB L.ax-CX02-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CX12 = HB1.hb606
  hypB L.ax-CX02-CX12-CCX2-CCX0-Swap01=CCX0-CCX2-CX01-CX12-CX10 = HB1.hb607
  hypB L.ax-CX02-CX12-CCX0-Swap01=CX20-CCX2-CX01-CX21-CX12-CX20 = HB1.hb608

  hypB L.ax-CX02-CX21-CCX2-CX01=CX12-CCX1-CX12-CX21 = HB1.hb609
  hypB L.ax-CX02-CX21-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb610
  hypB L.ax-CX02-CX21-CCX0-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX21-CX12-CX20-CCX0 = HB1.hb611
  hypB L.ax-CX02-Swap12-Swap01=Swap12-Swap01-CX10 = HB1.hb612
  hypB L.ax-CX02-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX12-CX10 = HB1.hb613
  hypB L.ax-CX02-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01-CX12-CX10 = HB1.hb614
  hypB L.ax-CX02-CX10-CX02-CCX1=CX10-CX12-CCX1 = HB1.hb615
  hypB L.ax-CX02-CX10-CCX1-CX02=CX12-CX01-CCX0-Swap01 = HB1.hb616
  hypB L.ax-CX02-CX10-CCX1-CCX2-CX01=CX10-CCX2-CCX1-CX12 = HB1.hb617
  hypB L.ax-CX02-CX10-CCX2-CCX1=CX10-CCX1-CCX2-CX01-CX12 = HB1.hb618
  hypB L.ax-CX02-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-CX01-CX12-CX10 = HB1.hb619
  hypB L.ax-CX02-CX10-CX12-CCX1=CX10-CX02-CCX1 = HB1.hb620
  hypB L.ax-CX02-CX10-Swap12-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX12 = HB1.hb621
  hypB L.ax-CX02-CX20-CX01-CCX2=CCX0-CX12-Swap01-Swap12-CX10 = HB1.hb622
  hypB L.ax-CX02-CX20-CCX1-CCX2=CCX1-CCX0-CX12-Swap01-Swap12-CX10 = HB1.hb623
  hypB L.ax-CX02-CX20-CCX1-CCX2-Swap01=CX01-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb624
  hypB L.ax-CX02-CX20-CCX1-CCX2-CX01=CCX1-CCX0-Swap12-Swap01-Swap12 = HB1.hb625
  hypB L.ax-CX02-CX20-CCX1-CCX2-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10 = HB1.hb626
  hypB L.ax-CX02-CX20-CCX2=CCX0-CX02-CX20 = HB1.hb627
  hypB L.ax-CX02-CX20-CCX2-Swap01=CCX0-Swap01-CX12-CX21 = HB1.hb628
  hypB L.ax-CX02-CX20-CCX2-CX01=CX12-CCX0-Swap01-CX12-CX21-CX10 = HB1.hb629
  hypB L.ax-CX02-CX20-CCX2-CX02=CCX0-Swap12-Swap01-Swap12 = HB1.hb630
  hypB L.ax-CX02-CX20-CCX2-CCX1=CCX0-CX02-CCX1-CX21-CX20 = HB1.hb631
  hypB L.ax-CX02-CX20-CCX2-CCX1-CX01=CCX0-CCX1-CX02-CX20 = HB1.hb632
  hypB L.ax-CX02-CX20-CCX2-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10 = HB1.hb633
  hypB L.ax-CX02-CX20-CX21-CCX2-CX01=CX10-Swap12-CCX2-Swap01-CX12 = HB1.hb634
  hypB L.ax-CX02-CCX0-Swap01=CX20-CCX2-Swap01-CX21-CX12 = HB1.hb635
  hypB L.ax-CX02-CCX0-CX01-CCX2=CCX2-CCX0-CX01 = HB1.hb636
  hypB L.ax-CX02-CCX0-CX02=CX20-CCX2-CX20 = HB1.hb637
  hypB L.ax-CX02-CCX0-CX02-CCX1=CX20-CCX2-CCX1-CX21-CX20 = HB1.hb638
  hypB L.ax-CX02-CCX0-CCX1-CX02=CX20-CCX2-CCX1-CX01-CX20 = HB1.hb639
  hypB L.ax-CX02-CCX0-CCX1-CCX2=CCX0-CX21-CCX2-CX01-CX21-CCX0 = HB1.hb640
  hypB L.ax-CX02-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX10 = HB1.hb641
  hypB L.ax-CX02-CCX0-CCX1-CX12-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX20 = HB1.hb642
  hypB L.ax-CX02-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX12 = HB1.hb643
  hypB L.ax-CX02-CCX0-CCX2-CX01=CX12-CCX2-CCX0-Swap01-CX12-CX10 = HB1.hb644
  hypB L.ax-CX02-CCX0-CCX2-CCX1=CCX2-CCX0-CX02-CCX1 = HB1.hb645
  hypB L.ax-CX02-CCX0-CX12-Swap01=CX20-CX01-CCX2-Swap12-CX20 = HB1.hb646
  hypB L.ax-CX02-CCX0-CX12-CCX2-Swap01=CCX2-CCX0-CX12-Swap01-CX12 = HB1.hb647
  hypB L.ax-CX02-CCX0-CX21-CCX2-CX01=CCX0-CCX1-CCX2-CX21-CX20-CCX0 = HB1.hb648
  hypB L.ax-CX02-CCX0-Swap12-Swap01=CX20-CCX2-CX02-Swap12 = HB1.hb649
  hypB L.ax-CX02-CCX0-Swap12-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX12-CX21 = HB1.hb650
  hypB L.ax-CCX1-Swap01=Swap01-CCX0 = HB1.hb651
  hypB L.ax-CCX1-CX01-CCX2-CCX0-Swap01=CX21-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0 = HB1.hb652
  hypB L.ax-CCX1-CX01-CX20-CCX2=CX02-CCX1-CCX0-CX02-CX20 = HB1.hb653
  hypB L.ax-CCX1-CX01-CCX0-Swap01=CCX0-Swap01-CX10-CCX0 = HB1.hb654
  hypB L.ax-CCX1-CX01-CCX0-CX02=CCX0-CX02-CCX1 = HB1.hb655
  hypB L.ax-CCX1-CX01-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX12-CX10 = HB1.hb656
  hypB L.ax-CCX1-CX01-CCX0-CCX2-CX01=CX01-CCX0-CCX2-CX01-CCX0 = HB1.hb657
  hypB L.ax-CCX1-CX02-CX01=CX02-CCX1 = HB1.hb658
  hypB L.ax-CCX1-CX02-CCX1=CX02-CX01 = HB1.hb659
  hypB L.ax-CCX1-CX02-CCX1-CCX0-CX02=CX01-CX20-CCX2-CX20 = HB1.hb660
  hypB L.ax-CCX1-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10-CCX0 = HB1.hb661
  hypB L.ax-CCX1-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10-CCX0 = HB1.hb662
  hypB L.ax-CCX1-CCX1-CX01=CX01 = HB1.hb663
  hypB L.ax-CCX1-CCX1-CX01-CCX2=CX01-CCX2 = HB1.hb664
  hypB L.ax-CCX1-CCX1-CX02=CX02 = HB1.hb665
  hypB L.ax-CCX1-CCX1-CCX2-Swap01=CCX2-Swap01 = HB1.hb666
  hypB L.ax-CCX1-CCX1-CCX2-CX01=CCX2-CX01 = HB1.hb667
  hypB L.ax-CCX1-CCX1-CCX2-CX02=CCX2-CX02 = HB1.hb668
  hypB L.ax-CCX1-CCX1-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01 = HB1.hb669
  hypB L.ax-CCX1-CCX1-CX12-Swap01=CX12-Swap01 = HB1.hb670
  hypB L.ax-CCX1-CCX1-CX12-CCX0-Swap01=CX12-CCX0-Swap01 = HB1.hb671
  hypB L.ax-CCX1-CCX1-CX20-CCX2-CX02=CX20-CCX2-CX02 = HB1.hb672
  hypB L.ax-CCX1-CCX1-CCX0-CX01-CCX2=CCX0-CX01-CCX2 = HB1.hb673
  hypB L.ax-CCX1-CCX1-CCX0-CX02=CCX0-CX02 = HB1.hb674
  hypB L.ax-CCX1-CCX1-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01 = HB1.hb675
  hypB L.ax-CCX1-CCX1-CCX0-CX12-Swap01=CCX0-CX12-Swap01 = HB1.hb676
  hypB L.ax-CCX1-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01 = HB1.hb677
  hypB L.ax-CCX1-CCX2-CX02-CCX1=CX12-CCX1-CX01-CX12 = HB1.hb678
  hypB L.ax-CCX1-CCX2-CCX1=CX12-CCX1-CX12 = HB1.hb679
  hypB L.ax-CCX1-CCX2-CCX1-CX01=CX21-CCX2-CX01-CX21 = HB1.hb680
  hypB L.ax-CCX1-CCX2-CCX1-CX02=CX12-CCX1-CX02-CX12 = HB1.hb681
  hypB L.ax-CCX1-CCX2-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CCX0 = HB1.hb682
  hypB L.ax-CCX1-CCX2-CX10-CCX1=CCX0-CCX1-CCX2-CX10 = HB1.hb683
  hypB L.ax-CCX1-CCX2-CCX0-CX01=CCX0-CX21-CCX2-CX01-CX21-CCX0 = HB1.hb684
  hypB L.ax-CCX1-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX12-Swap01-CCX0 = HB1.hb685
  hypB L.ax-CCX1-CX12-CX01-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX20 = HB1.hb686
  hypB L.ax-CCX1-CX12-CCX1=CCX2-CCX1-CX12 = HB1.hb687
  hypB L.ax-CCX1-CX12-CCX1-CX01=CCX2-CX02-CCX1-CX12 = HB1.hb688
  hypB L.ax-CCX1-CX12-CCX1-CX02=CCX2-CCX1-CX02-CX12 = HB1.hb689
  hypB L.ax-CCX1-CX12-CCX2-Swap01=CX12-CCX2-Swap01-CCX0 = HB1.hb690
  hypB L.ax-CCX1-CX12-CCX2-CCX0-Swap01=CX10-CCX2-CCX1-CX01-CX10-CCX0 = HB1.hb691
  hypB L.ax-CCX1-CX21-CCX2-CX01=CCX2-CCX1-CX01-CX21 = HB1.hb692
  hypB L.ax-CCX1-CX21-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0 = HB1.hb693
  hypB L.ax-CCX1-CX21-CCX0-CCX2-CX01=CX21-CCX0-CCX2-CX01-CCX0 = HB1.hb694
  hypB L.ax-CCX1-Swap12-Swap01=Swap12-CCX2-Swap01 = HB1.hb695
  hypB L.ax-CCX1-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CCX0 = HB1.hb696
  hypB L.ax-CCX1-Swap12-CCX2-Swap01=Swap12-Swap01 = HB1.hb697
  hypB L.ax-CCX1-CX10-CX02-CCX1=CCX0-CCX1-CX12-Swap01-CX12-CX10 = HB1.hb698
  hypB L.ax-CCX1-CX10-CCX1=CX10-CCX1-CCX0 = HB1.hb699
  hypB L.ax-CCX1-CX10-CCX1-CX02=CCX0-CCX1-CX02-CX12-CX10 = HB1.hb700
  hypB L.ax-CCX1-CX10-CCX1-CCX2-CX01=CCX0-CX12-CCX2-Swap01-CX10-CCX0 = HB1.hb701
  hypB L.ax-CCX1-CX10-CCX2-CCX1=CX10-CCX2-CCX1-CCX0 = HB1.hb702
  hypB L.ax-CCX1-CX10-CCX2-CCX1-CX01=CX12-CCX2-CCX0-Swap01-CX10-CCX0 = HB1.hb703
  hypB L.ax-CCX1-CX10-CX12-CCX1=CX20-CCX1-CCX2-Swap12-CX20 = HB1.hb704
  hypB L.ax-CCX1-CX10-Swap12-CCX2-Swap01=CCX0-Swap12-CCX2-Swap01-CX21 = HB1.hb705
  hypB L.ax-CCX1-CX20-CX01-CCX2=CX20-CCX2-CCX1-CX02-CX21 = HB1.hb706
  hypB L.ax-CCX1-CX20-CCX1-CCX2=CX10-CX12-CCX1-Swap12-CX10 = HB1.hb707
  hypB L.ax-CCX1-CX20-CCX1-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb708
  hypB L.ax-CCX1-CX20-CCX1-CCX2-CX01=CX20-CX21-CCX2-CX01 = HB1.hb709
  hypB L.ax-CCX1-CX20-CCX1-CCX2-CX02=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10 = HB1.hb710
  hypB L.ax-CCX1-CX20-CCX2=CX20-CCX2-CCX1-CX21 = HB1.hb711
  hypB L.ax-CCX1-CX20-CCX2-Swap01=CX20-CCX2-Swap01-CX20-CCX0 = HB1.hb712
  hypB L.ax-CCX1-CX20-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21 = HB1.hb713
  hypB L.ax-CCX1-CX20-CCX2-CCX1=CX20-CCX2-CX21 = HB1.hb714
  hypB L.ax-CCX1-CX20-CCX2-CCX1-CX01=CX20-CCX2-CX01-CX21 = HB1.hb715

  hypB L.ax-CCX1-CX20-CCX2-CCX1-CX02=CX20-CX01-CCX2-CX21 = HB1.hb716
  hypB L.ax-CCX1-CX20-CX21-CCX2-CX01=CX20-CCX1-CCX2-CX01 = HB1.hb717
  hypB L.ax-CCX1-CCX0-Swap01=CX01-CCX0-Swap01-CX10-CCX0 = HB1.hb718
  hypB L.ax-CCX1-CCX0-CX01=CCX0-CX01-CCX0 = HB1.hb719
  hypB L.ax-CCX1-CCX0-CX02-CCX1=CX01-CCX0-CX02 = HB1.hb720
  hypB L.ax-CCX1-CCX0-CCX1-CX02=CX10-CCX1-CX02-CX12-CX10 = HB1.hb721
  hypB L.ax-CCX1-CCX0-CCX1-CCX2=CCX2-CX10-CCX1-CX10 = HB1.hb722
  hypB L.ax-CCX1-CCX0-CCX1-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10 = HB1.hb723
  hypB L.ax-CCX1-CCX0-CCX1-CX12-Swap01=CX10-CX02-CCX1-CX12-CX10 = HB1.hb724
  hypB L.ax-CCX1-CCX0-CCX2-CCX1=CCX0-CCX2-CCX1-CCX0 = HB1.hb725
  hypB L.ax-CCX1-CCX0-CX12-CCX1-CX02=CCX0-CX12-CCX1-CX02-CX10-CCX0 = HB1.hb726
  hypB L.ax-CCX1-CCX0-CX12-CCX2-Swap01=CX10-CCX1-CCX2-CX01-CX10-CCX0 = HB1.hb727
  hypB L.ax-CCX1-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20-CCX0 = HB1.hb728
  hypB L.ax-CCX1-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CCX0 = HB1.hb729
  hypB L.ax-CCX1-CCX0-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX21 = HB1.hb730
  hypB L.ax-CCX2-CX01-CCX2=CX02-CX01 = HB1.hb731
  hypB L.ax-CCX2-CX01-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb732
  hypB L.ax-CCX2-CX01-CCX2-CCX0-CX01=CX02-CX10-CCX1-CX10 = HB1.hb733
  hypB L.ax-CCX2-CX01-CX20-CCX2=CX01-CCX0-CX02-CX20-CCX0 = HB1.hb734
  hypB L.ax-CCX2-CX01-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12 = HB1.hb735
  hypB L.ax-CCX2-CX01-CCX0-CX02=CX01-CX20-CCX2-CX20-CCX0 = HB1.hb736
  hypB L.ax-CCX2-CX01-CCX0-CCX2-Swap01=CX01-CCX0-Swap01-CX12 = HB1.hb737
  hypB L.ax-CCX2-CX01-CCX0-CCX2-CX01=CX10-CCX1-CX02-CX12-CX10 = HB1.hb738
  hypB L.ax-CCX2-CX02-CX01=CX01-CCX2 = HB1.hb739
  hypB L.ax-CCX2-CX02-CX10-CCX1=CX01-CCX2-CCX0-CX01-CX10 = HB1.hb740
  hypB L.ax-CCX2-CX02-CCX0-CX01=CCX0-CX01-CCX2 = HB1.hb741
  hypB L.ax-CCX2-CCX1-CX01-CCX2=CX12-CCX1-CX01-CX12 = HB1.hb742
  hypB L.ax-CCX2-CCX1-CCX2=CX12-CCX1-CX12 = HB1.hb743
  hypB L.ax-CCX2-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01-CCX0 = HB1.hb744
  hypB L.ax-CCX2-CCX1-CCX2-CX01=CX21-CCX2-CX01-CX21 = HB1.hb745
  hypB L.ax-CCX2-CCX1-CCX2-CX02=CX12-CCX1-CX02-CX12 = HB1.hb746
  hypB L.ax-CCX2-CCX1-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CCX0 = HB1.hb747
  hypB L.ax-CCX2-CCX1-CX12-Swap01=CCX1-CX12-Swap01-CCX0 = HB1.hb748
  hypB L.ax-CCX2-CCX1-CX12-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0 = HB1.hb749
  hypB L.ax-CCX2-CCX1-CX20-CCX2-CX02=CCX0-Swap12-CCX1-CCX2-Swap01-Swap12-CX20 = HB1.hb750
  hypB L.ax-CCX2-CCX1-CCX0-CX02=CCX0-CX12-CCX1-CX02-CX12-CCX0 = HB1.hb751
  hypB L.ax-CCX2-CCX1-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CCX0 = HB1.hb752
  hypB L.ax-CCX2-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CCX0 = HB1.hb753
  hypB L.ax-CCX2-CCX2-Swap01=Swap01 = HB1.hb754
  hypB L.ax-CCX2-CCX2-CX02=CX02 = HB1.hb755
  hypB L.ax-CCX2-CCX2-CX02-CCX1=CX02-CCX1 = HB1.hb756
  hypB L.ax-CCX2-CCX2-CCX1=CCX1 = HB1.hb757
  hypB L.ax-CCX2-CCX2-CCX1-CX01=CCX1-CX01 = HB1.hb758
  hypB L.ax-CCX2-CCX2-CCX1-CX02=CCX1-CX02 = HB1.hb759
  hypB L.ax-CCX2-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-Swap12-Swap01 = HB1.hb760
  hypB L.ax-CCX2-CCX2-CX10-CCX1=CX10-CCX1 = HB1.hb761
  hypB L.ax-CCX2-CCX2-CCX0-Swap01=CCX0-Swap01 = HB1.hb762
  hypB L.ax-CCX2-CCX2-CCX0-CX01=CCX0-CX01 = HB1.hb763
  hypB L.ax-CCX2-CCX2-CCX0-CX02-CCX1=CCX0-CX02-CCX1 = HB1.hb764
  hypB L.ax-CCX2-CCX2-CCX0-CX12-Swap01=CCX0-CX12-Swap01 = HB1.hb765
  hypB L.ax-CCX2-CX12-Swap01=CX12-CCX2-Swap01 = HB1.hb766
  hypB L.ax-CCX2-CX12-CX01-CCX0-Swap01=CX10-CCX2-CCX1-CX01 = HB1.hb767
  hypB L.ax-CCX2-CX12-CCX1=CCX1-CCX2-CX12 = HB1.hb768
  hypB L.ax-CCX2-CX12-CCX1-CX01=CCX1-CX01-CCX2-CX12 = HB1.hb769
  hypB L.ax-CCX2-CX12-CCX1-CX02=CCX1-CCX2-CX02-CX12 = HB1.hb770
  hypB L.ax-CCX2-CX12-CCX2-Swap01=CX12-Swap01 = HB1.hb771
  hypB L.ax-CCX2-CX12-CCX2-CCX0-Swap01=CX12-CCX0-Swap01 = HB1.hb772
  hypB L.ax-CCX2-CX12-CCX0-Swap01=CX12-CCX2-CCX0-Swap01 = HB1.hb773
  hypB L.ax-CCX2-CX21-CCX2-CX01=CCX1-CCX2-CX01-CX21 = HB1.hb774
  hypB L.ax-CCX2-CX21-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CCX0 = HB1.hb775
  hypB L.ax-CCX2-CX21-CCX0-CCX2-CX01=CX20-CCX1-CCX2-CX01-CX21-CX20-CCX0 = HB1.hb776
  hypB L.ax-CCX2-Swap12-Swap01=Swap12-Swap01-CCX0 = HB1.hb777
  hypB L.ax-CCX2-Swap12-CCX1-CCX2-Swap01=Swap12-CCX2-Swap01 = HB1.hb778
  hypB L.ax-CCX2-Swap12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01 = HB1.hb779
  hypB L.ax-CCX2-CX10-CX02-CCX1=CX10-CCX1-CCX2-CX01-CX12 = HB1.hb780
  hypB L.ax-CCX2-CX10-CCX1-CX02=CX01-CCX0-CCX2-CX01-CX12-CX10 = HB1.hb781
  hypB L.ax-CCX2-CX10-CCX1-CCX2-CX01=CX10-CX02-CCX1-CX12 = HB1.hb782
  hypB L.ax-CCX2-CX10-CCX2-CCX1=CX10-CX12-CCX1 = HB1.hb783
  hypB L.ax-CCX2-CX10-CCX2-CCX1-CX01=CX12-CX01-CCX0-Swap01 = HB1.hb784
  hypB L.ax-CCX2-CX10-CX12-CCX1=CX10-CCX2-CCX1 = HB1.hb785
  hypB L.ax-CCX2-CX10-Swap12-CCX2-Swap01=CX10-Swap12-CCX2-Swap01-CX20-CCX0 = HB1.hb786
  hypB L.ax-CCX2-CX20-CX01-CCX2=CCX0-CX12-CCX2-Swap01-CX21-CX12-CX10 = HB1.hb787
  hypB L.ax-CCX2-CX20-CCX1-CCX2=CX20-CCX1-CCX2-CCX0 = HB1.hb788
  hypB L.ax-CCX2-CX20-CCX1-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb789
  hypB L.ax-CCX2-CX20-CCX1-CCX2-CX01=CX21-CCX0-CCX2-CX01-CX21-CCX0 = HB1.hb790
  hypB L.ax-CCX2-CX20-CCX1-CCX2-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10-CX20-CCX0 = HB1.hb791
  hypB L.ax-CCX2-CX20-CCX2=CX20-CCX2-CCX0 = HB1.hb792
  hypB L.ax-CCX2-CX20-CCX2-Swap01=CCX0-CCX2-Swap01-CX21 = HB1.hb793
  hypB L.ax-CCX2-CX20-CCX2-CX01=CCX0-CCX2-CX01-CX21-CX20 = HB1.hb794
  hypB L.ax-CCX2-CX20-CCX2-CX02=CCX0-Swap12-Swap01-Swap12-CX20-CCX0 = HB1.hb795
  hypB L.ax-CCX2-CX20-CCX2-CCX1=CCX0-CCX2-CCX1-CX21-CX20 = HB1.hb796
  hypB L.ax-CCX2-CX20-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX01-CCX0 = HB1.hb797
  hypB L.ax-CCX2-CX20-CCX2-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb798
  hypB L.ax-CCX2-CX20-CX21-CCX2-CX01=CX20-CX21-CCX2-CX01-CX20-CCX0 = HB1.hb799
  hypB L.ax-CCX2-CCX0-CX01-CCX2=CX02-CCX0-CX01 = HB1.hb800
  hypB L.ax-CCX2-CCX0-CX02=CCX0-CX02-CCX0 = HB1.hb801
  hypB L.ax-CCX2-CCX0-CCX1-CX02=CCX0-CCX1-CX02-CCX0 = HB1.hb802
  hypB L.ax-CCX2-CCX0-CCX1-CCX2=CCX0-CCX1-CCX2-CCX0 = HB1.hb803
  hypB L.ax-CCX2-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CCX0 = HB1.hb804
  hypB L.ax-CCX2-CCX0-CCX1-CX12-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX10-CX20-CCX0 = HB1.hb805
  hypB L.ax-CCX2-CCX0-CCX2-Swap01=CX20-CCX2-Swap01-CX21 = HB1.hb806
  hypB L.ax-CCX2-CCX0-CCX2-CX01=CX20-CCX2-CX01-CX21-CX20 = HB1.hb807
  hypB L.ax-CCX2-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX21-CX20 = HB1.hb808
  hypB L.ax-CCX2-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10-CCX0 = HB1.hb809
  hypB L.ax-CCX2-CCX0-CX12-CCX2-Swap01=CX20-CX01-CCX2-CX12-CX21-CX10-CX20 = HB1.hb810
  hypB L.ax-CCX2-CCX0-CX21-CCX2-CX01=CCX0-CX21-CCX2-CX01-CX20-CCX0 = HB1.hb811
  hypB L.ax-CCX2-CCX0-Swap12-Swap01=CX20-CCX2-CX02-Swap12-CX10-CCX0 = HB1.hb812
  hypB L.ax-CCX2-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CX20-CCX2-CX02-Swap12-CX10 = HB1.hb813
  hypB L.ax-CX12-CX01=CX02-CX01-CX12 = HB1.hb814
  hypB L.ax-CX12-CX01-CCX2=CCX2-CX01-CX12 = HB1.hb815
  hypB L.ax-CX12-CX01-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-CX01-CX12-CX10 = HB1.hb816
  hypB L.ax-CX12-CX01-CCX2-CCX0-CX01=CX10-CCX1-CCX2-CX01-CX12-CX10 = HB1.hb817
  hypB L.ax-CX12-CX01-CX20-CCX2=CX01-CCX0-CX02-CX10-CX20 = HB1.hb818
  hypB L.ax-CX12-CX01-CCX0-CX02=CX01-CX20-CCX2-CX10-CX20 = HB1.hb819
  hypB L.ax-CX12-CX01-CCX0-CCX2-Swap01=CX10-CCX2-CCX1-CX01-CX12 = HB1.hb820
  hypB L.ax-CX12-CX01-CCX0-CCX2-CX01=CX01-CCX2-CCX0-Swap01-CX12-CX10 = HB1.hb821

  hypB L.ax-CX12-CX02=CX02-CX12 = HB1.hb822
  hypB L.ax-CX12-CX02-CX01=CX01-CX12 = HB1.hb823
  hypB L.ax-CX12-CX02-CCX1=CX21-CCX2-CX01-CX21-CX12 = HB1.hb824
  hypB L.ax-CX12-CX02-CX10-CCX1=CX10-CX02-CCX1 = HB1.hb825
  hypB L.ax-CX12-CX02-CCX0-CX01=CX20-CX01-CCX2-Swap12-CX10-CX20 = HB1.hb826
  hypB L.ax-CX12-CCX1-CX01-CCX2=CCX2-CCX1-CX01-CX12 = HB1.hb827
  hypB L.ax-CX12-CCX1-CCX2=CCX2-CCX1-CX12 = HB1.hb828
  hypB L.ax-CX12-CCX1-CCX2-Swap01=CCX1-CX12-Swap01-CCX0 = HB1.hb829
  hypB L.ax-CX12-CCX1-CCX2-CX01=CCX2-CX02-CCX1-CX12 = HB1.hb830
  hypB L.ax-CX12-CCX1-CCX2-CX02=CCX2-CCX1-CX02-CX12 = HB1.hb831
  hypB L.ax-CX12-CCX1-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0 = HB1.hb832
  hypB L.ax-CX12-CCX1-CX12-Swap01=CCX1-CCX2-Swap01-CCX0 = HB1.hb833
  hypB L.ax-CX12-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CCX0 = HB1.hb834
  hypB L.ax-CX12-CCX1-CX20-CCX2-CX02=CCX2-CCX1-CCX0-Swap12-Swap01-CX12-CX21-CX10-CX20-CCX0 = HB1.hb835
  hypB L.ax-CX12-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CX12-Swap01-CX12-CCX0 = HB1.hb836
  hypB L.ax-CX12-CCX1-CCX0-CX02=CCX0-CX12-CCX1-CX02-CX12-CX10 = HB1.hb837
  hypB L.ax-CX12-CCX1-CCX0-CCX2-Swap01=CX20-CCX2-CCX1-CX01-CX10-CX20-CCX0 = HB1.hb838
  hypB L.ax-CX12-CCX1-CCX0-CX12-Swap01=CCX0-CX21-CCX2-CX01-CX21-CX10 = HB1.hb839
  hypB L.ax-CX12-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CCX0 = HB1.hb840
  hypB L.ax-CX12-CCX2=CCX2-CX12 = HB1.hb841
  hypB L.ax-CX12-CCX2-CX01=CX01-CCX2-CX12 = HB1.hb842
  hypB L.ax-CX12-CCX2-CX02=CCX2-CX02-CX12 = HB1.hb843
  hypB L.ax-CX12-CCX2-CX02-CCX1=CCX1-CCX2-CX01-CX12 = HB1.hb844
  hypB L.ax-CX12-CCX2-CCX1=CCX1-CCX2-CX12 = HB1.hb845
  hypB L.ax-CX12-CCX2-CCX1-CX01=CCX1-CX01-CCX2-CX12 = HB1.hb846
  hypB L.ax-CX12-CCX2-CCX1-CX02=CCX1-CCX2-CX02-CX12 = HB1.hb847
  hypB L.ax-CX12-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CX20-CCX2-CX02-CX21-CX12-CX10-CX20-CCX0 = HB1.hb848
  hypB L.ax-CX12-CCX2-CX10-CCX1=CX10-CCX2-CCX1 = HB1.hb849
  hypB L.ax-CX12-CCX2-CCX0-CX01=CCX2-CCX0-CX12-Swap01-CX10 = HB1.hb850
  hypB L.ax-CX12-CCX2-CCX0-CX02-CCX1=CCX0-CX02-CCX1-CX10-CCX0 = HB1.hb851
  hypB L.ax-CX12-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-CX01-CX10 = HB1.hb852
  hypB L.ax-CX12-CX12-Swap01=Swap01 = HB1.hb853
  hypB L.ax-CX12-CX12-CX01-CCX0-Swap01=CX01-CCX0-Swap01 = HB1.hb854
  hypB L.ax-CX12-CX12-CCX1=CCX1 = HB1.hb855
  hypB L.ax-CX12-CX12-CCX1-CX01=CCX1-CX01 = HB1.hb856
  hypB L.ax-CX12-CX12-CCX1-CX02=CCX1-CX02 = HB1.hb857
  hypB L.ax-CX12-CX12-CCX2-Swap01=CCX2-Swap01 = HB1.hb858
  hypB L.ax-CX12-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-Swap01 = HB1.hb859
  hypB L.ax-CX12-CX12-CCX0-Swap01=CCX0-Swap01 = HB1.hb860
  hypB L.ax-CX12-CX21-CCX2-CX01=CX02-CCX1-CX12-CX21 = HB1.hb861
  hypB L.ax-CX12-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CX02-Swap12-CX10 = HB1.hb862
  hypB L.ax-CX12-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX2-Swap01-CX10 = HB1.hb863
  hypB L.ax-CX12-Swap12-Swap01=Swap12-Swap01-CX20 = HB1.hb864
  hypB L.ax-CX12-Swap12-CCX1-CCX2-Swap01=Swap12-CCX2-Swap01-CX20-CCX0 = HB1.hb865
  hypB L.ax-CX12-Swap12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb866
  hypB L.ax-CX12-CX10-CX02-CCX1=CX02-CX10-CCX1 = HB1.hb867
  hypB L.ax-CX12-CX10-CCX1=CX10-CX12-CCX1 = HB1.hb868
  hypB L.ax-CX12-CX10-CCX1-CX02=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb869
  hypB L.ax-CX12-CX10-CCX1-CCX2-CX01=CX01-CCX2-CCX0-CX01-CX12-CX10 = HB1.hb870
  hypB L.ax-CX12-CX10-CCX2-CCX1=CCX2-CX10-CCX1 = HB1.hb871
  hypB L.ax-CX12-CX10-CCX2-CCX1-CX01=CX01-CCX0-CCX2-Swap01-CX12 = HB1.hb872
  hypB L.ax-CX12-CX10-CX12-CCX1=CX10-CCX1 = HB1.hb873
  hypB L.ax-CX12-CX10-Swap12-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10 = HB1.hb874
  hypB L.ax-CX12-CX20-CX01-CCX2=CX02-CCX0-CX01-Swap12-CX10-CX20 = HB1.hb875
  hypB L.ax-CX12-CX20-CCX1-CCX2=CCX0-CCX1-CCX2-Swap12-CX10-CX20-CCX0 = HB1.hb876
  hypB L.ax-CX12-CX20-CCX1-CCX2-Swap01=CX10-CCX1-CX02-Swap12-CX10-CX20-CCX0 = HB1.hb877
  hypB L.ax-CX12-CX20-CCX1-CCX2-CX02=CCX1-CCX2-CCX0-Swap01-CX12-CX21-CX10-CX20-CCX0 = HB1.hb878
  hypB L.ax-CX12-CX20-CCX2=CX20-CCX2-CX10 = HB1.hb879
  hypB L.ax-CX12-CX20-CCX2-Swap01=CX20-CCX2-CX01-CX10 = HB1.hb880
  hypB L.ax-CX12-CX20-CCX2-CX01=CX20-CCX2-Swap01-CX10 = HB1.hb881
  hypB L.ax-CX12-CX20-CCX2-CX02=CX20-CCX2-CX02-CX12-CX10 = HB1.hb882
  hypB L.ax-CX12-CX20-CCX2-CCX1=CCX0-CCX2-CCX1-CX21-CX10-CX20-CCX0 = HB1.hb883
  hypB L.ax-CX12-CX20-CCX2-CCX1-CX01=CCX1-CCX0-CCX2-Swap01-CX10-CX20-CCX0 = HB1.hb884
  hypB L.ax-CX12-CX20-CX21-CCX2-CX01=CX10-Swap12-CCX2-Swap01-CX10 = HB1.hb885
  hypB L.ax-CX12-CCX0-CX01=CCX0-CX12-Swap01-CX10 = HB1.hb886
  hypB L.ax-CX12-CCX0-CX01-CCX2=CCX0-CX12-CCX2-Swap01-CX12-CX10 = HB1.hb887
  hypB L.ax-CX12-CCX0-CX02=CCX0-CX02-CX10 = HB1.hb888
  hypB L.ax-CX12-CCX0-CX02-CCX1=CCX2-CCX0-CX02-CCX1-CX10-CCX0 = HB1.hb889
  hypB L.ax-CX12-CCX0-CCX1-CX02=CX21-CCX0-CCX2-Swap01-Swap12-CX20 = HB1.hb890
  hypB L.ax-CX12-CCX0-CCX1-CCX2=CX20-CCX1-CCX2-Swap12-CX10-CX20-CCX0 = HB1.hb891
  hypB L.ax-CX12-CCX0-CCX1-CCX2-Swap01=CCX1-CX12-CCX0-Swap01-CCX0 = HB1.hb892
  hypB L.ax-CX12-CCX0-CCX1-CX12-Swap01=CCX1-CCX0-CX01-CCX2-CX12-CX10-CCX0 = HB1.hb893
  hypB L.ax-CX12-CCX0-CCX2-Swap01=CCX0-CCX2-CX01-CX10 = HB1.hb894
  hypB L.ax-CX12-CCX0-CCX2-CX01=CCX0-CCX2-Swap01-CX10 = HB1.hb895
  hypB L.ax-CX12-CCX0-CCX2-CCX1=CX20-CCX2-CCX1-CX21-CX10-CX20-CCX0 = HB1.hb896
  hypB L.ax-CX12-CCX0-CX12-Swap01=CCX0-CX01-CX10 = HB1.hb897
  hypB L.ax-CX12-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10 = HB1.hb898
  hypB L.ax-CX12-CCX0-CX12-CCX2-Swap01=CCX0-CX01-CCX2-CX12-CX10 = HB1.hb899
  hypB L.ax-CX12-CCX0-CX21-CCX2-CX01=CCX1-CCX0-CX12-Swap01-CX21-CX10-CX20 = HB1.hb900
  hypB L.ax-CX12-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21-CX20 = HB1.hb901
  hypB L.ax-CX12-CCX0-Swap12-CCX1-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX20-CCX0 = HB1.hb902
  hypB L.ax-CX12-CCX0-Swap12-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10 = HB1.hb903
  hypB L.ax-CX21-Swap01=Swap01-CX20 = HB1.hb904
  hypB L.ax-CX21-CX01=CX01-CX21 = HB1.hb905
  hypB L.ax-CX21-CX01-CCX2=CX12-CCX1-CX02-CX12-CX21 = HB1.hb906
  hypB L.ax-CX21-CX01-CCX2-CCX0-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0 = HB1.hb907
  hypB L.ax-CX21-CX01-CX20-CCX2=CX20-CX01-CCX2 = HB1.hb908
  hypB L.ax-CX21-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX21-CX20 = HB1.hb909
  hypB L.ax-CX21-CX01-CCX0-CX02=CX10-CX02-CCX1-Swap12-CX10-CX20 = HB1.hb910
  hypB L.ax-CX21-CX01-CCX0-CCX2-Swap01=CCX1-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0 = HB1.hb911
  hypB L.ax-CX21-CX02=CX02-CX01-CX21 = HB1.hb912
  hypB L.ax-CX21-CX02-CX01=CX02-CX21 = HB1.hb913
  hypB L.ax-CX21-CX02-CCX1=CCX1-CX02-CX21 = HB1.hb914
  hypB L.ax-CX21-CX02-CCX1-CCX0-CX02=CX20-CCX2-CCX1-CX02-CX21-CX20 = HB1.hb915
  hypB L.ax-CX21-CX02-CX10-CCX1=CX02-CCX0-CX01-CX10-CX20 = HB1.hb916
  hypB L.ax-CX21-CX02-CCX0-CX01=CX02-CX10-CCX1-CX10-CX20 = HB1.hb917
  hypB L.ax-CX21-CCX1=CCX1-CX21 = HB1.hb918
  hypB L.ax-CX21-CCX1-CX01=CCX1-CX01-CX21 = HB1.hb919
  hypB L.ax-CX21-CCX1-CX01-CCX2=CCX2-CCX1-CX02-CX21 = HB1.hb920
  hypB L.ax-CX21-CCX1-CX02=CX02-CCX1-CX21 = HB1.hb921
  hypB L.ax-CX21-CCX1-CCX2=CCX2-CCX1-CX21 = HB1.hb922
  hypB L.ax-CX21-CCX1-CCX2-Swap01=CCX2-Swap01-CX20-CCX0 = HB1.hb923
  hypB L.ax-CX21-CCX1-CCX2-CX01=CCX2-CCX1-CX01-CX21 = HB1.hb924
  hypB L.ax-CX21-CCX1-CCX2-CX02=CCX2-CX02-CCX1-CX21 = HB1.hb925
  hypB L.ax-CX21-CCX1-CCX2-CCX0-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX21-CX10-CX20-CCX0 = HB1.hb926
  hypB L.ax-CX21-CCX1-CX12-Swap01=Swap12-CCX2-Swap01-CX20 = HB1.hb927

  hypB L.ax-CX21-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01-CX21-CX20 = HB1.hb928
  hypB L.ax-CX21-CCX1-CX20-CCX2-CX02=CX20-CCX1-CCX2-CX02 = HB1.hb929
  hypB L.ax-CX21-CCX1-CCX0-CX01-CCX2=CCX0-CX01-CCX2-CX20-CCX0 = HB1.hb930
  hypB L.ax-CX21-CCX1-CCX0-CX02=CCX1-CCX0-CX12-Swap01-Swap12-CX10-CX20 = HB1.hb931
  hypB L.ax-CX21-CCX1-CCX0-CCX2-Swap01=CX01-CCX2-CCX0-Swap01-CX21-CX12-CX10-CX20-CCX0 = HB1.hb932
  hypB L.ax-CX21-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-CX02-Swap12-CX10-CX20 = HB1.hb933
  hypB L.ax-CX21-CCX1-CCX0-Swap12-Swap01=CCX1-CX12-CCX0-Swap01-CX21-CX20 = HB1.hb934
  hypB L.ax-CX21-CCX2=CX12-CCX1-CX12-CX21 = HB1.hb935
  hypB L.ax-CX21-CCX2-Swap01=CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb936
  hypB L.ax-CX21-CCX2-CX02=CX12-CCX1-CX01-CX12-CX21 = HB1.hb937
  hypB L.ax-CX21-CCX2-CX02-CCX1=CCX1-CCX2-CX02-CX21 = HB1.hb938
  hypB L.ax-CX21-CCX2-CCX1=CCX1-CCX2-CX21 = HB1.hb939
  hypB L.ax-CX21-CCX2-CCX1-CX01=CCX1-CCX2-CX01-CX21 = HB1.hb940
  hypB L.ax-CX21-CCX2-CCX1-CX02=CCX1-CX01-CCX2-CX21 = HB1.hb941
  hypB L.ax-CX21-CCX2-CCX1-CCX0-Swap12-Swap01=CX10-CCX2-CCX1-CX01-CX21-CX10-CX20-CCX0 = HB1.hb942
  hypB L.ax-CX21-CCX2-CX10-CCX1=CCX0-CCX1-CCX2-CX10-CX20-CCX0 = HB1.hb943
  hypB L.ax-CX21-CCX2-CCX0-Swap01=CCX0-CCX1-CCX2-Swap01-CX21-CCX0 = HB1.hb944
  hypB L.ax-CX21-CCX2-CCX0-CX01=CCX0-CX21-CCX2-CX01-CX21-CX20 = HB1.hb945
  hypB L.ax-CX21-CCX2-CCX0-CX02-CCX1=CCX0-CX12-CCX2-Swap01-CX21-CX12-CX10-CX20-CCX0 = HB1.hb946
  hypB L.ax-CX21-CCX2-CCX0-CX12-Swap01=CCX0-CX12-CCX1-CX02-CX21-CX12-CX10-CX20 = HB1.hb947
  hypB L.ax-CX21-CX12-Swap01=Swap12-Swap01-CX20 = HB1.hb948
  hypB L.ax-CX21-CX12-CX01-CCX0-Swap01=CX20-CCX2-CX02-CX21-CX12-CX20 = HB1.hb949
  hypB L.ax-CX21-CX12-CCX1=CCX2-CX21-CX12 = HB1.hb950
  hypB L.ax-CX21-CX12-CCX1-CX01=CCX2-CX02-CX21-CX12 = HB1.hb951
  hypB L.ax-CX21-CX12-CCX1-CX02=CX01-CCX2-CX21-CX12 = HB1.hb952
  hypB L.ax-CX21-CX12-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb953
  hypB L.ax-CX21-CX12-CCX2-CCX0-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CCX0 = HB1.hb954
  hypB L.ax-CX21-CX12-CCX0-Swap01=CCX0-Swap12-Swap01-CX21-CX20 = HB1.hb955
  hypB L.ax-CX21-CX21-CCX2-CX01=CCX2-CX01 = HB1.hb956
  hypB L.ax-CX21-CX21-CCX0-CCX2-Swap01=CCX0-CCX2-Swap01 = HB1.hb957
  hypB L.ax-CX21-CX21-CCX0-CCX2-CX01=CCX0-CCX2-CX01 = HB1.hb958
  hypB L.ax-CX21-Swap12-Swap01=CX12-Swap01-CX20 = HB1.hb959
  hypB L.ax-CX21-Swap12-CCX1-CCX2-Swap01=CX12-CCX2-Swap01-CX20-CCX0 = HB1.hb960
  hypB L.ax-CX21-Swap12-CCX2-Swap01=CCX1-CX12-Swap01-CX20 = HB1.hb961
  hypB L.ax-CX21-CX10-CX02-CCX1=CX01-CCX0-CX02-Swap12-CX10-CX20 = HB1.hb962
  hypB L.ax-CX21-CX10-CCX1=CX10-CCX1-CX20 = HB1.hb963
  hypB L.ax-CX21-CX10-CCX1-CX02=CX10-Swap12-CCX2-Swap01-Swap12-CX20 = HB1.hb964
  hypB L.ax-CX21-CX10-CCX2-CCX1=CCX0-CCX2-CCX1-Swap12-CX10-CX20-CCX0 = HB1.hb965
  hypB L.ax-CX21-CX10-CCX2-CCX1-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX21-CX10-CX20-CCX0 = HB1.hb966
  hypB L.ax-CX21-CX10-CX12-CCX1=CX20-CCX2-Swap12-CX20 = HB1.hb967
  hypB L.ax-CX21-CX10-Swap12-CCX2-Swap01=CX10-CCX1-CX02-Swap12-CX10 = HB1.hb968
  hypB L.ax-CX21-CX20-CX01-CCX2=CX01-CX20-CCX2 = HB1.hb969
  hypB L.ax-CX21-CX20-CCX1-CCX2=CX20-CCX2-CCX1-CX21 = HB1.hb970
  hypB L.ax-CX21-CX20-CCX1-CCX2-Swap01=CX20-CCX2-Swap01-CX20-CCX0 = HB1.hb971
  hypB L.ax-CX21-CX20-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX01-CX21 = HB1.hb972
  hypB L.ax-CX21-CX20-CCX1-CCX2-CX02=CCX1-CX20-CCX2-CX02 = HB1.hb973
  hypB L.ax-CX21-CX20-CCX2=CX10-CX12-CCX1-Swap12-CX10 = HB1.hb974
  hypB L.ax-CX21-CX20-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb975
  hypB L.ax-CX21-CX20-CCX2-CX01=CX20-CX21-CCX2-CX01 = HB1.hb976
  hypB L.ax-CX21-CX20-CCX2-CX02=CX12-CX01-CCX0-Swap01-CX12-CX21-CX10 = HB1.hb977
  hypB L.ax-CX21-CX20-CCX2-CCX1=CX20-CCX1-CCX2-CX21 = HB1.hb978
  hypB L.ax-CX21-CX20-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX01-CX21 = HB1.hb979
  hypB L.ax-CX21-CX20-CCX2-CCX1-CX02=CX02-CCX1-CCX0-CX02-CX21-CX20 = HB1.hb980
  hypB L.ax-CX21-CX20-CX21-CCX2-CX01=CX20-CCX2-CX01 = HB1.hb981
  hypB L.ax-CX21-CCX0-Swap01=CCX0-Swap01-CX21-CX20 = HB1.hb982
  hypB L.ax-CX21-CCX0-CX01=CCX0-CX01-CX20 = HB1.hb983
  hypB L.ax-CX21-CCX0-CX01-CCX2=CCX1-CCX0-CX01-CCX2-CX20-CCX0 = HB1.hb984
  hypB L.ax-CX21-CCX0-CX02=CCX0-CX12-Swap01-Swap12-CX10-CX20 = HB1.hb985
  hypB L.ax-CX21-CCX0-CX02-CCX1=CCX0-CCX1-CX12-Swap01-CX21-CX12-CX10 = HB1.hb986
  hypB L.ax-CX21-CCX0-CCX1-CX02=CCX0-Swap12-CCX2-Swap01-Swap12-CX20 = HB1.hb987
  hypB L.ax-CX21-CCX0-CCX1-CCX2=CCX2-CX10-CCX1-CX10-CX20-CCX0 = HB1.hb988
  hypB L.ax-CX21-CCX0-CCX1-CCX2-Swap01=CCX2-CCX0-Swap01-CX21-CX20-CCX0 = HB1.hb989
  hypB L.ax-CX21-CCX0-CCX1-CX12-Swap01=CCX0-CX02-CCX1-CX12-CX21-CX10-CX20 = HB1.hb990
  hypB L.ax-CX21-CCX0-CCX2-CCX1=CX10-CCX2-CCX1-Swap12-CX10-CX20-CCX0 = HB1.hb991
  hypB L.ax-CX21-CCX0-CX12-Swap01=CCX0-CX02-Swap12-CX10-CX20 = HB1.hb992
  hypB L.ax-CX21-CCX0-CX12-CCX1-CX02=CCX2-CCX0-CX12-Swap01-CX12-CX21-CX20 = HB1.hb993
  hypB L.ax-CX21-CCX0-CX12-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10-CX20-CCX0 = HB1.hb994
  hypB L.ax-CX21-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20 = HB1.hb995
  hypB L.ax-CX21-CCX0-Swap12-Swap01=CX12-CCX0-Swap01-CX21-CX20 = HB1.hb996
  hypB L.ax-CX21-CCX0-Swap12-CCX1-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-CX21-CX20-CCX0 = HB1.hb997
  hypB L.ax-CX21-CCX0-Swap12-CCX2-Swap01=CCX0-CCX1-CX02-Swap12-CX10 = HB1.hb998
  hypB L.ax-Swap12-CX01=CX02-Swap12 = HB1.hb999
  hypB L.ax-Swap12-CX01-CCX2=CX02-CCX1-Swap12 = HB1.hb1000
  hypB L.ax-Swap12-CX01-CCX2-CCX0-Swap01=CX20-CCX1-CCX2-CX01-Swap12 = HB1.hb1001
  hypB L.ax-Swap12-CX01-CCX2-CCX0-CX01=CX02-CCX1-CCX0-CX02-Swap12 = HB1.hb1002
  hypB L.ax-Swap12-CX01-CX20-CCX2=CX02-CX10-CCX1-Swap12 = HB1.hb1003
  hypB L.ax-Swap12-CX01-CCX0-Swap01=CX20-CCX2-CX02-Swap12 = HB1.hb1004
  hypB L.ax-Swap12-CX01-CCX0-CX02=CX02-CCX0-CX01-Swap12 = HB1.hb1005
  hypB L.ax-Swap12-CX01-CCX0-CCX2-Swap01=CCX1-CX20-CCX2-CX02-CX12-CX21 = HB1.hb1006
  hypB L.ax-Swap12-CX01-CCX0-CCX2-CX01=CX20-CCX2-CCX1-CX01-Swap12-CX10 = HB1.hb1007
  hypB L.ax-Swap12-CX02=CX01-Swap12 = HB1.hb1008
  hypB L.ax-Swap12-CX02-CX01=CX02-CX01-Swap12 = HB1.hb1009
  hypB L.ax-Swap12-CX02-CCX1=CX01-CCX2-Swap12 = HB1.hb1010
  hypB L.ax-Swap12-CX02-CCX1-CCX0-CX02=CX01-CCX2-CCX0-CX01-Swap12 = HB1.hb1011
  hypB L.ax-Swap12-CX02-CX10-CCX1=CX01-CX20-CCX2-Swap12 = HB1.hb1012
  hypB L.ax-Swap12-CX02-CCX0-CX01=CX01-CCX0-CX02-Swap12 = HB1.hb1013
  hypB L.ax-Swap12-CCX1=CCX2-Swap12 = HB1.hb1014
  hypB L.ax-Swap12-CCX1-CX01=CCX2-CX02-Swap12 = HB1.hb1015
  hypB L.ax-Swap12-CCX1-CX01-CCX2=CCX2-CX02-CCX1-Swap12 = HB1.hb1016
  hypB L.ax-Swap12-CCX1-CX02=CCX2-CX01-Swap12 = HB1.hb1017
  hypB L.ax-Swap12-CCX1-CCX2=CCX2-CCX1-Swap12 = HB1.hb1018
  hypB L.ax-Swap12-CCX1-CCX2-CX01=CCX2-CCX1-CX02-Swap12 = HB1.hb1019
  hypB L.ax-Swap12-CCX1-CCX2-CX02=CCX2-CCX1-CX01-Swap12 = HB1.hb1020
  hypB L.ax-Swap12-CCX1-CCX2-CCX0-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01 = HB1.hb1021
  hypB L.ax-Swap12-CCX1-CX12-Swap01=CX12-CCX2-Swap01-CX20 = HB1.hb1022
  hypB L.ax-Swap12-CCX1-CX12-CCX0-Swap01=CX12-CCX2-CCX0-Swap01-CX21-CX20 = HB1.hb1023
  hypB L.ax-Swap12-CCX1-CX20-CCX2-CX02=CX01-CCX0-CCX2-Swap01-CX21-CX12 = HB1.hb1024
  hypB L.ax-Swap12-CCX1-CCX0-CX01-CCX2=CCX2-CCX0-CX02-CCX1-Swap12 = HB1.hb1025
  hypB L.ax-Swap12-CCX1-CCX0-CX02=CCX2-CCX0-CX01-Swap12 = HB1.hb1026
  hypB L.ax-Swap12-CCX1-CCX0-CX12-Swap01=CCX2-CCX0-CX12-Swap01-CX20 = HB1.hb1027
  hypB L.ax-Swap12-CCX1-CCX0-Swap12-Swap01=CCX2-CCX0-Swap01 = HB1.hb1028
  hypB L.ax-Swap12-CCX2=CCX1-Swap12 = HB1.hb1029
  hypB L.ax-Swap12-CCX2-CX01=CCX1-CX02-Swap12 = HB1.hb1030
  hypB L.ax-Swap12-CCX2-CX02=CCX1-CX01-Swap12 = HB1.hb1031
  hypB L.ax-Swap12-CCX2-CX02-CCX1=CCX1-CX01-CCX2-Swap12 = HB1.hb1032
  hypB L.ax-Swap12-CCX2-CCX1=CCX1-CCX2-Swap12 = HB1.hb1033
  hypB L.ax-Swap12-CCX2-CCX1-CX01=CCX1-CCX2-CX02-Swap12 = HB1.hb1034
  hypB L.ax-Swap12-CCX2-CCX1-CX02=CCX1-CCX2-CX01-Swap12 = HB1.hb1035
  hypB L.ax-Swap12-CCX2-CCX1-CCX0-Swap12-Swap01=CCX1-CCX2-CCX0-Swap01 = HB1.hb1036
  hypB L.ax-Swap12-CCX2-CX10-CCX1=CX20-CCX2-CCX1-CX12-CX21 = HB1.hb1037
  hypB L.ax-Swap12-CCX2-CCX0-Swap01=CCX1-CCX0-Swap12-Swap01 = HB1.hb1038
  hypB L.ax-Swap12-CCX2-CCX0-CX01=CCX1-CCX0-CX02-Swap12 = HB1.hb1039
  hypB L.ax-Swap12-CCX2-CCX0-CX02-CCX1=CCX1-CCX0-CX01-CCX2-Swap12 = HB1.hb1040
  hypB L.ax-Swap12-CCX2-CCX0-CX12-Swap01=CCX1-CCX0-CX12-Swap01-CX20 = HB1.hb1041
  hypB L.ax-Swap12-CX12-Swap01=CX12-Swap01-CX20 = HB1.hb1042
  hypB L.ax-Swap12-CX12-CX01-CCX0-Swap01=CX12-CX01-CCX0-Swap01-CX21-CX20 = HB1.hb1043
  hypB L.ax-Swap12-CX12-CCX1=CX12-CCX1-CX21 = HB1.hb1044
  hypB L.ax-Swap12-CX12-CCX1-CX01=CX12-CCX1-CX01-CX21 = HB1.hb1045
  hypB L.ax-Swap12-CX12-CCX1-CX02=CX21-CCX2-CX01-Swap12 = HB1.hb1046
  hypB L.ax-Swap12-CX12-CCX2-Swap01=CCX1-CX12-Swap01-CX20 = HB1.hb1047
  hypB L.ax-Swap12-CX12-CCX2-CCX0-Swap01=CCX1-CX12-CCX0-Swap01-CX21-CX20 = HB1.hb1048
  hypB L.ax-Swap12-CX12-CCX0-Swap01=CX12-CCX0-Swap01-CX21-CX20 = HB1.hb1049
  hypB L.ax-Swap12-CX21-CCX2-CX01=CX12-CCX1-CX02-Swap12 = HB1.hb1050
  hypB L.ax-Swap12-CX21-CCX0-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10 = HB1.hb1051
  hypB L.ax-Swap12-CX21-CCX0-CCX2-CX01=CX21-CCX0-CCX2-Swap01-CX10 = HB1.hb1052
  hypB L.ax-Swap12-Swap12-Swap01=Swap01 = HB1.hb1053
  hypB L.ax-Swap12-Swap12-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01 = HB1.hb1054
  hypB L.ax-Swap12-Swap12-CCX2-Swap01=CCX2-Swap01 = HB1.hb1055
  hypB L.ax-Swap12-CX10-CX02-CCX1=CX20-CX01-CCX2-Swap12 = HB1.hb1056
  hypB L.ax-Swap12-CX10-CCX1=CX20-CCX2-Swap12 = HB1.hb1057
  hypB L.ax-Swap12-CX10-CCX1-CX02=CX20-CCX2-CX01-Swap12 = HB1.hb1058
  hypB L.ax-Swap12-CX10-CCX1-CCX2-CX01=CX20-CCX2-CCX1-CX02-Swap12 = HB1.hb1059
  hypB L.ax-Swap12-CX10-CCX2-CCX1=CX20-CCX1-CCX2-Swap12 = HB1.hb1060
  hypB L.ax-Swap12-CX10-CCX2-CCX1-CX01=CX20-CCX1-CCX2-CX02-Swap12 = HB1.hb1061
  hypB L.ax-Swap12-CX10-CX12-CCX1=CX10-CX12-CCX1-CX20 = HB1.hb1062
  hypB L.ax-Swap12-CX10-Swap12-CCX2-Swap01=CX20-CCX2-Swap01 = HB1.hb1063
  hypB L.ax-Swap12-CX20-CX01-CCX2=CX10-CX02-CCX1-Swap12 = HB1.hb1064
  hypB L.ax-Swap12-CX20-CCX1-CCX2=CX10-CCX2-CCX1-Swap12 = HB1.hb1065
  hypB L.ax-Swap12-CX20-CCX1-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10-CX20-CCX0 = HB1.hb1066
  hypB L.ax-Swap12-CX20-CCX1-CCX2-CX01=CX01-CCX2-CCX0-Swap01-Swap12 = HB1.hb1067
  hypB L.ax-Swap12-CX20-CCX1-CCX2-CX02=CX10-CCX2-CCX1-CX01-Swap12 = HB1.hb1068
  hypB L.ax-Swap12-CX20-CCX2=CX10-CCX1-Swap12 = HB1.hb1069
  hypB L.ax-Swap12-CX20-CCX2-Swap01=CX10-Swap12-CCX2-Swap01 = HB1.hb1070
  hypB L.ax-Swap12-CX20-CCX2-CX01=CX10-CCX1-CX02-Swap12 = HB1.hb1071
  hypB L.ax-Swap12-CX20-CCX2-CX02=CX01-CCX0-Swap01-Swap12 = HB1.hb1072
  hypB L.ax-Swap12-CX20-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX12 = HB1.hb1073
  hypB L.ax-Swap12-CX20-CCX2-CCX1-CX01=CX01-CCX0-CCX2-CX01-Swap12-CX20 = HB1.hb1074
  hypB L.ax-Swap12-CX20-CCX2-CCX1-CX02=CX10-CCX1-CCX2-CX01-Swap12 = HB1.hb1075
  hypB L.ax-Swap12-CX20-CX21-CCX2-CX01=CX20-CCX1-CCX2-Swap01-CX10-CX20-CCX0 = HB1.hb1076
  hypB L.ax-Swap12-CCX0-Swap01=CCX0-Swap12-Swap01 = HB1.hb1077
  hypB L.ax-Swap12-CCX0-CX01=CCX0-CX02-Swap12 = HB1.hb1078
  hypB L.ax-Swap12-CCX0-CX01-CCX2=CCX0-CX02-CCX1-Swap12 = HB1.hb1079
  hypB L.ax-Swap12-CCX0-CX02=CCX0-CX01-Swap12 = HB1.hb1080
  hypB L.ax-Swap12-CCX0-CX02-CCX1=CCX0-CX01-CCX2-Swap12 = HB1.hb1081
  hypB L.ax-Swap12-CCX0-CCX1-CX02=CCX0-CCX2-CX01-Swap12 = HB1.hb1082
  hypB L.ax-Swap12-CCX0-CCX1-CCX2=CCX0-CCX2-CCX1-Swap12 = HB1.hb1083
  hypB L.ax-Swap12-CCX0-CCX1-CCX2-Swap01=CCX0-Swap12-CCX1-CCX2-Swap01 = HB1.hb1084
  hypB L.ax-Swap12-CCX0-CCX1-CX12-Swap01=CCX0-CX12-CCX2-Swap01-CX20 = HB1.hb1085
  hypB L.ax-Swap12-CCX0-CCX2-Swap01=CCX0-Swap12-CCX2-Swap01 = HB1.hb1086
  hypB L.ax-Swap12-CCX0-CCX2-CX01=CCX0-CCX1-CX02-Swap12 = HB1.hb1087
  hypB L.ax-Swap12-CCX0-CCX2-CCX1=CCX0-CCX1-CCX2-Swap12 = HB1.hb1088
  hypB L.ax-Swap12-CCX0-CX12-Swap01=CCX0-CX12-Swap01-CX20 = HB1.hb1089
  hypB L.ax-Swap12-CCX0-CX12-CCX1-CX02=CCX0-CX21-CCX2-CX01-Swap12 = HB1.hb1090
  hypB L.ax-Swap12-CCX0-CX12-CCX2-Swap01=CCX0-CCX1-CX12-Swap01-CX20 = HB1.hb1091
  hypB L.ax-Swap12-CCX0-CX21-CCX2-CX01=CCX0-CX12-CCX1-CX02-Swap12 = HB1.hb1092
  hypB L.ax-Swap12-CCX0-Swap12-Swap01=CCX0-Swap01 = HB1.hb1093
  hypB L.ax-Swap12-CCX0-Swap12-CCX1-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01 = HB1.hb1094
  hypB L.ax-Swap12-CCX0-Swap12-CCX2-Swap01=CCX0-CCX2-Swap01 = HB1.hb1095
  
  hypB L.ax-CX10-Swap01=CX01-CX10 = HB1.hb1096
  hypB L.ax-CX10-CX01=Swap01-CX10 = HB1.hb1097
  hypB L.ax-CX10-CX01-CCX2=CCX2-Swap01-CX12-CX10 = HB1.hb1098
  hypB L.ax-CX10-CX01-CCX2-CCX0-Swap01=CCX2-CCX1-CX02 = HB1.hb1099
  hypB L.ax-CX10-CX01-CCX2-CCX0-CX01=CCX2-CX02-CCX1-CX10 = HB1.hb1100
  hypB L.ax-CX10-CX01-CX20-CCX2=CCX1-CCX2-Swap01-CX12-CX10-CX20-CCX0 = HB1.hb1101
  hypB L.ax-CX10-CX01-CCX0-Swap01=CCX1-CX01 = HB1.hb1102
  hypB L.ax-CX10-CX01-CCX0-CX02=CCX1-CX12-Swap01-CX12-CX10 = HB1.hb1103
  hypB L.ax-CX10-CX01-CCX0-CCX2-Swap01=CCX1-CX01-CCX2 = HB1.hb1104
  hypB L.ax-CX10-CX01-CCX0-CCX2-CX01=CCX1-CCX2-CX02-CX10 = HB1.hb1105
  hypB L.ax-CX10-CX02=CX02-CX12-CX10 = HB1.hb1106
  hypB L.ax-CX10-CX02-CX01=CX12-Swap01-CX12-CX10 = HB1.hb1107
  hypB L.ax-CX10-CX02-CCX1-CCX0-CX02=CCX1-CCX0-CCX2-Swap01-CX12-CX10-CCX0 = HB1.hb1108
  hypB L.ax-CX10-CX02-CX10-CCX1=CX21-CCX2-CX01-CX21-CX12 = HB1.hb1109
  hypB L.ax-CX10-CX02-CCX0-CX01=CX20-CCX2-CX01-CX21-CX12-CX10-CX20 = HB1.hb1110
  hypB L.ax-CX10-CCX1-CX01=CX01-CCX0-Swap01 = HB1.hb1111
  hypB L.ax-CX10-CCX1-CX01-CCX2=CX01-CCX0-CCX2-Swap01 = HB1.hb1112
  hypB L.ax-CX10-CCX1-CCX2=CCX2-CX10-CCX1-CX12 = HB1.hb1113
  hypB L.ax-CX10-CCX1-CCX2-Swap01=CX01-CX20-CCX2-CX12-CX10-CX20-CCX0 = HB1.hb1114
  hypB L.ax-CX10-CCX1-CCX2-CX02=CX01-CCX0-CCX2-CX01-CX10 = HB1.hb1115
  hypB L.ax-CX10-CCX1-CCX2-CCX0-Swap01=CX20-CCX2-CCX1-CX02-Swap12-CX10-CX20-CCX0 = HB1.hb1116
  hypB L.ax-CX10-CCX1-CX12-Swap01=CX01-CCX0-CX02-CX12-CX10 = HB1.hb1117
  hypB L.ax-CX10-CCX1-CX12-CCX0-Swap01=CCX0-CCX1-CX12-Swap01 = HB1.hb1118
  hypB L.ax-CX10-CCX1-CCX0-CX01-CCX2=CCX0-CCX1-CCX2-Swap01-CX12-CX10 = HB1.hb1119
  hypB L.ax-CX10-CCX1-CCX0-CX02=CCX0-CCX1-CX02-CX12-CX10 = HB1.hb1120
  hypB L.ax-CX10-CCX1-CCX0-CCX2-Swap01=CX02-CCX1-CCX0-CX02-CX12-CCX0 = HB1.hb1121
  hypB L.ax-CX10-CCX1-CCX0-CX12-Swap01=CCX0-CX02-CCX1-CX12-CX10 = HB1.hb1122
  hypB L.ax-CX10-CCX1-CCX0-Swap12-Swap01=CCX0-Swap12-CCX2-Swap01-CX21 = HB1.hb1123
  hypB L.ax-CX10-CCX2=CCX2-CX12-CX10 = HB1.hb1124
  hypB L.ax-CX10-CCX2-Swap01=CX01-CCX2-CX12-CX10 = HB1.hb1125
  hypB L.ax-CX10-CCX2-CX01=CX12-CCX2-Swap01-CX10 = HB1.hb1126
  hypB L.ax-CX10-CCX2-CX02=CCX2-CX02-CX10 = HB1.hb1127
  hypB L.ax-CX10-CCX2-CX02-CCX1=CX01-CCX2-CCX0-CX01-CX10 = HB1.hb1128
  hypB L.ax-CX10-CCX2-CCX1-CX02=CX01-CCX2-CCX0-Swap01 = HB1.hb1129
  hypB L.ax-CX10-CCX2-CCX1-CCX0-Swap12-Swap01=CX20-CCX1-CCX2-CX01-CX10-CX20-CCX0 = HB1.hb1130
  hypB L.ax-CX10-CCX2-CX10-CCX1=CCX1-CCX2-CX12 = HB1.hb1131
  hypB L.ax-CX10-CCX2-CCX0-Swap01=CCX2-CCX0-CX12-Swap01 = HB1.hb1132
  hypB L.ax-CX10-CCX2-CCX0-CX01=CX12-CCX2-CCX0-Swap01-CX10 = HB1.hb1133
  hypB L.ax-CX10-CCX2-CCX0-CX02-CCX1=CCX0-CX21-CCX2-CX01-CX21-CX12-CX10-CCX0 = HB1.hb1134
  hypB L.ax-CX10-CCX2-CCX0-CX12-Swap01=CCX2-CCX0-Swap01 = HB1.hb1135
  hypB L.ax-CX10-CX12-Swap01=CX02-CX01-CX12-CX10 = HB1.hb1136
  hypB L.ax-CX10-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01 = HB1.hb1137
  hypB L.ax-CX10-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01 = HB1.hb1138
  hypB L.ax-CX10-CX12-CCX1-CX02=CX20-CCX1-CCX2-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb1139
  hypB L.ax-CX10-CX12-CCX2-Swap01=CCX2-CX01-CX10 = HB1.hb1140
  hypB L.ax-CX10-CX12-CCX2-CCX0-Swap01=CCX2-CCX0-CX01-CX10 = HB1.hb1141
  hypB L.ax-CX10-CX12-CCX0-Swap01=CCX0-CX12-Swap01 = HB1.hb1142
  hypB L.ax-CX10-CX21-CCX2-CX01=CX02-CX10-CCX1-CX12-CX21 = HB1.hb1143
  hypB L.ax-CX10-CX21-CCX0-CCX2-Swap01=CCX0-CX12-CCX1-CX02-Swap12-CX10 = HB1.hb1144
  hypB L.ax-CX10-CX21-CCX0-CCX2-CX01=CCX0-Swap12-CCX1-CCX2-Swap01-CX10-CX20-CCX0 = HB1.hb1145
  hypB L.ax-CX10-Swap12-Swap01=Swap12-Swap01-CX21 = HB1.hb1146
  hypB L.ax-CX10-Swap12-CCX1-CCX2-Swap01=CX20-CX21-CCX2-CX01-CX10-CX20-CCX0 = HB1.hb1147
  hypB L.ax-CX10-CX10-CX02-CCX1=CX02-CCX1 = HB1.hb1148
  hypB L.ax-CX10-CX10-CCX1=CCX1 = HB1.hb1149
  hypB L.ax-CX10-CX10-CCX1-CX02=CCX1-CX02 = HB1.hb1150
  hypB L.ax-CX10-CX10-CCX1-CCX2-CX01=CCX1-CCX2-CX01 = HB1.hb1151
  hypB L.ax-CX10-CX10-CCX2-CCX1=CCX2-CCX1 = HB1.hb1152
  hypB L.ax-CX10-CX10-CCX2-CCX1-CX01=CCX2-CCX1-CX01 = HB1.hb1153
  hypB L.ax-CX10-CX10-CX12-CCX1=CX12-CCX1 = HB1.hb1154
  hypB L.ax-CX10-CX10-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01 = HB1.hb1155
  hypB L.ax-CX10-CX20-CX01-CCX2=CX20-CCX2-Swap01-CX12-CX10 = HB1.hb1156
  hypB L.ax-CX10-CX20-CCX1-CCX2=CCX0-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0 = HB1.hb1157
  hypB L.ax-CX10-CX20-CCX1-CCX2-Swap01=CX12-CCX1-CX02-Swap12-CX10-CX20-CCX0 = HB1.hb1158
  hypB L.ax-CX10-CX20-CCX1-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10-CX20-CCX0 = HB1.hb1159
  hypB L.ax-CX10-CX20-CCX2=CX20-CCX2-CX12-CX10 = HB1.hb1160
  hypB L.ax-CX10-CX20-CCX2-Swap01=CX20-CX01-CCX2-CX12-CX10 = HB1.hb1161
  hypB L.ax-CX10-CX20-CCX2-CX01=CX02-CCX0-CX01-CX12-CX21-CX20 = HB1.hb1162
  hypB L.ax-CX10-CX20-CCX2-CX02=CX20-CCX2-CX02-CX10 = HB1.hb1163
  hypB L.ax-CX10-CX20-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0 = HB1.hb1164
  hypB L.ax-CX10-CX20-CCX2-CCX1-CX02=CCX1-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb1165
  hypB L.ax-CX10-CX20-CX21-CCX2-CX01=Swap12-CCX1-CCX2-Swap01-CX10-CX20-CCX0 = HB1.hb1166
  hypB L.ax-CX10-CCX0-Swap01=CCX0-CX01-CX10 = HB1.hb1167
  hypB L.ax-CX10-CCX0-CX01=CCX0-Swap01-CX10 = HB1.hb1168
  hypB L.ax-CX10-CCX0-CX01-CCX2=CCX0-CCX2-Swap01-CX12-CX10 = HB1.hb1169
  hypB L.ax-CX10-CCX0-CX02=CCX0-CX02-CX12-CX10 = HB1.hb1170
  hypB L.ax-CX10-CCX0-CX02-CCX1=CCX1-CCX0-CX12-Swap01-CX12-CX10 = HB1.hb1171
  hypB L.ax-CX10-CCX0-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10 = HB1.hb1172
  hypB L.ax-CX10-CCX0-CCX1-CCX2=CX20-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0 = HB1.hb1173
  hypB L.ax-CX10-CCX0-CCX1-CCX2-Swap01=CCX1-CCX0-CX01-CCX2-CX12-CX10 = HB1.hb1174
  hypB L.ax-CX10-CCX0-CCX1-CX12-Swap01=CCX1-CX12-CCX0-Swap01 = HB1.hb1175
  hypB L.ax-CX10-CCX0-CCX2-Swap01=CCX0-CX01-CCX2-CX12-CX10 = HB1.hb1176
  hypB L.ax-CX10-CCX0-CCX2-CX01=CCX0-CX12-CCX2-Swap01-CX10 = HB1.hb1177
  hypB L.ax-CX10-CCX0-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0 = HB1.hb1178
  hypB L.ax-CX10-CCX0-CX12-Swap01=CX12-CCX0-Swap01 = HB1.hb1179
  hypB L.ax-CX10-CCX0-CX12-CCX1-CX02=CX21-CCX0-CCX2-Swap01-Swap12-CX20 = HB1.hb1180
  hypB L.ax-CX10-CCX0-CX12-CCX2-Swap01=CCX0-CCX2-CX01-CX10 = HB1.hb1181
  hypB L.ax-CX10-CCX0-CX21-CCX2-CX01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX20-CCX0 = HB1.hb1182
  hypB L.ax-CX10-CCX0-Swap12-Swap01=CCX0-Swap12-Swap01-CX21 = HB1.hb1183
  hypB L.ax-CX10-CCX0-Swap12-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-CX01-CX10-CX20-CCX0 = HB1.hb1184
  hypB L.ax-CX10-CCX0-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21 = HB1.hb1185
  hypB L.ax-CX20-Swap01=Swap01-CX21 = HB1.hb1186
  hypB L.ax-CX20-CX01=CX01-CX21-CX20 = HB1.hb1187
  hypB L.ax-CX20-CX01-CCX2-CCX0-Swap01=CCX1-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb1188
  hypB L.ax-CX20-CX01-CX20-CCX2=CX12-CCX1-CX02-CX12-CX21 = HB1.hb1189
  hypB L.ax-CX20-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CX20 = HB1.hb1190

  hypB L.ax-CX20-CX01-CCX0-CX02=CX10-CCX1-CX02-CX12-CX21-CX10-CX20 = HB1.hb1191
  hypB L.ax-CX20-CX01-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10-CX20-CCX0 = HB1.hb1192
  hypB L.ax-CX20-CX02=Swap12-Swap01-Swap12-CX20 = HB1.hb1193
  hypB L.ax-CX20-CX02-CX01=CX12-Swap01-CX21-CX12-CX10 = HB1.hb1194
  hypB L.ax-CX20-CX02-CCX1=Swap12-CCX2-Swap01-CX21-CX12-CX20 = HB1.hb1195
  hypB L.ax-CX20-CX02-CCX1-CCX0-CX02=CCX1-CX01-CCX2-CX20 = HB1.hb1196
  hypB L.ax-CX20-CX02-CX10-CCX1=Swap12-CCX1-CCX2-Swap01-CX21-CX12-CX10-CX20-CCX0 = HB1.hb1197
  hypB L.ax-CX20-CX02-CCX0-CX01=CX12-CCX2-Swap01-CX21-CX12-CX10 = HB1.hb1198
  hypB L.ax-CX20-CCX1=CCX1-CX21-CX20 = HB1.hb1199
  hypB L.ax-CX20-CCX1-CX01=CCX1-CX01-CX20 = HB1.hb1200
  hypB L.ax-CX20-CCX1-CX01-CCX2=CX02-CCX1-CCX0-CX02-CX20 = HB1.hb1201
  hypB L.ax-CX20-CCX1-CX02=CCX1-CX12-Swap01-Swap12-CX10-CX20 = HB1.hb1202
  hypB L.ax-CX20-CCX1-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-Swap01-Swap12-CX10-CX20-CCX0 = HB1.hb1203
  hypB L.ax-CX20-CCX1-CX12-Swap01=CCX1-CX02-Swap12-CX10-CX20 = HB1.hb1204
  hypB L.ax-CX20-CCX1-CX12-CCX0-Swap01=CCX1-CCX0-CX02-CX21-CX12-CX10 = HB1.hb1205
  hypB L.ax-CX20-CCX1-CX20-CCX2-CX02=CCX2-CX02-CCX1-CX21 = HB1.hb1206
  hypB L.ax-CX20-CCX1-CCX0-CX01-CCX2=CCX0-CX12-CCX1-CX02-CX12-CX21-CX20-CCX0 = HB1.hb1207
  hypB L.ax-CX20-CCX1-CCX0-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX21-CX10-CX20 = HB1.hb1208
  hypB L.ax-CX20-CCX1-CCX0-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10-CX20-CCX0 = HB1.hb1209
  hypB L.ax-CX20-CCX1-CCX0-CX12-Swap01=CCX1-CCX0-Swap12-Swap01-CX20 = HB1.hb1210
  hypB L.ax-CX20-CCX1-CCX0-Swap12-Swap01=CCX1-CCX0-CX12-Swap01-CX20 = HB1.hb1211
  hypB L.ax-CX20-CCX2-CX02-CCX1=CCX1-CX20-CCX2-CX02-CX21 = HB1.hb1212
  hypB L.ax-CX20-CCX2-CCX1-CCX0-Swap12-Swap01=CX10-CCX1-CCX2-CX01-CX10-CX20-CCX0 = HB1.hb1213
  hypB L.ax-CX20-CCX2-CX10-CCX1=CCX0-CCX2-CCX1-CX21-CX10-CX20-CCX0 = HB1.hb1214
  hypB L.ax-CX20-CCX2-CCX0-Swap01=CCX0-CCX2-Swap01-CX21 = HB1.hb1215
  hypB L.ax-CX20-CCX2-CCX0-CX01=CCX0-CCX2-CX01-CX21-CX20 = HB1.hb1216
  hypB L.ax-CX20-CCX2-CCX0-CX02-CCX1=CCX0-Swap12-CCX1-CCX2-Swap01-CX21-CX12-CX20 = HB1.hb1217
  hypB L.ax-CX20-CCX2-CCX0-CX12-Swap01=CCX0-CX01-CCX2-CX12-CX21-CX10-CX20 = HB1.hb1218
  hypB L.ax-CX20-CX12-Swap01=CX02-CX01-CX12-CX21-CX10-CX20 = HB1.hb1219
  hypB L.ax-CX20-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01-CX20 = HB1.hb1220
  hypB L.ax-CX20-CX12-CCX1=CX10-CX12-CCX1-CX21-CX20 = HB1.hb1221
  hypB L.ax-CX20-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01-CX20 = HB1.hb1222
  hypB L.ax-CX20-CX12-CCX1-CX02=CX01-CX20-CCX2-CX21-CX12 = HB1.hb1223
  hypB L.ax-CX20-CX12-CCX2-Swap01=CX02-CCX0-CX01-CX12-CX21-CX10-CX20 = HB1.hb1224
  hypB L.ax-CX20-CX12-CCX2-CCX0-Swap01=CCX0-CX12-CCX2-Swap01-CX21 = HB1.hb1225
  hypB L.ax-CX20-CX12-CCX0-Swap01=CCX0-CX12-Swap01-CX21 = HB1.hb1226
  hypB L.ax-CX20-CX21-CCX0-CCX2-Swap01=CCX0-CCX1-CCX2-Swap01-CX20-CCX0 = HB1.hb1227
  hypB L.ax-CX20-CX21-CCX0-CCX2-CX01=CCX0-CX21-CCX2-CX01 = HB1.hb1228
  hypB L.ax-CX20-Swap12-Swap01=CX02-Swap12-CX10 = HB1.hb1229
  hypB L.ax-CX20-Swap12-CCX1-CCX2-Swap01=CX02-CX10-CCX1-CX12-CX21-CX10-CX20-CCX0 = HB1.hb1230
  hypB L.ax-CX20-Swap12-CCX2-Swap01=CX02-CCX1-CX12-CX21-CX10 = HB1.hb1231
  hypB L.ax-CX20-CX10-CX02-CCX1=CX10-Swap12-CCX2-Swap01-CX21-CX12-CX20 = HB1.hb1232
  hypB L.ax-CX20-CX10-CCX1=CX10-CCX1-CX21-CX20 = HB1.hb1233
  hypB L.ax-CX20-CX10-CCX1-CX02=CX01-CCX0-CX02-CX21-CX12-CX10 = HB1.hb1234
  hypB L.ax-CX20-CX10-CCX1-CCX2-CX01=CCX2-CCX1-CCX0-Swap12-Swap01-CX10-CX20-CCX0 = HB1.hb1235
  hypB L.ax-CX20-CX10-CCX2-CCX1=CCX0-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0 = HB1.hb1236
  hypB L.ax-CX20-CX10-CX12-CCX1=CX12-CCX1-CX21-CX20 = HB1.hb1237
  hypB L.ax-CX20-CX10-Swap12-CCX2-Swap01=CX10-CX02-CCX1-CX12-CX21-CX10 = HB1.hb1238
  hypB L.ax-CX20-CX20-CX01-CCX2=CX01-CCX2 = HB1.hb1239
  hypB L.ax-CX20-CX20-CCX1-CCX2=CCX1-CCX2 = HB1.hb1240
  hypB L.ax-CX20-CX20-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01 = HB1.hb1241
  hypB L.ax-CX20-CX20-CCX1-CCX2-CX01=CCX1-CCX2-CX01 = HB1.hb1242
  hypB L.ax-CX20-CX20-CCX1-CCX2-CX02=CCX1-CCX2-CX02 = HB1.hb1243
  hypB L.ax-CX20-CX20-CCX2=CCX2 = HB1.hb1244
  hypB L.ax-CX20-CX20-CCX2-Swap01=CCX2-Swap01 = HB1.hb1245
  hypB L.ax-CX20-CX20-CCX2-CX01=CCX2-CX01 = HB1.hb1246
  hypB L.ax-CX20-CX20-CCX2-CX02=CCX2-CX02 = HB1.hb1247
  hypB L.ax-CX20-CX20-CCX2-CCX1=CCX2-CCX1 = HB1.hb1248
  hypB L.ax-CX20-CX20-CCX2-CCX1-CX01=CCX2-CCX1-CX01 = HB1.hb1249
  hypB L.ax-CX20-CX20-CCX2-CCX1-CX02=CCX2-CCX1-CX02 = HB1.hb1250
  hypB L.ax-CX20-CX20-CX21-CCX2-CX01=CX21-CCX2-CX01 = HB1.hb1251
  hypB L.ax-CX20-CCX0-Swap01=CCX0-Swap01-CX21 = HB1.hb1252
  hypB L.ax-CX20-CCX0-CX01=CCX0-CX01-CX21-CX20 = HB1.hb1253
  hypB L.ax-CX20-CCX0-CX01-CCX2=CCX2-CCX0-CX12-Swap01-CX21-CX12-CX10 = HB1.hb1254
  hypB L.ax-CX20-CCX0-CX02=CCX0-Swap12-Swap01-Swap12-CX20 = HB1.hb1255
  hypB L.ax-CX20-CCX0-CX02-CCX1=CCX0-Swap12-CCX2-Swap01-CX21-CX12-CX20 = HB1.hb1256
  hypB L.ax-CX20-CCX0-CCX1-CX02=CCX0-CCX1-CX12-Swap01-Swap12-CX10-CX20 = HB1.hb1257
  hypB L.ax-CX20-CCX0-CCX1-CCX2=CX10-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0 = HB1.hb1258
  hypB L.ax-CX20-CCX0-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX20-CCX0 = HB1.hb1259
  hypB L.ax-CX20-CCX0-CCX1-CX12-Swap01=CCX0-CCX1-CX02-Swap12-CX10-CX20 = HB1.hb1260
  hypB L.ax-CX20-CCX0-CCX2-Swap01=CCX2-CCX0-Swap01-CX21 = HB1.hb1261
  hypB L.ax-CX20-CCX0-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20 = HB1.hb1262
  hypB L.ax-CX20-CCX0-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX10-CX20-CCX0 = HB1.hb1263
  hypB L.ax-CX20-CCX0-CX12-Swap01=CX12-CCX0-Swap01-CX21 = HB1.hb1264
  hypB L.ax-CX20-CCX0-CX12-CCX1-CX02=CCX1-CCX0-CX01-CCX2-CX21-CX12-CX10-CCX0 = HB1.hb1265
  hypB L.ax-CX20-CCX0-CX12-CCX2-Swap01=CX12-CCX2-CCX0-Swap01-CX21 = HB1.hb1266
  hypB L.ax-CX20-CCX0-CX21-CCX2-CX01=CX21-CCX0-CCX2-CX01 = HB1.hb1267
  hypB L.ax-CX20-CCX0-Swap12-Swap01=CCX0-CX02-Swap12-CX10 = HB1.hb1268
  hypB L.ax-CX20-CCX0-Swap12-CCX1-CCX2-Swap01=CCX2-CCX0-CX02-CCX1-CX12-CX21-CX10 = HB1.hb1269
  hypB L.ax-CX20-CCX0-Swap12-CCX2-Swap01=CCX0-CX02-CCX1-CX12-CX21-CX10 = HB1.hb1270
  
  hypB L.ax-CCX0-CX01-CCX2-CCX0-Swap01=CX01-CCX2-CCX0-Swap01-CCX0 = HB1.hb1271
  hypB L.ax-CCX0-CX01-CCX2-CCX0-CX01=CCX2-CX02-CCX1-CCX0 = HB1.hb1272
  hypB L.ax-CCX0-CX01-CX20-CCX2=CCX1-CCX0-CX01-CCX2-CX20-CCX0 = HB1.hb1273
  hypB L.ax-CCX0-CX01-CCX0-Swap01=CX01-CCX0-Swap01-CCX0 = HB1.hb1274
  hypB L.ax-CCX0-CX01-CCX0-CX02=CCX1-CX12-CCX0-Swap01-CX12-CX10 = HB1.hb1275
  hypB L.ax-CCX0-CX01-CCX0-CCX2-Swap01=CCX1-CCX0-CCX2-Swap01-CX12-CX10 = HB1.hb1276
  hypB L.ax-CCX0-CX01-CCX0-CCX2-CX01=CCX1-CCX2-CX02-CCX0 = HB1.hb1277
  hypB L.ax-CCX0-CX02-CX01=CX12-CCX0-Swap01-CX12-CX10 = HB1.hb1278
  hypB L.ax-CCX0-CX02-CCX1-CCX0-CX02=CCX1-CX01-CCX2-CCX0 = HB1.hb1279
  hypB L.ax-CCX0-CX02-CX10-CCX1=CCX2-CCX0-CX02-CCX1-CX10-CCX0 = HB1.hb1280
  hypB L.ax-CCX0-CX02-CCX0-CX01=CX12-CCX2-CCX0-Swap01-CX12-CX10 = HB1.hb1281
  hypB L.ax-CCX0-CCX1=CX10-CCX1-CX10-CCX0 = HB1.hb1282
  hypB L.ax-CCX0-CCX1-CX01=CCX1-CX01-CCX0 = HB1.hb1283
  hypB L.ax-CCX0-CCX1-CX01-CCX2=CX02-CCX1-CCX0-CX02-CCX0 = HB1.hb1284
  hypB L.ax-CCX0-CCX1-CCX2-CX01=CCX1-CCX2-CX01-CCX0 = HB1.hb1285
  hypB L.ax-CCX0-CCX1-CCX2-CX02=CX01-CCX0-CCX2-CX01-CCX0 = HB1.hb1286
  hypB L.ax-CCX0-CCX1-CCX2-CCX0-Swap01=CCX1-CCX2-CCX0-Swap01-CCX0 = HB1.hb1287
  hypB L.ax-CCX0-CCX1-CX12-CCX0-Swap01=CX01-CCX0-CX02-CX12-CX10 = HB1.hb1288
  hypB L.ax-CCX0-CCX1-CCX0-CX01-CCX2=CX01-CX20-CCX2-CX20-CCX0 = HB1.hb1289
  hypB L.ax-CCX0-CCX1-CCX0-CX02=CX10-CCX1-CX02-CX12-CX10 = HB1.hb1290
  hypB L.ax-CCX0-CCX1-CCX0-CCX2-Swap01=CX01-CCX0-CCX2-Swap01-CX12-CX10 = HB1.hb1291
  hypB L.ax-CCX0-CCX1-CCX0-CX12-Swap01=CX10-CX02-CCX1-CX12-CX10 = HB1.hb1292
  hypB L.ax-CCX0-CCX1-CCX0-Swap12-Swap01=CX10-Swap12-CCX2-Swap01-CX21 = HB1.hb1293
  hypB L.ax-CCX0-CCX2=CX20-CCX2-CX20-CCX0 = HB1.hb1294
  hypB L.ax-CCX0-CCX2-CX02=CCX2-CX02-CCX0 = HB1.hb1295
  hypB L.ax-CCX0-CCX2-CX02-CCX1=CX01-CCX2-CCX0-CX01-CCX0 = HB1.hb1296
  hypB L.ax-CCX0-CCX2-CCX1-CX01=CX20-CCX2-CCX1-CX01-CX20-CCX0 = HB1.hb1297
  hypB L.ax-CCX0-CCX2-CCX1-CX02=CCX2-CCX1-CX02-CCX0 = HB1.hb1298
  hypB L.ax-CCX0-CCX2-CCX1-CCX0-Swap12-Swap01=CCX2-CCX1-CCX0-Swap12-Swap01-CCX0 = HB1.hb1299
  hypB L.ax-CCX0-CCX2-CX10-CCX1=CX20-CCX2-CCX1-CX21-CX10-CX20-CCX0 = HB1.hb1300
  hypB L.ax-CCX0-CCX2-CCX0-Swap01=CX20-CCX2-Swap01-CX21 = HB1.hb1301
  hypB L.ax-CCX0-CCX2-CCX0-CX01=CX20-CCX2-CX01-CX21-CX20 = HB1.hb1302
  hypB L.ax-CCX0-CCX2-CCX0-CX02-CCX1=CX02-CX10-CCX1-CX10-CCX0 = HB1.hb1303
  hypB L.ax-CCX0-CCX2-CCX0-CX12-Swap01=CX20-CX01-CCX2-CX12-CX21-CX10-CX20 = HB1.hb1304
  hypB L.ax-CCX0-CX12-CX01-CCX0-Swap01=CX12-CCX1-CX01-CCX0 = HB1.hb1305
  hypB L.ax-CCX0-CX12-CCX1=CX12-CCX1-CX10-CCX0 = HB1.hb1306
  hypB L.ax-CCX0-CX12-CCX1-CX01=CX12-CX01-CCX0-Swap01-CCX0 = HB1.hb1307
  hypB L.ax-CCX0-CX12-CCX2-CCX0-Swap01=CX02-CCX0-CX01-CX12-CX10 = HB2.hb1308
  hypB L.ax-CCX0-CX12-CCX0-Swap01=CX02-CX01-CX12-CX10 = HB2.hb1309
  hypB L.ax-CCX0-CX21-CCX0-CCX2-Swap01=CX20-CCX1-CCX2-Swap01-CX20-CCX0 = HB2.hb1310
  hypB L.ax-CCX0-CX21-CCX0-CCX2-CX01=CX20-CX21-CCX2-CX01 = HB2.hb1311
  hypB L.ax-CCX0-CX10-CX02-CCX1=CCX1-CCX0-CX12-Swap01-CX12-CX10 = HB2.hb1312
  hypB L.ax-CCX0-CX10-CCX1=CCX1-CX10-CCX0 = HB2.hb1313
  hypB L.ax-CCX0-CX10-CCX1-CX02=CCX1-CCX0-CX02-CX12-CX10 = HB2.hb1314
  hypB L.ax-CCX0-CX10-CCX1-CCX2-CX01=CX10-CCX1-CCX2-CX01-CCX0 = HB2.hb1315
  hypB L.ax-CCX0-CX10-CCX2-CCX1=CX20-CCX1-CCX2-CX12-CX21-CX10-CX20-CCX0 = HB2.hb1316
  hypB L.ax-CCX0-CX10-CX12-CCX1=CX10-CX12-CCX1-CX10-CCX0 = HB2.hb1317
  hypB L.ax-CCX0-CX10-Swap12-CCX2-Swap01=CCX1-CCX0-Swap12-Swap01-CX21 = HB2.hb1318
  hypB L.ax-CCX0-CX20-CX01-CCX2=CCX2-CCX0-CX12-Swap01-CX21-CX12-CX10 = HB2.hb1319
  hypB L.ax-CCX0-CX20-CCX1-CCX2=CX10-CCX2-CCX1-CX21-CX12-CX10-CX20-CCX0 = HB2.hb1320
  hypB L.ax-CCX0-CX20-CCX1-CCX2-Swap01=CX21-CCX0-CCX2-Swap01-CX20-CCX0 = HB2.hb1321
  hypB L.ax-CCX0-CX20-CCX1-CCX2-CX01=CX20-CCX1-CCX2-CX01-CCX0 = HB2.hb1322
  hypB L.ax-CCX0-CX20-CCX2=CCX2-CX20-CCX0 = HB2.hb1323
  hypB L.ax-CCX0-CX20-CCX2-Swap01=CCX2-CCX0-Swap01-CX21 = HB2.hb1324
  hypB L.ax-CCX0-CX20-CCX2-CX01=CCX2-CCX0-CX01-CX21-CX20 = HB2.hb1325
  hypB L.ax-CCX0-CX20-CCX2-CX02=CX20-CCX2-CX02-CCX0 = HB2.hb1326
  hypB L.ax-CCX0-CX20-CCX2-CCX1=CCX2-CX10-CCX1-CX21-CX10-CX20-CCX0 = HB2.hb1327
  hypB L.ax-CCX0-CX20-CCX2-CCX1-CX01=CCX2-CCX1-CX01-CX20-CCX0 = HB2.hb1328
  hypB L.ax-CCX0-CX20-CCX2-CCX1-CX02=CX20-CCX2-CCX1-CX02-CCX0 = HB2.hb1329
  hypB L.ax-CCX0-CX20-CX21-CCX2-CX01=CX21-CCX0-CCX2-CX01 = HB2.hb1330
  hypB L.ax-CCX0-CCX0-Swap01=Swap01 = HB2.hb1331
  hypB L.ax-CCX0-CCX0-CX01=CX01 = HB2.hb1332
  hypB L.ax-CCX0-CCX0-CX01-CCX2=CX01-CCX2 = HB2.hb1333
  hypB L.ax-CCX0-CCX0-CX02=CX02 = HB2.hb1334
  hypB L.ax-CCX0-CCX0-CX02-CCX1=CX02-CCX1 = HB2.hb1335
  hypB L.ax-CCX0-CCX0-CCX1-CX02=CCX1-CX02 = HB2.hb1336
  hypB L.ax-CCX0-CCX0-CCX1-CCX2=CCX1-CCX2 = HB2.hb1337
  hypB L.ax-CCX0-CCX0-CCX1-CCX2-Swap01=CCX1-CCX2-Swap01 = HB2.hb1338
  hypB L.ax-CCX0-CCX0-CCX1-CX12-Swap01=CCX1-CX12-Swap01 = HB2.hb1339
  hypB L.ax-CCX0-CCX0-CCX2-Swap01=CCX2-Swap01 = HB2.hb1340
  hypB L.ax-CCX0-CCX0-CCX2-CCX1=CCX2-CCX1 = HB2.hb1341
  hypB L.ax-CCX0-CCX0-CX12-Swap01=CX12-Swap01 = HB2.hb1342
  hypB L.ax-CCX0-CCX0-CX12-CCX1-CX02=CX12-CCX1-CX02 = HB2.hb1343
  hypB L.ax-CCX0-CCX0-CX12-CCX2-Swap01=CX12-CCX2-Swap01 = HB2.hb1344
  hypB L.ax-CCX0-CCX0-CX21-CCX2-CX01=CX21-CCX2-CX01 = HB2.hb1345
  hypB L.ax-CCX0-CCX0-Swap12-Swap01=Swap12-Swap01 = HB2.hb1346
  hypB L.ax-CCX0-CCX0-Swap12-CCX1-CCX2-Swap01=Swap12-CCX1-CCX2-Swap01 = HB2.hb1347
  hypB L.ax-CCX0-CCX0-Swap12-CCX2-Swap01=Swap12-CCX2-Swap01 = HB2.hb1348

  hypB L.ax-iI-S0-K0-S0-CK10=S0-K0-S0-CK10-iI = HB2.hb1349
  hypB L.ax-iI-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-iI = HB2.hb1350
  hypB L.ax-iI-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-iI = HB2.hb1351
  hypB L.ax-iI-S0-K0-S0-CK20=S0-K0-S0-CK20-iI = HB2.hb1352
  hypB L.ax-iI-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-iI = HB2.hb1353
  hypB L.ax-iI-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-iI = HB2.hb1354
  hypB L.ax-iI-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-iI = HB2.hb1355
  hypB L.ax-iI-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-iI = HB2.hb1356
  hypB L.ax-iI-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-iI = HB2.hb1357
  hypB L.ax-iI-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-iI = HB2.hb1358
  hypB L.ax-iI-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-iI = HB2.hb1359
  hypB L.ax-iI-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-iI = HB2.hb1360
  hypB L.ax-iI-S0-K0-CK10=S0-K0-CK10-iI = HB2.hb1361
  hypB L.ax-iI-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-iI = HB2.hb1362
  hypB L.ax-iI-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-iI = HB2.hb1363
  hypB L.ax-iI-S0-K0-CK20=S0-K0-CK20-iI = HB2.hb1364
  hypB L.ax-iI-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-iI = HB2.hb1365
  hypB L.ax-iI-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-iI = HB2.hb1366
  hypB L.ax-iI-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-iI = HB2.hb1367
  hypB L.ax-iI-S0-K0-CK20-CK10=S0-K0-CK20-CK10-iI = HB2.hb1368
  hypB L.ax-iI-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-iI = HB2.hb1369
  hypB L.ax-iI-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-iI = HB2.hb1370
  hypB L.ax-iI-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-iI = HB2.hb1371
  hypB L.ax-iI-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-iI = HB2.hb1372
  hypB L.ax-iI-S0-K0-CCK'=S0-K0-CCK'-iI = HB2.hb1373
  hypB L.ax-iI-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-iI = HB2.hb1374
  hypB L.ax-iI-S0-CK10-CCK'=S0-CK10-CCK'-iI = HB2.hb1375
  hypB L.ax-iI-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-iI = HB2.hb1376
  hypB L.ax-iI-S0-CK20-S0-CK10=S0-CK20-S0-CK10-iI = HB2.hb1377
  hypB L.ax-iI-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-iI = HB2.hb1378
  hypB L.ax-iI-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-iI = HB2.hb1379
  hypB L.ax-iI-S0-CK20-CK10=S0-CK20-CK10-iI = HB2.hb1380
  hypB L.ax-iI-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-iI = HB2.hb1381
  hypB L.ax-iI-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-iI = HB2.hb1382
  hypB L.ax-iI-S0-CK20-CCK'=S0-CK20-CCK'-iI = HB2.hb1383
  hypB L.ax-iI-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-iI = HB2.hb1384
  hypB L.ax-iI-K0-S0-CK10=K0-S0-CK10-iI = HB2.hb1385
  hypB L.ax-iI-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-iI = HB2.hb1386
  hypB L.ax-iI-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-iI = HB2.hb1387
  hypB L.ax-iI-K0-S0-CK20=K0-S0-CK20-iI = HB2.hb1388
  hypB L.ax-iI-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-iI = HB2.hb1389
  hypB L.ax-iI-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-iI = HB2.hb1390
  hypB L.ax-iI-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-iI = HB2.hb1391
  hypB L.ax-iI-K0-S0-CK20-CK10=K0-S0-CK20-CK10-iI = HB2.hb1392
  hypB L.ax-iI-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-iI = HB2.hb1393
  hypB L.ax-iI-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-iI = HB2.hb1394
  hypB L.ax-iI-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-iI = HB2.hb1395
  hypB L.ax-iI-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-iI = HB2.hb1396
  hypB L.ax-iI-K0-CK10=K0-CK10-iI = HB2.hb1397
  hypB L.ax-iI-K0-CK10-CCK'=K0-CK10-CCK'-iI = HB2.hb1398
  hypB L.ax-iI-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-iI = HB2.hb1399
  hypB L.ax-iI-K0-CK20=K0-CK20-iI = HB2.hb1400
  hypB L.ax-iI-K0-CK20-S0-CK10=K0-CK20-S0-CK10-iI = HB2.hb1401
  hypB L.ax-iI-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-iI = HB2.hb1402
  hypB L.ax-iI-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-iI = HB2.hb1403
  hypB L.ax-iI-K0-CK20-CK10=K0-CK20-CK10-iI = HB2.hb1404
  hypB L.ax-iI-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-iI = HB2.hb1405
  hypB L.ax-iI-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-iI = HB2.hb1406
  hypB L.ax-iI-K0-CK20-CCK'=K0-CK20-CCK'-iI = HB2.hb1407
  hypB L.ax-iI-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-iI = HB2.hb1408
  hypB L.ax-iI-K0-CCK'=K0-CCK'-iI = HB2.hb1409
  hypB L.ax-iI-K0-CCK'-CCK'=K0-CCK'-CCK'-iI = HB2.hb1410
  hypB L.ax-iI-CK10-CCK'=CK10-CCK'-iI = HB2.hb1411
  hypB L.ax-iI-CK10-CCK'-CCK'=CK10-CCK'-CCK'-iI = HB2.hb1412
  hypB L.ax-iI-CK20-S0-CK10=CK20-S0-CK10-iI = HB2.hb1413
  hypB L.ax-iI-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-iI = HB2.hb1414
  hypB L.ax-iI-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-iI = HB2.hb1415
  hypB L.ax-iI-CK20-CK10=CK20-CK10-iI = HB2.hb1416
  hypB L.ax-iI-CK20-CK10-CCK'=CK20-CK10-CCK'-iI = HB2.hb1417
  hypB L.ax-iI-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-iI = HB2.hb1418
  hypB L.ax-iI-CK20-CCK'=CK20-CCK'-iI = HB2.hb1419
  hypB L.ax-iI-CK20-CCK'-CCK'=CK20-CCK'-CCK'-iI = HB2.hb1420

  hypB L.ax-S0-S0-K0-S0-CK10=K0-S0-CK10-X0-S0-S0-S1-S1-iI-iI-iI = HB2.hb1421
  hypB L.ax-S0-S0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI-iI-iI = HB2.hb1422
  hypB L.ax-S0-S0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI-iI-iI = HB2.hb1423
  hypB L.ax-S0-S0-K0-S0-CK20=K0-S0-CK20-X0-S0-S0-S2-S2-iI-iI-iI = HB2.hb1424
  hypB L.ax-S0-S0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01-iI-iI = HB2.hb1425
  hypB L.ax-S0-S0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12-iI-iI = HB2.hb1426
  hypB L.ax-S0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ-iI-iI = HB2.hb1427
  hypB L.ax-S0-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI-iI-iI = HB2.hb1428
  hypB L.ax-S0-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI = HB2.hb1429
  hypB L.ax-S0-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI-iI-iI = HB2.hb1430
  hypB L.ax-S0-S0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI = HB2.hb1431
  hypB L.ax-S0-S0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI-iI-iI = HB2.hb1432
  hypB L.ax-S0-S0-K0-CK10=K0-CK10-X0-CX10-CS01-CS01 = HB2.hb1433
  hypB L.ax-S0-S0-K0-CK10-CCK'=K0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12 = HB2.hb1434
  hypB L.ax-S0-S0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ = HB2.hb1435
  hypB L.ax-S0-S0-K0-CK20=K0-CK20-X0-CX20-CS02-CS02 = HB2.hb1436
  hypB L.ax-S0-S0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI = HB2.hb1437
  hypB L.ax-S0-S0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI = HB2.hb1438
  hypB L.ax-S0-S0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI = HB2.hb1439
  hypB L.ax-S0-S0-K0-CK20-CK10=K0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02 = HB2.hb1440
  hypB L.ax-S0-S0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1441
  hypB L.ax-S0-S0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ = HB2.hb1442
  hypB L.ax-S0-S0-K0-CK20-CCK'=K0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12 = HB2.hb1443
  hypB L.ax-S0-S0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ = HB2.hb1444
  hypB L.ax-S0-S0-K0-CCK'=K0-CCK'-X0-CCX0-CCZ = HB2.hb1445
  hypB L.ax-S0-S0-K0-CCK'-CCK'=K0-CCK'-CCK'-X0-CS12-CCZ = HB2.hb1446
  hypB L.ax-S0-S0-CK10-CCK'=CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ = HB2.hb1447
  hypB L.ax-S0-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ = HB2.hb1448
  hypB L.ax-S0-S0-CK20-S0-CK10=CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = HB2.hb1449
  hypB L.ax-S0-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12 = HB2.hb1450
  hypB L.ax-S0-S0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ = HB2.hb1451
  hypB L.ax-S0-S0-CK20-CK10=CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = HB2.hb1452
  hypB L.ax-S0-S0-CK20-CK10-CCK'=CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = HB2.hb1453
  hypB L.ax-S0-S0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1454
  hypB L.ax-S0-S0-CK20-CCK'=CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ = HB2.hb1455
  hypB L.ax-S0-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ = HB2.hb1456

  hypB L.ax-S1-S0-K0-S0-CK10=S0-K0-S0-CK10-S1 = HB2.hb1457
  hypB L.ax-S1-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-S1 = HB2.hb1458
  hypB L.ax-S1-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-S1 = HB2.hb1459
  hypB L.ax-S1-S0-K0-S0-CK20=S0-K0-S0-CK20-S1 = HB2.hb1460
  hypB L.ax-S1-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S1 = HB2.hb1461
  hypB L.ax-S1-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-S1 = HB2.hb1462
  hypB L.ax-S1-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S1 = HB2.hb1463
  hypB L.ax-S1-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-S1 = HB2.hb1464
  hypB L.ax-S1-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S1 = HB2.hb1465
  hypB L.ax-S1-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-S1 = HB2.hb1466
  hypB L.ax-S1-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-S1 = HB2.hb1467
  hypB L.ax-S1-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-S1 = HB2.hb1468
  hypB L.ax-S1-S0-K0-CK10=S0-K0-CK10-S1 = HB2.hb1469
  hypB L.ax-S1-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-S1 = HB2.hb1470
  hypB L.ax-S1-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-S1 = HB2.hb1471
  hypB L.ax-S1-S0-K0-CK20=S0-K0-CK20-S1 = HB2.hb1472
  hypB L.ax-S1-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-S1 = HB2.hb1473
  hypB L.ax-S1-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-S1 = HB2.hb1474
  hypB L.ax-S1-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-S1 = HB2.hb1475
  hypB L.ax-S1-S0-K0-CK20-CK10=S0-K0-CK20-CK10-S1 = HB2.hb1476
  hypB L.ax-S1-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-S1 = HB2.hb1477
  hypB L.ax-S1-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S1 = HB2.hb1478
  hypB L.ax-S1-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-S1 = HB2.hb1479
  hypB L.ax-S1-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S1 = HB2.hb1480
  hypB L.ax-S1-S0-K0-CCK'=S0-K0-CCK'-S1 = HB2.hb1481
  hypB L.ax-S1-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-S1 = HB2.hb1482
  
  hypB L.ax-S1-S0-CK10-CCK'=S0-CK10-CCK'-S1 = HB2.hb1483
  hypB L.ax-S1-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S1 = HB2.hb1484
  hypB L.ax-S1-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S1 = HB2.hb1485
  hypB L.ax-S1-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-S1 = HB2.hb1486
  hypB L.ax-S1-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-S1 = HB2.hb1487
  hypB L.ax-S1-S0-CK20-CK10=S0-CK20-CK10-S1 = HB2.hb1488
  hypB L.ax-S1-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-S1 = HB2.hb1489
  hypB L.ax-S1-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-S1 = HB2.hb1490
  hypB L.ax-S1-S0-CK20-CCK'=S0-CK20-CCK'-S1 = HB2.hb1491
  hypB L.ax-S1-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S1 = HB2.hb1492
  hypB L.ax-S1-K0-S0-CK10=K0-S0-CK10-S1 = HB2.hb1493
  hypB L.ax-S1-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-S1 = HB2.hb1494
  hypB L.ax-S1-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S1 = HB2.hb1495
  hypB L.ax-S1-K0-S0-CK20=K0-S0-CK20-S1 = HB2.hb1496
  hypB L.ax-S1-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S1 = HB2.hb1497
  hypB L.ax-S1-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-S1 = HB2.hb1498
  hypB L.ax-S1-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S1 = HB2.hb1499
  hypB L.ax-S1-K0-S0-CK20-CK10=K0-S0-CK20-CK10-S1 = HB2.hb1500
  hypB L.ax-S1-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-S1 = HB2.hb1501
  hypB L.ax-S1-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-S1 = HB2.hb1502
  hypB L.ax-S1-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-S1 = HB2.hb1503
  hypB L.ax-S1-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-S1 = HB2.hb1504
  hypB L.ax-S1-K0-CK10=K0-CK10-S1 = HB2.hb1505
  hypB L.ax-S1-K0-CK10-CCK'=K0-CK10-CCK'-S1 = HB2.hb1506
  hypB L.ax-S1-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S1 = HB2.hb1507
  hypB L.ax-S1-K0-CK20=K0-CK20-S1 = HB2.hb1508
  hypB L.ax-S1-K0-CK20-S0-CK10=K0-CK20-S0-CK10-S1 = HB2.hb1509
  hypB L.ax-S1-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-S1 = HB2.hb1510
  hypB L.ax-S1-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-S1 = HB2.hb1511
  hypB L.ax-S1-K0-CK20-CK10=K0-CK20-CK10-S1 = HB2.hb1512
  hypB L.ax-S1-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-S1 = HB2.hb1513
  hypB L.ax-S1-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-S1 = HB2.hb1514
  hypB L.ax-S1-K0-CK20-CCK'=K0-CK20-CCK'-S1 = HB2.hb1515
  hypB L.ax-S1-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-S1 = HB2.hb1516
  hypB L.ax-S1-K0-CCK'=K0-CCK'-S1 = HB2.hb1517
  hypB L.ax-S1-K0-CCK'-CCK'=K0-CCK'-CCK'-S1 = HB2.hb1518
  hypB L.ax-S1-CK10-CCK'=CK10-CCK'-S1 = HB2.hb1519
  hypB L.ax-S1-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S1 = HB2.hb1520
  hypB L.ax-S1-CK20-S0-CK10=CK20-S0-CK10-S1 = HB2.hb1521
  hypB L.ax-S1-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-S1 = HB2.hb1522
  hypB L.ax-S1-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-S1 = HB2.hb1523
  hypB L.ax-S1-CK20-CK10=CK20-CK10-S1 = HB2.hb1524
  hypB L.ax-S1-CK20-CK10-CCK'=CK20-CK10-CCK'-S1 = HB2.hb1525
  hypB L.ax-S1-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-S1 = HB2.hb1526
  hypB L.ax-S1-CK20-CCK'=CK20-CCK'-S1 = HB2.hb1527
  hypB L.ax-S1-CK20-CCK'-CCK'=CK20-CCK'-CCK'-S1 = HB2.hb1528
  hypB L.ax-S2-S0-K0-S0-CK10=S0-K0-S0-CK10-S2 = HB2.hb1529
  hypB L.ax-S2-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-S2 = HB2.hb1530
  hypB L.ax-S2-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-S2 = HB2.hb1531
  hypB L.ax-S2-S0-K0-S0-CK20=S0-K0-S0-CK20-S2 = HB2.hb1532
  hypB L.ax-S2-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S2 = HB2.hb1533
  hypB L.ax-S2-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-S2 = HB2.hb1534
  hypB L.ax-S2-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S2 = HB2.hb1535
  hypB L.ax-S2-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-S2 = HB2.hb1536
  hypB L.ax-S2-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S2 = HB2.hb1537
  hypB L.ax-S2-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-S2 = HB2.hb1538
  hypB L.ax-S2-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-S2 = HB2.hb1539
  hypB L.ax-S2-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-S2 = HB2.hb1540
  hypB L.ax-S2-S0-K0-CK10=S0-K0-CK10-S2 = HB2.hb1541
  hypB L.ax-S2-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-S2 = HB2.hb1542
  hypB L.ax-S2-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-S2 = HB2.hb1543
  hypB L.ax-S2-S0-K0-CK20=S0-K0-CK20-S2 = HB2.hb1544
  hypB L.ax-S2-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-S2 = HB2.hb1545
  hypB L.ax-S2-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-S2 = HB2.hb1546
  hypB L.ax-S2-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-S2 = HB2.hb1547
  hypB L.ax-S2-S0-K0-CK20-CK10=S0-K0-CK20-CK10-S2 = HB2.hb1548
  hypB L.ax-S2-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-S2 = HB2.hb1549
  hypB L.ax-S2-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S2 = HB2.hb1550
  hypB L.ax-S2-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-S2 = HB2.hb1551
  hypB L.ax-S2-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S2 = HB2.hb1552
  hypB L.ax-S2-S0-K0-CCK'=S0-K0-CCK'-S2 = HB2.hb1553
  hypB L.ax-S2-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-S2 = HB2.hb1554
  hypB L.ax-S2-S0-CK10-CCK'=S0-CK10-CCK'-S2 = HB2.hb1555
  hypB L.ax-S2-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S2 = HB2.hb1556
  hypB L.ax-S2-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S2 = HB2.hb1557
  hypB L.ax-S2-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-S2 = HB2.hb1558
  hypB L.ax-S2-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-S2 = HB2.hb1559
  hypB L.ax-S2-S0-CK20-CK10=S0-CK20-CK10-S2 = HB2.hb1560
  hypB L.ax-S2-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-S2 = HB2.hb1561
  hypB L.ax-S2-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-S2 = HB2.hb1562
  hypB L.ax-S2-S0-CK20-CCK'=S0-CK20-CCK'-S2 = HB2.hb1563
  hypB L.ax-S2-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S2 = HB2.hb1564
  hypB L.ax-S2-K0-S0-CK10=K0-S0-CK10-S2 = HB2.hb1565
  hypB L.ax-S2-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-S2 = HB2.hb1566
  hypB L.ax-S2-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S2 = HB2.hb1567
  hypB L.ax-S2-K0-S0-CK20=K0-S0-CK20-S2 = HB2.hb1568
  hypB L.ax-S2-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S2 = HB2.hb1569
  hypB L.ax-S2-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-S2 = HB2.hb1570
  hypB L.ax-S2-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S2 = HB2.hb1571
  hypB L.ax-S2-K0-S0-CK20-CK10=K0-S0-CK20-CK10-S2 = HB2.hb1572
  hypB L.ax-S2-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-S2 = HB2.hb1573
  hypB L.ax-S2-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-S2 = HB2.hb1574
  hypB L.ax-S2-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-S2 = HB2.hb1575
  hypB L.ax-S2-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-S2 = HB2.hb1576
  hypB L.ax-S2-K0-CK10=K0-CK10-S2 = HB2.hb1577
  hypB L.ax-S2-K0-CK10-CCK'=K0-CK10-CCK'-S2 = HB2.hb1578
  hypB L.ax-S2-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S2 = HB2.hb1579
  hypB L.ax-S2-K0-CK20=K0-CK20-S2 = HB2.hb1580
  hypB L.ax-S2-K0-CK20-S0-CK10=K0-CK20-S0-CK10-S2 = HB2.hb1581
  hypB L.ax-S2-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-S2 = HB2.hb1582
  hypB L.ax-S2-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-S2 = HB2.hb1583
  hypB L.ax-S2-K0-CK20-CK10=K0-CK20-CK10-S2 = HB2.hb1584
  hypB L.ax-S2-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-S2 = HB2.hb1585
  hypB L.ax-S2-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-S2 = HB2.hb1586
  hypB L.ax-S2-K0-CK20-CCK'=K0-CK20-CCK'-S2 = HB2.hb1587
  hypB L.ax-S2-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-S2 = HB2.hb1588
  hypB L.ax-S2-K0-CCK'=K0-CCK'-S2 = HB2.hb1589
  hypB L.ax-S2-K0-CCK'-CCK'=K0-CCK'-CCK'-S2 = HB2.hb1590
  hypB L.ax-S2-CK10-CCK'=CK10-CCK'-S2 = HB2.hb1591
  hypB L.ax-S2-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S2 = HB2.hb1592
  hypB L.ax-S2-CK20-S0-CK10=CK20-S0-CK10-S2 = HB2.hb1593
  hypB L.ax-S2-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-S2 = HB2.hb1594
  hypB L.ax-S2-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-S2 = HB2.hb1595
  hypB L.ax-S2-CK20-CK10=CK20-CK10-S2 = HB2.hb1596
  hypB L.ax-S2-CK20-CK10-CCK'=CK20-CK10-CCK'-S2 = HB2.hb1597
  hypB L.ax-S2-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-S2 = HB2.hb1598
  hypB L.ax-S2-CK20-CCK'=CK20-CCK'-S2 = HB2.hb1599
  hypB L.ax-S2-CK20-CCK'-CCK'=CK20-CCK'-CCK'-S2 = HB2.hb1600

  hypB L.ax-CS01-S0-K0-S0-CK10=S0-K0-S0-CS01-CS01 = HB2.hb1601
  hypB L.ax-CS01-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-CCX0-S0-CS01-CS01-CS12 = HB2.hb1602
  hypB L.ax-CS01-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CCK'-S0-CS01-CS01-CS12-CS12-CS12-CCZ = HB2.hb1603
  hypB L.ax-CS01-S0-K0-S0-CK20=S0-K0-S0-CK20-CK10-CX10-CCX0-S1-CCZ = HB2.hb1604
  hypB L.ax-CS01-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-S1-CS01-CS01-CS01-CS12-CS12-CS12-CCZ = HB2.hb1605
  hypB L.ax-CS01-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-S1-CS01-CS01-CS01 = HB2.hb1606
  hypB L.ax-CS01-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCX0-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB2.hb1607
  hypB L.ax-CS01-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CCX0-CS01-CS01-CCZ = HB2.hb1608
  hypB L.ax-CS01-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CCK'-CS01-CS01 = HB2.hb1609
  hypB L.ax-CS01-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12 = HB2.hb1610
  hypB L.ax-CS01-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX10-S1-CS12-CCZ = HB2.hb1611
  hypB L.ax-CS01-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX10-S1 = HB2.hb1612
  hypB L.ax-CS01-S0-K0-CK10=S0-K0-CK10-CS01 = HB2.hb1613
  hypB L.ax-CS01-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCK'-CS01-CS12-CCZ = HB2.hb1614
  hypB L.ax-CS01-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCX0-CS01-CCZ = HB2.hb1615
  hypB L.ax-CS01-S0-K0-CK20=S0-K0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ = HB2.hb1616
  hypB L.ax-CS01-S0-K0-CK20-S0-CK10=S0-K0-CK20-CCK'-CCX0-S0-CS01-CS01-CS12 = HB2.hb1617
  hypB L.ax-CS01-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CS01-CS01-CS12-CS12-CS12-CCZ = HB2.hb1618
  hypB L.ax-CS01-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-S0-CS01-CS01 = HB2.hb1619
  hypB L.ax-CS01-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ = HB2.hb1620
  hypB L.ax-CS01-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS01 = HB2.hb1621
  hypB L.ax-CS01-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS01-CS12-CS12-CS12-CCZ = HB2.hb1622
  hypB L.ax-CS01-S0-K0-CK20-CCK'=S0-K0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12 = HB2.hb1623
  hypB L.ax-CS01-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-S1 = HB2.hb1624
  hypB L.ax-CS01-S0-K0-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ = HB2.hb1625
  hypB L.ax-CS01-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12 = HB2.hb1626
  hypB L.ax-CS01-S0-CK10-CCK'=CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CCZ = HB2.hb1627
  hypB L.ax-CS01-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX10-S0-CS01-CS01-CS01-CS12-CCZ = HB2.hb1628
  hypB L.ax-CS01-S0-CK20=S0-CK20-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ = HB2.hb1629
  hypB L.ax-CS01-S0-CK20-S0-CK10=S0-CK20-CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12 = HB2.hb1630
  hypB L.ax-CS01-S0-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12 = HB2.hb1631
  hypB L.ax-CS01-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CX10-CCX0-S0-CS01-CS01-CS01-CS12-CS12-CS12 = HB2.hb1632
  hypB L.ax-CS01-S0-CK20-CK10=S0-CK20-S0-CK10-CCK'-CCK'-S0-S0-S0-CS01-CS12-CCZ = HB2.hb1633
  hypB L.ax-CS01-S0-CK20-CK10-CCK'=S0-CK20-S0-CK10-CCX0-S0-S0-S0-CS01-CCZ = HB2.hb1634
  hypB L.ax-CS01-S0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-S0-S0-S0-CS01-CS12-CS12-CS12 = HB2.hb1635
  hypB L.ax-CS01-S0-CK20-CCK'=S0-CK20-CCK'-CS01 = HB2.hb1636
  hypB L.ax-CS01-S0-CK20-CCK'-CCK'=S0-CK20-CS01-CS12-CS12-CS12-CCZ = HB2.hb1637
  hypB L.ax-CS01-K0-S0-CK10=K0-S0-CS01-CS01 = HB2.hb1638
  hypB L.ax-CS01-K0-S0-CK10-CCK'=K0-CCK'-CCK'-CCX0-S0-CS01-CS01-CS12 = HB2.hb1639
  hypB L.ax-CS01-K0-S0-CK10-CCK'-CCK'=K0-CCK'-S0-CS01-CS01-CS12-CS12-CS12-CCZ = HB2.hb1640
  hypB L.ax-CS01-K0-S0-CK20=K0-S0-CK20-CK10-CX10-CCX0-S1-CCZ = HB2.hb1641
  hypB L.ax-CS01-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-S1-CS01-CS01-CS01-CS12-CS12-CS12-CCZ = HB2.hb1642
  hypB L.ax-CS01-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-S1-CS01-CS01-CS01 = HB2.hb1643
  hypB L.ax-CS01-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB2.hb1644
  hypB L.ax-CS01-K0-S0-CK20-CK10=K0-S0-CK20-CCX0-CS01-CS01-CCZ = HB2.hb1645
  hypB L.ax-CS01-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CCK'-CS01-CS01 = HB2.hb1646
  hypB L.ax-CS01-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12 = HB2.hb1647
  hypB L.ax-CS01-K0-S0-CK20-CCK'=K0-S0-CK20-CK10-CCK'-CX10-S1-CS12-CCZ = HB2.hb1648
  hypB L.ax-CS01-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10-S1 = HB2.hb1649
  hypB L.ax-CS01-K0-CK10=K0-CK10-CS01 = HB2.hb1650
  hypB L.ax-CS01-K0-CK10-CCK'=K0-CK10-CCK'-CCK'-CS01-CS12-CCZ = HB2.hb1651
  hypB L.ax-CS01-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCX0-CS01-CCZ = HB2.hb1652
  hypB L.ax-CS01-K0-CK20=K0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ = HB2.hb1653
  hypB L.ax-CS01-K0-CK20-S0-CK10=K0-CK20-CCK'-CCX0-S0-CS01-CS01-CS12 = HB2.hb1654
  hypB L.ax-CS01-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CS01-CS01-CS12-CS12-CS12-CCZ = HB2.hb1655
  hypB L.ax-CS01-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-S0-CS01-CS01 = HB2.hb1656
  hypB L.ax-CS01-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ = HB2.hb1657
  hypB L.ax-CS01-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS01 = HB2.hb1658
  hypB L.ax-CS01-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CS01-CS12-CS12-CS12-CCZ = HB2.hb1659
  hypB L.ax-CS01-K0-CK20-CCK'=K0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12 = HB2.hb1660
  hypB L.ax-CS01-K0-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-S1 = HB2.hb1661
  hypB L.ax-CS01-K0-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-S1-CCZ = HB2.hb1662
  hypB L.ax-CS01-K0-CCK'-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-S0-S1-CS12-CS12-CS12 = HB2.hb1663
  hypB L.ax-CS01-CK10-CCK'=S0-CK10-CCK'-S0-S0-S0-CS01 = HB2.hb1664
  hypB L.ax-CS01-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S0-S0-S0-CS01 = HB2.hb1665
  hypB L.ax-CS01-CK20=CK20-CCK'-CCK'-CCX0-CS01-CS12-CS12-CCZ = HB2.hb1666
  hypB L.ax-CS01-CK20-S0-CK10=CK20-CK10-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12 = HB2.hb1667
  hypB L.ax-CS01-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-CS01-CS01-CS01-CS12 = HB2.hb1668
  hypB L.ax-CS01-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CX10-CCX0-S0-CS01-CS01-CS01-CS12-CS12-CS12 = HB2.hb1669
  hypB L.ax-CS01-CK20-CK10=CK20-S0-CK10-CCK'-CCK'-S0-S0-S0-CS01-CS12-CCZ = HB2.hb1670
  hypB L.ax-CS01-CK20-CK10-CCK'=CK20-S0-CK10-CCX0-S0-S0-S0-CS01-CCZ = HB2.hb1671
  hypB L.ax-CS01-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCX0-S0-S0-S0-CS01-CS12-CS12-CS12 = HB2.hb1672
  hypB L.ax-CS01-CK20-CCK'=CK20-CCK'-CS01 = HB2.hb1673
  hypB L.ax-CS01-CK20-CCK'-CCK'=CK20-CS01-CS12-CS12-CS12-CCZ = HB2.hb1674
  hypB L.ax-CS02-S0-K0-S0-CK10=S0-K0-S0-CK20-CK10-CX20-CCX0-S2-CCZ = HB2.hb1675
  hypB L.ax-CS02-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX20-S2-CS12-CCZ = HB2.hb1676
  hypB L.ax-CS02-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX20-S2 = HB2.hb1677
  hypB L.ax-CS02-S0-K0-S0-CK20=S0-K0-S0-CS02-CS02 = HB2.hb1678
  hypB L.ax-CS02-S0-K0-S0-CK20-S0-CK10=S0-K0-CK10-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1679
  hypB L.ax-CS02-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1680
  hypB L.ax-CS02-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1681
  hypB L.ax-CS02-S0-K0-S0-CK20-CK10=S0-K0-S0-CK10-CCX0-CS02-CS02-CCZ = HB2.hb1682
  hypB L.ax-CS02-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK10-CCK'-CS02-CS02 = HB2.hb1683
  hypB L.ax-CS02-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = HB2.hb1684
  hypB L.ax-CS02-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-CCX0-S0-CS02-CS02-CS12 = HB2.hb1685
  hypB L.ax-CS02-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CCK'-S0-CS02-CS02-CS12-CS12-CS12-CCZ = HB2.hb1686
  hypB L.ax-CS02-S0-K0-CK10=S0-K0-S0-CK20-S0-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = HB2.hb1687
  hypB L.ax-CS02-S0-K0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = HB2.hb1688
  hypB L.ax-CS02-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1689
  hypB L.ax-CS02-S0-K0-CK20=S0-K0-CK20-CS02 = HB2.hb1690
  hypB L.ax-CS02-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = HB2.hb1691
  hypB L.ax-CS02-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS02 = HB2.hb1692
  hypB L.ax-CS02-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ = HB2.hb1693
  hypB L.ax-CS02-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = HB2.hb1694
  hypB L.ax-CS02-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS02 = HB2.hb1695
  hypB L.ax-CS02-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ = HB2.hb1696
  hypB L.ax-CS02-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCK'-CS02-CS12-CCZ = HB2.hb1697
  hypB L.ax-CS02-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCX0-CS02-CCZ = HB2.hb1698
  hypB L.ax-CS02-S0-K0-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX20-CCX0-S0-S0-S0-S2-CCZ = HB2.hb1699
  hypB L.ax-CS02-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-S0-S2-CS12-CS12-CS12 = HB2.hb1700

  hypB L.ax-CS02-S0-CK10=S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = HB2.hb1701
  hypB L.ax-CS02-S0-CK10-CCK'=S0-CK10-CCK'-CS02 = HB2.hb1702
  hypB L.ax-CS02-S0-CK10-CCK'-CCK'=S0-CK10-CS02-CS12-CS12-CS12-CCZ = HB2.hb1703
  hypB L.ax-CS02-S0-CK20-S0-CK10=CK20-CK10-CCK'-CCK'-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = HB2.hb1704
  hypB L.ax-CS02-S0-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12 = HB2.hb1705
  hypB L.ax-CS02-S0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ = HB2.hb1706
  hypB L.ax-CS02-S0-CK20-CK10=CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ = HB2.hb1707
  hypB L.ax-CS02-S0-CK20-CK10-CCK'=CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ = HB2.hb1708
  hypB L.ax-CS02-S0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12 = HB2.hb1709
  hypB L.ax-CS02-S0-CK20-CCK'=CK20-CCK'-CX20-CCX0-S0-CS02-CS02-CS02-CCZ = HB2.hb1710
  hypB L.ax-CS02-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX20-S0-CS02-CS02-CS02-CS12-CCZ = HB2.hb1711
  hypB L.ax-CS02-K0-S0-CK10=K0-S0-CK20-CK10-CX20-CCX0-S2-CCZ = HB2.hb1712
  hypB L.ax-CS02-K0-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-S2-CS12-CCZ = HB2.hb1713
  hypB L.ax-CS02-K0-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX20-S2 = HB2.hb1714
  hypB L.ax-CS02-K0-S0-CK20=K0-S0-CS02-CS02 = HB2.hb1715
  hypB L.ax-CS02-K0-S0-CK20-S0-CK10=K0-CK10-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1716
  hypB L.ax-CS02-K0-S0-CK20-S0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1717
  hypB L.ax-CS02-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1718
  hypB L.ax-CS02-K0-S0-CK20-CK10=K0-S0-CK10-CCX0-CS02-CS02-CCZ = HB2.hb1719
  hypB L.ax-CS02-K0-S0-CK20-CK10-CCK'=K0-S0-CK10-CCK'-CS02-CS02 = HB2.hb1720
  hypB L.ax-CS02-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = HB2.hb1721
  hypB L.ax-CS02-K0-S0-CK20-CCK'=K0-CCK'-CCK'-CCX0-S0-CS02-CS02-CS12 = HB2.hb1722
  hypB L.ax-CS02-K0-S0-CK20-CCK'-CCK'=K0-CCK'-S0-CS02-CS02-CS12-CS12-CS12-CCZ = HB2.hb1723
  hypB L.ax-CS02-K0-CK10=K0-S0-CK20-S0-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = HB2.hb1724
  hypB L.ax-CS02-K0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = HB2.hb1725
  hypB L.ax-CS02-K0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB2.hb1726
  hypB L.ax-CS02-K0-CK20=K0-CK20-CS02 = HB2.hb1727
  hypB L.ax-CS02-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = HB2.hb1728
  hypB L.ax-CS02-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CS02 = HB2.hb1729
  hypB L.ax-CS02-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ = HB2.hb1730
  hypB L.ax-CS02-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = HB2.hb1731
  hypB L.ax-CS02-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS02 = HB2.hb1732
  hypB L.ax-CS02-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ = HB2.hb1733
  hypB L.ax-CS02-K0-CK20-CCK'=K0-CK20-CCK'-CCK'-CS02-CS12-CCZ = HB2.hb1734
  hypB L.ax-CS02-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCX0-CS02-CCZ = HB2.hb1735
  hypB L.ax-CS02-K0-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CCX0-S0-S0-S0-S2-CCZ = HB2.hb1736
  hypB L.ax-CS02-K0-CCK'-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-S0-S2-CS12-CS12-CS12 = HB2.hb1737
  hypB L.ax-CS02-CK10=CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = HB2.hb1738
  hypB L.ax-CS02-CK10-CCK'=CK10-CCK'-CS02 = HB2.hb1739
  hypB L.ax-CS02-CK10-CCK'-CCK'=CK10-CS02-CS12-CS12-CS12-CCZ = HB2.hb1740
  hypB L.ax-CS02-CK20-S0-CK10=S0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = HB2.hb1741
  hypB L.ax-CS02-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CS02 = HB2.hb1742
  hypB L.ax-CS02-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CS02-CS12-CS12-CS12-CCZ = HB2.hb1743
  hypB L.ax-CS02-CK20-CK10=S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS12 = HB2.hb1744
  hypB L.ax-CS02-CK20-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CCZ = HB2.hb1745
  hypB L.ax-CS02-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX10-S0-S0-CS01-CS01-CS02-CS12-CS12-CS12-CCZ = HB2.hb1746
  hypB L.ax-CS02-CK20-CCK'=S0-CK20-CCK'-S0-S0-S0-CS02 = HB2.hb1747
  hypB L.ax-CS02-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-S0-S0-S0-CS02 = HB2.hb1748

  hypB L.ax-CS12-S0-K0-S0-CK10=S0-K0-S0-CK10-CS12 = HB2.hb1749
  hypB L.ax-CS12-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CS12 = HB2.hb1750
  hypB L.ax-CS12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CS12 = HB2.hb1751
  hypB L.ax-CS12-S0-K0-S0-CK20=S0-K0-S0-CK20-CS12 = HB2.hb1752
  hypB L.ax-CS12-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CS12 = HB2.hb1753
  hypB L.ax-CS12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CS12 = HB2.hb1754
  hypB L.ax-CS12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12 = HB2.hb1755
  hypB L.ax-CS12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CS12 = HB2.hb1756
  hypB L.ax-CS12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS12 = HB2.hb1757
  hypB L.ax-CS12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CS12 = HB2.hb1758
  hypB L.ax-CS12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CS12 = HB2.hb1759
  hypB L.ax-CS12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CS12 = HB2.hb1760
  hypB L.ax-CS12-S0-K0-CK10=S0-K0-CK10-CS12 = HB2.hb1761
  hypB L.ax-CS12-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CS12 = HB2.hb1762
  hypB L.ax-CS12-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CS12 = HB2.hb1763
  hypB L.ax-CS12-S0-K0-CK20=S0-K0-CK20-CS12 = HB2.hb1764
  hypB L.ax-CS12-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS12 = HB2.hb1765
  hypB L.ax-CS12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS12 = HB2.hb1766
  hypB L.ax-CS12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CS12 = HB2.hb1767
  hypB L.ax-CS12-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CS12 = HB2.hb1768
  hypB L.ax-CS12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CS12 = HB2.hb1769
  hypB L.ax-CS12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CS12 = HB2.hb1770
  hypB L.ax-CS12-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CS12 = HB2.hb1771
  hypB L.ax-CS12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CS12 = HB2.hb1772
  hypB L.ax-CS12-S0-K0-CCK'=S0-K0-CCK'-CS12 = HB2.hb1773
  hypB L.ax-CS12-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CS12 = HB2.hb1774
  hypB L.ax-CS12-S0-CK10-CCK'=S0-CK10-CCK'-CS12 = HB2.hb1775
  hypB L.ax-CS12-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CS12 = HB2.hb1776
  hypB L.ax-CS12-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CS12 = HB2.hb1777
  hypB L.ax-CS12-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CS12 = HB2.hb1778
  hypB L.ax-CS12-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CS12 = HB2.hb1779
  hypB L.ax-CS12-S0-CK20-CK10=S0-CK20-CK10-CS12 = HB2.hb1780
  hypB L.ax-CS12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CS12 = HB2.hb1781
  hypB L.ax-CS12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CS12 = HB2.hb1782
  hypB L.ax-CS12-S0-CK20-CCK'=S0-CK20-CCK'-CS12 = HB2.hb1783
  hypB L.ax-CS12-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CS12 = HB2.hb1784
  hypB L.ax-CS12-K0-S0-CK10=K0-S0-CK10-CS12 = HB2.hb1785
  hypB L.ax-CS12-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CS12 = HB2.hb1786
  hypB L.ax-CS12-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CS12 = HB2.hb1787
  hypB L.ax-CS12-K0-S0-CK20=K0-S0-CK20-CS12 = HB2.hb1788
  hypB L.ax-CS12-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CS12 = HB2.hb1789
  hypB L.ax-CS12-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CS12 = HB2.hb1790
  hypB L.ax-CS12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12 = HB2.hb1791
  hypB L.ax-CS12-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CS12 = HB2.hb1792
  hypB L.ax-CS12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CS12 = HB2.hb1793
  hypB L.ax-CS12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12 = HB2.hb1794
  hypB L.ax-CS12-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CS12 = HB2.hb1795
  hypB L.ax-CS12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CS12 = HB2.hb1796
  hypB L.ax-CS12-K0-CK10=K0-CK10-CS12 = HB2.hb1797
  hypB L.ax-CS12-K0-CK10-CCK'=K0-CK10-CCK'-CS12 = HB2.hb1798
  hypB L.ax-CS12-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CS12 = HB2.hb1799
  hypB L.ax-CS12-K0-CK20=K0-CK20-CS12 = HB2.hb1800
  hypB L.ax-CS12-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CS12 = HB2.hb1801
  hypB L.ax-CS12-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CS12 = HB2.hb1802
  hypB L.ax-CS12-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CS12 = HB2.hb1803
  hypB L.ax-CS12-K0-CK20-CK10=K0-CK20-CK10-CS12 = HB2.hb1804
  hypB L.ax-CS12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CS12 = HB2.hb1805
  hypB L.ax-CS12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CS12 = HB2.hb1806
  hypB L.ax-CS12-K0-CK20-CCK'=K0-CK20-CCK'-CS12 = HB2.hb1807
  hypB L.ax-CS12-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CS12 = HB2.hb1808
  hypB L.ax-CS12-K0-CCK'=K0-CCK'-CS12 = HB2.hb1809
  hypB L.ax-CS12-K0-CCK'-CCK'=K0-CCK'-CCK'-CS12 = HB2.hb1810
  hypB L.ax-CS12-CK10-CCK'=CK10-CCK'-CS12 = HB2.hb1811
  hypB L.ax-CS12-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CS12 = HB2.hb1812
  hypB L.ax-CS12-CK20-S0-CK10=CK20-S0-CK10-CS12 = HB2.hb1813
  hypB L.ax-CS12-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CS12 = HB2.hb1814
  hypB L.ax-CS12-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CS12 = HB2.hb1815
  hypB L.ax-CS12-CK20-CK10=CK20-CK10-CS12 = HB2.hb1816
  hypB L.ax-CS12-CK20-CK10-CCK'=CK20-CK10-CCK'-CS12 = HB2.hb1817
  hypB L.ax-CS12-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CS12 = HB2.hb1818
  hypB L.ax-CS12-CK20-CCK'=CK20-CCK'-CS12 = HB2.hb1819
  hypB L.ax-CS12-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CS12 = HB2.hb1820

  hypB L.ax-CCZ-S0-K0-S0-CK10=S0-K0-S0-CK10-CCX0-CS12-CCZ = HB2.hb1821
  hypB L.ax-CCZ-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0 = HB2.hb1822
  hypB L.ax-CCZ-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCZ = HB2.hb1823
  hypB L.ax-CCZ-S0-K0-S0-CK20=S0-K0-S0-CK20-CCX0-CS12-CCZ = HB2.hb1824
  hypB L.ax-CCZ-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCZ = HB2.hb1825
  hypB L.ax-CCZ-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ = HB2.hb1826
  hypB L.ax-CCZ-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0 = HB2.hb1827
  hypB L.ax-CCZ-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ = HB2.hb1828
  hypB L.ax-CCZ-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCX0-CS12-CS12 = HB2.hb1829
  hypB L.ax-CCZ-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ = HB2.hb1830
  hypB L.ax-CCZ-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0 = HB2.hb1831
  hypB L.ax-CCZ-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCZ = HB2.hb1832
  hypB L.ax-CCZ-S0-K0-CK10=S0-K0-CK10-CCZ = HB2.hb1833
  hypB L.ax-CCZ-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-CS12-CCZ = HB2.hb1834
  hypB L.ax-CCZ-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CCX0 = HB2.hb1835
  hypB L.ax-CCZ-S0-K0-CK20=S0-K0-CK20-CCZ = HB2.hb1836
  hypB L.ax-CCZ-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCX0 = HB2.hb1837
  hypB L.ax-CCZ-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCZ = HB2.hb1838
  hypB L.ax-CCZ-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB2.hb1839
  hypB L.ax-CCZ-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCX0 = HB2.hb1840
  hypB L.ax-CCZ-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCZ = HB2.hb1841
  hypB L.ax-CCZ-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB2.hb1842
  hypB L.ax-CCZ-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-CS12-CCZ = HB2.hb1843
  hypB L.ax-CCZ-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CCX0 = HB2.hb1844
  hypB L.ax-CCZ-S0-K0-CCK'=S0-K0-CCK'-CCZ = HB2.hb1845
  hypB L.ax-CCZ-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CCX0-CS12-CCZ = HB2.hb1846
  hypB L.ax-CCZ-S0-CK10-CCK'=S0-CK10-CCK'-CCZ = HB2.hb1847
  hypB L.ax-CCZ-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB2.hb1848
  hypB L.ax-CCZ-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCX0-CS12-CCZ = HB2.hb1849
  hypB L.ax-CCZ-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0 = HB2.hb1850
  hypB L.ax-CCZ-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCZ = HB2.hb1851
  hypB L.ax-CCZ-S0-CK20-CK10=S0-CK20-CK10-CCZ = HB2.hb1852
  hypB L.ax-CCZ-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CCX0-CS12-CCZ = HB2.hb1853
  hypB L.ax-CCZ-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CCX0 = HB2.hb1854
  hypB L.ax-CCZ-S0-CK20-CCK'=S0-CK20-CCK'-CCZ = HB2.hb1855
  hypB L.ax-CCZ-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CCX0-CS12-CCZ = HB2.hb1856

  hypB L.ax-CCZ-K0-S0-CK10=K0-S0-CK10-CCX0-CS12-CCZ = HB2.hb1857
  hypB L.ax-CCZ-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCX0 = HB2.hb1858
  hypB L.ax-CCZ-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCZ = HB2.hb1859
  hypB L.ax-CCZ-K0-S0-CK20=K0-S0-CK20-CCX0-CS12-CCZ = HB2.hb1860
  hypB L.ax-CCZ-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCZ = HB2.hb1861
  hypB L.ax-CCZ-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ = HB2.hb1862
  hypB L.ax-CCZ-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0 = HB2.hb1863
  hypB L.ax-CCZ-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ = HB2.hb1864
  hypB L.ax-CCZ-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCX0-CS12-CS12 = HB2.hb1865
  hypB L.ax-CCZ-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ = HB2.hb1866
  hypB L.ax-CCZ-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCX0 = HB2.hb1867
  hypB L.ax-CCZ-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCZ = HB2.hb1868
  hypB L.ax-CCZ-K0-CK10=K0-CK10-CCZ = HB2.hb1869
  hypB L.ax-CCZ-K0-CK10-CCK'=K0-CK10-CCK'-CCX0-CS12-CCZ = HB2.hb1870
  hypB L.ax-CCZ-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0 = HB2.hb1871
  hypB L.ax-CCZ-K0-CK20=K0-CK20-CCZ = HB2.hb1872
  hypB L.ax-CCZ-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCX0 = HB2.hb1873
  hypB L.ax-CCZ-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCZ = HB2.hb1874
  hypB L.ax-CCZ-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB2.hb1875
  hypB L.ax-CCZ-K0-CK20-CK10=K0-CK20-CK10-CCX0 = HB3.hb1876
  hypB L.ax-CCZ-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCZ = HB3.hb1877
  hypB L.ax-CCZ-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB3.hb1878
  hypB L.ax-CCZ-K0-CK20-CCK'=K0-CK20-CCK'-CCX0-CS12-CCZ = HB3.hb1879
  hypB L.ax-CCZ-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0 = HB3.hb1880
  hypB L.ax-CCZ-K0-CCK'=K0-CCK'-CCZ = HB3.hb1881
  hypB L.ax-CCZ-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS12-CCZ = HB3.hb1882
  hypB L.ax-CCZ-CK10-CCK'=CK10-CCK'-CCZ = HB3.hb1883
  hypB L.ax-CCZ-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB3.hb1884
  hypB L.ax-CCZ-CK20-S0-CK10=CK20-S0-CK10-CCX0-CS12-CCZ = HB3.hb1885
  hypB L.ax-CCZ-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCX0 = HB3.hb1886
  hypB L.ax-CCZ-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCZ = HB3.hb1887
  hypB L.ax-CCZ-CK20-CK10=CK20-CK10-CCZ = HB3.hb1888
  hypB L.ax-CCZ-CK20-CK10-CCK'=CK20-CK10-CCK'-CCX0-CS12-CCZ = HB3.hb1889
  hypB L.ax-CCZ-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0 = HB3.hb1890
  hypB L.ax-CCZ-CK20-CCK'=CK20-CCK'-CCZ = HB3.hb1891
  hypB L.ax-CCZ-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0-CS12-CCZ = HB3.hb1892
  hypB L.ax-K0-S0-K0-S0-CK10=S0-K0-CK10-X0-CX10-CS01-CS01 = HB3.hb1893
  hypB L.ax-K0-S0-K0-S0-CK10-CCK'=S0-K0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12 = HB3.hb1894
  hypB L.ax-K0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ = HB3.hb1895
  hypB L.ax-K0-S0-K0-S0-CK20=S0-K0-CK20-X0-CX20-CS02-CS02 = HB3.hb1896
  hypB L.ax-K0-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI = HB3.hb1897
  hypB L.ax-K0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI = HB3.hb1898
  hypB L.ax-K0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI = HB3.hb1899
  hypB L.ax-K0-S0-K0-S0-CK20-CK10=S0-K0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02 = HB3.hb1900
  hypB L.ax-K0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ = HB3.hb1901
  hypB L.ax-K0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ = HB3.hb1902
  hypB L.ax-K0-S0-K0-S0-CK20-CCK'=S0-K0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12 = HB3.hb1903
  hypB L.ax-K0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ = HB3.hb1904
  hypB L.ax-K0-S0-K0-CK10=S0-K0-S0-CK10-X0-CX10-CS01-CS01-iI-iI-iI = HB3.hb1905
  hypB L.ax-K0-S0-K0-CK10-CCK'=S0-K0-S0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12-iI-iI-iI = HB3.hb1906
  hypB L.ax-K0-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ-iI-iI-iI = HB3.hb1907
  hypB L.ax-K0-S0-K0-CK20=S0-K0-S0-CK20-X0-CX20-CS02-CS02-iI-iI-iI = HB3.hb1908
  hypB L.ax-K0-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI = HB3.hb1909
  hypB L.ax-K0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI = HB3.hb1910
  hypB L.ax-K0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI = HB3.hb1911
  hypB L.ax-K0-S0-K0-CK20-CK10=S0-K0-S0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02-iI-iI-iI = HB3.hb1912
  hypB L.ax-K0-S0-K0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ-iI-iI-iI = HB3.hb1913
  hypB L.ax-K0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ-iI-iI-iI = HB3.hb1914
  hypB L.ax-K0-S0-K0-CK20-CCK'=S0-K0-S0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12-iI-iI-iI = HB3.hb1915
  hypB L.ax-K0-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ-iI-iI-iI = HB3.hb1916
  hypB L.ax-K0-S0-K0-CCK'=S0-K0-CCK'-CCK'-X0-CCX0-S0-S0-S0-CCZ = HB3.hb1917
  hypB L.ax-K0-S0-K0-CCK'-CCK'=S0-K0-CCK'-X0-CCX0-S0-S0-S0-CS12-CS12-CS12 = HB3.hb1918
  hypB L.ax-K0-K0-S0-CK10=S0-CK10-iI-iI-iI = HB3.hb1919
  hypB L.ax-K0-K0-S0-CK10-CCK'=S0-CK10-CCK'-iI-iI-iI = HB3.hb1920
  hypB L.ax-K0-K0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-iI-iI-iI = HB3.hb1921
  hypB L.ax-K0-K0-S0-CK20=S0-CK20-iI-iI-iI = HB3.hb1922
  hypB L.ax-K0-K0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-iI-iI-iI = HB3.hb1923
  hypB L.ax-K0-K0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-iI-iI-iI = HB3.hb1924
  hypB L.ax-K0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-iI-iI-iI = HB3.hb1925
  hypB L.ax-K0-K0-S0-CK20-CK10=S0-CK20-CK10-iI-iI-iI = HB3.hb1926
  hypB L.ax-K0-K0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-iI-iI-iI = HB3.hb1927
  hypB L.ax-K0-K0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-iI-iI-iI = HB3.hb1928
  hypB L.ax-K0-K0-S0-CK20-CCK'=S0-CK20-CCK'-iI-iI-iI = HB3.hb1929
  hypB L.ax-K0-K0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-iI-iI-iI = HB3.hb1930
  hypB L.ax-K0-K0-CK10=CK10-iI-iI-iI = HB3.hb1931
  hypB L.ax-K0-K0-CK10-CCK'=CK10-CCK'-iI-iI-iI = HB3.hb1932
  hypB L.ax-K0-K0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-iI-iI-iI = HB3.hb1933
  hypB L.ax-K0-K0-CK20=CK20-iI-iI-iI = HB3.hb1934
  hypB L.ax-K0-K0-CK20-S0-CK10=CK20-S0-CK10-iI-iI-iI = HB3.hb1935
  hypB L.ax-K0-K0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-iI-iI-iI = HB3.hb1936
  hypB L.ax-K0-K0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-iI-iI-iI = HB3.hb1937
  hypB L.ax-K0-K0-CK20-CK10=CK20-CK10-iI-iI-iI = HB3.hb1938
  hypB L.ax-K0-K0-CK20-CK10-CCK'=CK20-CK10-CCK'-iI-iI-iI = HB3.hb1939
  hypB L.ax-K0-K0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-iI-iI-iI = HB3.hb1940
  hypB L.ax-K0-K0-CK20-CCK'=CK20-CCK'-iI-iI-iI = HB3.hb1941
  hypB L.ax-K0-K0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-iI-iI-iI = HB3.hb1942
  hypB L.ax-K0-K0-CCK'=CCK'-iI-iI-iI = HB3.hb1943
  hypB L.ax-K0-K0-CCK'-CCK'=CCK'-CCK'-iI-iI-iI = HB3.hb1944
  hypB L.ax-X0-S0-K0-S0-CK10=S0-K0-S0-CK10-X0-CX10-CS01-CS01 = HB3.hb1945
  hypB L.ax-X0-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12 = HB3.hb1946
  hypB L.ax-X0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ = HB3.hb1947
  hypB L.ax-X0-S0-K0-S0-CK20=S0-K0-S0-CK20-X0-CX20-CS02-CS02 = HB3.hb1948
  hypB L.ax-X0-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI = HB3.hb1949
  hypB L.ax-X0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI = HB3.hb1950
  hypB L.ax-X0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI = HB3.hb1951
  hypB L.ax-X0-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02 = HB3.hb1952
  hypB L.ax-X0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ = HB3.hb1953
  hypB L.ax-X0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ = HB3.hb1954
  hypB L.ax-X0-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12 = HB3.hb1955
  hypB L.ax-X0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ = HB3.hb1956
  hypB L.ax-X0-S0-K0-CK10=S0-K0-CK10-X0-S0-S0-S1-S1-iI = HB3.hb1957
  hypB L.ax-X0-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI = HB3.hb1958
  hypB L.ax-X0-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI = HB3.hb1959
  hypB L.ax-X0-S0-K0-CK20=S0-K0-CK20-X0-S0-S0-S2-S2-iI = HB3.hb1960
  hypB L.ax-X0-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01 = HB3.hb1961
  hypB L.ax-X0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12 = HB3.hb1962
  hypB L.ax-X0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ = HB3.hb1963
  hypB L.ax-X0-S0-K0-CK20-CK10=S0-K0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI = HB3.hb1964
  hypB L.ax-X0-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI = HB3.hb1965
  hypB L.ax-X0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI = HB3.hb1966
  hypB L.ax-X0-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI = HB3.hb1967
  hypB L.ax-X0-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI = HB3.hb1968
  hypB L.ax-X0-S0-K0-CCK'=S0-K0-CCK'-X0-S0-S0-CS12-CS12-CS12-CCZ-iI = HB3.hb1969
  hypB L.ax-X0-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-X0-CCX0-S0-S0-CS12-CS12-CS12-iI = HB3.hb1970

  hypB L.ax-X0-S0-CK10-CCK'=S0-CK10-CCK'-X0-S0-S0-S1-S1-CS12-CS12-CS12-CCZ-iI-iI-iI = HB3.hb1971
  hypB L.ax-X0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-CS12-CS12-CS12-iI-iI-iI = HB3.hb1972
  hypB L.ax-X0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-X0-CX10-S2-S2-CS01-CS01-iI-iI = HB3.hb1973
  hypB L.ax-X0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CS12-iI-iI = HB3.hb1974
  hypB L.ax-X0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X0-CX10-CCX0-S2-S2-CS01-CS01-CCZ-iI-iI = HB3.hb1975
  hypB L.ax-X0-S0-CK20-CK10=S0-CK20-CK10-X0-S0-S0-S1-S1-S2-S2-iI-iI-iI = HB3.hb1976
  hypB L.ax-X0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-X0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI = HB3.hb1977
  hypB L.ax-X0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X0-CCX0-S0-S0-S1-S1-S2-S2-CS12-CS12-CS12-iI-iI-iI = HB3.hb1978
  hypB L.ax-X0-S0-CK20-CCK'=S0-CK20-CCK'-X0-S0-S0-S2-S2-CS12-CS12-CS12-CCZ-iI-iI-iI = HB3.hb1979
  hypB L.ax-X0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-X0-CCX0-S0-S0-S2-S2-CS12-CS12-CS12-iI-iI-iI = HB3.hb1980
  hypB L.ax-X0-K0-S0-CK10=K0-S0-CK10-CX10-S0-S0-CS01-CS01 = HB3.hb1981
  hypB L.ax-X0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ = HB3.hb1982
  hypB L.ax-X0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ = HB3.hb1983
  hypB L.ax-X0-K0-S0-CK20=K0-S0-CK20-CX20-S0-S0-CS02-CS02 = HB3.hb1984
  hypB L.ax-X0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = HB3.hb1985
  hypB L.ax-X0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12 = HB3.hb1986
  hypB L.ax-X0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ = HB3.hb1987
  hypB L.ax-X0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = HB3.hb1988
  hypB L.ax-X0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = HB3.hb1989
  hypB L.ax-X0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB3.hb1990
  hypB L.ax-X0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ = HB3.hb1991
  hypB L.ax-X0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ = HB3.hb1992
  hypB L.ax-X0-K0-CK10=K0-CK10-CX10-S0-S0-CS01-CS01 = HB3.hb1993
  hypB L.ax-X0-K0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CCZ = HB3.hb1994
  hypB L.ax-X0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-S0-S0-CS01-CS01-CS12-CCZ = HB3.hb1995
  hypB L.ax-X0-K0-CK20=K0-CK20-CX20-S0-S0-CS02-CS02 = HB3.hb1996
  hypB L.ax-X0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = HB3.hb1997
  hypB L.ax-X0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX10-CX20-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS12 = HB3.hb1998
  hypB L.ax-X0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS12-CCZ = HB3.hb1999
  hypB L.ax-X0-K0-CK20-CK10=K0-CK20-CK10-CX10-CX20-S0-S0-CS01-CS01-CS02-CS02 = HB3.hb2000
  hypB L.ax-X0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS12 = HB3.hb2001
  hypB L.ax-X0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX10-CX20-CCX0-S0-S0-CS01-CS01-CS02-CS02-CCZ = HB3.hb2002
  hypB L.ax-X0-K0-CK20-CCK'=K0-CK20-CCK'-CX20-CCX0-S0-S0-CS02-CS02-CCZ = HB3.hb2003
  hypB L.ax-X0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX20-S0-S0-CS02-CS02-CS12-CCZ = HB3.hb2004
  hypB L.ax-X0-K0-CCK'=K0-CCK'-CCX0-S0-S0-CS12 = HB3.hb2005
  hypB L.ax-X0-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-S0-S0-CCZ = HB3.hb2006
  hypB L.ax-X0-CK10-CCK'=CK10-CCK'-X0-CX10-CCX0-CS01-CS01-CS12 = HB3.hb2007
  hypB L.ax-X0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-X0-CX10-CCX0-CS01-CS01-CCZ = HB3.hb2008
  hypB L.ax-X0-CK20-S0-CK10=CK20-S0-CK10-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CCZ-iI-iI-iI = HB3.hb2009
  hypB L.ax-X0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-X0-CX20-S0-S0-S1-S1-S2-CS12-CS12-iI-iI-iI = HB3.hb2010
  hypB L.ax-X0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X0-CX20-CCX0-S0-S0-S1-S1-S2-CS12-CS12-CS12-iI-iI-iI = HB3.hb2011
  hypB L.ax-X0-CK20-CK10=CK20-CK10-X0-CX10-CX20-CS01-CS01-CS02-CS02 = HB3.hb2012
  hypB L.ax-X0-CK20-CK10-CCK'=CK20-CK10-CCK'-X0-CX10-CX20-CCX0-CS01-CS01-CS02-CS02-CCZ = HB3.hb2013
  hypB L.ax-X0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X0-CX10-CX20-CS01-CS01-CS02-CS02-CS12-CCZ = HB3.hb2014
  hypB L.ax-X0-CK20-CCK'=CK20-CCK'-X0-CX20-CCX0-CS02-CS02-CS12 = HB3.hb2015
  hypB L.ax-X0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-X0-CX20-CCX0-CS02-CS02-CCZ = HB3.hb2016
  hypB L.ax-X1-S0-K0=S0-K0-X1 = HB3.hb2017
  hypB L.ax-X1-S0-K0-S0-CK10=K0-S0-CK10-X1-X0-CX10-S1-S1-S1-CS01-CS01-iI = HB3.hb2018
  hypB L.ax-X1-S0-K0-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-X1-X0-CX10-CCX0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CCZ-iI = HB3.hb2019
  hypB L.ax-X1-S0-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI = HB3.hb2020
  hypB L.ax-X1-S0-K0-S0-CK20=S0-K0-S0-CK20-X1 = HB3.hb2021
  hypB L.ax-X1-S0-K0-S0-CK20-S0-CK10=S0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12 = HB3.hb2022
  hypB L.ax-X1-S0-K0-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CS12 = HB3.hb2023
  hypB L.ax-X1-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ = HB3.hb2024
  hypB L.ax-X1-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X1-X0-CX10-CX20-S1-S1-S1-CS01-CS01-CS02-CS02-iI = HB3.hb2025

  hypB L.ax-X1-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-iI = HB3.hb2026
  hypB L.ax-X1-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI = HB3.hb2027
  hypB L.ax-X1-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12 = HB3.hb2028
  hypB L.ax-X1-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = HB3.hb2029
  hypB L.ax-X1-S0-K0-CK10=S0-CK10-X1-S1-S1-S1 = HB3.hb2030
  hypB L.ax-X1-S0-K0-CK10-CCK'=S0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ = HB3.hb2031
  hypB L.ax-X1-S0-K0-CK10-CCK'-CCK'=CK20-S0-CK10-X1-CX20-S1-S1-S1-S2-CS02-CS02-CS02-CS12-CCZ = HB3.hb2032
  hypB L.ax-X1-S0-K0-CK20=S0-K0-CK20-X1 = HB3.hb2033
  hypB L.ax-X1-S0-K0-CK20-S0-CK10=K0-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-iI = HB3.hb2034
  hypB L.ax-X1-S0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI = HB3.hb2035
  hypB L.ax-X1-S0-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X1-X0-CX10-CCX0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CCZ-iI = HB3.hb2036
  hypB L.ax-X1-S0-K0-CK20-CK10=S0-CK20-CK10-X1-S1-S1-S1 = HB3.hb2037
  hypB L.ax-X1-S0-K0-CK20-CK10-CCK'=S0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ = HB3.hb2038
  hypB L.ax-X1-S0-K0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X1-S1-S1-S1-S2-CS02-CS02-CS12-CS12 = HB3.hb2039
  hypB L.ax-X1-S0-K0-CK20-CCK'=S0-K0-CCK'-X1-CS02-CS12-CS12-CS12-CCZ = HB3.hb2040

  hypB L.ax-X1-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = HB3.hb2041
  hypB L.ax-X1-S0-K0-CCK'=S0-K0-CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ = HB3.hb2042
  hypB L.ax-X1-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12 = HB3.hb2043
  hypB L.ax-X1-S0-CK10=S0-K0-CK10-X1-S1-S1-S1-iI = HB3.hb2044
  hypB L.ax-X1-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI = HB3.hb2045
  hypB L.ax-X1-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI = HB3.hb2046
  hypB L.ax-X1-S0-CK20=S0-CK20-X1 = HB3.hb2047
  hypB L.ax-X1-S0-CK20-S0-CK10=K0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-iI = HB3.hb2048
  hypB L.ax-X1-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-X1-X0-S0-S0-S1-S2-CS02-CS02-iI = HB3.hb2049
  hypB L.ax-X1-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ-iI = HB3.hb2050
  hypB L.ax-X1-S0-CK20-CK10=S0-K0-CK20-CK10-X1-S1-S1-S1-iI = HB3.hb2051
  hypB L.ax-X1-S0-CK20-CK10-CCK'=S0-K0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ-iI = HB3.hb2052
  hypB L.ax-X1-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI = HB3.hb2053
  hypB L.ax-X1-S0-CK20-CCK'=CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12 = HB3.hb2054
  hypB L.ax-X1-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = HB3.hb2055
  hypB L.ax-X1-K0-S0-CK10=S0-K0-S0-CK10-X1-CX10-S0-S0-S1-S1-S1-CS01-CS01 = HB3.hb2056
  hypB L.ax-X1-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS12-CS12-CS12 = HB3.hb2057
  hypB L.ax-X1-K0-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ = HB3.hb2058
  hypB L.ax-X1-K0-S0-CK20=K0-S0-CK20-X1 = HB3.hb2059
  hypB L.ax-X1-K0-S0-CK20-S0-CK10=CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12 = HB3.hb2060
  hypB L.ax-X1-K0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-X1-X0-S0-S0-S1-S2-CS02-CS02 = HB3.hb2061
  hypB L.ax-X1-K0-S0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ = HB3.hb2062
  hypB L.ax-X1-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X1-CX10-CX20-S0-S0-S1-S1-S1-CS01-CS01-CS02-CS02 = HB3.hb2063
  hypB L.ax-X1-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK10-CCK'-X1-CX10-CX20-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS12-CS12-CCZ = HB3.hb2064
  hypB L.ax-X1-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X1-CX10-CX20-CCX0-S0-S0-S1-S1-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = HB3.hb2065
  hypB L.ax-X1-K0-S0-CK20-CCK'=K0-CCK'-CCK'-X1-S0-S2-CS02-CS02-CS02-CS12-CS12 = HB3.hb2066
  hypB L.ax-X1-K0-S0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-X1-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = HB3.hb2067
  hypB L.ax-X1-K0-CK10=CK10-X1-S1-S1-S1 = HB3.hb2068
  hypB L.ax-X1-K0-CK10-CCK'=CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ = HB3.hb2069
  hypB L.ax-X1-K0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12 = HB3.hb2070
  hypB L.ax-X1-K0-CK20=K0-CK20-X1 = HB3.hb2071
  hypB L.ax-X1-K0-CK20-S0-CK10=S0-K0-S0-CK10-CCK'-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12 = HB3.hb2072
  hypB L.ax-X1-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-X1-CX10-CCX0-S0-S0-S1-S1-S1-S2-CS01-CS01-CS02-CS02-CS12-CS12-CS12 = HB3.hb2073
  hypB L.ax-X1-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X1-CX10-CX20-S0-S0-S1-S1-S1-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ = HB3.hb2074
  hypB L.ax-X1-K0-CK20-CK10=CK20-CK10-X1-S1-S1-S1 = HB3.hb2075
  hypB L.ax-X1-K0-CK20-CK10-CCK'=CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ = HB3.hb2076
  hypB L.ax-X1-K0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ = HB3.hb2077
  hypB L.ax-X1-K0-CK20-CCK'=K0-CCK'-X1-CS02-CS12-CS12-CS12-CCZ = HB3.hb2078
  hypB L.ax-X1-K0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = HB3.hb2079
  hypB L.ax-X1-K0-CCK'=K0-CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ = HB3.hb2080
  hypB L.ax-X1-K0-CCK'-CCK'=K0-S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12 = HB3.hb2081
  hypB L.ax-X1-CK10=K0-CK10-X1-S1-S1-S1-iI = HB3.hb2082
  hypB L.ax-X1-CK10-CCK'=K0-CK20-CK10-CCK'-X1-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI = HB3.hb2083
  hypB L.ax-X1-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS12-CS12-CS12-iI = HB3.hb2084
  hypB L.ax-X1-CK20-S0-CK10=S0-K0-CK10-CCK'-CCK'-X1-CX20-S1-S1-S1-S2-CS02-CS12-CS12-CS12-CCZ-iI = HB3.hb2085
  hypB L.ax-X1-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X1-X0-CX10-CX20-CCX0-S1-S1-S1-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI = HB3.hb2086
  hypB L.ax-X1-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X1-S1-S1-S1-S2-CS02-CS02-CS12-CS12-iI = HB3.hb2087
  hypB L.ax-X1-CK20-CK10=K0-CK20-CK10-X1-S1-S1-S1-iI = HB3.hb2088
  hypB L.ax-X1-CK20-CK10-CCK'=K0-CK10-CCK'-X1-S1-S1-S1-CS02-CS12-CS12-CS12-CCZ-iI = HB3.hb2089
  hypB L.ax-X1-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X1-X0-CX10-CX20-S1-S1-S1-S2-CS01-CS01-CS12-CCZ-iI = HB3.hb2090
  hypB L.ax-X1-CK20-CCK'=CCK'-X1-CS02-CS12-CS12-CS12-CCZ = HB3.hb2091
  hypB L.ax-X1-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-X1-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = HB3.hb2092
  hypB L.ax-X1-CCK'=CK20-CCK'-X1-S2-CS02-CS12-CS12-CS12-CCZ = HB3.hb2093
  hypB L.ax-X1-CCK'-CCK'=S0-CK20-CCK'-X1-S0-S0-S0-S2-CS02-CS12-CS12 = HB3.hb2094

  hypB L.ax-X2-S0-K0=S0-K0-X2 = HB3.hb2095
  hypB L.ax-X2-S0-K0-S0-CK10=S0-K0-S0-CK10-X2 = HB3.hb2096
  hypB L.ax-X2-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12 = HB3.hb2097
  hypB L.ax-X2-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = HB3.hb2098
  hypB L.ax-X2-S0-K0-S0-CK20=K0-S0-CK20-X2-X0-CX20-S2-S2-S2-CS02-CS02-iI = HB3.hb2099
  hypB L.ax-X2-S0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-X2-X0-CX20-CCX0-S0-S0-S1-S1-CS12-CS12-CCZ = HB3.hb2100
  hypB L.ax-X2-S0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CCK'-CCK'-X2-X0-CX20-S0-S1-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CCZ-iI = HB3.hb2101
  hypB L.ax-X2-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-X2-X0-CX10-CX20-S0-S1-S1-S2-S2-S2-CS01-CS01-CS02-CS02-CS12-CCZ-iI = HB3.hb2102
  hypB L.ax-X2-S0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-X2-X0-CX10-CX20-S2-S2-S2-CS01-CS01-CS02-CS02-iI = HB3.hb2103
  hypB L.ax-X2-S0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CCK'-X2-X0-CX10-CX20-CCX0-S2-S2-S2-CS01-CS01-CS01-CS02-CS02-CS12-CS12-CS12-iI = HB3.hb2104
  hypB L.ax-X2-S0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-X2-X0-CX10-CX20-CCX0-S0-S1-S1-CS01-CS01-CS12 = HB3.hb2105
  hypB L.ax-X2-S0-K0-S0-CK20-CCK'=K0-S0-CK20-CK10-CCK'-X2-X0-CX20-CCX0-S1-S1-S2-S2-S2-CS01-CS01-CS01-CS02-CS02-CS12-CS12-CCZ-iI = HB3.hb2106
  hypB L.ax-X2-S0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-X2-X0-CX20-CCX0-S0-S1-S1-CS01-CS01-CS01-CS12 = HB3.hb2107
  hypB L.ax-X2-S0-K0-CK10=S0-K0-CK10-X2 = HB3.hb2108
  hypB L.ax-X2-S0-K0-CK10-CCK'=S0-K0-CCK'-X2-CS01-CS12-CS12-CS12-CCZ = HB3.hb2109
  hypB L.ax-X2-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = HB3.hb2110
  hypB L.ax-X2-S0-K0-CK20=S0-CK20-X2-S2-S2-S2 = HB3.hb2111
  hypB L.ax-X2-S0-K0-CK20-S0-CK10=S0-CK20-S0-CK10-X2-S2-S2-S2 = HB3.hb2112
  hypB L.ax-X2-S0-K0-CK20-S0-CK10-CCK'=S0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12 = HB3.hb2113
  hypB L.ax-X2-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12 = HB3.hb2114
  hypB L.ax-X2-S0-K0-CK20-CK10=S0-CK20-CK10-X2-S2-S2-S2 = HB3.hb2115
  hypB L.ax-X2-S0-K0-CK20-CK10-CCK'=S0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ = HB3.hb2116
  hypB L.ax-X2-S0-K0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = HB3.hb2117
  hypB L.ax-X2-S0-K0-CK20-CCK'=S0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ = HB3.hb2118
  hypB L.ax-X2-S0-K0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12 = HB3.hb2119
  hypB L.ax-X2-S0-K0-CCK'=S0-K0-CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ = HB3.hb2120
  hypB L.ax-X2-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12 = HB3.hb2121
  hypB L.ax-X2-S0-CK10=S0-CK10-X2 = HB3.hb2122
  hypB L.ax-X2-S0-CK10-CCK'=CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12 = HB3.hb2123
  hypB L.ax-X2-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = HB3.hb2124
  hypB L.ax-X2-S0-CK20=S0-K0-CK20-X2-S2-S2-S2-iI = HB3.hb2125
  hypB L.ax-X2-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-X2-S2-S2-S2-iI = HB3.hb2126
  hypB L.ax-X2-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12-iI = HB3.hb2127
  hypB L.ax-X2-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12-iI = HB3.hb2128
  hypB L.ax-X2-S0-CK20-CK10=S0-K0-CK20-CK10-X2-S2-S2-S2-iI = HB3.hb2129
  hypB L.ax-X2-S0-CK20-CK10-CCK'=S0-K0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI = HB3.hb2130
  hypB L.ax-X2-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ-iI = HB3.hb2131
  hypB L.ax-X2-S0-CK20-CCK'=S0-K0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI = HB3.hb2132
  hypB L.ax-X2-S0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12-iI = HB3.hb2133
  hypB L.ax-X2-K0-S0-CK10=K0-S0-CK10-X2 = HB3.hb2134
  hypB L.ax-X2-K0-S0-CK10-CCK'=K0-CCK'-CCK'-X2-S0-S1-CS01-CS01-CS01-CS12-CS12 = HB3.hb2135
  hypB L.ax-X2-K0-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = HB3.hb2136
  hypB L.ax-X2-K0-S0-CK20=S0-K0-S0-CK20-X2-CX20-S0-S0-S2-S2-S2-CS02-CS02 = HB3.hb2137
  hypB L.ax-X2-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-X2-CX10-CX20-CCX0-S0-S0-S2-S2-CS01-CS01-CS12-CS12-CCZ = HB3.hb2138
  hypB L.ax-X2-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CCK'-CCK'-X2-CX10-CX20-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CCZ = HB3.hb2139
  hypB L.ax-X2-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-X2-CX20-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS02-CS02-CS12-CS12-CCZ = HB3.hb2140
  hypB L.ax-X2-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-X2-CX10-CX20-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02 = HB3.hb2141
  hypB L.ax-X2-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CCK'-X2-CX10-CX20-CCX0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CCZ = HB4.hb2142
  hypB L.ax-X2-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X2-CX10-CX20-S0-S1-S1-S2-S2-CS01-CS01-CS12-CCZ = HB4.hb2143
  hypB L.ax-X2-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CK10-CCK'-X2-CX20-CCX0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CS12 = HB4.hb2144
  hypB L.ax-X2-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X2-CX20-S0-S1-S2-S2-CS01 = HB4.hb2145
  hypB L.ax-X2-K0-CK10=K0-CK10-X2 = HB4.hb2146
  hypB L.ax-X2-K0-CK10-CCK'=K0-CCK'-X2-CS01-CS12-CS12-CS12-CCZ = HB4.hb2147
  hypB L.ax-X2-K0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = HB4.hb2148
  hypB L.ax-X2-K0-CK20=CK20-X2-S2-S2-S2 = HB4.hb2149
  hypB L.ax-X2-K0-CK20-S0-CK10=CK20-S0-CK10-X2-S2-S2-S2 = HB4.hb2150
  hypB L.ax-X2-K0-CK20-S0-CK10-CCK'=CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12 = HB4.hb2151
  hypB L.ax-X2-K0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12 = HB4.hb2152
  hypB L.ax-X2-K0-CK20-CK10=CK20-CK10-X2-S2-S2-S2 = HB4.hb2153
  hypB L.ax-X2-K0-CK20-CK10-CCK'=CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ = HB4.hb2154
  hypB L.ax-X2-K0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ = HB4.hb2155
  hypB L.ax-X2-K0-CK20-CCK'=CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ = HB4.hb2156
  hypB L.ax-X2-K0-CK20-CCK'-CCK'=CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12 = HB4.hb2157
  hypB L.ax-X2-K0-CCK'=K0-CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ = HB4.hb2158
  hypB L.ax-X2-K0-CCK'-CCK'=K0-S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12 = HB4.hb2159
  hypB L.ax-X2-CK10-CCK'=CCK'-X2-CS01-CS12-CS12-CS12-CCZ = HB4.hb2160
  hypB L.ax-X2-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = HB4.hb2161
  hypB L.ax-X2-CK20=K0-CK20-X2-S2-S2-S2-iI = HB4.hb2162
  hypB L.ax-X2-CK20-S0-CK10=K0-CK20-S0-CK10-X2-S2-S2-S2-iI = HB4.hb2163
  hypB L.ax-X2-CK20-S0-CK10-CCK'=K0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12-iI = HB4.hb2164
  hypB L.ax-X2-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12-iI = HB4.hb2165
  hypB L.ax-X2-CK20-CK10=K0-CK20-CK10-X2-S2-S2-S2-iI = HB4.hb2166
  hypB L.ax-X2-CK20-CK10-CCK'=K0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI = HB4.hb2167
  hypB L.ax-X2-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ-iI = HB4.hb2168
  hypB L.ax-X2-CK20-CCK'=K0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI = HB4.hb2169
  hypB L.ax-X2-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12-iI = HB4.hb2170
  hypB L.ax-X2-CCK'=CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ = HB4.hb2171
  hypB L.ax-X2-CCK'-CCK'=S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12 = HB4.hb2172
  
  hypB L.ax-CX10-S0-K0-S0-CK10=S0-K0-S0-CK10-CS01-CS01 = HB4.hb2173
  hypB L.ax-CX10-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-CS01-CS01-CS12 = HB4.hb2174
  hypB L.ax-CX10-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-CS01-CS01-CCZ = HB4.hb2175
  hypB L.ax-CX10-S0-K0-S0-CK20=S0-K0-S0-CK20-CX10-CCX0-CCZ = HB4.hb2176
  hypB L.ax-CX10-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ = HB4.hb2177
  hypB L.ax-CX10-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12 = HB4.hb2178
  hypB L.ax-CX10-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S1-CS01-CS01 = HB4.hb2179
  hypB L.ax-CX10-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS01-CS01-CCZ = HB4.hb2180
  hypB L.ax-CX10-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS01-CS01 = HB4.hb2181
  hypB L.ax-CX10-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12 = HB4.hb2182
  hypB L.ax-CX10-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX10-CS12-CCZ = HB4.hb2183
  hypB L.ax-CX10-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX10 = HB4.hb2184
  hypB L.ax-CX10-S0-K0-CK10=S0-K0-CK10-CX10-S1-S1-S1-CS01-CS01 = HB4.hb2185
  hypB L.ax-CX10-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CS12-CS12-CCZ = HB4.hb2186
  hypB L.ax-CX10-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12-CS12-CS12 = HB4.hb2187
  hypB L.ax-CX10-S0-K0-CK20=S0-K0-CK20-CX10-S1-CS01-CS01-CS12-CS12 = HB4.hb2188
  hypB L.ax-CX10-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS01-CS01-CS12-CS12 = HB4.hb2189
  hypB L.ax-CX10-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCX0-CS01-CS01-CS12-CS12-CS12 = HB4.hb2190
  hypB L.ax-CX10-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12-CS12-CCZ = HB4.hb2191
  hypB L.ax-CX10-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CX10-S1-S1-S1-CS01-CS01-CS12-CS12 = HB4.hb2192
  hypB L.ax-CX10-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CCZ = HB4.hb2193
  hypB L.ax-CX10-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12 = HB4.hb2194
  hypB L.ax-CX10-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX10-S1-CS01-CS01-CS12-CCZ = HB4.hb2195
  hypB L.ax-CX10-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12 = HB4.hb2196
  hypB L.ax-CX10-S0-K0-CCK'=S0-K0-CCK'-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ = HB4.hb2197
  hypB L.ax-CX10-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12 = HB4.hb2198
  hypB L.ax-CX10-S0-CK10-CCK'=S0-CK10-CCK'-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ = HB4.hb2199
  hypB L.ax-CX10-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12 = HB4.hb2200
  hypB L.ax-CX10-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S1-S1-CS01-CS01-CS12-CS12 = HB4.hb2201
  hypB L.ax-CX10-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-S1-S1-CS01-CS01-CS12-CS12-CS12 = HB4.hb2202
  hypB L.ax-CX10-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCX0-S1-S1-CS01-CS01-CS12-CS12-CCZ = HB4.hb2203
  hypB L.ax-CX10-S0-CK20-CK10=S0-CK20-CK10-CX10-S1-CS01-CS01-CS12-CS12 = HB4.hb2204
  hypB L.ax-CX10-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX10-S1-CS01-CS01-CS12-CCZ = HB4.hb2205
  hypB L.ax-CX10-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12 = HB4.hb2206
  hypB L.ax-CX10-S0-CK20-CCK'=S0-CK20-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CCZ = HB4.hb2207
  hypB L.ax-CX10-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12 = HB4.hb2208
  hypB L.ax-CX10-K0-S0-CK10=K0-S0-CK10-CX10 = HB4.hb2209
  hypB L.ax-CX10-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-CCZ = HB4.hb2210
  hypB L.ax-CX10-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CS12-CCZ = HB4.hb2211
  hypB L.ax-CX10-K0-S0-CK20=K0-S0-CK20-CCX0-CS01-CS01-CCZ = HB4.hb2212
  hypB L.ax-CX10-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX10-CS12-CCZ = HB4.hb2213
  hypB L.ax-CX10-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10 = HB4.hb2214
  hypB L.ax-CX10-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CCZ = HB4.hb2215
  hypB L.ax-CX10-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX10-CCX0-CCZ = HB4.hb2216
  hypB L.ax-CX10-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CS12-CCZ = HB4.hb2217
  hypB L.ax-CX10-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10 = HB4.hb2218
  hypB L.ax-CX10-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CS01-CS01 = HB4.hb2219
  hypB L.ax-CX10-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12 = HB4.hb2220
  hypB L.ax-CX10-K0-CK10=K0-CK10-CX10 = HB4.hb2221
  hypB L.ax-CX10-K0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-CCZ = HB4.hb2222
  hypB L.ax-CX10-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-CS12-CCZ = HB4.hb2223
  hypB L.ax-CX10-K0-CK20=K0-CK20-CCX0-CS01-CS01-CCZ = HB4.hb2224
  hypB L.ax-CX10-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CS12-CCZ = HB4.hb2225
  hypB L.ax-CX10-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX10 = HB4.hb2226
  hypB L.ax-CX10-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CCZ = HB4.hb2227
  hypB L.ax-CX10-K0-CK20-CK10=K0-CK20-CK10-CX10-CCX0-CCZ = HB4.hb2228
  hypB L.ax-CX10-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX10-CS12-CCZ = HB4.hb2229
  hypB L.ax-CX10-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX10 = HB4.hb2230
  hypB L.ax-CX10-K0-CK20-CCK'=K0-CK20-CCK'-CS01-CS01 = HB4.hb2231
  hypB L.ax-CX10-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12 = HB4.hb2232
  hypB L.ax-CX10-K0-CCK'=K0-CCK'-CCX0-CS01-CS01-CS12 = HB4.hb2233
  hypB L.ax-CX10-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS01-CS01-CCZ = HB4.hb2234
  hypB L.ax-CX10-CK10-CCK'=CK10-CCK'-CCX0-CS01-CS01-CS12 = HB4.hb2235
  hypB L.ax-CX10-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0-CS01-CS01-CCZ = HB4.hb2236
  hypB L.ax-CX10-CK20-S0-CK10=CK20-S0-CK10-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ = HB4.hb2237
  hypB L.ax-CX10-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12 = HB4.hb2238
  hypB L.ax-CX10-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-S1-CS01-CS01 = HB4.hb2239
  hypB L.ax-CX10-CK20-CK10=CK20-CK10-CCX0-CS01-CS01-CCZ = HB4.hb2240
  hypB L.ax-CX10-CK20-CK10-CCK'=CK20-CK10-CCK'-CS01-CS01 = HB4.hb2241
  hypB L.ax-CX10-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12 = HB4.hb2242
  hypB L.ax-CX10-CK20-CCK'=CK20-CCK'-CX10-CS12-CCZ = HB4.hb2243
  hypB L.ax-CX10-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX10 = HB4.hb2244
  
  hypB L.ax-CX12-S0-K0=S0-K0-CX12 = HB4.hb2245
  hypB L.ax-CX12-S0-K0-S0-CK10=S0-K0-S0-CK10-CX12 = HB4.hb2246
  hypB L.ax-CX12-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12 = HB4.hb2247
  hypB L.ax-CX12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = HB4.hb2248
  hypB L.ax-CX12-S0-K0-S0-CK20=S0-K0-S0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = HB4.hb2249
  hypB L.ax-CX12-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB4.hb2250
  hypB L.ax-CX12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = HB4.hb2251
  hypB L.ax-CX12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = HB4.hb2252
  hypB L.ax-CX12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CX12-CS12-CS12-CS12 = HB4.hb2253
  hypB L.ax-CX12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2254
  hypB L.ax-CX12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = HB4.hb2255
  hypB L.ax-CX12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2256
  hypB L.ax-CX12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = HB4.hb2257
  hypB L.ax-CX12-S0-K0-CK10=S0-K0-CK10-CX12 = HB4.hb2258
  hypB L.ax-CX12-S0-K0-CK10-CCK'=S0-K0-CCK'-CX12-CS01-CS12-CS12-CS12-CCZ = HB4.hb2259
  hypB L.ax-CX12-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = HB4.hb2260
  hypB L.ax-CX12-S0-K0-CK20=S0-K0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = HB4.hb2261
  hypB L.ax-CX12-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB4.hb2262
  hypB L.ax-CX12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = HB4.hb2263
  hypB L.ax-CX12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = HB4.hb2264
  hypB L.ax-CX12-S0-K0-CK20-CK10=S0-K0-CK20-CX12-CS12-CS12-CS12 = HB4.hb2265
  hypB L.ax-CX12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2266
  hypB L.ax-CX12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = HB4.hb2267
  hypB L.ax-CX12-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2268
  hypB L.ax-CX12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = HB4.hb2269
  hypB L.ax-CX12-S0-K0-CCK'=S0-K0-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ = HB4.hb2270
  hypB L.ax-CX12-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12 = HB4.hb2271
  hypB L.ax-CX12-S0-CK10=S0-CK10-CX12 = HB4.hb2272
  hypB L.ax-CX12-S0-CK10-CCK'=CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12 = HB4.hb2273
  hypB L.ax-CX12-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = HB4.hb2274
  hypB L.ax-CX12-S0-CK20=S0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = HB4.hb2275
  hypB L.ax-CX12-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB4.hb2276
  hypB L.ax-CX12-S0-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = HB4.hb2277
  hypB L.ax-CX12-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = HB4.hb2278
  hypB L.ax-CX12-S0-CK20-CK10=S0-CK20-CX12-CS12-CS12-CS12 = HB4.hb2279
  hypB L.ax-CX12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2280
  hypB L.ax-CX12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = HB4.hb2281
  hypB L.ax-CX12-S0-CK20-CCK'=S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2282
  hypB L.ax-CX12-S0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = HB4.hb2283
  hypB L.ax-CX12-K0-S0-CK10=K0-S0-CK10-CX12 = HB4.hb2284
  hypB L.ax-CX12-K0-S0-CK10-CCK'=K0-CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12 = HB4.hb2285
  hypB L.ax-CX12-K0-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12 = HB4.hb2286
  hypB L.ax-CX12-K0-S0-CK20=K0-S0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = HB4.hb2287
  hypB L.ax-CX12-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB4.hb2288
  hypB L.ax-CX12-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = HB4.hb2289
  hypB L.ax-CX12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = HB4.hb2290
  hypB L.ax-CX12-K0-S0-CK20-CK10=K0-S0-CK20-CX12-CS12-CS12-CS12 = HB4.hb2291
  hypB L.ax-CX12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2292
  hypB L.ax-CX12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = HB4.hb2293
  hypB L.ax-CX12-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2294
  hypB L.ax-CX12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = HB4.hb2295
  hypB L.ax-CX12-K0-CK10=K0-CK10-CX12 = HB4.hb2296
  hypB L.ax-CX12-K0-CK10-CCK'=K0-CCK'-CX12-CS01-CS12-CS12-CS12-CCZ = HB4.hb2297
  hypB L.ax-CX12-K0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = HB4.hb2298
  hypB L.ax-CX12-K0-CK20=K0-CK20-CK10-CX12-S1-CS12-CS12-CS12 = HB4.hb2299
  hypB L.ax-CX12-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB4.hb2300
  hypB L.ax-CX12-K0-CK20-S0-CK10-CCK'=K0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = HB4.hb2301
  hypB L.ax-CX12-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = HB4.hb2302
  hypB L.ax-CX12-K0-CK20-CK10=K0-CK20-CX12-CS12-CS12-CS12 = HB4.hb2303
  hypB L.ax-CX12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2304
  hypB L.ax-CX12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = HB4.hb2305
  hypB L.ax-CX12-K0-CK20-CCK'=K0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2306
  hypB L.ax-CX12-K0-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = HB4.hb2307
  hypB L.ax-CX12-K0-CCK'=K0-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ = HB4.hb2308
  hypB L.ax-CX12-K0-CCK'-CCK'=K0-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12 = HB4.hb2309
  hypB L.ax-CX12-CK10-CCK'=CCK'-CX12-CS01-CS12-CS12-CS12-CCZ = HB4.hb2310
  hypB L.ax-CX12-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ = HB4.hb2311
  hypB L.ax-CX12-CK20=CK20-CK10-CX12-S1-CS12-CS12-CS12 = HB4.hb2312
  hypB L.ax-CX12-CK20-S0-CK10=CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB4.hb2313
  hypB L.ax-CX12-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12 = HB4.hb2314
  hypB L.ax-CX12-CK20-S0-CK10-CCK'-CCK'=CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01 = HB4.hb2315
  hypB L.ax-CX12-CK20-CK10=CK20-CX12-CS12-CS12-CS12 = HB4.hb2316
  hypB L.ax-CX12-CK20-CK10-CCK'=CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2317
  hypB L.ax-CX12-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12 = HB4.hb2318
  hypB L.ax-CX12-CK20-CCK'=CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ = HB4.hb2319
  hypB L.ax-CX12-CK20-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ = HB4.hb2320
  hypB L.ax-CX12-CCK'=CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ = HB4.hb2321
  hypB L.ax-CX12-CCK'-CCK'=S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12 = HB4.hb2322
  
  hypB L.ax-CX20-S0-K0-S0-CK10=S0-K0-S0-CK10-CX20-CCX0-CCZ = HB4.hb2323
  hypB L.ax-CX20-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX20-CS12-CCZ = HB4.hb2324
  hypB L.ax-CX20-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX20 = HB4.hb2325
  hypB L.ax-CX20-S0-K0-S0-CK20=S0-K0-S0-CK20-CS02-CS02 = HB4.hb2326
  hypB L.ax-CX20-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCX0-CS02-CS02-CCZ = HB4.hb2327
  hypB L.ax-CX20-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CS02-CS02 = HB4.hb2328
  hypB L.ax-CX20-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2329
  hypB L.ax-CX20-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS02-CS02-CCZ = HB4.hb2330
  hypB L.ax-CX20-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS02-CS02 = HB4.hb2331
  hypB L.ax-CX20-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2332
  hypB L.ax-CX20-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2333
  hypB L.ax-CX20-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-CS02-CS02-CCZ = HB4.hb2334
  hypB L.ax-CX20-S0-K0-CK10=S0-K0-CK10-CX20-S2-CS02-CS02-CS12-CS12 = HB4.hb2335
  hypB L.ax-CX20-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX20-S2-CS02-CS02-CS12-CCZ = HB4.hb2336
  hypB L.ax-CX20-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12 = HB4.hb2337
  hypB L.ax-CX20-S0-K0-CK20=S0-K0-CK20-CX20-S2-S2-S2-CS02-CS02 = HB4.hb2338
  hypB L.ax-CX20-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CX20-CCX0-S2-S2-CCZ = HB4.hb2339
  hypB L.ax-CX20-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX20-S2-S2-CS12-CCZ = HB4.hb2340
  hypB L.ax-CX20-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX20-S2-S2 = HB4.hb2341
  hypB L.ax-CX20-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12 = HB4.hb2342
  hypB L.ax-CX20-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ = HB4.hb2343
  hypB L.ax-CX20-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12 = HB4.hb2344
  hypB L.ax-CX20-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CS12-CS12-CCZ = HB4.hb2345
  hypB L.ax-CX20-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12-CS12-CS12 = HB4.hb2346
  hypB L.ax-CX20-S0-K0-CCK'=S0-K0-CCK'-CX20-S2-CS02-CS02-CS12-CS12-CS12-CCZ = HB4.hb2347
  hypB L.ax-CX20-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12-CS12-CS12 = HB4.hb2348
  hypB L.ax-CX20-S0-CK10-CCK'=S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ = HB4.hb2349
  hypB L.ax-CX20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12 = HB4.hb2350
  hypB L.ax-CX20-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CX20-CCX0-CCZ = HB4.hb2351
  hypB L.ax-CX20-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX20-CS12-CCZ = HB4.hb2352
  hypB L.ax-CX20-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX20 = HB4.hb2353
  hypB L.ax-CX20-S0-CK20-CK10=S0-CK20-CK10-CX20-S2-CS02-CS02-CS12-CS12 = HB4.hb2354
  hypB L.ax-CX20-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX20-S2-CS02-CS02-CS12-CCZ = HB4.hb2355
  hypB L.ax-CX20-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12 = HB4.hb2356
  hypB L.ax-CX20-S0-CK20-CCK'=S0-CK20-CCK'-CX20-S2-CS02-CS02-CS12-CS12-CS12-CCZ = HB4.hb2357
  hypB L.ax-CX20-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12-CS12-CS12 = HB4.hb2358
  hypB L.ax-CX20-K0-S0-CK10=K0-S0-CK10-CCX0-CS02-CS02-CCZ = HB4.hb2359
  hypB L.ax-CX20-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CS02-CS02 = HB4.hb2360
  hypB L.ax-CX20-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2361
  hypB L.ax-CX20-K0-S0-CK20=K0-S0-CK20-CX20 = HB4.hb2362
  hypB L.ax-CX20-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12 = HB4.hb2363
  hypB L.ax-CX20-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ = HB4.hb2364
  hypB L.ax-CX20-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12 = HB4.hb2365
  hypB L.ax-CX20-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX20-CCX0-CCZ = HB4.hb2366
  hypB L.ax-CX20-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-CS12-CCZ = HB4.hb2367
  hypB L.ax-CX20-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX20 = HB4.hb2368
  hypB L.ax-CX20-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-CCZ = HB4.hb2369
  hypB L.ax-CX20-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CS12-CCZ = HB4.hb2370
  hypB L.ax-CX20-K0-CK10=K0-CK10-CCX0-CS02-CS02-CCZ = HB4.hb2371
  hypB L.ax-CX20-K0-CK10-CCK'=K0-CK10-CCK'-CS02-CS02 = HB4.hb2372
  hypB L.ax-CX20-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2373
  hypB L.ax-CX20-K0-CK20=K0-CK20-CX20 = HB4.hb2374
  hypB L.ax-CX20-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12 = HB4.hb2375
  hypB L.ax-CX20-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ = HB4.hb2376
  hypB L.ax-CX20-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12 = HB4.hb2377
  hypB L.ax-CX20-K0-CK20-CK10=K0-CK20-CK10-CX20-CCX0-CCZ = HB4.hb2378
  hypB L.ax-CX20-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX20-CS12-CCZ = HB4.hb2379
  hypB L.ax-CX20-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX20 = HB4.hb2380
  hypB L.ax-CX20-K0-CK20-CCK'=K0-CK20-CCK'-CX20-CCX0-CCZ = HB4.hb2381
  hypB L.ax-CX20-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX20-CS12-CCZ = HB4.hb2382
  hypB L.ax-CX20-K0-CCK'=K0-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2383
  hypB L.ax-CX20-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS02-CS02-CCZ = HB4.hb2384
  hypB L.ax-CX20-CK10-CCK'=CK10-CCK'-CX20-CS12-CCZ = HB4.hb2385
  hypB L.ax-CX20-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX20 = HB4.hb2386
  hypB L.ax-CX20-CK20-S0-CK10=CK20-S0-CK10-CCX0-CS02-CS02-CCZ = HB4.hb2387
  hypB L.ax-CX20-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CS02-CS02 = HB4.hb2388
  hypB L.ax-CX20-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2389
  hypB L.ax-CX20-CK20-CK10=CK20-CK10-CCX0-CS02-CS02-CCZ = HB4.hb2390
  hypB L.ax-CX20-CK20-CK10-CCK'=CK20-CK10-CCK'-CS02-CS02 = HB4.hb2391
  hypB L.ax-CX20-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2392
  hypB L.ax-CX20-CK20-CCK'=CK20-CCK'-CCX0-CS02-CS02-CS12 = HB4.hb2393
  hypB L.ax-CX20-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0-CS02-CS02-CCZ = HB4.hb2394
  hypB L.ax-CX21-S0-K0=S0-K0-CX21 = HB4.hb2395
  hypB L.ax-CX21-S0-K0-S0-CK10=S0-K0-S0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = HB4.hb2396
  hypB L.ax-CX21-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB4.hb2397
  hypB L.ax-CX21-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12 = HB4.hb2398
  hypB L.ax-CX21-S0-K0-S0-CK20=S0-K0-S0-CK20-CX21 = HB4.hb2399
  hypB L.ax-CX21-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = HB4.hb2400
  hypB L.ax-CX21-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB4.hb2401
  hypB L.ax-CX21-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = HB4.hb2402
  hypB L.ax-CX21-S0-K0-S0-CK20-CK10=S0-K0-S0-CK10-CX21-CS12-CS12-CS12 = HB4.hb2403
  hypB L.ax-CX21-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB4.hb2404
  hypB L.ax-CX21-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ = HB4.hb2405
  hypB L.ax-CX21-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12 = HB4.hb2406
  hypB L.ax-CX21-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = HB4.hb2407
  hypB L.ax-CX21-S0-K0-CK10=S0-K0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = HB4.hb2408
  hypB L.ax-CX21-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB4.hb2409
  hypB L.ax-CX21-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = HB4.hb2410
  hypB L.ax-CX21-S0-K0-CK20=S0-K0-CK20-CX21 = HB5.hb2411
  hypB L.ax-CX21-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ = HB5.hb2412
  hypB L.ax-CX21-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2413
  hypB L.ax-CX21-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12 = HB5.hb2414
  hypB L.ax-CX21-S0-K0-CK20-CK10=S0-K0-CK10-CX21-CS12-CS12-CS12 = HB5.hb2415
  hypB L.ax-CX21-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2416
  hypB L.ax-CX21-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = HB5.hb2417
  hypB L.ax-CX21-S0-K0-CK20-CCK'=S0-K0-CCK'-CX21-CS02-CS12-CS12-CS12-CCZ = HB5.hb2418
  hypB L.ax-CX21-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = HB5.hb2419
  hypB L.ax-CX21-S0-K0-CCK'=S0-K0-CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ = HB5.hb2420
  hypB L.ax-CX21-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12 = HB5.hb2421
  hypB L.ax-CX21-S0-CK10=S0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = HB5.hb2422
  hypB L.ax-CX21-S0-CK10-CCK'=S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2423
  hypB L.ax-CX21-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12 = HB5.hb2424
  hypB L.ax-CX21-S0-CK20=S0-CK20-CX21 = HB5.hb2425
  hypB L.ax-CX21-S0-CK20-S0-CK10=CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = HB5.hb2426
  hypB L.ax-CX21-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2427
  hypB L.ax-CX21-S0-CK20-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = HB5.hb2428
  hypB L.ax-CX21-S0-CK20-CK10=S0-CK10-CX21-CS12-CS12-CS12 = HB5.hb2429
  hypB L.ax-CX21-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2430
  hypB L.ax-CX21-S0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ = HB5.hb2431
  hypB L.ax-CX21-S0-CK20-CCK'=CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12 = HB5.hb2432
  hypB L.ax-CX21-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = HB5.hb2433
  hypB L.ax-CX21-K0-S0-CK10=K0-S0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = HB5.hb2434
  hypB L.ax-CX21-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2435
  hypB L.ax-CX21-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12 = HB5.hb2436
  hypB L.ax-CX21-K0-S0-CK20=K0-S0-CK20-CX21 = HB5.hb2437
  hypB L.ax-CX21-K0-S0-CK20-S0-CK10=K0-CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = HB5.hb2438
  hypB L.ax-CX21-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2439
  hypB L.ax-CX21-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = HB5.hb2440
  hypB L.ax-CX21-K0-S0-CK20-CK10=K0-S0-CK10-CX21-CS12-CS12-CS12 = HB5.hb2441
  hypB L.ax-CX21-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2442
  hypB L.ax-CX21-K0-S0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ = HB5.hb2443
  hypB L.ax-CX21-K0-S0-CK20-CCK'=K0-CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12 = HB5.hb2444
  hypB L.ax-CX21-K0-S0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12 = HB5.hb2445
  hypB L.ax-CX21-K0-CK10=K0-CK20-CK10-CX21-S2-CS12-CS12-CS12 = HB5.hb2446
  hypB L.ax-CX21-K0-CK10-CCK'=K0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2447
  hypB L.ax-CX21-K0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = HB5.hb2448
  hypB L.ax-CX21-K0-CK20=K0-CK20-CX21 = HB5.hb2449
  hypB L.ax-CX21-K0-CK20-S0-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ = HB5.hb2450
  hypB L.ax-CX21-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2451
  hypB L.ax-CX21-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12 = HB5.hb2452
  hypB L.ax-CX21-K0-CK20-CK10=K0-CK10-CX21-CS12-CS12-CS12 = HB5.hb2453
  hypB L.ax-CX21-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2454
  hypB L.ax-CX21-K0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = HB5.hb2455
  hypB L.ax-CX21-K0-CK20-CCK'=K0-CCK'-CX21-CS02-CS12-CS12-CS12-CCZ = HB5.hb2456
  hypB L.ax-CX21-K0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = HB5.hb2457
  hypB L.ax-CX21-K0-CCK'=K0-CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ = HB5.hb2458
  hypB L.ax-CX21-K0-CCK'-CCK'=K0-S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12 = HB5.hb2459
  hypB L.ax-CX21-CK10=CK20-CK10-CX21-S2-CS12-CS12-CS12 = HB5.hb2460
  hypB L.ax-CX21-CK10-CCK'=CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2461
  hypB L.ax-CX21-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ = HB5.hb2462
  hypB L.ax-CX21-CK20-S0-CK10=S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ = HB5.hb2463
  hypB L.ax-CX21-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2464
  hypB L.ax-CX21-CK20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12 = HB5.hb2465
  hypB L.ax-CX21-CK20-CK10=CK10-CX21-CS12-CS12-CS12 = HB5.hb2466
  hypB L.ax-CX21-CK20-CK10-CCK'=CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ = HB5.hb2467
  hypB L.ax-CX21-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = HB5.hb2468
  hypB L.ax-CX21-CK20-CCK'=CCK'-CX21-CS02-CS12-CS12-CS12-CCZ = HB5.hb2469
  hypB L.ax-CX21-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ = HB5.hb2470
  hypB L.ax-CX21-CCK'=CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ = HB5.hb2471
  hypB L.ax-CX21-CCK'-CCK'=S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12 = HB5.hb2472
  hypB L.ax-CCX0-S0-K0-S0-CK10=S0-K0-S0-CK10-CCZ = HB5.hb2473
  hypB L.ax-CCX0-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-CS12-CCZ = HB5.hb2474
  hypB L.ax-CCX0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0 = HB5.hb2475
  hypB L.ax-CCX0-S0-K0-S0-CK20=S0-K0-S0-CK20-CCZ = HB5.hb2476
  hypB L.ax-CCX0-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCX0 = HB5.hb2477
  hypB L.ax-CCX0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCZ = HB5.hb2478
  hypB L.ax-CCX0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB5.hb2479
  hypB L.ax-CCX0-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0 = HB5.hb2480
  hypB L.ax-CCX0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCZ = HB5.hb2481
  hypB L.ax-CCX0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB5.hb2482
  hypB L.ax-CCX0-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-CS12-CCZ = HB5.hb2483
  hypB L.ax-CCX0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0 = HB5.hb2484
  hypB L.ax-CCX0-S0-K0-CK10=S0-K0-CK10-CCX0-CS12-CS12-CS12-CCZ = HB5.hb2485
  hypB L.ax-CCX0-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-CS12-CS12 = HB5.hb2486
  hypB L.ax-CCX0-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CS12-CS12-CCZ = HB5.hb2487
  hypB L.ax-CCX0-S0-K0-CK20=S0-K0-CK20-CCX0-CS12-CS12-CS12-CCZ = HB5.hb2488
  hypB L.ax-CCX0-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS12-CS12-CCZ = HB5.hb2489
  hypB L.ax-CCX0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCX0-CS12-CS12-CS12-CCZ = HB5.hb2490
  hypB L.ax-CCX0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12 = HB5.hb2491
  hypB L.ax-CCX0-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCX0-CS12-CCZ = HB5.hb2492
  hypB L.ax-CCX0-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCX0 = HB5.hb2493
  hypB L.ax-CCX0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CCZ = HB5.hb2494
  hypB L.ax-CCX0-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-CS12-CS12 = HB5.hb2495
  hypB L.ax-CCX0-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CS12-CS12-CCZ = HB5.hb2496
  hypB L.ax-CCX0-S0-K0-CCK'=S0-K0-CCK'-CCX0 = HB5.hb2497
  hypB L.ax-CCX0-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CCZ = HB5.hb2498
  hypB L.ax-CCX0-S0-CK10-CCK'=S0-CK10-CCK'-CCX0 = HB5.hb2499
  hypB L.ax-CCX0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CCZ = HB5.hb2500
  hypB L.ax-CCX0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCZ = HB5.hb2501
  hypB L.ax-CCX0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ = HB5.hb2502
  hypB L.ax-CCX0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCX0 = HB5.hb2503
  hypB L.ax-CCX0-S0-CK20-CK10=S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ = HB5.hb2504
  hypB L.ax-CCX0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CCX0-CS12-CS12 = HB5.hb2505
  hypB L.ax-CCX0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ = HB5.hb2506
  hypB L.ax-CCX0-S0-CK20-CCK'=S0-CK20-CCK'-CCX0 = HB5.hb2507
  hypB L.ax-CCX0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CCZ = HB5.hb2508
  hypB L.ax-CCX0-K0-S0-CK10=K0-S0-CK10-CCX0 = HB5.hb2509
  hypB L.ax-CCX0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCZ = HB5.hb2510
  hypB L.ax-CCX0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB5.hb2511
  hypB L.ax-CCX0-K0-S0-CK20=K0-S0-CK20-CCX0 = HB5.hb2512
  hypB L.ax-CCX0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCX0-CS12-CCZ = HB5.hb2513
  hypB L.ax-CCX0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0 = HB5.hb2514
  hypB L.ax-CCX0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CCZ = HB5.hb2515
  hypB L.ax-CCX0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCZ = HB5.hb2516
  hypB L.ax-CCX0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCX0-CS12-CCZ = HB5.hb2517
  hypB L.ax-CCX0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CCX0 = HB5.hb2518
  hypB L.ax-CCX0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCZ = HB5.hb2519
  hypB L.ax-CCX0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS12-CCZ = HB5.hb2520
  hypB L.ax-CCX0-K0-CK10=K0-CK10-CCX0 = HB5.hb2521
  hypB L.ax-CCX0-K0-CK10-CCK'=K0-CK10-CCK'-CCZ = HB5.hb2522
  hypB L.ax-CCX0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB5.hb2523
  hypB L.ax-CCX0-K0-CK20=K0-CK20-CCX0 = HB5.hb2524
  hypB L.ax-CCX0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCX0-CS12-CCZ = HB5.hb2525
  hypB L.ax-CCX0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCX0 = HB5.hb2526
  hypB L.ax-CCX0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CCZ = HB5.hb2527
  hypB L.ax-CCX0-K0-CK20-CK10=K0-CK20-CK10-CCZ = HB5.hb2528
  hypB L.ax-CCX0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCX0-CS12-CCZ = HB5.hb2529
  hypB L.ax-CCX0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CCX0 = HB5.hb2530
  hypB L.ax-CCX0-K0-CK20-CCK'=K0-CK20-CCK'-CCZ = HB5.hb2531
  hypB L.ax-CCX0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0-CS12-CCZ = HB5.hb2532
  hypB L.ax-CCX0-K0-CCK'=K0-CCK'-CCX0-CS12-CCZ = HB5.hb2533
  hypB L.ax-CCX0-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0 = HB5.hb2534
  hypB L.ax-CCX0-CK10-CCK'=CK10-CCK'-CCX0-CS12-CCZ = HB5.hb2535
  hypB L.ax-CCX0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0 = HB5.hb2536
  hypB L.ax-CCX0-CK20-S0-CK10=CK20-S0-CK10-CCX0 = HB5.hb2537
  hypB L.ax-CCX0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCZ = HB5.hb2538
  hypB L.ax-CCX0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB5.hb2539
  hypB L.ax-CCX0-CK20-CK10=CK20-CK10-CCX0 = HB5.hb2540
  hypB L.ax-CCX0-CK20-CK10-CCK'=CK20-CK10-CCK'-CCZ = HB5.hb2541
  hypB L.ax-CCX0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ = HB5.hb2542
  hypB L.ax-CCX0-CK20-CCK'=CK20-CCK'-CCX0-CS12-CCZ = HB5.hb2543
  hypB L.ax-CCX0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0 = HB5.hb2544

  hypB L.ax-Swap12-S0-K0=S0-K0-Swap12 = HB5.hb2545
  hypB L.ax-Swap12-S0-K0-S0-CK10=S0-K0-S0-CK20-Swap12 = HB5.hb2546
  hypB L.ax-Swap12-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CCK'-Swap12 = HB5.hb2547
  hypB L.ax-Swap12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-Swap12 = HB5.hb2548
  hypB L.ax-Swap12-S0-K0-S0-CK20=S0-K0-S0-CK10-Swap12 = HB5.hb2549
  hypB L.ax-Swap12-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ = HB5.hb2550
  hypB L.ax-Swap12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ = HB5.hb2551
  hypB L.ax-Swap12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12 = HB5.hb2552
  hypB L.ax-Swap12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-Swap12 = HB5.hb2553
  hypB L.ax-Swap12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-Swap12 = HB5.hb2554
  hypB L.ax-Swap12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-Swap12 = HB5.hb2555
  hypB L.ax-Swap12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK10-CCK'-Swap12 = HB5.hb2556
  hypB L.ax-Swap12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-Swap12 = HB5.hb2557
  hypB L.ax-Swap12-S0-K0-CK10=S0-K0-CK20-Swap12 = HB5.hb2558
  hypB L.ax-Swap12-S0-K0-CK10-CCK'=S0-K0-CK20-CCK'-Swap12 = HB5.hb2559
  hypB L.ax-Swap12-S0-K0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-Swap12 = HB5.hb2560
  hypB L.ax-Swap12-S0-K0-CK20=S0-K0-CK10-Swap12 = HB5.hb2561
  hypB L.ax-Swap12-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ = HB5.hb2562
  hypB L.ax-Swap12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12 = HB5.hb2563
  hypB L.ax-Swap12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ = HB5.hb2564
  hypB L.ax-Swap12-S0-K0-CK20-CK10=S0-K0-CK20-CK10-Swap12 = HB5.hb2565
  hypB L.ax-Swap12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-Swap12 = HB5.hb2566
  hypB L.ax-Swap12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-Swap12 = HB5.hb2567
  hypB L.ax-Swap12-S0-K0-CK20-CCK'=S0-K0-CK10-CCK'-Swap12 = HB5.hb2568
  hypB L.ax-Swap12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-Swap12 = HB5.hb2569
  hypB L.ax-Swap12-S0-K0-CCK'=S0-K0-CCK'-Swap12 = HB5.hb2570
  hypB L.ax-Swap12-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-Swap12 = HB5.hb2571
  hypB L.ax-Swap12-S0-CK10=S0-CK20-Swap12 = HB5.hb2572
  hypB L.ax-Swap12-S0-CK10-CCK'=S0-CK20-CCK'-Swap12 = HB5.hb2573
  hypB L.ax-Swap12-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-Swap12 = HB5.hb2574
  hypB L.ax-Swap12-S0-CK20=S0-CK10-Swap12 = HB5.hb2575
  hypB L.ax-Swap12-S0-CK20-S0-CK10=CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ = HB5.hb2576
  hypB L.ax-Swap12-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ = HB5.hb2577
  hypB L.ax-Swap12-S0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12 = HB5.hb2578
  hypB L.ax-Swap12-S0-CK20-CK10=S0-CK20-CK10-Swap12 = HB5.hb2579
  hypB L.ax-Swap12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-Swap12 = HB5.hb2580
  hypB L.ax-Swap12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-Swap12 = HB5.hb2581
  hypB L.ax-Swap12-S0-CK20-CCK'=S0-CK10-CCK'-Swap12 = HB5.hb2582
  hypB L.ax-Swap12-S0-CK20-CCK'-CCK'=S0-CK10-CCK'-CCK'-Swap12 = HB5.hb2583
  hypB L.ax-Swap12-K0-S0-CK10=K0-S0-CK20-Swap12 = HB5.hb2584
  hypB L.ax-Swap12-K0-S0-CK10-CCK'=K0-S0-CK20-CCK'-Swap12 = HB5.hb2585
  hypB L.ax-Swap12-K0-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-Swap12 = HB5.hb2586
  hypB L.ax-Swap12-K0-S0-CK20=K0-S0-CK10-Swap12 = HB5.hb2587
  hypB L.ax-Swap12-K0-S0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ = HB5.hb2588
  hypB L.ax-Swap12-K0-S0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ = HB5.hb2589
  hypB L.ax-Swap12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12 = HB5.hb2590
  hypB L.ax-Swap12-K0-S0-CK20-CK10=K0-S0-CK20-CK10-Swap12 = HB5.hb2591
  hypB L.ax-Swap12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-Swap12 = HB5.hb2592
  hypB L.ax-Swap12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-Swap12 = HB5.hb2593
  hypB L.ax-Swap12-K0-S0-CK20-CCK'=K0-S0-CK10-CCK'-Swap12 = HB5.hb2594
  hypB L.ax-Swap12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-Swap12 = HB5.hb2595
  hypB L.ax-Swap12-K0-CK10=K0-CK20-Swap12 = HB5.hb2596
  hypB L.ax-Swap12-K0-CK10-CCK'=K0-CK20-CCK'-Swap12 = HB5.hb2597
  hypB L.ax-Swap12-K0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-Swap12 = HB5.hb2598
  hypB L.ax-Swap12-K0-CK20=K0-CK10-Swap12 = HB5.hb2599
  hypB L.ax-Swap12-K0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ = HB5.hb2600
  hypB L.ax-Swap12-K0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12 = HB5.hb2601
  hypB L.ax-Swap12-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ = HB5.hb2602
  hypB L.ax-Swap12-K0-CK20-CK10=K0-CK20-CK10-Swap12 = HB5.hb2603
  hypB L.ax-Swap12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-Swap12 = HB5.hb2604
  hypB L.ax-Swap12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-Swap12 = HB5.hb2605
  hypB L.ax-Swap12-K0-CK20-CCK'=K0-CK10-CCK'-Swap12 = HB5.hb2606
  hypB L.ax-Swap12-K0-CK20-CCK'-CCK'=K0-CK10-CCK'-CCK'-Swap12 = HB5.hb2607
  hypB L.ax-Swap12-K0-CCK'=K0-CCK'-Swap12 = HB5.hb2608
  hypB L.ax-Swap12-K0-CCK'-CCK'=K0-CCK'-CCK'-Swap12 = HB5.hb2609
  hypB L.ax-Swap12-CK10-CCK'=CK20-CCK'-Swap12 = HB5.hb2610
  hypB L.ax-Swap12-CK10-CCK'-CCK'=CK20-CCK'-CCK'-Swap12 = HB5.hb2611
  hypB L.ax-Swap12-CK20-S0-CK10=S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ = HB5.hb2612
  hypB L.ax-Swap12-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12 = HB5.hb2613
  hypB L.ax-Swap12-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ = HB5.hb2614
  hypB L.ax-Swap12-CK20-CK10=CK20-CK10-Swap12 = HB5.hb2615
  hypB L.ax-Swap12-CK20-CK10-CCK'=CK20-CK10-CCK'-Swap12 = HB5.hb2616
  hypB L.ax-Swap12-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-Swap12 = HB5.hb2617
  hypB L.ax-Swap12-CK20-CCK'=CK10-CCK'-Swap12 = HB5.hb2618
  hypB L.ax-Swap12-CK20-CCK'-CCK'=CK10-CCK'-CCK'-Swap12 = HB5.hb2619
  hypB L.ax-Swap12-CCK'-CCK'=CCK'-CCK'-Swap12 = HB5.hb2620

  hypB L.ax-CK10-S0-K0-S0-CK10=S0-K0-CK10-S0-CS01 = HB5.hb2621
  hypB L.ax-CK10-S0-K0-S0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-S0-CS01-CS12 = HB5.hb2622
  hypB L.ax-CK10-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CCX0-S0-CS01-CCZ = HB5.hb2623
  hypB L.ax-CK10-S0-K0-S0-CK20=S0-K0-S0-CK20-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS12-CS12-CCZ = HB5.hb2624
  hypB L.ax-CK10-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CX10-CCX0-S0-S1-CS01-CS12-CS12-CS12 = HB5.hb2625
  hypB L.ax-CK10-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX10-S0-S1-CS01 = HB5.hb2626
  hypB L.ax-CK10-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CX10-S0-S1-CS01-CS12-CCZ = HB5.hb2627
  hypB L.ax-CK10-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-CS01-CS01-CS01-CS12-CCZ = HB5.hb2628
  hypB L.ax-CK10-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS01-CS12-CS12-CS12 = HB5.hb2629
  hypB L.ax-CK10-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS01 = HB5.hb2630
  hypB L.ax-CK10-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX10-S1-S1-S1-CS01-CS12-CCZ = HB5.hb2631
  hypB L.ax-CK10-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CX10-CCX0-S1-S1-S1-CS01-CS12-CS12-CS12 = HB5.hb2632
  hypB L.ax-CK10-S0-K0-CK10=S0-K0-S0-CK10-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01 = HB5.hb2633
  hypB L.ax-CK10-S0-K0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CS12 = HB5.hb2634
  hypB L.ax-CK10-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CCZ = HB5.hb2635
  hypB L.ax-CK10-S0-K0-CK20=S0-K0-CK20-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2636
  hypB L.ax-CK10-S0-K0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCX0-S0-CS01-CCZ = HB5.hb2637
  hypB L.ax-CK10-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S0-CS01 = HB5.hb2638
  hypB L.ax-CK10-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCX0-S0-CS01-CS12-CS12-CS12 = HB5.hb2639
  hypB L.ax-CK10-S0-K0-CK20-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CS12-CS12-CS12 = HB5.hb2640
  hypB L.ax-CK10-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-S0-CK10-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CCZ = HB5.hb2641
  hypB L.ax-CK10-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01 = HB5.hb2642
  hypB L.ax-CK10-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2643
  hypB L.ax-CK10-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2644
  hypB L.ax-CK10-S0-K0-CCK'=S0-K0-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = HB5.hb2645
  hypB L.ax-CK10-S0-K0-CCK'-CCK'=S0-K0-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = HB5.hb2646
  hypB L.ax-CK10-S0-CK10-CCK'=S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = HB5.hb2647
  hypB L.ax-CK10-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = HB5.hb2648
  hypB L.ax-CK10-S0-CK20-S0-CK10=S0-CK20-CCK'-CX10-CCX0-S0-S1-S1-CS12-CS12-CCZ = HB5.hb2649
  hypB L.ax-CK10-S0-CK20-S0-CK10-CCK'=S0-CK20-CX10-S0-S1-S1-CS12-CCZ = HB5.hb2650
  hypB L.ax-CK10-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX10-CCX0-S0-S1-S1-CS12 = HB5.hb2651
  hypB L.ax-CK10-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2652
  hypB L.ax-CK10-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2653
  hypB L.ax-CK10-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2654
  hypB L.ax-CK10-S0-CK20-CCK'=S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS12-CS12-CS12 = HB5.hb2655
  hypB L.ax-CK10-S0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-CS01-CS01-CCZ = HB5.hb2656
  hypB L.ax-CK10-K0-S0-CK10=K0-S0-CK10-CX10-CS01-CS01-CS01 = HB5.hb2657
  hypB L.ax-CK10-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = HB5.hb2658
  hypB L.ax-CK10-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = HB5.hb2659
  hypB L.ax-CK10-K0-S0-CK20=K0-S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS12-CCZ = HB5.hb2660
  hypB L.ax-CK10-K0-S0-CK20-S0-CK10=K0-S0-CK20-CCK'-CX10-CCX0-S0-S1-S1-CS12-CS12-CCZ = HB5.hb2661
  hypB L.ax-CK10-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CX10-S0-S1-S1-CS12-CCZ = HB5.hb2662
  hypB L.ax-CK10-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX10-CCX0-S0-S1-S1-CS12 = HB5.hb2663
  hypB L.ax-CK10-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2664
  hypB L.ax-CK10-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2665
  hypB L.ax-CK10-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CX10-CS01-CS01-CS01-CS12-CCZ = HB5.hb2666
  hypB L.ax-CK10-K0-S0-CK20-CCK'=K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS12-CS12-CS12 = HB5.hb2667
  hypB L.ax-CK10-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-CS01-CS01-CCZ = HB5.hb2668
  hypB L.ax-CK10-K0-CK10=K0-S1-S1-S1 = HB5.hb2669
  hypB L.ax-CK10-K0-CK10-CCK'=K0-CCK'-S1-S1-S1 = HB5.hb2670
  hypB L.ax-CK10-K0-CK10-CCK'-CCK'=K0-CCK'-CCK'-S1-S1-S1 = HB5.hb2671
  hypB L.ax-CK10-K0-CK20=K0-CK20-CK10 = HB5.hb2672
  hypB L.ax-CK10-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CS01-CS01-CS01 = HB5.hb2673
  hypB L.ax-CK10-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = HB5.hb2674
  hypB L.ax-CK10-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = HB5.hb2675
  hypB L.ax-CK10-K0-CK20-CK10=K0-CK20-S1-S1-S1 = HB5.hb2676
  hypB L.ax-CK10-K0-CK20-CK10-CCK'=K0-CK20-CCK'-S1-S1-S1 = HB5.hb2677
  hypB L.ax-CK10-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-S1-S1-S1 = HB5.hb2678
  hypB L.ax-CK10-K0-CK20-CCK'=K0-CK20-CK10-CCK' = HB5.hb2679
  hypB L.ax-CK10-K0-CK20-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK' = HB5.hb2680
  hypB L.ax-CK10-K0-CCK'=K0-CK10-CCK' = HB5.hb2681
  hypB L.ax-CK10-K0-CCK'-CCK'=K0-CK10-CCK'-CCK' = HB5.hb2682
  hypB L.ax-CK10-CK10-CCK'=CCK'-S1-S1-S1 = HB5.hb2683
  hypB L.ax-CK10-CK10-CCK'-CCK'=CCK'-CCK'-S1-S1-S1 = HB5.hb2684
  hypB L.ax-CK10-CK20-S0-CK10=CK20-S0-CK10-CX10-CS01-CS01-CS01 = HB5.hb2685
  hypB L.ax-CK10-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ = HB5.hb2686
  hypB L.ax-CK10-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12 = HB5.hb2687
  hypB L.ax-CK10-CK20-CK10=CK20-S1-S1-S1 = HB5.hb2688
  hypB L.ax-CK10-CK20-CK10-CCK'=CK20-CCK'-S1-S1-S1 = HB5.hb2689
  hypB L.ax-CK10-CK20-CK10-CCK'-CCK'=CK20-CCK'-CCK'-S1-S1-S1 = HB5.hb2690
  hypB L.ax-CK10-CK20-CCK'=CK20-CK10-CCK' = HB5.hb2691
  hypB L.ax-CK10-CK20-CCK'-CCK'=CK20-CK10-CCK'-CCK' = HB5.hb2692
  hypB L.ax-CK20-S0-K0-S0-CK10=S0-K0-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ = HB5.hb2693
  hypB L.ax-CK20-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ = HB5.hb2694
  hypB L.ax-CK20-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12 = HB5.hb2695
  hypB L.ax-CK20-S0-K0-S0-CK20=S0-K0-CK20-S0-CS02 = HB5.hb2696
  hypB L.ax-CK20-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS12 = HB5.hb2697
  hypB L.ax-CK20-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CCZ = HB5.hb2698
  hypB L.ax-CK20-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CX10-S0-S0-CS01-CS01-CS02-CS12-CS12-CS12-CCZ = HB5.hb2699
  hypB L.ax-CK20-S0-K0-S0-CK20-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ = HB5.hb2700
  hypB L.ax-CK20-S0-K0-S0-CK20-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS02 = HB5.hb2701
  hypB L.ax-CK20-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ = HB5.hb2702
  hypB L.ax-CK20-S0-K0-S0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-S0-CS02-CS12 = HB5.hb2703
  hypB L.ax-CK20-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CCX0-S0-CS02-CCZ = HB5.hb2704
  hypB L.ax-CK20-S0-K0-CK10=S0-K0-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2705
  hypB L.ax-CK20-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2706
  hypB L.ax-CK20-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2707
  hypB L.ax-CK20-S0-K0-CK20=S0-K0-S0-CK20-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02 = HB5.hb2708
  hypB L.ax-CK20-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-S2-S2-S2-CS02-CS02-CS02-CS12-CCZ = HB5.hb2709
  hypB L.ax-CK20-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S2-S2-S2-CS02-CS02-CS02 = HB5.hb2710
  hypB L.ax-CK20-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCX0-S2-S2-S2-CS02-CS02-CS02-CS12-CS12-CS12 = HB5.hb2711
  hypB L.ax-CK20-S0-K0-CK20-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12 = HB5.hb2712
  hypB L.ax-CK20-S0-K0-CK20-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CCZ = HB5.hb2713
  hypB L.ax-CK20-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12 = HB5.hb2714
  hypB L.ax-CK20-S0-K0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02-CS12 = HB5.hb2715
  hypB L.ax-CK20-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02-CCZ = HB5.hb2716
  hypB L.ax-CK20-S0-K0-CCK'=S0-K0-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ = HB5.hb2717
  hypB L.ax-CK20-S0-K0-CCK'-CCK'=S0-K0-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12 = HB5.hb2718
  hypB L.ax-CK20-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ = HB5.hb2719
  hypB L.ax-CK20-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ = HB5.hb2720
  hypB L.ax-CK20-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12 = HB5.hb2721
  hypB L.ax-CK20-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2722
  hypB L.ax-CK20-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2723
  hypB L.ax-CK20-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2724
  hypB L.ax-CK20-S0-CK20-CCK'=S0-CK20-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ = HB5.hb2725
  hypB L.ax-CK20-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12 = HB5.hb2726
  hypB L.ax-CK20-K0-S0-CK10=K0-CK20-S0-CK10 = HB5.hb2727
  hypB L.ax-CK20-K0-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK' = HB5.hb2728
  hypB L.ax-CK20-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK' = HB5.hb2729
  hypB L.ax-CK20-K0-S0-CK20=K0-S0-CK20-CX20-CS02-CS02-CS02 = HB5.hb2730
  hypB L.ax-CK20-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ = HB5.hb2731
  hypB L.ax-CK20-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ = HB5.hb2732
  hypB L.ax-CK20-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12 = HB5.hb2733
  hypB L.ax-CK20-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2734
  hypB L.ax-CK20-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2735
  hypB L.ax-CK20-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CX20-CS02-CS02-CS02-CS12-CCZ = HB5.hb2736
  hypB L.ax-CK20-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ = HB5.hb2737
  hypB L.ax-CK20-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12 = HB5.hb2738
  hypB L.ax-CK20-K0-CK10=K0-CK20-CK10 = HB5.hb2739
  hypB L.ax-CK20-K0-CK10-CCK'=K0-CK20-CK10-CCK' = HB5.hb2740
  hypB L.ax-CK20-K0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK' = HB5.hb2741
  hypB L.ax-CK20-K0-CK20=K0-S2-S2-S2 = HB5.hb2742
  hypB L.ax-CK20-K0-CK20-S0-CK10=K0-S0-CK10-S2-S2-S2 = HB5.hb2743
  hypB L.ax-CK20-K0-CK20-S0-CK10-CCK'=K0-S0-CK10-CCK'-S2-S2-S2 = HB5.hb2744
  hypB L.ax-CK20-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S2-S2-S2 = HB5.hb2745
  hypB L.ax-CK20-K0-CK20-CK10=K0-CK10-S2-S2-S2 = HB5.hb2746
  hypB L.ax-CK20-K0-CK20-CK10-CCK'=K0-CK10-CCK'-S2-S2-S2 = HB5.hb2747
  hypB L.ax-CK20-K0-CK20-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S2-S2-S2 = HB5.hb2748
  hypB L.ax-CK20-K0-CK20-CCK'=K0-CCK'-S2-S2-S2 = HB5.hb2749
  hypB L.ax-CK20-K0-CK20-CCK'-CCK'=K0-CCK'-CCK'-S2-S2-S2 = HB5.hb2750
  hypB L.ax-CK20-K0-CCK'=K0-CK20-CCK' = HB5.hb2751
  hypB L.ax-CK20-K0-CCK'-CCK'=K0-CK20-CCK'-CCK' = HB5.hb2752
  hypB L.ax-CK20-CK20-S0-CK10=S0-CK10-S2-S2-S2 = HB5.hb2753
  hypB L.ax-CK20-CK20-S0-CK10-CCK'=S0-CK10-CCK'-S2-S2-S2 = HB5.hb2754
  hypB L.ax-CK20-CK20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S2-S2-S2 = HB5.hb2755
  hypB L.ax-CK20-CK20-CK10=CK10-S2-S2-S2 = HB5.hb2756
  hypB L.ax-CK20-CK20-CK10-CCK'=CK10-CCK'-S2-S2-S2 = HB5.hb2757
  hypB L.ax-CK20-CK20-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S2-S2-S2 = HB5.hb2758
  hypB L.ax-CK20-CK20-CCK'=CCK'-S2-S2-S2 = HB5.hb2759
  hypB L.ax-CK20-CK20-CCK'-CCK'=CCK'-CCK'-S2-S2-S2 = HB5.hb2760
  hypB L.ax-CCK'-S0-K0-S0-CK10=S0-K0-S0-CK10-CCK' = HB5.hb2761
  hypB L.ax-CCK'-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCK' = HB5.hb2762
  hypB L.ax-CCK'-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CS12-CS12 = HB5.hb2763
  hypB L.ax-CCK'-S0-K0-S0-CK20=S0-K0-S0-CK20-CCK' = HB5.hb2764
  hypB L.ax-CCK'-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCK' = HB5.hb2765
  hypB L.ax-CCK'-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK' = HB5.hb2766
  hypB L.ax-CCK'-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CS12-CS12 = HB5.hb2767
  hypB L.ax-CCK'-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS12 = HB5.hb2768
  hypB L.ax-CCK'-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CS12-CS12-CS12-CCZ = HB5.hb2769
  hypB L.ax-CCK'-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCX0-CCZ = HB5.hb2770
  hypB L.ax-CCK'-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCK' = HB5.hb2771
  hypB L.ax-CCK'-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CS12-CS12 = HB5.hb2772
  hypB L.ax-CCK'-S0-K0-CK10=S0-K0-CK10-CCK'-CCK'-CCX0-CS12 = HB5.hb2773
  hypB L.ax-CCK'-S0-K0-CK10-CCK'=S0-K0-CK10-CS12-CS12-CS12-CCZ = HB5.hb2774
  hypB L.ax-CCK'-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCX0-CCZ = HB5.hb2775
  hypB L.ax-CCK'-S0-K0-CK20=S0-K0-CK20-CCK'-CCK'-CCX0-CS12 = HB5.hb2776
  hypB L.ax-CCK'-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ = HB5.hb2777
  hypB L.ax-CCK'-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCX0-CS12-CS12-CS12 = HB5.hb2778
  hypB L.ax-CCK'-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS12-CS12-CS12-CCZ = HB5.hb2779
  hypB L.ax-CCK'-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK' = HB5.hb2780
  hypB L.ax-CCK'-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK' = HB5.hb2781
  hypB L.ax-CCK'-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS12-CS12 = HB5.hb2782
  hypB L.ax-CCK'-S0-K0-CK20-CCK'=S0-K0-CK20-CS12-CS12-CS12-CCZ = HB5.hb2783
  hypB L.ax-CCK'-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCX0-CCZ = HB5.hb2784
  hypB L.ax-CCK'-S0-K0-CCK'=S0-K0-CCK'-CCK' = HB5.hb2785
  hypB L.ax-CCK'-S0-K0-CCK'-CCK'=S0-K0-CS12-CS12 = HB5.hb2786
  hypB L.ax-CCK'-S0-CK10-CCK'=S0-CK10-CCK'-CCK' = HB5.hb2787
  hypB L.ax-CCK'-S0-CK10-CCK'-CCK'=S0-CK10-CS12-CS12 = HB5.hb2788
  hypB L.ax-CCK'-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCK' = HB5.hb2789
  hypB L.ax-CCK'-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCK' = HB5.hb2790
  hypB L.ax-CCK'-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CS12-CS12 = HB5.hb2791
  hypB L.ax-CCK'-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CCX0-CS12 = HB5.hb2792
  hypB L.ax-CCK'-S0-CK20-CK10-CCK'=S0-CK20-CK10-CS12-CS12-CS12-CCZ = HB5.hb2793
  hypB L.ax-CCK'-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCX0-CCZ = HB5.hb2794
  hypB L.ax-CCK'-S0-CK20-CCK'=S0-CK20-CCK'-CCK' = HB5.hb2795
  hypB L.ax-CCK'-S0-CK20-CCK'-CCK'=S0-CK20-CS12-CS12 = HB5.hb2796
  hypB L.ax-CCK'-K0-S0-CK10=K0-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ = HB5.hb2797
  hypB L.ax-CCK'-K0-S0-CK10-CCK'=K0-S0-CK10-CCX0-CS12-CS12-CS12 = HB5.hb2798
  hypB L.ax-CCK'-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CS12-CS12-CS12-CCZ = HB5.hb2799
  hypB L.ax-CCK'-K0-S0-CK20=K0-S0-CK20-CCK'-CCK'-CCX0-CS12-CS12-CCZ = HB5.hb2800
  hypB L.ax-CCK'-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12-CCZ = HB5.hb2801
  hypB L.ax-CCK'-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCX0-CCZ = HB5.hb2802
  hypB L.ax-CCK'-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CS12-CS12 = HB5.hb2803
  hypB L.ax-CCK'-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCX0-CS12 = HB5.hb2804
  hypB L.ax-CCK'-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12-CCZ = HB5.hb2805
  hypB L.ax-CCK'-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCX0-CCZ = HB5.hb2806
  hypB L.ax-CCK'-K0-S0-CK20-CCK'=K0-S0-CK20-CCX0-CS12-CS12-CS12 = HB5.hb2807
  hypB L.ax-CCK'-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CS12-CS12-CS12-CCZ = HB5.hb2808
  hypB L.ax-CCK'-K0-CK10=K0-CK10-CCK' = HB5.hb2809
  hypB L.ax-CCK'-K0-CK10-CCK'=K0-CK10-CCK'-CCK' = HB5.hb2810
  hypB L.ax-CCK'-K0-CK10-CCK'-CCK'=K0-CK10-CS12-CS12 = HB5.hb2811
  hypB L.ax-CCK'-K0-CK20=K0-CK20-CCK' = HB5.hb2812
  hypB L.ax-CCK'-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK' = HB5.hb2813
  hypB L.ax-CCK'-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCK' = HB5.hb2814
  hypB L.ax-CCK'-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CS12-CS12 = HB5.hb2815
  hypB L.ax-CCK'-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS12 = HB5.hb2816
  hypB L.ax-CCK'-K0-CK20-CK10-CCK'=K0-CK20-CK10-CS12-CS12-CS12-CCZ = HB5.hb2817
  hypB L.ax-CCK'-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCX0-CCZ = HB5.hb2818
  hypB L.ax-CCK'-K0-CK20-CCK'=K0-CK20-CCK'-CCK' = HB5.hb2819
  hypB L.ax-CCK'-K0-CK20-CCK'-CCK'=K0-CK20-CS12-CS12 = HB5.hb2820
  hypB L.ax-CCK'-K0-CCK'=K0-CS12-CS12-CS12-CCZ = HB5.hb2821
  hypB L.ax-CCK'-K0-CCK'-CCK'=K0-CCK'-CCX0-CCZ = HB5.hb2822
  hypB L.ax-CCK'-CK10-CCK'=CK10-CS12-CS12-CS12-CCZ = HB5.hb2823
  hypB L.ax-CCK'-CK10-CCK'-CCK'=CK10-CCK'-CCX0-CCZ = HB5.hb2824
  hypB L.ax-CCK'-CK20-S0-CK10=CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ = HB5.hb2825
  hypB L.ax-CCK'-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCX0-CS12-CS12-CS12 = HB5.hb2826
  hypB L.ax-CCK'-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CS12-CS12-CS12-CCZ = HB5.hb2827
  hypB L.ax-CCK'-CK20-CK10=CK20-CK10-CCK' = HB5.hb2828
  hypB L.ax-CCK'-CK20-CK10-CCK'=CK20-CK10-CCK'-CCK' = HB5.hb2829
  hypB L.ax-CCK'-CK20-CK10-CCK'-CCK'=CK20-CK10-CS12-CS12 = HB5.hb2830
  hypB L.ax-CCK'-CK20-CCK'=CK20-CS12-CS12-CS12-CCZ = HB5.hb2831
  hypB L.ax-CCK'-CK20-CCK'-CCK'=CK20-CCK'-CCX0-CCZ = HB5.hb2832



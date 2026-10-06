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
open import Examples.Groups.Clifford+CS-3qubit.Step6.Basis-Change

module Examples.Groups.Clifford+CS-3qubit.Step6.PLemmas where

  lemma-CCX1-CCX1=ε : Rel ⊢ CCX1 • CCX1 === ε
  lemma-CCX1-CCX1=ε = B01.by-basis-change Swap01 Swap01 (axiom ax-CCX0-CCX0=ε) 50 auto

  lemma-CCX2-CCX2=ε : Rel ⊢ CCX2 • CCX2 === ε
  lemma-CCX2-CCX2=ε = by-basis-change Swap12 Swap12 (lemma-CCX1-CCX1=ε) 50 auto

  lemma-CX02-CX02=ε : Rel ⊢ CX02 • CX02 === ε
  lemma-CX02-CX02=ε = B01.by-basis-change Swap01 Swap01 (axiom ax-CX12-CX12=ε) 50 auto

  lemma-CX20-CX20=ε : Rel ⊢ CX20 • CX20 === ε
  lemma-CX20-CX20=ε = B01.by-basis-change Swap01 Swap01 (axiom ax-CX21-CX21=ε) 50 auto


  lemma-X1-X1=ε : Rel ⊢ X1 • X1 === ε
  lemma-X1-X1=ε = B01.by-basis-change Swap01 Swap01 (axiom ax-X0-X0=ε) 50 auto

  lemma-X2-X2=ε : Rel ⊢ X2 • X2 === ε
  lemma-X2-X2=ε = by-basis-change Swap12 Swap12 (lemma-X1-X1=ε) 50 auto


  lemma-S1-S1-S1-S1=ε : Rel ⊢ S1 • S1 • S1 • S1 === ε
  lemma-S1-S1-S1-S1=ε = B01.by-basis-change Swap01 Swap01 (axiom ax-S0-S0-S0-S0=ε) 50 auto

  lemma-S2-S2-S2-S2=ε : Rel ⊢ S2 • S2 • S2 • S2 === ε
  lemma-S2-S2-S2-S2=ε = by-basis-change Swap12 Swap12 (lemma-S1-S1-S1-S1=ε) 50 auto

  lemma-CS02-CS02-CS02-CS02=ε : Rel ⊢ CS02 • CS02 • CS02 • CS02 === ε
  lemma-CS02-CS02-CS02-CS02=ε = B01.by-basis-change Swap01 Swap01 (axiom ax-CS12-CS12-CS12-CS12=ε) 50 auto


  lemma-iI-CCX1=CCX1-iI : Rel ⊢ iI • CCX1 === CCX1 • iI
  lemma-iI-CCX1=CCX1-iI = B01.by-basis-change Swap01 Swap01 (axiom ax-iI-CCX0=CCX0-iI) 50 auto

  lemma-iI-CCX2=CCX2-iI : Rel ⊢ iI • CCX2 === CCX2 • iI
  lemma-iI-CCX2=CCX2-iI = by-basis-change Swap12 Swap12 (lemma-iI-CCX1=CCX1-iI) 50 auto


  lemma-iI-CX10=CX10-iI : Rel ⊢ iI • CX10 === CX10 • iI
  lemma-iI-CX10=CX10-iI = B01.by-basis-change Swap01 Swap01 (axiom ax-iI-CX01=CX01-iI) 50 auto

  lemma-iI-CX20=CX20-iI : Rel ⊢ iI • CX20 === CX20 • iI
  lemma-iI-CX20=CX20-iI = by-basis-change Swap12 Swap12 (lemma-iI-CX10=CX10-iI) 50 auto

  lemma-iI-CX02=CX02-iI : Rel ⊢ iI • CX02 === CX02 • iI
  lemma-iI-CX02=CX02-iI = by-basis-change Swap12 Swap12 (axiom ax-iI-CX01=CX01-iI) 50 auto


  lemma-iI-CX21=CX21-iI : Rel ⊢ iI • CX21 === CX21 • iI
  lemma-iI-CX21=CX21-iI = B01.by-basis-change Swap01 Swap01 (lemma-iI-CX20=CX20-iI) 50 auto

  lemma-iI-CX12=CX12-iI : Rel ⊢ iI • CX12 === CX12 • iI
  lemma-iI-CX12=CX12-iI = by-basis-change Swap12 Swap12 (lemma-iI-CX21=CX21-iI) 50 auto

  lemma-iI-X1=X1-iI : Rel ⊢ iI • X1 === X1 • iI
  lemma-iI-X1=X1-iI = B01.by-basis-change Swap01 Swap01 (axiom ax-iI-X0=X0-iI) 50 auto


  lemma-iI-X2=X2-iI : Rel ⊢ iI • X2 === X2 • iI
  lemma-iI-X2=X2-iI = by-basis-change Swap12 Swap12 (lemma-iI-X1=X1-iI) 50 auto


  lemma-iI-S1=S1-iI : Rel ⊢ iI • S1 === S1 • iI
  lemma-iI-S1=S1-iI = B01.by-basis-change Swap01 Swap01 (axiom ax-iI-S0=S0-iI) 50 auto


  lemma-iI-S2=S2-iI : Rel ⊢ iI • S2 === S2 • iI
  lemma-iI-S2=S2-iI = by-basis-change Swap12 Swap12 (lemma-iI-S1=S1-iI) 50 auto

  lemma-iI-CS02=CS02-iI : Rel ⊢ iI • CS02 === CS02 • iI
  lemma-iI-CS02=CS02-iI = by-basis-change Swap12 Swap12 (axiom ax-iI-CS01=CS01-iI) 50 auto

  lemma-CX20-S1=S1-CX20 : Rel ⊢ CX20 • S1 === S1 • CX20
  lemma-CX20-S1=S1-CX20 = by-basis-change Swap12 Swap12 (axiom ax-CX10-S2=S2-CX10) 50 auto

  lemma-CX20-CS01=CS01-CS12-CCZ-CX20 : Rel ⊢ CX20 • CS01 === CS01 • CS12 • CCZ • CX20
  lemma-CX20-CS01=CS01-CS12-CCZ-CX20 = by-basis-change Swap12 Swap12 (axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10) 50 auto

  lemma-CX20-CS12=CS12-CX20 : Rel ⊢ CX20 • CS12 === CS12 • CX20
  lemma-CX20-CS12=CS12-CX20 = by-basis-change Swap12 Swap12 (axiom ax-CX10-CS12=CS12-CX10) 50 auto

  lemma-CCX0-S2=S2-CCX0 : Rel ⊢ CCX0 • S2 === S2 • CCX0
  lemma-CCX0-S2=S2-CCX0 = by-basis-change Swap12 Swap12 (axiom ax-CCX0-S1=S1-CCX0) 50 auto

  lemma-CCX0-CS02=CS02-CS12-CCZ-CCX0 : Rel ⊢ CCX0 • CS02 === CS02 • CS12 • CCZ • CCX0
  lemma-CCX0-CS02=CS02-CS12-CCZ-CCX0 = by-basis-change Swap12 Swap12 (axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0) 50 auto

  lemma-S2-S1=S1-S2 : Rel ⊢ S2 • S1 === S1 • S2
  lemma-S2-S1=S1-S2 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-S1-S0=S0-S1) 50 auto


  lemma-CS12-S0=S0-CS12 : Rel ⊢  CS12 • S0 === S0 • CS12
  lemma-CS12-S0=S0-CS12 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-CS01-S2=S2-CS01) 50 auto
  lemma-CS12-S1=S1-CS12 : Rel ⊢  CS12 • S1 === S1 • CS12
  lemma-CS12-S1=S1-CS12 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-CS01-S0=S0-CS01) 50 auto
  lemma-CS12-S2=S2-CS12 : Rel ⊢  CS12 • S2 === S2 • CS12
  lemma-CS12-S2=S2-CS12 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-CS01-S1=S1-CS01) 50 auto


  lemma-CS02-S1=S1-CS02 : Rel ⊢ CS02 • S1 === S1 • CS02
  lemma-CS02-S1=S1-CS02 = B01.by-basis-change (Swap01) (Swap01) (lemma-CS12-S0=S0-CS12) 50 auto

  lemma-CS12-CS02=CS02-CS12 : Rel ⊢ CS12 • CS02 === CS02 • CS12
  lemma-CS12-CS02=CS02-CS12 = by-basis-change Swap12 Swap12 (axiom ax-CS12-CS01=CS01-CS12) 50 auto


  lemma-CCZ-S1=S1-CCZ : Rel ⊢ CCZ • S1 === S1 • CCZ
  lemma-CCZ-S1=S1-CCZ = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CCZ-S0=S0-CCZ) 50 auto

  lemma-CCZ-CS12=CS12-CCZ : Rel ⊢ CCZ • CS12 === CS12 • CCZ
  lemma-CCZ-CS12=CS12-CCZ = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-CCZ-CS01=CS01-CCZ) 50 auto

  lemma-CX01-S0=S0-CX01 : Rel ⊢  CX01 • S0 === S0 • CX01
  lemma-CX01-S0=S0-CX01 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CX10-S1=S1-CX10) 50 auto
  lemma-CX01-S1=S0-S1-CS01-CS01-CX01 : Rel ⊢  CX01 • S1 === S0 • S1 • CS01 • CS01 • CX01
  lemma-CX01-S1=S0-S1-CS01-CS01-CX01 =
    equational CX01 • S1
      by B01.by-basis-change (Swap01) (Swap01) (axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10) 50 auto
    equals S1 • S0 • CS01 • CS01 • CX01
      by general-assoc auto
    equals (S1 • S0) • CS01 • CS01 • CX01
      by left axiom ax-S1-S0=S0-S1
    equals (S0 • S1) • CS01 • CS01 • CX01
      by general-assoc auto
    equals S0 • S1 • CS01 • CS01 • CX01
  lemma-CX01-S2=S2-CX01 : Rel ⊢  CX01 • S2 === S2 • CX01
  lemma-CX01-S2=S2-CX01 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CX10-S2=S2-CX10) 50 auto
  lemma-CX01-CS01=S0-CS01-CS01-CS01-CX01 : Rel ⊢  CX01 • CS01 === S0 • CS01 • CS01 • CS01 • CX01
  lemma-CX01-CS01=S0-CS01-CS01-CS01-CX01 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10) 50 auto
  lemma-CX01-CS02=CS02-CX01 : Rel ⊢  CX01 • CS02 === CS02 • CX01
  lemma-CX01-CS02=CS02-CX01 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CX10-CS12=CS12-CX10) 50 auto
  lemma-CX01-CS12=CS02-CS12-CCZ-CX01 : Rel ⊢  CX01 • CS12 === CS02 • CS12 • CCZ • CX01
  lemma-CX01-CS12=CS02-CS12-CCZ-CX01 =
    equational CX01 • CS12
      by B01.by-basis-change (Swap01) (Swap01) (axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10) 50 auto
    equals CS12 • CS02 • CCZ • CX01
      by general-assoc auto
    equals (CS12 • CS02) • CCZ • CX01
      by left lemma-CS12-CS02=CS02-CS12
    equals (CS02 • CS12) • CCZ • CX01
      by general-assoc auto
    equals CS02 • CS12 • CCZ • CX01
  lemma-CX01-CCZ=CS02-CS02-CCZ-CX01 : Rel ⊢  CX01 • CCZ === CS02 • CS02 • CCZ • CX01
  lemma-CX01-CCZ=CS02-CS02-CCZ-CX01 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10) 50 auto

  lemma-CX02-S1=S1-CX02 : Rel ⊢ CX02 • S1 === S1 • CX02
  lemma-CX02-S1=S1-CX02 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CX20-S1=S1-CX20) 50 auto

  lemma-CX20-CS02=S2-CS02-CS02-CS02-CX20 : Rel ⊢ CX20 • CS02 === S2 • CS02 • CS02 • CS02 • CX20
  lemma-CX20-CS02=S2-CS02-CS02-CS02-CX20 = by-basis-change (Swap12) (Swap12) (axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10) 50 auto


  lemma-CX02-CS12=CS01-CS12-CCZ-CX02 : Rel ⊢ CX02 • CS12 === CS01 • CS12 • CCZ • CX02
  lemma-CX02-CS12=CS01-CS12-CCZ-CX02 =
    equational CX02 • CS12
      by B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CX20-CS01=CS01-CS12-CCZ-CX20) 50 auto
    equals CS12 • CS01 • CCZ • CX02
      by general-assoc auto
    equals (CS12 • CS01) • CCZ • CX02
      by left axiom ax-CS12-CS01=CS01-CS12
    equals (CS01 • CS12) • CCZ • CX02
      by general-assoc auto
    equals CS01 • CS12 • CCZ • CX02

  lemma-CCX1-S0=S0-CCX1 : Rel ⊢  CCX1 • S0 === S0 • CCX1
  lemma-CCX1-S0=S0-CCX1 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CCX0-S1=S1-CCX0) 50 auto
  lemma-CCX1-S1=S1-CS02-CCZ-CCX1 : Rel ⊢  CCX1 • S1 === S1 • CS02 • CCZ • CCX1
  lemma-CCX1-S1=S1-CS02-CCZ-CCX1 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CCX0-S0=S0-CS12-CCZ-CCX0) 50 auto
  lemma-CCX1-S2=S2-CCX1 : Rel ⊢  CCX1 • S2 === S2 • CCX1
  lemma-CCX1-S2=S2-CCX1 = B01.by-basis-change (Swap01) (Swap01) (lemma-CCX0-S2=S2-CCX0) 50 auto
  lemma-CCX1-CS01=CS01-CS02-CCZ-CCX1 : Rel ⊢  CCX1 • CS01 === CS01 • CS02 • CCZ • CCX1
  lemma-CCX1-CS01=CS01-CS02-CCZ-CCX1 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0) 50 auto
  lemma-CCX1-CS02=CS02-CCX1 : Rel ⊢  CCX1 • CS02 === CS02 • CCX1
  lemma-CCX1-CS02=CS02-CCX1 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CCX0-CS12=CS12-CCX0) 50 auto
  lemma-CCX1-CS12=CS02-CS12-CCZ-CCX1 : Rel ⊢  CCX1 • CS12 === CS02 • CS12 • CCZ • CCX1
  lemma-CCX1-CS12=CS02-CS12-CCZ-CCX1 =
    equational CCX1 • CS12
      by B01.by-basis-change (Swap01) (Swap01) (lemma-CCX0-CS02=CS02-CS12-CCZ-CCX0) 50 auto
    equals CS12 • CS02 • CCZ • CCX1
      by general-assoc auto
    equals (CS12 • CS02) • CCZ • CCX1
      by left lemma-CS12-CS02=CS02-CS12
    equals (CS02 • CS12) • CCZ • CCX1
      by general-assoc auto
    equals CS02 • CS12 • CCZ • CCX1
  lemma-CCX1-CCZ=CS02-CS02-CCZ-CCX1 : Rel ⊢  CCX1 • CCZ === CS02 • CS02 • CCZ • CCX1
  lemma-CCX1-CCZ=CS02-CS02-CCZ-CCX1 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0) 50 auto


  lemma-CCX2-S1=S1-CCX2 : Rel ⊢  CCX2 • S1 === S1 • CCX2
  lemma-CCX2-S1=S1-CCX2 = by-basis-change (Swap12) (Swap12) (lemma-CCX1-S2=S2-CCX1) 50 auto
  lemma-CCX2-CS01=CS01-CCX2 : Rel ⊢  CCX2 • CS01 === CS01 • CCX2
  lemma-CCX2-CS01=CS01-CCX2 = by-basis-change (Swap12) (Swap12) (lemma-CCX1-CS02=CS02-CCX1) 50 auto

  lemma-X0-S2=S2-X0 : Rel ⊢ X0 • S2 === S2 • X0
  lemma-X0-S2=S2-X0 = by-basis-change Swap12 Swap12 (axiom ax-X0-S1=S1-X0) 50 auto

  lemma-X0-CS02=S2-CS02-CS02-CS02-X0 : Rel ⊢ X0 • CS02 === S2 • CS02 • CS02 • CS02 • X0
  lemma-X0-CS02=S2-CS02-CS02-CS02-X0 = by-basis-change Swap12 Swap12 (axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0) 50 auto

  lemma-CX20-S0=S0-S2-CS02-CS02-CX20 : Rel ⊢ CX20 • S0 === S0 • S2 • CS02 • CS02 • CX20
  lemma-CX20-S0=S0-S2-CS02-CS02-CX20 = by-basis-change Swap12 Swap12 (axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10) 50 auto

  lemma-CX20-S2=S2-CX20 : Rel ⊢ CX20 • S2 === S2 • CX20
  lemma-CX20-S2=S2-CX20 = by-basis-change Swap12 Swap12 (axiom ax-CX10-S1=S1-CX10) 50 auto
  
  lemma-CX02-CS01=CS01-CX02 : Rel ⊢ CX02 • CS01 === CS01 • CX02
  lemma-CX02-CS01=CS01-CX02 = B02.by-basis-change (Swap01 • Swap12 • Swap01) (Swap01 • Swap12 • Swap01) (lemma-CX20-CS12=CS12-CX20) 50 auto


  lemma-CX12-CS01=CS01-CX12 : Rel ⊢ CX12 • CS01 === CS01 • CX12
  lemma-CX12-CS01=CS01-CX12 = B01.by-basis-change (Swap01) (Swap01) (lemma-CX02-CS01=CS01-CX02) 50 auto

  lemma-CX20-CCZ=CS12-CS12-CCZ-CX20 : Rel ⊢ CX20 • CCZ === CS12 • CS12 • CCZ • CX20
  lemma-CX20-CCZ=CS12-CS12-CCZ-CX20 = by-basis-change Swap12 Swap12 (axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10) 50 auto


  lemma-X1-S0=S0-X1 : Rel ⊢  X1 • S0 === S0 • X1
  lemma-X1-S0=S0-X1 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-X0-S1=S1-X0) 50 auto
  lemma-X1-S2=S2-X1 : Rel ⊢  X1 • S2 === S2 • X1
  lemma-X1-S2=S2-X1 = B01.by-basis-change (Swap01) (Swap01) (lemma-X0-S2=S2-X0) 50 auto
  lemma-X1-CS02=CS02-X1 : Rel ⊢  X1 • CS02 === CS02 • X1
  lemma-X1-CS02=CS02-X1 = B01.by-basis-change (Swap01) (Swap01) (axiom ax-X0-CS12=CS12-X0) 50 auto

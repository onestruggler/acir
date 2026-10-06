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

open import Examples.Groups.Clifford+CS-3qubit.Step7.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step7.MvI
open import Examples.Groups.Clifford+CS-3qubit.Step7.Order
open import Examples.Groups.Clifford+CS-3qubit.Step7.Basis-Change

module Examples.Groups.Clifford+CS-3qubit.Step7.PLemmas where

  lemma-CCX0-CX20=CX20-CCX0 : Rel ⊢ CCX0 • CX20 === CX20 • CCX0
  lemma-CCX0-CX20=CX20-CCX0 = by-basis-change Swap12 Swap12 (axiom ax-CCX0-CX10=CX10-CCX0) 50 auto


  lemma-CCX1-CX21=CX21-CCX1 : Rel ⊢ CCX1 • CX21 === CX21 • CCX1
  lemma-CCX1-CX21=CX21-CCX1 = B01.by-basis-change Swap01 Swap01 (lemma-CCX0-CX20=CX20-CCX0) 50 auto

  lemma-CCX1-CX01=CX01-CCX1 : Rel ⊢ CCX1 • CX01 === CX01 • CCX1
  lemma-CCX1-CX01=CX01-CCX1 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CCX1-CX21=CX21-CCX1) 50 auto

  lemma-CCX2-CX12=CX12-CCX2 : Rel ⊢ CCX2 • CX12 === CX12 • CCX2
  lemma-CCX2-CX12=CX12-CCX2 = by-basis-change Swap12 Swap12 (lemma-CCX1-CX21=CX21-CCX1) 50 auto

  lemma-CCX2-CX12=CX12-CCX2-cong : Rel ⊢ (CCX2 • CX12) • CX21 === (CX12 • CCX2) • CX21
  lemma-CCX2-CX12=CX12-CCX2-cong =  (cong lemma-CCX2-CX12=CX12-CCX2 refl)


  lemma-CX02=CX01-CCX2-CX01-CCX2 : Rel ⊢ CX02 === CX01 • CCX2 • CX01 • CCX2
  lemma-CX02=CX01-CCX2-CX01-CCX2 =
    equational CX02
      by Order.general-rewrite 100 auto
    equals CX01 • (CX01 • CX02 • CCX2) • CCX2
      by right left symm (axiom ax-CCX2-CX01=CX01-CX02-CCX2)
    equals CX01 • (CCX2 • CX01) • CCX2
      by general-assoc auto
    equals CX01 • CCX2 • CX01 • CCX2


  lemma-CX01-CCX2-CX01-CCX2=CCX2-CX02 : Rel ⊢ CX01 • CCX2 • CX01 === CCX2 • CX02
  lemma-CX01-CCX2-CX01-CCX2=CCX2-CX02 =
    equational CX01 • CCX2 • CX01
      by right right trans (symm right-unit) (right symm (lemma-CCX2-CCX2=ε))
    equals CX01 • CCX2 • CX01 • CCX2 • CCX2
      by general-assoc auto
    equals (CX01 • CCX2 • CX01 • CCX2) • CCX2
      by left symm (lemma-CX02=CX01-CCX2-CX01-CCX2)
    equals CX02 • CCX2
      by symm (B01.by-basis-change Swap01 Swap01 (lemma-CCX2-CX12=CX12-CCX2) 50 auto)
    equals CCX2 • CX02


  lemma-CCX2-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX2 : Rel ⊢ CCX2 • CX01 • CCX2 • CX01 === CX01 • CCX2 • CX01 • CCX2
  lemma-CCX2-CX01-CCX2-CX01=CX01-CCX2-CX01-CCX2 =
    equational CCX2 • CX01 • CCX2 • CX01
      by right lemma-CX01-CCX2-CX01-CCX2=CCX2-CX02
    equals CCX2 • CCX2 • CX02
      by general-assoc auto
    equals (CCX2 • CCX2) • CX02
      by trans (cong (lemma-CCX2-CCX2=ε) refl) left-unit
    equals CX02
      by trans (symm right-unit) (symm (cong refl (lemma-CCX2-CCX2=ε)))
    equals CX02 • (CCX2 • CCX2)
      by general-assoc auto
    equals (CX02 • CCX2) • CCX2
      by left B01.by-basis-change Swap01 Swap01 (lemma-CCX2-CX12=CX12-CCX2) 50 auto reversed
    equals (CCX2 • CX02) • CCX2
      by left lemma-CX01-CCX2-CX01-CCX2=CCX2-CX02 reversed
    equals (CX01 • CCX2 • CX01) • CCX2
      by general-assoc auto
    equals CX01 • CCX2 • CX01 • CCX2

  lemma-CCX2-CCX2-CX01=CX01 : Rel ⊢ CCX2 • CCX2 • CX01 === CX01
  lemma-CCX2-CCX2-CX01=CX01 = DO.general-rewrite 20 auto


  lemma-CX12-CX02=CX02-CX12 : Rel ⊢ CX12 • CX02 === CX02 • CX12
  lemma-CX12-CX02=CX02-CX12 =
    equational CX12 • CX02
      by symm (by-basis-change Swap12 Swap12 (axiom ax-CX01-CX21=CX21-CX01) 100 auto)
    equals CX02 • CX12
    

  lemma-CX21-CX20=CX20-CX21 : Rel ⊢ CX21 • CX20 === CX20 • CX21
  lemma-CX21-CX20=CX20-CX21 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (axiom ax-CX01-CX02=CX02-CX01) 50 auto


  lemma-CX20-CX21-CX20=CX21 : Rel ⊢ CX20 • CX21 • CX20 === CX21
  lemma-CX20-CX21-CX20=CX21 =
    equational CX20 • CX21 • CX20
      by general-assoc auto
    equals (CX20 • CX21) • CX20
      by left (symm (lemma-CX21-CX20=CX20-CX21))
    equals (CX21 • CX20) • CX20
      by assoc
    equals CX21 • CX20 • CX20
      by trans (cong refl (lemma-CX20-CX20=ε)) right-unit
    equals CX21

  lemma-CX10-CX20=CX20-CX10 : Rel ⊢ CX10 • CX20 === CX20 • CX10
  lemma-CX10-CX20=CX20-CX10 = B01.by-basis-change Swap01 Swap01 (axiom ax-CX01-CX21=CX21-CX01) 50 auto


  lemma-CX10-CX21-CX20=CX21-CX10 : Rel ⊢ CX10 • CX21 • CX20 === CX21 • CX10
  lemma-CX10-CX21-CX20=CX21-CX10 =
    equational CX10 • CX21 • CX20
      by symm assoc
    equals (CX10 • CX21) • CX20
      by left axiom ax-CX10-CX21=CX21-CX20-CX10
    equals (CX21 • CX20 • CX10) • CX20
      by general-assoc auto
    equals CX21 • (CX20 • CX10) • CX20
      by right left symm (lemma-CX10-CX20=CX20-CX10)
    equals CX21 • (CX10 • CX20) • CX20
      by general-assoc auto
    equals (CX21 • CX10) • CX20 • CX20
      by trans (cong refl (lemma-CX20-CX20=ε)) right-unit
    equals CX21 • CX10

  lemma-CX01-CX20=CX21-CX20-CX01 : Rel ⊢ CX01 • CX20 === CX21 • CX20 • CX01
  lemma-CX01-CX20=CX21-CX20-CX01 =
    equational CX01 • CX20
      by B01.by-basis-change Swap01 Swap01 (axiom ax-CX10-CX21=CX21-CX20-CX10) 50 auto
    equals CX20 • CX21 • CX01
      by symm assoc
    equals (CX20 • CX21) • CX01
      by left (symm (lemma-CX21-CX20=CX20-CX21))
    equals (CX21 • CX20) • CX01
      by assoc
    equals CX21 • CX20 • CX01


  lemma-CX02-CX02-CX20=CX20 : Rel ⊢ CX02 • CX02 • CX20 === CX20
  lemma-CX02-CX02-CX20=CX20 = DO.general-rewrite 20 auto

  lemma-CX12-CX12-CX21=CX21 : Rel ⊢ CX12 • CX12 • CX21 === CX21
  lemma-CX12-CX12-CX21=CX21 = DO.general-rewrite 20 auto

  lemma-CX21-CX21-CX20=CX20 : Rel ⊢ CX21 • CX21 • CX20 === CX20
  lemma-CX21-CX21-CX20=CX20 = DO.general-rewrite 20 auto

  lemma-CX10-iI=iI-CX10 : Rel ⊢ CX10 • iI === iI • CX10
  lemma-CX10-iI=iI-CX10 = mvID.general-rewrite 30 auto


  lemma-CCX0-S2=S2-CCX0 : Rel ⊢ CCX0 • S2 === S2 • CCX0
  lemma-CCX0-S2=S2-CCX0 = by-basis-change Swap12 Swap12 (axiom ax-CCX0-S1=S1-CCX0) 50 auto







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


  lemma-CCX0-CS02=CS02-CS12-CCZ-CCX0 : Rel ⊢ CCX0 • CS02 === CS02 • CS12 • CCZ • CCX0
  lemma-CCX0-CS02=CS02-CS12-CCZ-CCX0 = by-basis-change Swap12 Swap12 (axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0) 50 auto

  lemma-S2-S1=S1-S2 : Rel ⊢ S2 • S1 === S1 • S2
  lemma-S2-S1=S1-S2 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-S1-S0=S0-S1) 50 auto

  lemma-CS01-S1=S1-CS01 : Rel ⊢ CS01 • S1 === S1 • CS01
  lemma-CS01-S1=S1-CS01 = B01.by-basis-change Swap01 Swap01 (axiom ax-CS01-S0=S0-CS01) 100 auto


  lemma-CS12-S0=S0-CS12 : Rel ⊢  CS12 • S0 === S0 • CS12
  lemma-CS12-S0=S0-CS12 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-CS01-S2=S2-CS01) 50 auto
  lemma-CS12-S1=S1-CS12 : Rel ⊢  CS12 • S1 === S1 • CS12
  lemma-CS12-S1=S1-CS12 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-CS01-S0=S0-CS01) 50 auto
  lemma-CS12-S2=S2-CS12 : Rel ⊢  CS12 • S2 === S2 • CS12
  lemma-CS12-S2=S2-CS12 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (lemma-CS01-S1=S1-CS01) 50 auto


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


  lemma-S2-S0=S0-S2 : Rel ⊢ S2 • S0 === S0 • S2
  lemma-S2-S0=S0-S2 = by-basis-change Swap12 Swap12 (axiom ax-S1-S0=S0-S1) 50 auto

  lemma-CS02-S0=S0-CS02 : Rel ⊢ CS02 • S0 === S0 • CS02
  lemma-CS02-S0=S0-CS02 = by-basis-change Swap12 Swap12 (axiom ax-CS01-S0=S0-CS01) 50 auto

  lemma-CS02-S2=S2-CS02 : Rel ⊢  CS02 • S2 === S2 • CS02
  lemma-CS02-S2=S2-CS02 = by-basis-change Swap12 Swap12 (lemma-CS01-S1=S1-CS01) 50 auto

  lemma-CCZ-S2=S2-CCZ : Rel ⊢ CCZ • S2 === S2 • CCZ
  lemma-CCZ-S2=S2-CCZ = by-basis-change Swap12 Swap12 (lemma-CCZ-S1=S1-CCZ) 50 auto

  lemma-CCZ-CS02=CS02-CCZ : Rel ⊢ CCZ • CS02 === CS02 • CCZ
  lemma-CCZ-CS02=CS02-CCZ = by-basis-change Swap12 Swap12 (axiom ax-CCZ-CS01=CS01-CCZ) 50 auto

  lemma-iI-CS12=CS12-iI : Rel ⊢ iI • CS12 === CS12 • iI
  lemma-iI-CS12=CS12-iI = mvID.general-rewrite 20 auto

  lemma-CX10-K0=K0-CS01-CS01 : Rel ⊢ CX10 • K0 === K0 • CS01 • CS01
  lemma-CX10-K0=K0-CS01-CS01 =
    equational CX10 • K0
      by mvID.general-rewrite 100 auto
    equals iI ^ 3 • CX10 • K0 • iI
      by Order.general-rewrite 100 auto
    equals K0 • (K0 • CX10) • K0 • iI
      by right left symm (axiom ax-CS01-CS01-K0=K0-CX10)
    equals K0 • (CS01 • CS01 • K0) • K0 • iI
      by Order.general-rewrite 100 auto
    equals K0 • CS01 • CS01

  lemma-X0-K0=K0-S0-S0 : Rel ⊢ X0 • K0 === K0 • S0 • S0
  lemma-X0-K0=K0-S0-S0 =
    equational X0 • K0
      by mvI.general-rewrite 100 auto
    equals iI ^ 3 • X0 • K0 • iI
      by Order.general-rewrite 100 auto
    equals K0 • (K0 • X0) • K0 • iI
      by right left symm (axiom ax-S0-S0-K0=K0-X0)
    equals K0 • (S0 • S0 • K0) • K0 • iI
      by Order.general-rewrite 100 auto
    equals K0 • S0 • S0


  lemma-CCX0-K0=K0-CCZ : Rel ⊢ CCX0 • K0 === K0 • CCZ
  lemma-CCX0-K0=K0-CCZ =
    equational CCX0 • K0
      by mvI.general-rewrite 100 auto
    equals iI ^ 3 • CCX0 • K0 • iI
      by Order.general-rewrite 100 auto
    equals K0 • (K0 • CCX0) • K0 • iI
      by right left symm (axiom ax-CCZ-K0=K0-CCX0)
    equals K0 • (CCZ • K0) • K0 • iI
      by Order.general-rewrite 100 auto
    equals K0 • CCZ


  lemma-CS02-CS01=CS01-CS02 : Rel ⊢ CS02 • CS01 === CS01 • CS02
  lemma-CS02-CS01=CS01-CS02 = B01.by-basis-change Swap01 Swap01 (axiom ax-CS12-CS01=CS01-CS12) 100 auto




  a-step : Step-Function Gate Rel
  a-step (CX02-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ CX02-gen ∷ xs , at-head (symm (axiom ax-CX01-CX02=CX02-CX01)))
  a-step (X0-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-S1=S1-X0))
  a-step (S1-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-K0=K0-S1))
  a-step (X1-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ X1-gen ∷ xs , at-head (axiom ax-X1-K0=K0-X1))
  a-step (CS12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-K0=K0-CS12))
  a-step (Swap12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-K0=K0-Swap12))
  a-step (CX12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CX12-K0=K0-CX12))
  a-step (CS01-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CS01-CS01-K0=K0-CX10))
  a-step (CCZ-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCZ-K0=K0-CCX0))
  a-step (CX10-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS01-gen ∷ CS01-gen ∷ xs , at-head (lemma-CX10-K0=K0-CS01-CS01))
  a-step (CCX0-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CCZ-gen ∷ xs , at-head (lemma-CCX0-K0=K0-CCZ))
  a-step (CS01-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01))
  a-step (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ))
  a-step (X0-gen ∷ CS01-gen ∷ xs) = just (S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0))
  a-step (X0-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CS12=CS12-X0))
  a-step (X0-gen ∷ CCZ-gen ∷ xs) = just (CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CCZ=CS12-CS12-CCZ-X0))
  a-step (CX10-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10))
  a-step (CX10-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-S1=S1-CX10))
  a-step (CX10-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-S2=S2-CX10))
  a-step (CX10-gen ∷ CS01-gen ∷ xs) = just (S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10))
  a-step (CX10-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10))
  a-step (CX10-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-CS12=CS12-CX10))
  a-step (CX10-gen ∷ CCZ-gen ∷ xs) = just (CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10))
  a-step (CX10-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ CX10-gen ∷ xs , at-head (lemma-CX10-iI=iI-CX10))
  a-step (CCX0-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS12-gen ∷ CCZ-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-S0=S0-CS12-CCZ-CCX0))
  a-step (CCX0-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-S1=S1-CCX0))
  a-step (CCX0-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCX0-S2=S2-CCX0))
  a-step (CCX0-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0))
  a-step (CCX0-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCX0-CS02=CS02-CS12-CCZ-CCX0))
  a-step (CCX0-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CS12=CS12-CCX0))
  a-step (CCX0-gen ∷ CCZ-gen ∷ xs) = just (CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0))
  a-step (CCX0-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ CCX0-gen ∷ xs , at-head (symm (axiom ax-iI-CCX0=CCX0-iI)))
  a-step (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom ax-S0-S0-S0-S0=ε))
  a-step (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ xs) = just (xs , at-head (lemma-S1-S1-S1-S1=ε))
  a-step (S2-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ xs) = just (xs , at-head (lemma-S2-S2-S2-S2=ε))
  a-step (CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs) = just (xs , at-head (axiom ax-CS01-CS01-CS01-CS01=ε))
  a-step (CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ xs) = just (xs , at-head (lemma-CS02-CS02-CS02-CS02=ε))
  a-step (CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ xs) = just (xs , at-head (lemma-CS12-CS12-CS12-CS12=ε))
  a-step (CCZ-gen ∷ CCZ-gen ∷ xs) = just (xs , at-head (axiom ax-CCZ-CCZ=ε))
  a-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  a-step (S1-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-S0=S0-S1))
  a-step (S2-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S2-gen ∷ xs , at-head (lemma-S2-S0=S0-S2))
  a-step (S2-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ S2-gen ∷ xs , at-head (lemma-S2-S1=S1-S2))
  a-step (CS01-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-S0=S0-CS01))
  a-step (CS01-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CS01-gen ∷ xs , at-head (lemma-CS01-S1=S1-CS01))
  a-step (CS01-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-S2=S2-CS01))
  a-step (CS12-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS12-gen ∷ xs , at-head (lemma-CS12-S0=S0-CS12))
  a-step (CS12-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CS12-gen ∷ xs , at-head (lemma-CS12-S1=S1-CS12))
  a-step (CS12-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CS12-gen ∷ xs , at-head (lemma-CS12-S2=S2-CS12))
  a-step (CS12-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-CS01=CS01-CS12))
  a-step (CS12-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ CS12-gen ∷ xs , at-head (lemma-CS12-CS02=CS02-CS12))
  a-step (CS02-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS02-gen ∷ xs , at-head (lemma-CS02-S0=S0-CS02))
  a-step (CS02-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CS02-gen ∷ xs , at-head (lemma-CS02-S1=S1-CS02))
  a-step (CS02-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CS02-gen ∷ xs , at-head (lemma-CS02-S2=S2-CS02))
  a-step (CS02-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CS02-gen ∷ xs , at-head (lemma-CS02-CS01=CS01-CS02))
  a-step (CCZ-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCZ-S0=S0-CCZ))
  a-step (CCZ-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CCZ-gen ∷ xs , at-head (lemma-CCZ-S1=S1-CCZ))
  a-step (CCZ-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CCZ-gen ∷ xs , at-head (lemma-CCZ-S2=S2-CCZ))
  a-step (CCZ-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCZ-CS01=CS01-CCZ))
  a-step (CCZ-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ CCZ-gen ∷ xs , at-head (lemma-CCZ-CS12=CS12-CCZ))
  a-step (CCZ-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ CCZ-gen ∷ xs , at-head (lemma-CCZ-CS02=CS02-CCZ))
  a-step (iI-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S0=S0-iI))
  a-step (iI-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-S1=S1-iI))
  a-step (iI-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-S2=S2-iI))
  a-step (iI-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS01=CS01-iI))
  a-step (iI-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-CS12=CS12-iI))
  a-step (iI-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-CS02=CS02-iI))
  a-step (iI-gen ∷ CCZ-gen ∷ xs) = just (CCZ-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCZ=CCZ-iI))
  a-step (X1-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ X1-gen ∷ xs , at-head (axiom ax-X1-X0=X0-X1))

  a-step _ = nothing

  module SA = Rewriting.Step (step-cong (swap-step then a-step))



  lemma-S1-K0=K0-S1 : Rel ⊢ S1 • K0 === K0 • S1
  lemma-S1-K0=K0-S1 = SA.general-rewrite 20 auto
  lemma-S2-K0=K0-S2 : Rel ⊢ S2 • K0 === K0 • S2
  lemma-S2-K0=K0-S2 = by-basis-change Swap12 Swap12 lemma-S1-K0=K0-S1 20 auto
  lemma-X1-K0=K0-X1 : Rel ⊢ X1 • K0 === K0 • X1
  lemma-X1-K0=K0-X1 = SA.general-rewrite 20 auto
  lemma-X2-K0=K0-X2 : Rel ⊢ X2 • K0 === K0 • X2
  lemma-X2-K0=K0-X2 = by-basis-change Swap12 Swap12 lemma-X1-K0=K0-X1 20 auto
  lemma-CS12-K0=K0-CS12 : Rel ⊢ CS12 • K0 === K0 • CS12
  lemma-CS12-K0=K0-CS12 = SA.general-rewrite 20 auto
  lemma-CX12-K0=K0-CX12 : Rel ⊢ CX12 • K0 === K0 • CX12
  lemma-CX12-K0=K0-CX12 = SA.general-rewrite 20 auto
  lemma-CX21-K0=K0-CX21 : Rel ⊢ CX21 • K0 === K0 • CX21
  lemma-CX21-K0=K0-CX21 = by-basis-change Swap12 Swap12 lemma-CX12-K0=K0-CX12 20 auto
  lemma-Swap12-K0=K0-Swap12 : Rel ⊢ Swap12 • K0 === K0 • Swap12
  lemma-Swap12-K0=K0-Swap12 = SA.general-rewrite 20 auto
  lemma-CS01-CS01-K0=K0-CX10 : Rel ⊢ CS01 • CS01 • K0 === K0 • CX10
  lemma-CS01-CS01-K0=K0-CX10 = SA.general-rewrite 20 auto
  lemma-CS02-CS02-K0=K0-CX20 : Rel ⊢ CS02 • CS02 • K0 === K0 • CX20
  lemma-CS02-CS02-K0=K0-CX20 = by-basis-change Swap12 Swap12 lemma-CS01-CS01-K0=K0-CX10 20 auto
  lemma-CCZ-K0=K0-CCX0 : Rel ⊢ CCZ • K0 === K0 • CCX0
  lemma-CCZ-K0=K0-CCX0 = SA.general-rewrite 20 auto
  lemma-CX20-K0=K0-CS02-CS02 : Rel ⊢ CX20 • K0 === K0 • CS02 • CS02
  lemma-CX20-K0=K0-CS02-CS02 = by-basis-change Swap12 Swap12 lemma-CX10-K0=K0-CS01-CS01 20 auto



  lemma-X1-X0=X0-X1 : Rel ⊢ X1 • X0 === X0 • X1
  lemma-X1-X0=X0-X1 = SA.general-rewrite 50 auto
  lemma-X2-X0=X0-X2 : Rel ⊢ X2 • X0 === X0 • X2
  lemma-X2-X0=X0-X2 = by-basis-change Swap12 Swap12 (lemma-X1-X0=X0-X1) 50 auto 
  lemma-X2-X1=X1-X2 : Rel ⊢ X2 • X1 === X1 • X2
  lemma-X2-X1=X1-X2 = B01.by-basis-change Swap01 Swap01 (lemma-X2-X0=X0-X2) 50 auto
  lemma-X0-CX02=CX02-X0-X2 : Rel ⊢ X0 • CX02 === CX02 • X0 • X2
  lemma-X0-CX02=CX02-X0-X2 = by-basis-change Swap12 Swap12 (axiom ax-X0-CX01=CX01-X0-X1) 50 auto 
  lemma-X0-CX20=CX20-X0 : Rel ⊢ X0 • CX20 === CX20 • X0
  lemma-X0-CX20=CX20-X0 = by-basis-change Swap12 Swap12 (axiom ax-X0-CX10=CX10-X0) 50 auto 
  lemma-X0-CX12=CX12-X0 : Rel ⊢ X0 • CX12 === CX12 • X0
  lemma-X0-CX12=CX12-X0 = axiom ax-X0-CX12=CX12-X0
  lemma-X0-CX21=CX21-X0 : Rel ⊢ X0 • CX21 === CX21 • X0
  lemma-X0-CX21=CX21-X0 = by-basis-change Swap12 Swap12 (lemma-X0-CX12=CX12-X0) 50 auto 
  lemma-X0-CX10=CX10-X0 : Rel ⊢ X0 • CX10 === CX10 • X0
  lemma-X0-CX10=CX10-X0 = axiom ax-X0-CX10=CX10-X0
  lemma-X0-CX01=CX01-X0-X1 : Rel ⊢ X0 • CX01 === CX01 • X0 • X1
  lemma-X0-CX01=CX01-X0-X1 = axiom ax-X0-CX01=CX01-X0-X1
  lemma-X0-CCX1=CCX1-CX21-X0 : Rel ⊢ X0 • CCX1 === CCX1 • CX21 • X0
  lemma-X0-CCX1=CCX1-CX21-X0 = axiom ax-X0-CCX1=CCX1-CX21-X0
  lemma-X0-CCX2=CCX2-CX12-X0 : Rel ⊢ X0 • CCX2 === CCX2 • CX12 • X0
  lemma-X0-CCX2=CCX2-CX12-X0 = by-basis-change Swap12 Swap12 (lemma-X0-CCX1=CCX1-CX21-X0) 50 auto 
  lemma-X0-CCX0=CCX0-X0 : Rel ⊢ X0 • CCX0 === CCX0 • X0
  lemma-X0-CCX0=CCX0-X0 = axiom ax-X0-CCX0=CCX0-X0
  lemma-X1-CX02=CX02-X1 : Rel ⊢ X1 • CX02 === CX02 • X1
  lemma-X1-CX02=CX02-X1 = B01.by-basis-change Swap01 Swap01 (lemma-X0-CX12=CX12-X0) 50 auto
  lemma-X1-CX20=CX20-X1 : Rel ⊢ X1 • CX20 === CX20 • X1
  lemma-X1-CX20=CX20-X1 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-X1-CX02=CX02-X1) 50 auto
  lemma-X1-CX12=CX12-X1-X2 : Rel ⊢ X1 • CX12 === CX12 • X1 • X2
  lemma-X1-CX12=CX12-X1-X2 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-X0-CX01=CX01-X0-X1) 50 auto
  
  lemma-X1-CX10=CX10-X0-X1 : Rel ⊢ X1 • CX10 === CX10 • X0 • X1
  lemma-X1-CX10=CX10-X0-X1 =
    equational X1 • CX10
      by B01.by-basis-change Swap01 Swap01 (lemma-X0-CX01=CX01-X0-X1) 50 auto
    equals CX10 • X1 • X0
      by right axiom ax-X1-X0=X0-X1
    equals CX10 • X0 • X1
  
  lemma-X1-CX01=CX01-X1 : Rel ⊢ X1 • CX01 === CX01 • X1
  lemma-X1-CX01=CX01-X1 = B01.by-basis-change Swap01 Swap01 (lemma-X0-CX10=CX10-X0) 50 auto
  lemma-X1-CX21=CX21-X1 : Rel ⊢ X1 • CX21 === CX21 • X1
  lemma-X1-CX21=CX21-X1 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-X1-CX01=CX01-X1) 50 auto
  lemma-X1-CCX0=CCX0-CX20-X1 : Rel ⊢ X1 • CCX0 === CCX0 • CX20 • X1
  lemma-X1-CCX0=CCX0-CX20-X1 = B01.by-basis-change Swap01 Swap01 (lemma-X0-CCX1=CCX1-CX21-X0) 50 auto
  lemma-X1-CCX2=CCX2-CX02-X1 : Rel ⊢ X1 • CCX2 === CCX2 • CX02 • X1
  lemma-X1-CCX2=CCX2-CX02-X1 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-X1-CCX0=CCX0-CX20-X1) 50 auto
  lemma-X1-CCX1=CCX1-X1 : Rel ⊢ X1 • CCX1 === CCX1 • X1
  lemma-X1-CCX1=CCX1-X1 = B01.by-basis-change Swap01 Swap01 (lemma-X0-CCX0=CCX0-X0) 50 auto
  
  lemma-X2-CX02=CX02-X2 : Rel ⊢ X2 • CX02 === CX02 • X2
  lemma-X2-CX02=CX02-X2 = by-basis-change Swap12 Swap12 (lemma-X1-CX01=CX01-X1) 50 auto
  
  lemma-X2-CX20=CX20-X0-X2 : Rel ⊢ X2 • CX20 === CX20 • X0 • X2
  lemma-X2-CX20=CX20-X0-X2 = by-basis-change Swap12 Swap12 (lemma-X1-CX10=CX10-X0-X1) 50 auto
  lemma-X2-CX12=CX12-X2 : Rel ⊢ X2 • CX12 === CX12 • X2
  lemma-X2-CX12=CX12-X2 = B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (lemma-X1-CX01=CX01-X1) 50 auto
  
  lemma-X2-CX21=CX21-X1-X2 : Rel ⊢ X2 • CX21 === CX21 • X1 • X2
  lemma-X2-CX21=CX21-X1-X2 = B01.by-basis-change Swap01 Swap01 (lemma-X2-CX20=CX20-X0-X2) 50 auto
  lemma-X2-CX01=CX01-X2 : Rel ⊢ X2 • CX01 === CX01 • X2
  lemma-X2-CX01=CX01-X2 = by-basis-change Swap12 Swap12 (lemma-X1-CX02=CX02-X1) 50 auto
  lemma-X2-CX10=CX10-X2 : Rel ⊢ X2 • CX10 === CX10 • X2
  lemma-X2-CX10=CX10-X2 = B01.by-basis-change Swap01 Swap01 (lemma-X2-CX01=CX01-X2) 50 auto
  lemma-X2-CCX2=CCX2-X2 : Rel ⊢ X2 • CCX2 === CCX2 • X2
  lemma-X2-CCX2=CCX2-X2 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-X0-CCX0=CCX0-X0) 50 auto
  lemma-X2-CCX1=CCX1-CX01-X2 : Rel ⊢ X2 • CCX1 === CCX1 • CX01 • X2
  lemma-X2-CCX1=CCX1-CX01-X2 = by-basis-change Swap12 Swap12 (lemma-X1-CCX2=CCX2-CX02-X1) 50 auto
  lemma-X2-CCX0=CCX0-CX10-X2 : Rel ⊢ X2 • CCX0 === CCX0 • CX10 • X2
  lemma-X2-CCX0=CCX0-CX10-X2 = by-basis-change Swap12 Swap12 (lemma-X1-CCX0=CCX0-CX20-X1) 50 auto

  a2-step : Step-Function Gate Rel

  a2-step (X1-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ X1-gen ∷ xs , at-head (axiom ax-X1-X0=X0-X1))
  a2-step (X2-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-X0=X0-X2))
  a2-step (X2-gen ∷ X1-gen ∷ xs) = just (X1-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-X1=X1-X2))
  a2-step (X0-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ X0-gen ∷ X2-gen ∷ xs , at-head (lemma-X0-CX02=CX02-X0-X2))
  a2-step (X0-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ X0-gen ∷ xs , at-head (lemma-X0-CX20=CX20-X0))
  a2-step (X0-gen ∷ CX12-gen ∷ xs) = just (CX12-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CX12=CX12-X0))
  a2-step (X0-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ X0-gen ∷ xs , at-head (lemma-X0-CX21=CX21-X0))
  a2-step (X0-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CX10=CX10-X0))
  a2-step (X0-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ X0-gen ∷ X1-gen ∷ xs , at-head (axiom ax-X0-CX01=CX01-X0-X1))
  a2-step (X0-gen ∷ CCX2-gen ∷ xs) = just (CCX2-gen ∷ CX12-gen ∷ X0-gen ∷ xs , at-head (lemma-X0-CCX2=CCX2-CX12-X0))
  a2-step (X0-gen ∷ CCX1-gen ∷ xs) = just (CCX1-gen ∷ CX21-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CCX1=CCX1-CX21-X0))
  a2-step (X0-gen ∷ CCX0-gen ∷ xs) = just (CCX0-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CCX0=CCX0-X0))
  a2-step (X1-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ X1-gen ∷ xs , at-head (lemma-X1-CX02=CX02-X1))
  a2-step (X1-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ X1-gen ∷ xs , at-head (lemma-X1-CX20=CX20-X1))
  a2-step (X1-gen ∷ CX12-gen ∷ xs) = just (CX12-gen ∷ X1-gen ∷ X2-gen ∷ xs , at-head (lemma-X1-CX12=CX12-X1-X2))
  a2-step (X1-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ X1-gen ∷ xs , at-head (lemma-X1-CX21=CX21-X1))
  a2-step (X1-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ X0-gen ∷ X1-gen ∷ xs , at-head (lemma-X1-CX10=CX10-X0-X1))
  a2-step (X1-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ X1-gen ∷ xs , at-head (lemma-X1-CX01=CX01-X1))
  a2-step (X1-gen ∷ CCX2-gen ∷ xs) = just (CCX2-gen ∷ CX02-gen ∷ X1-gen ∷ xs , at-head (lemma-X1-CCX2=CCX2-CX02-X1))
  a2-step (X1-gen ∷ CCX1-gen ∷ xs) = just (CCX1-gen ∷ X1-gen ∷ xs , at-head (lemma-X1-CCX1=CCX1-X1))
  a2-step (X1-gen ∷ CCX0-gen ∷ xs) = just (CCX0-gen ∷ CX20-gen ∷ X1-gen ∷ xs , at-head (lemma-X1-CCX0=CCX0-CX20-X1))
  a2-step (X2-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CX02=CX02-X2))
  a2-step (X2-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ X0-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CX20=CX20-X0-X2))
  a2-step (X2-gen ∷ CX12-gen ∷ xs) = just (CX12-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CX12=CX12-X2))
  a2-step (X2-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ X1-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CX21=CX21-X1-X2))
  a2-step (X2-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CX10=CX10-X2))
  a2-step (X2-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CX01=CX01-X2))
  a2-step (X2-gen ∷ CCX2-gen ∷ xs) = just (CCX2-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CCX2=CCX2-X2))
  a2-step (X2-gen ∷ CCX1-gen ∷ xs) = just (CCX1-gen ∷ CX01-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CCX1=CCX1-CX01-X2))
  a2-step (X2-gen ∷ CCX0-gen ∷ xs) = just (CCX0-gen ∷ CX10-gen ∷ X2-gen ∷ xs , at-head (lemma-X2-CCX0=CCX0-CX10-X2))
  a2-step _ = nothing

  module SA2 = Rewriting.Step (step-cong (swap-step then a2-step))


  lemma-CCX1-CX02=CX02-CX01-CCX1 : Rel ⊢ CCX1 • CX02 === CX02 • CX01 • CCX1
  lemma-CCX1-CX02=CX02-CX01-CCX1 = by-basis-change Swap12 Swap12 (axiom ax-CCX2-CX01=CX01-CX02-CCX2) 50 auto
  lemma-CCX0-CX12=CX12-CX10-CCX0 : Rel ⊢ CCX0 • CX12 === CX12 • CX10 • CCX0
  lemma-CCX0-CX12=CX12-CX10-CCX0 = B01.by-basis-change Swap01 Swap01 (lemma-CCX1-CX02=CX02-CX01-CCX1) 50 auto


  lemma-CCX2-CX02=CX02-CCX2 : Rel ⊢ CCX2 • CX02 === CX02 • CCX2
  lemma-CCX2-CX02=CX02-CCX2 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CCX0-CX20=CX20-CCX0) 50 auto

  lemma-CCX2-CX10=CX10-CX12-CCX2 : Rel ⊢ CCX2 • CX10 === CX10 • CX12 • CCX2
  lemma-CCX2-CX10=CX10-CX12-CCX2 = B01.by-basis-change Swap01 Swap01 (axiom ax-CCX2-CX01=CX01-CX02-CCX2) 50 auto

  lemma-CCX1-CX20=CX20-CX21-CCX1 : Rel ⊢ CCX1 • CX20 === CX20 • CX21 • CCX1
  lemma-CCX1-CX20=CX20-CX21-CCX1 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CCX1-CX02=CX02-CX01-CCX1) 50 auto
  
  lemma-CCX0-CX21=CX21-CX20-CCX0 : Rel ⊢ CCX0 • CX21 === CX21 • CX20 • CCX0
  lemma-CCX0-CX21=CX21-CX20-CCX0 = by-basis-change Swap12 Swap12 (lemma-CCX0-CX12=CX12-CX10-CCX0) 50 auto



  lemma-CCX1-CX10=CX10-CCX0-CCX1-CCX0 : Rel ⊢ CCX1 • CX10 === CX10 • CCX0 • CCX1 • CCX0
  lemma-CCX1-CX10=CX10-CCX0-CCX1-CCX0 = B01.by-basis-change Swap01 Swap01 (axiom ax-CCX0-CX01=CX01-CCX1-CCX0-CCX1) 50 auto
  lemma-CCX2-CX21=CX21-CCX1-CCX2-CCX1 : Rel ⊢ CCX2 • CX21 === CX21 • CCX1 • CCX2 • CCX1
  lemma-CCX2-CX21=CX21-CCX1-CCX2-CCX1 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (axiom ax-CCX0-CX01=CX01-CCX1-CCX0-CCX1) 50 auto

  lemma-CX10-CX01-CX10=CX01-CX10-CX01 : Rel ⊢ CX10 • CX01 • CX10 === CX01 • CX10 • CX01
  lemma-CX10-CX01-CX10=CX01-CX10-CX01 =
    equational CX10 • CX01 • CX10
      by symm (B01.by-basis-change Swap01 Swap01 (axiom ax-Swap01=CX01-CX10-CX01) 50 auto)
    equals Swap01 
      by axiom ax-Swap01=CX01-CX10-CX01
    equals CX01 • CX10 • CX01


  lemma-CX20-CX02-CX20=CX02-CX20-CX02 : Rel ⊢ CX20 • CX02 • CX20 === CX02 • CX20 • CX02
  lemma-CX20-CX02-CX20=CX02-CX20-CX02 = by-basis-change (Swap12) (Swap12) (lemma-CX10-CX01-CX10=CX01-CX10-CX01) 50 auto
  lemma-CX21-CX12-CX21=CX12-CX21-CX12 : Rel ⊢ CX21 • CX12 • CX21 === CX12 • CX21 • CX12
  lemma-CX21-CX12-CX21=CX12-CX21-CX12 = B01.by-basis-change Swap01 Swap01 (lemma-CX20-CX02-CX20=CX02-CX20-CX02) 50 auto


  lemma-CX10-CX12=CX12-CX10 : Rel ⊢ CX10 • CX12 === CX12 • CX10
  lemma-CX10-CX12=CX12-CX10 = B01.by-basis-change Swap01 Swap01 (axiom ax-CX01-CX02=CX02-CX01) 50 auto



  lemma-CX20-CX10-CX21=CX21-CX10 : Rel ⊢ CX20 • CX10 • CX21 === CX21 • CX10
  lemma-CX20-CX10-CX21=CX21-CX10 =
    equational CX20 • CX10 • CX21
      by Order.general-rewrite 100 auto
    equals CX21 • (CX21 • CX20 • CX10) • CX21
      by right left symm (axiom ax-CX10-CX21=CX21-CX20-CX10)
    equals CX21 • (CX10 • CX21) • CX21
      by Order.general-rewrite 100 auto
    equals CX21 • CX10


  lemma-CX20-CX21-CX10=CX10-CX21 : Rel ⊢ CX20 • CX21 • CX10 === CX10 • CX21
  lemma-CX20-CX21-CX10=CX10-CX21 =
    equational CX20 • CX21 • CX10
      by general-assoc auto
    equals (CX20 • CX21) • CX10
      by left symm lemma-CX21-CX20=CX20-CX21
    equals (CX21 • CX20) • CX10
      by general-assoc auto
    equals CX21 • CX20 • CX10
      by symm (axiom ax-CX10-CX21=CX21-CX20-CX10)
    equals CX10 • CX21


  lemma-CX21-CX01-CX20=CX20-CX01 : Rel ⊢ CX21 • CX01 • CX20 === CX20 • CX01
  lemma-CX21-CX01-CX20=CX20-CX01 = B01.by-basis-change Swap01 Swap01 (lemma-CX20-CX10-CX21=CX21-CX10) 50 auto

  lemma-CX02-CX01-CX12=CX12-CX01 : Rel ⊢ CX02 • CX01 • CX12 === CX12 • CX01
  lemma-CX02-CX01-CX12=CX12-CX01 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CX20-CX21-CX10=CX10-CX21) 50 auto


  lemma-CX12-CX20-CX10=CX20-CX12 : Rel ⊢ CX12 • CX20 • CX10 === CX20 • CX12
  lemma-CX12-CX20-CX10=CX20-CX12 =
    equational CX12 • CX20 • CX10
      by right symm lemma-CX10-CX20=CX20-CX10
    equals CX12 • CX10 • CX20 
      by symm (by-basis-change Swap12 Swap12 (axiom ax-CX10-CX21=CX21-CX20-CX10) 100 auto) 
    equals CX20 • CX12

  lemma-CX02-CX21-CX01=CX21-CX02 : Rel ⊢ CX02 • CX21 • CX01 === CX21 • CX02
  lemma-CX02-CX21-CX01=CX21-CX02 = B01.by-basis-change Swap01 Swap01 (lemma-CX12-CX20-CX10=CX20-CX12) 50 auto


  lemma-CX21-CX02=CX02-CX21-CX01 : Rel ⊢ CX21 • CX02 === CX02 • CX21 • CX01
  lemma-CX21-CX02=CX02-CX21-CX01 =
    equational CX21 • CX02
      by B02.by-basis-change (Swap01 • Swap12) (Swap12 • Swap01) (axiom ax-CX10-CX21=CX21-CX20-CX10) 50 auto
    equals CX02 • CX01 • CX21
      by right axiom ax-CX01-CX21=CX21-CX01
    equals CX02 • CX21 • CX01


  lemma-CX21-CX02-CX01=CX02-CX21 : Rel ⊢ CX21 • CX02 • CX01 === CX02 • CX21
  lemma-CX21-CX02-CX01=CX02-CX21 =
    equational CX21 • CX02 • CX01
      by general-assoc auto
    equals (CX21 • CX02) • CX01
      by left lemma-CX21-CX02=CX02-CX21-CX01
    equals (CX02 • CX21 • CX01) • CX01
      by Order.general-rewrite 100 auto
    equals CX02 • CX21

  lemma-CX01-CX20-CX21=CX20-CX01 : Rel ⊢ CX01 • CX20 • CX21 === CX20 • CX01
  lemma-CX01-CX20-CX21=CX20-CX01 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CX21-CX02-CX01=CX02-CX21) 50 auto


  lemma-CX01-CX20=CX20-CX21-CX01 : Rel ⊢ CX01 • CX20 === CX20 • CX21 • CX01
  lemma-CX01-CX20=CX20-CX21-CX01 =
    equational CX01 • CX20
      by Order.general-rewrite 100 auto
    equals (CX01 • CX20 • CX21) • CX21
      by left lemma-CX01-CX20-CX21=CX20-CX01
    equals (CX20 • CX01) • CX21
      by assoc
    equals CX20 • CX01 • CX21
      by cong refl (axiom ax-CX01-CX21=CX21-CX01)
    equals CX20 • CX21 • CX01


  lemma-CX02-CX12-CX10=CX10-CX02 : Rel ⊢ CX02 • CX12 • CX10 === CX10 • CX02
  lemma-CX02-CX12-CX10=CX10-CX02 = symm (axiom ax-CX10-CX02=CX02-CX12-CX10)

  lemma-CX02-CX12-CX01=CX01-CX12 : Rel ⊢ CX02 • CX12 • CX01 === CX01 • CX12
  lemma-CX02-CX12-CX01=CX01-CX12 =
    equational CX02 • CX12 • CX01
      by symm assoc
    equals (CX02 • CX12) • CX01
      by left symm (lemma-CX12-CX02=CX02-CX12)
    equals (CX12 • CX02) • CX01
      by B01.by-basis-change Swap01 Swap01 (lemma-CX02-CX12-CX10=CX10-CX02) 50 auto
    equals CX01 • CX12


  lemma-CX10-CX02-CX12=CX02-CX10 : Rel ⊢ CX10 • CX02 • CX12 === CX02 • CX10
  lemma-CX10-CX02-CX12=CX02-CX10 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CX12-CX20-CX10=CX20-CX12) 50 auto


  lemma-Swap12-Swap01-Swap12=CX02-CX20-CX02 : Rel ⊢ Swap12 • Swap01 • Swap12 === CX02 • CX20 • CX02
  lemma-Swap12-Swap01-Swap12=CX02-CX20-CX02 =
    equational Swap12 • Swap01 • Swap12
      by right left axiom ax-Swap01=CX01-CX10-CX01
    equals Swap12 • (CX01 • CX10 • CX01) • Swap12
      by MvSwap.general-rewrite 100 auto
    equals CX02 • CX20 • CX02


  lemma-CX01-CX10-CX02-CX10-CX01=CX12 : Rel ⊢ CX01 • CX10 • CX02 • CX10 • CX01 === CX12
  lemma-CX01-CX10-CX02-CX10-CX01=CX12 =
    equational CX01 • CX10 • CX02 • CX10 • CX01
      by Order.general-rewrite 100 auto
    equals (CX01 • CX10 • CX01) • (CX01 • CX02) • CX10 • CX01
      by right left axiom ax-CX01-CX02=CX02-CX01
    equals (CX01 • CX10 • CX01) • (CX02 • CX01) • CX10 • CX01
      by general-assoc auto
    equals (CX01 • CX10 • CX01) • CX02 • (CX01 • CX10 • CX01)
      by cong (symm (axiom ax-Swap01=CX01-CX10-CX01)) (cong refl (symm (axiom ax-Swap01=CX01-CX10-CX01)))
    equals (Swap01) • CX02 • Swap01
      by MvSwap.general-rewrite 100 auto
    equals CX12
    
  lemma-CX02-CX20-CX12-CX20-CX02=CX10 : Rel ⊢ CX02 • CX20 • CX12 • CX20 • CX02 === CX10
  lemma-CX02-CX20-CX12-CX20-CX02=CX10 =
    equational CX02 • CX20 • CX12 • CX20 • CX02
      by Order.general-rewrite 100 auto
    equals (CX02 • CX20 • CX02) • (CX02 • CX12) • CX20 • CX02
      by right left symm lemma-CX12-CX02=CX02-CX12
    equals (CX02 • CX20 • CX02) • (CX12 • CX02) • CX20 • CX02
      by general-assoc auto
    equals (CX02 • CX20 • CX02) • CX12 • (CX02 • CX20 • CX02)
      by cong (symm lemma-Swap12-Swap01-Swap12=CX02-CX20-CX02) (cong refl (symm lemma-Swap12-Swap01-Swap12=CX02-CX20-CX02))
    equals (Swap12 • Swap01 • Swap12) • CX12 • (Swap12 • Swap01 • Swap12)
      by MvSwap.general-rewrite 100 auto
    equals CX10


  lemma-CCX0-CX02=CX02-CCX2-CCX0-CCX2 : Rel ⊢ CCX0 • CX02 === CX02 • CCX2 • CCX0 • CCX2
  lemma-CCX0-CX02=CX02-CCX2-CCX0-CCX2 = by-basis-change Swap12 Swap12 (axiom ax-CCX0-CX01=CX01-CCX1-CCX0-CCX1) 100 auto

  lemma-CCX0-CX02-CCX2=CX02-CCX2-CCX0 : Rel ⊢ CCX0 • CX02 • CCX2 === CX02 • CCX2 • CCX0
  lemma-CCX0-CX02-CCX2=CX02-CCX2-CCX0 =
    equational CCX0 • CX02 • CCX2
      by general-assoc auto
    equals (CCX0 • CX02) • CCX2
      by left lemma-CCX0-CX02=CX02-CCX2-CCX0-CCX2
    equals (CX02 • CCX2 • CCX0 • CCX2) • CCX2
      by Order.general-rewrite 100 auto
    equals CX02 • CCX2 • CCX0


  lemma-CX02-CX20-CX01-CX20-CX02=CX21 : Rel ⊢ CX02 • CX20 • CX01 • CX20 • CX02 === CX21
  lemma-CX02-CX20-CX01-CX20-CX02=CX21 = by-basis-change Swap12 Swap12 (lemma-CX01-CX10-CX02-CX10-CX01=CX12) 50 auto
  lemma-CX12-CX21-CX10-CX21-CX12=CX20 : Rel ⊢ CX12 • CX21 • CX10 • CX21 • CX12 === CX20
  lemma-CX12-CX21-CX10-CX21-CX12=CX20 = B01.by-basis-change Swap01 Swap01 (lemma-CX02-CX20-CX01-CX20-CX02=CX21) 50 auto

  lemma-CX12-CX21-CX02-CX21-CX12=CX01 : Rel ⊢ CX12 • CX21 • CX02 • CX21 • CX12 === CX01
  lemma-CX12-CX21-CX02-CX21-CX12=CX01 = B01.by-basis-change Swap01 Swap01 (lemma-CX02-CX20-CX12-CX20-CX02=CX10) 50 auto

  lemma-CCX2-CX20-CCX0=CX20-CCX0-CCX2 : Rel ⊢ CCX2 • CX20 • CCX0 === CX20 • CCX0 • CCX2
  lemma-CCX2-CX20-CCX0=CX20-CCX0-CCX2 = B02.by-basis-change (Swap12 • Swap01 • Swap12) (Swap12 • Swap01 • Swap12) (lemma-CCX0-CX02-CCX2=CX02-CCX2-CCX0) 50 auto
  lemma-CCX1-CX12-CCX2=CX12-CCX2-CCX1 : Rel ⊢ CCX1 • CX12 • CCX2 === CX12 • CCX2 • CCX1
  lemma-CCX1-CX12-CCX2=CX12-CCX2-CCX1 = B01.by-basis-change Swap01 Swap01 (lemma-CCX0-CX02-CCX2=CX02-CCX2-CCX0) 50 auto


  
  lemma-CCX0-CCX2-CCX0=CCX2-CCX0-CCX2 : Rel ⊢ CCX0 • CCX2 • CCX0 === CCX2 • CCX0 • CCX2
  lemma-CCX0-CCX2-CCX0=CCX2-CCX0-CCX2 = by-basis-change Swap12 Swap12 (axiom ax-CCX0-CCX1-CCX0=CCX1-CCX0-CCX1) 50 auto
  lemma-CCX1-CCX2-CCX1=CCX2-CCX1-CCX2 : Rel ⊢ CCX1 • CCX2 • CCX1 === CCX2 • CCX1 • CCX2
  lemma-CCX1-CCX2-CCX1=CCX2-CCX1-CCX2 = B01.by-basis-change Swap01 Swap01 (lemma-CCX0-CCX2-CCX0=CCX2-CCX0-CCX2) 50 auto


  lemma-CCX1-CCX2-CCX0-CCX2=CCX2-CCX0-CCX2-CCX1 : Rel ⊢ CCX1 • CCX2 • CCX0 • CCX2 === CCX2 • CCX0 • CCX2 • CCX1
  lemma-CCX1-CCX2-CCX0-CCX2=CCX2-CCX0-CCX2-CCX1 = B01.by-basis-change Swap01 Swap01 (axiom ax-CCX0-CCX2-CCX1-CCX2=CCX2-CCX1-CCX2-CCX0) 50 auto
  lemma-CCX2-CCX1-CCX0-CCX1=CCX1-CCX0-CCX1-CCX2 : Rel ⊢ CCX2 • CCX1 • CCX0 • CCX1 === CCX1 • CCX0 • CCX1 • CCX2
  lemma-CCX2-CCX1-CCX0-CCX1=CCX1-CCX0-CCX1-CCX2 = by-basis-change Swap12 Swap12 (lemma-CCX1-CCX2-CCX0-CCX2=CCX2-CCX0-CCX2-CCX1) 50 auto



  lemma-CX10-CX01-CX10=Swap01 : Rel ⊢ CX10 • CX01 • CX10 === Swap01
  lemma-CX10-CX01-CX10=Swap01 =
    equational CX10 • CX01 • CX10
      by lemma-CX10-CX01-CX10=CX01-CX10-CX01
    equals CX01 • CX10 • CX01
      by symm (axiom ax-Swap01=CX01-CX10-CX01)
    equals Swap01


  lemma-CCX1-CX10-CX01=CX10-CX01-CCX0 : Rel ⊢ CCX1 • CX10 • CX01 === CX10 • CX01 • CCX0
  lemma-CCX1-CX10-CX01=CX10-CX01-CCX0 =
    equational CCX1 • CX10 • CX01
      by Order.general-rewrite 100 auto
    equals CCX1 • (CX10 • CX01 • CX10) • CX10
      by right left lemma-CX10-CX01-CX10=CX01-CX10-CX01
    equals CCX1 • (CX01 • CX10 • CX01) • CX10
      by right left symm (axiom ax-Swap01=CX01-CX10-CX01)
    equals CCX1 • (Swap01) • CX10
      by symm assoc
    equals (CCX1 • Swap01) • CX10
      by symm (cong (axiom ax-Swap01-CCX0=CCX1-Swap01) refl)
    equals (Swap01 • CCX0) • CX10
      by assoc
    equals Swap01 • CCX0 • CX10
      by right axiom ax-CCX0-CX10=CX10-CCX0
    equals Swap01 • CX10 • CCX0
      by symm (left lemma-CX10-CX01-CX10=Swap01)
    equals (CX10 • CX01 • CX10) • CX10 • CCX0
      by Order.general-rewrite 100 auto
    equals CX10 • CX01 • CCX0


  lemma-CCX2-CX20-CX02=CX20-CX02-CCX0 : Rel ⊢ CCX2 • CX20 • CX02 === CX20 • CX02 • CCX0
  lemma-CCX2-CX20-CX02=CX20-CX02-CCX0 = by-basis-change Swap12 Swap12 (lemma-CCX1-CX10-CX01=CX10-CX01-CCX0) 100 auto




  lemma-CX21-CX02-CX20-CX02=CX02-CX20-CX02-CX01 : Rel ⊢ CX21 • CX02 • CX20 • CX02 === CX02 • CX20 • CX02 • CX01
  lemma-CX21-CX02-CX20-CX02=CX02-CX20-CX02-CX01 =
    equational CX21 • CX02 • CX20 • CX02
      by right symm lemma-Swap12-Swap01-Swap12=CX02-CX20-CX02
    equals CX21 • Swap12 • Swap01 • Swap12
      by MvSwap.general-rewrite 100 auto
    equals (Swap12 • Swap01 • Swap12) • CX01
      by left lemma-Swap12-Swap01-Swap12=CX02-CX20-CX02
    equals (CX02 • CX20 • CX02) • CX01
      by general-assoc auto
    equals CX02 • CX20 • CX02 • CX01


  lemma-CX12-CX10-CX02=CX02-CX10 : Rel ⊢ CX12 • CX10 • CX02 === CX02 • CX10
  lemma-CX12-CX10-CX02=CX02-CX10 =
    equational CX12 • CX10 • CX02
      by right axiom ax-CX10-CX02=CX02-CX12-CX10
    equals CX12 • CX02 • CX12 • CX10
      by general-assoc auto
    equals (CX12 • CX02) • CX12 • CX10
      by left lemma-CX12-CX02=CX02-CX12
    equals (CX02 • CX12) • CX12 • CX10
      by Order.general-rewrite 100 auto
    equals CX02 • CX10



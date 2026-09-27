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
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∨_)
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
open import Examples.Groups.Clifford+CS-3qubit.Step4.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8

module Examples.Groups.Clifford+CS-3qubit.Step4.S8D where

  lemma-K0^4=ε : Rel ⊢ K0 ^ 4 === iI • iI
  lemma-K0^4=ε =
    equational K0 • K0 • K0 • K0
            by in-context 0 2 auto (axiom ax-K0-K0=iI-iI-iI)
        equals iI • iI • iI • K0 • K0
            by in-context 3 2 auto (axiom ax-K0-K0=iI-iI-iI)
        equals iI • iI • iI • iI • iI • iI
            by in-context 0 4 auto (axiom ax-iI-iI-iI-iI=ε)
        equals iI • iI

  lemma-K0^8=ε : Rel ⊢ K0 ^ 8 === ε
  lemma-K0^8=ε =
    equational K0 • K0 • K0 • K0 • K0 • K0 • K0 • K0
            by in-context 0 4 auto lemma-K0^4=ε
        equals iI • iI • K0 • K0 • K0 • K0
            by in-context 2 4 auto lemma-K0^4=ε
        equals iI • iI • iI • iI
            by in-context 0 4 auto (axiom ax-iI-iI-iI-iI=ε)
        equals ε

  lemma-CK10^4=ε : Rel ⊢ CK10 ^ 4 === S1 • S1
  lemma-CK10^4=ε =
    equational CK10 • CK10 • CK10 • CK10
            by in-context 0 2 auto (axiom ax-CK10-CK10=S1-S1-S1)
        equals S1 • S1 • S1 • CK10 • CK10
            by in-context 3 2 auto (axiom ax-CK10-CK10=S1-S1-S1)
        equals S1 • S1 • S1 • S1 • S1 • S1
            by in-context 0 4 auto (axiom ax-S1-S1-S1-S1=ε)
        equals S1 • S1

  lemma-CK10^8=ε : Rel ⊢ CK10 ^ 8 === ε
  lemma-CK10^8=ε =
    equational CK10 • CK10 • CK10 • CK10 • CK10 • CK10 • CK10 • CK10
            by in-context 0 4 auto lemma-CK10^4=ε
        equals S1 • S1 • CK10 • CK10 • CK10 • CK10
            by in-context 2 4 auto lemma-CK10^4=ε
        equals S1 • S1 • S1 • S1
            by in-context 0 4 auto (axiom ax-S1-S1-S1-S1=ε)
        equals ε

  lemma-CK20^4=ε : Rel ⊢ CK20 ^ 4 === S2 • S2
  lemma-CK20^4=ε =
    equational CK20 • CK20 • CK20 • CK20
            by in-context 0 2 auto (axiom ax-CK20-CK20=S2-S2-S2)
        equals S2 • S2 • S2 • CK20 • CK20
            by in-context 3 2 auto (axiom ax-CK20-CK20=S2-S2-S2)
        equals S2 • S2 • S2 • S2 • S2 • S2
            by in-context 0 4 auto (axiom ax-S2-S2-S2-S2=ε)
        equals S2 • S2

  lemma-CK20^8=ε : Rel ⊢ CK20 ^ 8 === ε
  lemma-CK20^8=ε =
    equational CK20 • CK20 • CK20 • CK20 • CK20 • CK20 • CK20 • CK20
            by in-context 0 4 auto lemma-CK20^4=ε
        equals S2 • S2 • CK20 • CK20 • CK20 • CK20
            by in-context 2 4 auto lemma-CK20^4=ε
        equals S2 • S2 • S2 • S2
            by in-context 0 4 auto (axiom ax-S2-S2-S2-S2=ε)
        equals ε


  lemma-CCK'^6=ε : Rel ⊢ CCK' ^ 6 === ε
  lemma-CCK'^6=ε =
    equational CCK' • CCK' • CCK' • CCK' • CCK' • CCK'
            by in-context 0 3 auto (axiom ax-CCK'-CCK'-CCK'=CS12-CS12)
        equals CS12 • CS12 • CCK' • CCK' • CCK'
            by in-context 2 3 auto (axiom ax-CCK'-CCK'-CCK'=CS12-CS12)
        equals CS12 • CS12 • CS12 • CS12
            by in-context 0 4 auto (axiom ax-CS12-CS12-CS12-CS12=ε)
        equals ε

  lemma-K0-iI-K0=ε : Rel ⊢ (K0 • iI) • K0 === ε
  lemma-K0-iI-K0=ε =
    equational (K0 • iI) • K0
            by left symm (axiom ax-iI-K0=K0-iI)
        equals (iI • K0) • K0
            by assoc
        equals iI • K0 • K0
            by right axiom ax-K0-K0=iI-iI-iI
        equals iI • iI • iI • iI
            by axiom ax-iI-iI-iI-iI=ε
        equals ε

  lemma-iI-K1=K1-iI : Rel ⊢ iI • K1 === K1 • iI
  lemma-iI-K1=K1-iI =
    equational iI • K1
      by right axiom ax-K1=Swap01-K0-Swap01
    equals iI • (Swap01 • K0 • Swap01)
      by symm assoc
    equals (iI • Swap01) • K0 • Swap01
      by left axiom ax-iI-Swap01=Swap01-iI
    equals (Swap01 • iI) • K0 • Swap01
      by general-assoc auto
    equals Swap01 • (iI • K0) • Swap01
      by right left axiom ax-iI-K0=K0-iI
    equals Swap01 • (K0 • iI) • Swap01
      by right assoc
    equals Swap01 • K0 • (iI • Swap01)
      by right right axiom ax-iI-Swap01=Swap01-iI
    equals Swap01 • K0 • (Swap01 • iI)
      by general-assoc auto
    equals (Swap01 • K0 • Swap01) • iI
      by left symm (axiom ax-K1=Swap01-K0-Swap01)
    equals K1 • iI

  lemma-iI-K2=K2-iI : Rel ⊢ iI • K2 === K2 • iI
  lemma-iI-K2=K2-iI =
    equational iI • K2
      by right axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12
    equals iI • (Swap12 • Swap01 • K0 • Swap01 • Swap12)
      by general-assoc auto
    equals (iI • Swap12) • (Swap01 • K0 • Swap01) • Swap12
      by cong (axiom ax-iI-Swap12=Swap12-iI) (left symm (axiom ax-K1=Swap01-K0-Swap01))
    equals (Swap12 • iI) • K1 • Swap12
      by general-assoc auto
    equals Swap12 • (iI • K1) • Swap12
      by right left lemma-iI-K1=K1-iI
    equals Swap12 • (K1 • iI) • Swap12
      by general-assoc auto
    equals Swap12 • K1 • (iI • Swap12)
      by right right axiom ax-Swap12-iI=iI-Swap12 reversed
    equals Swap12 • K1 • (Swap12 •  iI)
      by right left axiom ax-K1=Swap01-K0-Swap01
    equals Swap12 • (Swap01 • K0 • Swap01) • (Swap12 • iI)
      by general-assoc auto
    equals (Swap12 • Swap01 • K0 • Swap01 • Swap12) • iI
      by left symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals K2 • iI


  mvI-step : Step-Function Gate Rel
  mvI-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  mvI-step (iI-gen ∷ CCX0-gen ∷ xs) = just (CCX0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCX0=CCX0-iI))
  mvI-step (iI-gen ∷ CCX1-gen ∷ xs) = just (CCX1-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCX1=CCX1-iI))
  mvI-step (iI-gen ∷ CCX2-gen ∷ xs) = just (CCX2-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCX2=CCX2-iI))
  mvI-step (iI-gen ∷ CX01-gen ∷ xs) = just (CX01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CX01=CX01-iI))
  mvI-step (iI-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CX10=CX10-iI))
  mvI-step (iI-gen ∷ CX12-gen ∷ xs) = just (CX12-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CX12=CX12-iI))
  mvI-step (iI-gen ∷ CX21-gen ∷ xs) = just (CX21-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CX21=CX21-iI))
  mvI-step (iI-gen ∷ CX02-gen ∷ xs) = just (CX02-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CX02=CX02-iI))
  mvI-step (iI-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CX20=CX20-iI))
  mvI-step (iI-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-X0=X0-iI))
  mvI-step (iI-gen ∷ X1-gen ∷ xs) = just (X1-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-X1=X1-iI))
  mvI-step (iI-gen ∷ X2-gen ∷ xs) = just (X2-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-X2=X2-iI))
  mvI-step (iI-gen ∷ Swap01-gen ∷ xs) = just (Swap01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-Swap01=Swap01-iI))
  mvI-step (iI-gen ∷ Swap12-gen ∷ xs) = just (Swap12-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-Swap12=Swap12-iI))
  mvI-step (iI-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S0=S0-iI))
  mvI-step (iI-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S1=S1-iI))
  mvI-step (iI-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S2=S2-iI))
  mvI-step (iI-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS01=CS01-iI))
  mvI-step (iI-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS12=CS12-iI))
  mvI-step (iI-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS02=CS02-iI))
  mvI-step (iI-gen ∷ CCZ-gen ∷ xs) = just (CCZ-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCZ=CCZ-iI))
  mvI-step (iI-gen ∷ CCK'-gen ∷ xs) = just (CCK'-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCK'=CCK'-iI))
  mvI-step (iI-gen ∷ CK10-gen ∷ xs) = just (CK10-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CK10=CK10-iI))
  mvI-step (iI-gen ∷ CK20-gen ∷ xs) = just (CK20-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CK20=CK20-iI))
  mvI-step (iI-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-K0=K0-iI))
  mvI-step (iI-gen ∷ K1-gen ∷ xs) = just (K1-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-K1=K1-iI))
  mvI-step (iI-gen ∷ K2-gen ∷ xs) = just (K2-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-K2=K2-iI))
  mvI-step _ = nothing

  module mvI = Rewriting.Step (step-cong mvI-step)


  lemma-K1-K1=iI-iI-iI : Rel ⊢ K1 • K1 === iI • iI • iI
  lemma-K1-K1=iI-iI-iI =
    equational K1 • K1
      by cong (axiom ax-K1=Swap01-K0-Swap01) (axiom ax-K1=Swap01-K0-Swap01)
    equals (Swap01 • K0 • Swap01) • Swap01 • K0 • Swap01
      by ListNF.listnfeq' nf-s7e auto
    equals Swap01 • (K0 • K0) • Swap01
      by right left axiom ax-K0-K0=iI-iI-iI
    equals Swap01 • (iI ^ 3) • Swap01
      by mvI.general-rewrite 100 auto
    equals (Swap01 • Swap01) • (iI ^ 3)
      by ListNF.listnfeq' nf-s7e auto
    equals iI • iI • iI

  lemma-K2-K2=iI-iI-iI : Rel ⊢ K2 • K2 === iI • iI • iI
  lemma-K2-K2=iI-iI-iI =
    equational K2 • K2
      by cong (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12) (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals (Swap12 • Swap01 • K0 • Swap01 • Swap12) • (Swap12 • Swap01 • K0 • Swap01 • Swap12)
      by ListNF.listnfeq' nf-s7e auto
    equals Swap12 • ((Swap01 • K0 • Swap01) • (Swap01 • K0 • Swap01)) • Swap12
      by right left cong (symm (axiom ax-K1=Swap01-K0-Swap01)) (symm (axiom ax-K1=Swap01-K0-Swap01))
    equals Swap12 • (K1 • K1) • Swap12
      by right left lemma-K1-K1=iI-iI-iI
    equals Swap12 • (iI ^ 3) • Swap12
      by mvI.general-rewrite 100 auto
    equals Swap12 • Swap12 • (iI ^ 3)
      by ListNF.listnfeq' nf-s7e auto
    equals iI • iI • iI


  lemma-K1-iI-K1=ε : Rel ⊢ (K1 • iI) • K1 === ε
  lemma-K1-iI-K1=ε =
    equational (K1 • iI) • K1
            by left symm (lemma-iI-K1=K1-iI)
        equals (iI • K1) • K1
            by assoc
        equals iI • K1 • K1
            by right lemma-K1-K1=iI-iI-iI
        equals iI • iI • iI • iI
            by axiom ax-iI-iI-iI-iI=ε
        equals ε
        
  lemma-K2-iI-K2=ε : Rel ⊢ (K2 • iI) • K2 === ε
  lemma-K2-iI-K2=ε =
    equational (K2 • iI) • K2
            by left symm (lemma-iI-K2=K2-iI)
        equals (iI • K2) • K2
            by assoc
        equals iI • K2 • K2
            by right lemma-K2-K2=iI-iI-iI
        equals iI • iI • iI • iI
            by axiom ax-iI-iI-iI-iI=ε
        equals ε


  lemma-CK10-S1-CK10=ε : Rel ⊢ (CK10 • S1) • CK10 === ε
  lemma-CK10-S1-CK10=ε =
    equational (CK10 • S1) • CK10
            by left symm (axiom ax-S1-CK10=CK10-S1)
        equals (S1 • CK10) • CK10
            by assoc
        equals S1 • CK10 • CK10
            by right axiom ax-CK10-CK10=S1-S1-S1
        equals S1 • S1 • S1 • S1
            by axiom ax-S1-S1-S1-S1=ε
        equals ε

  lemma-CK20-S2-CK20=ε : Rel ⊢ (CK20 • S2) • CK20 === ε
  lemma-CK20-S2-CK20=ε =
    equational (CK20 • S2) • CK20
            by left symm (axiom ax-S2-CK20=CK20-S2)
        equals (S2 • CK20) • CK20
            by assoc
        equals S2 • CK20 • CK20
            by right axiom ax-CK20-CK20=S2-S2-S2
        equals S2 • S2 • S2 • S2
            by axiom ax-S2-S2-S2-S2=ε
        equals ε

  lemma-CCK'-CCK'-CS12-CS12-CCK'=ε : Rel ⊢ CCK' • CCK' • CS12 • CS12 • CCK' === ε
  lemma-CCK'-CCK'-CS12-CS12-CCK'=ε =
    equational CCK' • CCK' • CS12 • CS12 • CCK'
            by in-context 3 2 auto (axiom ax-CS12-CCK'=CCK'-CS12)
        equals CCK' • CCK' • CS12 • CCK' • CS12
            by in-context 2 2 auto (axiom ax-CS12-CCK'=CCK'-CS12)
        equals CCK' • CCK' • CCK' • CS12 • CS12
            by in-context 0 3 auto (axiom ax-CCK'-CCK'-CCK'=CS12-CS12)
        equals CS12 • CS12 • CS12 • CS12
            by axiom ax-CS12-CS12-CS12-CS12=ε
        equals ε

  group-like : Grouplike Rel
  group-like CCX0-gen = CCX0 , axiom ax-CCX0-CCX0=ε
  group-like CCX1-gen = CCX1 , axiom ax-CCX1-CCX1=ε
  group-like CCX2-gen = CCX2 , axiom ax-CCX2-CCX2=ε
  group-like CX01-gen = CX01 , axiom ax-CX01-CX01=ε
  group-like CX10-gen = CX10 , axiom ax-CX10-CX10=ε
  group-like CX12-gen = CX12 , axiom ax-CX12-CX12=ε
  group-like CX21-gen = CX21 , axiom ax-CX21-CX21=ε
  group-like CX02-gen = CX02 , axiom ax-CX02-CX02=ε
  group-like CX20-gen = CX20 , axiom ax-CX20-CX20=ε
  group-like X0-gen = X0 , axiom ax-X0-X0=ε
  group-like X1-gen = X1 , axiom ax-X1-X1=ε
  group-like X2-gen = X2 , axiom ax-X2-X2=ε
  group-like Swap01-gen = Swap01 , axiom ax-Swap01-Swap01=ε
  group-like Swap12-gen = Swap12 , axiom ax-Swap12-Swap12=ε
  group-like S0-gen = S0 • S0 • S0 , up-to-assoc auto (axiom ax-S0-S0-S0-S0=ε)
  group-like S1-gen = S1 • S1 • S1 , up-to-assoc auto (axiom ax-S1-S1-S1-S1=ε)
  group-like S2-gen = S2 • S2 • S2 , up-to-assoc auto (axiom ax-S2-S2-S2-S2=ε)
  group-like CS01-gen = CS01 • CS01 • CS01 , up-to-assoc auto (axiom ax-CS01-CS01-CS01-CS01=ε)
  group-like CS12-gen = CS12 • CS12 • CS12 , up-to-assoc auto (axiom ax-CS12-CS12-CS12-CS12=ε)
  group-like CS02-gen = CS02 • CS02 • CS02 , up-to-assoc auto (axiom ax-CS02-CS02-CS02-CS02=ε)
  group-like CCZ-gen = CCZ , axiom ax-CCZ-CCZ=ε
  group-like iI-gen = iI • iI • iI , up-to-assoc auto (axiom ax-iI-iI-iI-iI=ε)
  group-like K0-gen = K0 • iI , up-to-assoc auto (lemma-K0-iI-K0=ε)
  group-like K1-gen = K1 • iI , up-to-assoc auto (lemma-K1-iI-K1=ε)
  group-like K2-gen = K2 • iI , up-to-assoc auto (lemma-K2-iI-K2=ε)
  group-like CK10-gen = CK10 • S1 , up-to-assoc auto (lemma-CK10-S1-CK10=ε)
  group-like CK20-gen = CK20 • S2 , up-to-assoc auto (lemma-CK20-S2-CK20=ε)
  group-like CCK'-gen = CCK' • CCK' • CS12 • CS12 , up-to-assoc auto (lemma-CCK'-CCK'-CS12-CS12-CCK'=ε)

  d-step : Step-Function Gate Rel

  d-step (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom ax-S0-S0-S0-S0=ε))
  d-step (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ xs) = just (xs , at-head (axiom ax-S1-S1-S1-S1=ε))
  d-step (S2-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ xs) = just (xs , at-head (axiom ax-S2-S2-S2-S2=ε))
  d-step (CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs) = just (xs , at-head (axiom ax-CS01-CS01-CS01-CS01=ε))
  d-step (CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ xs) = just (xs , at-head (axiom ax-CS02-CS02-CS02-CS02=ε))
  d-step (CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ xs) = just (xs , at-head (axiom ax-CS12-CS12-CS12-CS12=ε))
  d-step (CCZ-gen ∷ CCZ-gen ∷ xs) = just (xs , at-head (axiom ax-CCZ-CCZ=ε))
  d-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  d-step (S1-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-S0=S0-S1))
  d-step (S2-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-S0=S0-S2))
  d-step (S2-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-S1=S1-S2))
  d-step (CS01-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-S0=S0-CS01))
  d-step (CS01-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-S1=S1-CS01))
  d-step (CS01-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CS01-S2=S2-CS01))
  d-step (CS12-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-S0=S0-CS12))
  d-step (CS12-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-S1=S1-CS12))
  d-step (CS12-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-S2=S2-CS12))
  d-step (CS12-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-CS01=CS01-CS12))
  d-step (CS12-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-CS02=CS02-CS12))
  d-step (CS02-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS02-gen ∷ xs , at-head (axiom ax-CS02-S0=S0-CS02))
  d-step (CS02-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CS02-gen ∷ xs , at-head (axiom ax-CS02-S1=S1-CS02))
  d-step (CS02-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CS02-gen ∷ xs , at-head (axiom ax-CS02-S2=S2-CS02))
  d-step (CS02-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CS02-gen ∷ xs , at-head (axiom ax-CS02-CS01=CS01-CS02))
  d-step (CCZ-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCZ-S0=S0-CCZ))
  d-step (CCZ-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCZ-S1=S1-CCZ))
  d-step (CCZ-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCZ-S2=S2-CCZ))
  d-step (CCZ-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCZ-CS01=CS01-CCZ))
  d-step (CCZ-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCZ-CS12=CS12-CCZ))
  d-step (CCZ-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCZ-CS02=CS02-CCZ))
  d-step (iI-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S0=S0-iI))
  d-step (iI-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S1=S1-iI))
  d-step (iI-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-S2=S2-iI))
  d-step (iI-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS01=CS01-iI))
  d-step (iI-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS12=CS12-iI))
  d-step (iI-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CS02=CS02-iI))
  d-step (iI-gen ∷ CCZ-gen ∷ xs) = just (CCZ-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-CCZ=CCZ-iI))
  -- Catch-all
  d-step _ = nothing

  module Diag = Rewriting.Step (step-cong d-step)

  pd-conj : let X = Gate in let Γ = Rel in (h n : X) -> Maybe (∃ λ (n' : List X) -> Γ ⊢ [ h ]ʷ • [ n ]ʷ === word-of-list n' • [ h ]ʷ)
  pd-conj Swap01-gen S0-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-Swap01-S0=S1-Swap01) )
  pd-conj Swap01-gen S1-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-Swap01-S1=S0-Swap01) )
  pd-conj Swap01-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-Swap01-S2=S2-Swap01) )
  pd-conj Swap01-gen CS01-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-Swap01-CS01=CS01-Swap01) )
  pd-conj Swap01-gen CS02-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-Swap01-CS02=CS12-Swap01) )
  pd-conj Swap01-gen CS12-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-Swap01-CS12=CS02-Swap01) )
  pd-conj Swap01-gen CCZ-gen = just ( CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-Swap01-CCZ=CCZ-Swap01) )
  pd-conj Swap01-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-Swap01-iI=iI-Swap01) )
  pd-conj CX01-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-S0=S0-CX01) )
  pd-conj CX01-gen S1-gen = just ( S0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-S1=S0-S1-CS01-CS01-CX01) )
  pd-conj CX01-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-S2=S2-CX01) )
  pd-conj CX01-gen CS01-gen = just ( S0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CS01=S0-CS01-CS01-CS01-CX01) )
  pd-conj CX01-gen CS02-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CS02=CS02-CX01) )
  pd-conj CX01-gen CS12-gen = just ( CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CS12=CS02-CS12-CCZ-CX01) )
  pd-conj CX01-gen CCZ-gen = just ( CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-CCZ=CS02-CS02-CCZ-CX01) )
  pd-conj CX01-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX01-iI=iI-CX01) )
  pd-conj CX02-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-S0=S0-CX02) )
  pd-conj CX02-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-S1=S1-CX02) )
  pd-conj CX02-gen S2-gen = just ( S0-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-S2=S0-S2-CS02-CS02-CX02) )
  pd-conj CX02-gen CS01-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-CS01=CS01-CX02) )
  pd-conj CX02-gen CS02-gen = just ( S0-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-CS02=S0-CS02-CS02-CS02-CX02) )
  pd-conj CX02-gen CS12-gen = just ( CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-CS12=CS01-CS12-CCZ-CX02) )
  pd-conj CX02-gen CCZ-gen = just ( CS01-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-CCZ=CS01-CS01-CCZ-CX02) )
  pd-conj CX02-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX02-iI=iI-CX02) )
  pd-conj CCX1-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-S0=S0-CCX1) )
  pd-conj CCX1-gen S1-gen = just ( S1-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-S1=S1-CS02-CCZ-CCX1) )
  pd-conj CCX1-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-S2=S2-CCX1) )
  pd-conj CCX1-gen CS01-gen = just ( CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CS01=CS01-CS02-CCZ-CCX1) )
  pd-conj CCX1-gen CS02-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CS02=CS02-CCX1) )
  pd-conj CCX1-gen CS12-gen = just ( CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CS12=CS02-CS12-CCZ-CCX1) )
  pd-conj CCX1-gen CCZ-gen = just ( CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-CCZ=CS02-CS02-CCZ-CCX1) )
  pd-conj CCX1-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CCX1-iI=iI-CCX1) )
  pd-conj CCX2-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-S0=S0-CCX2) )
  pd-conj CCX2-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-S1=S1-CCX2) )
  pd-conj CCX2-gen S2-gen = just ( S2-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-S2=S2-CS01-CCZ-CCX2) )
  pd-conj CCX2-gen CS01-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CS01=CS01-CCX2) )
  pd-conj CCX2-gen CS02-gen = just ( CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CS02=CS01-CS02-CCZ-CCX2) )
  pd-conj CCX2-gen CS12-gen = just ( CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CS12=CS01-CS12-CCZ-CCX2) )
  pd-conj CCX2-gen CCZ-gen = just ( CS01-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-CCZ=CS01-CS01-CCZ-CCX2) )
  pd-conj CCX2-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CCX2-iI=iI-CCX2) )
  pd-conj X1-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-X1-S0=S0-X1) )
  pd-conj X1-gen S1-gen = just ( S1-gen ∷ S1-gen ∷ S1-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X1-S1=S1-S1-S1-iI-X1) )
  pd-conj X1-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-X1-S2=S2-X1) )
  pd-conj X1-gen CS01-gen = just ( S0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CS01=S0-CS01-CS01-CS01-X1) )
  pd-conj X1-gen CS02-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CS02=CS02-X1) )
  pd-conj X1-gen CS12-gen = just ( S2-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CS12=S2-CS12-CS12-CS12-X1) )
  pd-conj X1-gen CCZ-gen = just ( CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CCZ=CS02-CS02-CCZ-X1) )
  pd-conj X1-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-X1-iI=iI-X1) )
  pd-conj X2-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-X2-S0=S0-X2) )
  pd-conj X2-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-X2-S1=S1-X2) )
  pd-conj X2-gen S2-gen = just ( S2-gen ∷ S2-gen ∷ S2-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X2-S2=S2-S2-S2-iI-X2) )
  pd-conj X2-gen CS01-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CS01=CS01-X2) )
  pd-conj X2-gen CS02-gen = just ( S0-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CS02=S0-CS02-CS02-CS02-X2) )
  pd-conj X2-gen CS12-gen = just ( S1-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CS12=S1-CS12-CS12-CS12-X2) )
  pd-conj X2-gen CCZ-gen = just ( CS01-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CCZ=CS01-CS01-CCZ-X2) )
  pd-conj X2-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-X2-iI=iI-X2) )
  pd-conj CX12-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-S0=S0-CX12) )
  pd-conj CX12-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-S1=S1-CX12) )
  pd-conj CX12-gen S2-gen = just ( S1-gen ∷ S2-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-S2=S1-S2-CS12-CS12-CX12) )
  pd-conj CX12-gen CS01-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CS01=CS01-CX12) )
  pd-conj CX12-gen CS02-gen = just ( CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CS02=CS01-CS02-CCZ-CX12) )
  pd-conj CX12-gen CS12-gen = just ( S1-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CS12=S1-CS12-CS12-CS12-CX12) )
  pd-conj CX12-gen CCZ-gen = just ( CS01-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CCZ=CS01-CS01-CCZ-CX12) )
  pd-conj CX12-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-iI=iI-CX12) )
  pd-conj CX21-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-S0=S0-CX21) )
  pd-conj CX21-gen S1-gen = just ( S1-gen ∷ S2-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-S1=S1-S2-CS12-CS12-CX21) )
  pd-conj CX21-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-S2=S2-CX21) )
  pd-conj CX21-gen CS01-gen = just ( CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CS01=CS01-CS02-CCZ-CX21) )
  pd-conj CX21-gen CS02-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CS02=CS02-CX21) )
  pd-conj CX21-gen CS12-gen = just ( S2-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CS12=S2-CS12-CS12-CS12-CX21) )
  pd-conj CX21-gen CCZ-gen = just ( CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CCZ=CS02-CS02-CCZ-CX21) )
  pd-conj CX21-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-iI=iI-CX21) )
  pd-conj Swap12-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-S0=S0-Swap12) )
  pd-conj Swap12-gen S1-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-S1=S2-Swap12) )
  pd-conj Swap12-gen S2-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-S2=S1-Swap12) )
  pd-conj Swap12-gen CS01-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CS01=CS02-Swap12) )
  pd-conj Swap12-gen CS02-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CS02=CS01-Swap12) )
  pd-conj Swap12-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CS12=CS12-Swap12) )
  pd-conj Swap12-gen CCZ-gen = just ( CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CCZ=CCZ-Swap12) )
  pd-conj Swap12-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-iI=iI-Swap12) )
  pd-conj X0-gen S0-gen = just ( S0-gen ∷ S0-gen ∷ S0-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S0=S0-S0-S0-iI-X0) )
  pd-conj X0-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S1=S1-X0) )
  pd-conj X0-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S2=S2-X0) )
  pd-conj X0-gen CS01-gen = just ( S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0) )
  pd-conj X0-gen CS02-gen = just ( S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CS02=S2-CS02-CS02-CS02-X0) )
  pd-conj X0-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CS12=CS12-X0) )
  pd-conj X0-gen CCZ-gen = just ( CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CCZ=CS12-CS12-CCZ-X0) )
  pd-conj X0-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-X0-iI=iI-X0) )
  pd-conj CX10-gen S0-gen = just ( S0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10) )
  pd-conj CX10-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S1=S1-CX10) )
  pd-conj CX10-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S2=S2-CX10) )
  pd-conj CX10-gen CS01-gen = just ( S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10) )
  pd-conj CX10-gen CS02-gen = just ( CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10) )
  pd-conj CX10-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CS12=CS12-CX10) )
  pd-conj CX10-gen CCZ-gen = just ( CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10) )
  pd-conj CX10-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-iI=iI-CX10) )
  pd-conj CX20-gen S0-gen = just ( S0-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S0=S0-S2-CS02-CS02-CX20) )
  pd-conj CX20-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S1=S1-CX20) )
  pd-conj CX20-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S2=S2-CX20) )
  pd-conj CX20-gen CS01-gen = just ( CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CS01=CS01-CS12-CCZ-CX20) )
  pd-conj CX20-gen CS02-gen = just ( S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CS02=S2-CS02-CS02-CS02-CX20) )
  pd-conj CX20-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CS12=CS12-CX20) )
  pd-conj CX20-gen CCZ-gen = just ( CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CCZ=CS12-CS12-CCZ-CX20) )
  pd-conj CX20-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-iI=iI-CX20) )
  pd-conj CCX0-gen S0-gen = just ( S0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S0=S0-CS12-CCZ-CCX0) )
  pd-conj CCX0-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S1=S1-CCX0) )
  pd-conj CCX0-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S2=S2-CCX0) )
  pd-conj CCX0-gen CS01-gen = just ( CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0) )
  pd-conj CCX0-gen CS02-gen = just ( CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CS02=CS02-CS12-CCZ-CCX0) )
  pd-conj CCX0-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CS12=CS12-CCX0) )
  pd-conj CCX0-gen CCZ-gen = just ( CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0) )
  pd-conj CCX0-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-iI=iI-CCX0) )
  pd-conj _ _ = nothing


  nfd : ListNF Rel
  nfd = record { listnf = Diag.multistep 5000 ; lemma-listnf = Diag.lemma-multistep 5000 }



  isP : Gate -> Bool
  isP CCX0-gen = true
  isP CCX1-gen = true
  isP CCX2-gen = true
  isP CX01-gen = true
  isP CX10-gen = true
  isP CX12-gen = true
  isP CX21-gen = true
  isP CX02-gen = true
  isP CX20-gen = true
  isP X0-gen = true
  isP X1-gen = true
  isP X2-gen = true
  isP Swap01-gen = true
  isP Swap12-gen = true
  isP _ = false

  isD : Gate -> Bool
  isD S0-gen = true
  isD S1-gen = true
  isD S2-gen = true
  isD CS01-gen = true
  isD CS12-gen = true
  isD CS02-gen = true
  isD CCZ-gen = true
  isD iI-gen = true
  isD _ = false
  
  module PD = SemiDirect isP isD nfp nfd group-like pd-conj


  nf-pd : ListNF Rel
  nf-pd = record { listnf = PD.nfnh' ; lemma-listnf = PD.lemma-nfnh' }

  nf-pde : ListNF Rel
  nf-pde = extend-nf (\x -> isP x ∨ isD x) nf-pd

  nf-p : ListNF Rel
  nf-p = nfp


  lemma-comm-iI : ∀ {w : Word Gate} -> Rel ⊢ iI • w === w • iI
  lemma-comm-iI {[ CCX0-gen ]ʷ} = axiom ax-iI-CCX0=CCX0-iI
  lemma-comm-iI {[ CCX1-gen ]ʷ} = axiom ax-iI-CCX1=CCX1-iI
  lemma-comm-iI {[ CCX2-gen ]ʷ} = axiom ax-iI-CCX2=CCX2-iI
  lemma-comm-iI {[ CX01-gen ]ʷ} = axiom ax-iI-CX01=CX01-iI
  lemma-comm-iI {[ CX10-gen ]ʷ} = axiom ax-iI-CX10=CX10-iI
  lemma-comm-iI {[ CX12-gen ]ʷ} = axiom ax-iI-CX12=CX12-iI
  lemma-comm-iI {[ CX21-gen ]ʷ} = axiom ax-iI-CX21=CX21-iI
  lemma-comm-iI {[ CX02-gen ]ʷ} = axiom ax-iI-CX02=CX02-iI
  lemma-comm-iI {[ CX20-gen ]ʷ} = axiom ax-iI-CX20=CX20-iI
  lemma-comm-iI {[ X0-gen ]ʷ} = axiom ax-iI-X0=X0-iI
  lemma-comm-iI {[ X1-gen ]ʷ} = axiom ax-iI-X1=X1-iI
  lemma-comm-iI {[ X2-gen ]ʷ} = axiom ax-iI-X2=X2-iI
  lemma-comm-iI {[ Swap01-gen ]ʷ} = axiom ax-iI-Swap01=Swap01-iI
  lemma-comm-iI {[ Swap12-gen ]ʷ} = axiom ax-iI-Swap12=Swap12-iI
  lemma-comm-iI {[ S0-gen ]ʷ} = axiom ax-iI-S0=S0-iI
  lemma-comm-iI {[ S1-gen ]ʷ} = axiom ax-iI-S1=S1-iI
  lemma-comm-iI {[ S2-gen ]ʷ} = axiom ax-iI-S2=S2-iI
  lemma-comm-iI {[ CS01-gen ]ʷ} = axiom ax-iI-CS01=CS01-iI
  lemma-comm-iI {[ CS12-gen ]ʷ} = axiom ax-iI-CS12=CS12-iI
  lemma-comm-iI {[ CS02-gen ]ʷ} = axiom ax-iI-CS02=CS02-iI
  lemma-comm-iI {[ CCZ-gen ]ʷ} = axiom ax-iI-CCZ=CCZ-iI
  lemma-comm-iI {[ iI-gen ]ʷ} = refl
  lemma-comm-iI {[ CCK'-gen ]ʷ} = axiom ax-iI-CCK'=CCK'-iI
  lemma-comm-iI {[ CK10-gen ]ʷ} = axiom ax-iI-CK10=CK10-iI
  lemma-comm-iI {[ CK20-gen ]ʷ} = axiom ax-iI-CK20=CK20-iI
  lemma-comm-iI {[ K0-gen ]ʷ} = axiom ax-iI-K0=K0-iI
  lemma-comm-iI {[ K1-gen ]ʷ} = lemma-iI-K1=K1-iI
  lemma-comm-iI {[ K2-gen ]ʷ} = lemma-iI-K2=K2-iI
  lemma-comm-iI {ε} = trans right-unit (symm left-unit)
  lemma-comm-iI {w • w₁} with lemma-comm-iI {w} | lemma-comm-iI {w₁}
  ... | ih1 | ih2 = trans (symm assoc) (trans (left ih1) (trans assoc (trans (right ih2) (symm assoc))))

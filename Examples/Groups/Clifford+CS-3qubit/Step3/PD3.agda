------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
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
open import Examples.Groups.Clifford+CS-3qubit.Gate
open import Examples.Groups.Clifford+CS-3qubit.CosetNF as CosetNF
open CosetNF.Legacy

open import Examples.Groups.Clifford+CS-3qubit.Step3.Rel

module Examples.Groups.Clifford+CS-3qubit.Step3.PD3 where

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


  lemma-K1-iI-K1=ε : Rel ⊢ (K1 • iI) • K1 === ε
  lemma-K1-iI-K1=ε =
    equational (K1 • iI) • K1
            by left symm (axiom ax-iI-K1=K1-iI)
        equals (iI • K1) • K1
            by assoc
        equals iI • K1 • K1
            by right axiom ax-K1-K1=iI-iI-iI
        equals iI • iI • iI • iI
            by axiom ax-iI-iI-iI-iI=ε
        equals ε

  lemma-K2-iI-K2=ε : Rel ⊢ (K2 • iI) • K2 === ε
  lemma-K2-iI-K2=ε =
    equational (K2 • iI) • K2
            by left symm (axiom ax-iI-K2=K2-iI)
        equals (iI • K2) • K2
            by assoc
        equals iI • K2 • K2
            by right axiom ax-K2-K2=iI-iI-iI
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

  p16-step : Step-Function Gate Rel
  p16-step (X0-gen ∷ X0-gen ∷ xs) = just (xs , at-head (axiom ax-X0-X0=ε))
  p16-step (CX10-gen ∷ CX10-gen ∷ xs) = just (xs , at-head (axiom ax-CX10-CX10=ε))
  p16-step (CX20-gen ∷ CX20-gen ∷ xs) = just (xs , at-head (axiom ax-CX20-CX20=ε))
  p16-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  p16-step (CX10-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-X0=X0-CX10))
  p16-step (CX20-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-X0=X0-CX20))
  p16-step (CX20-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-CX10=CX10-CX20))
  p16-step (CCX0-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-X0=X0-CCX0))
  p16-step (CCX0-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CX10=CX10-CCX0))
  p16-step (CCX0-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CX20=CX20-CCX0))
  p16-step _ = nothing

  module P16 = Rewriting.Step (step-cong p16-step)

  p24-step : Step-Function Gate Rel
  p24-step (X1-gen ∷ X1-gen ∷ xs) = just (xs , at-head (axiom ax-X1-X1=ε))
  p24-step (X2-gen ∷ X2-gen ∷ xs) = just (xs , at-head (axiom ax-X2-X2=ε))
  p24-step (CX12-gen ∷ CX12-gen ∷ xs) = just (xs , at-head (axiom ax-CX12-CX12=ε))
  p24-step (CX21-gen ∷ CX21-gen ∷ xs) = just (xs , at-head (axiom ax-CX21-CX21=ε))
  p24-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (axiom ax-Swap12-Swap12=ε))
  p24-step (Swap12-gen ∷ X1-gen ∷ xs) = just (X2-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-X1=X2-Swap12))
  p24-step (Swap12-gen ∷ X2-gen ∷ xs) = just (X1-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-X2=X1-Swap12))
  p24-step (Swap12-gen ∷ CX12-gen ∷ xs) = just (CX21-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX12=CX21-Swap12))
  p24-step (Swap12-gen ∷ CX21-gen ∷ xs) = just (CX12-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX21=CX12-Swap12))
  p24-step (CX21-gen ∷ X1-gen ∷ xs) = just (X1-gen ∷ CX21-gen ∷ xs , at-head (axiom ax-CX21-X1=X1-CX21))
  p24-step (CX12-gen ∷ X2-gen ∷ xs) = just (X2-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CX12-X2=X2-CX12))
  p24-step (CX12-gen ∷ X1-gen ∷ xs) = just (X1-gen ∷ X2-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CX12-X1=X1-X2-CX12))
  p24-step (CX21-gen ∷ X2-gen ∷ xs) = just (X1-gen ∷ X2-gen ∷ CX21-gen ∷ xs , at-head (axiom ax-CX21-X2=X1-X2-CX21))
  p24-step (X2-gen ∷ X1-gen ∷ xs) = just (X1-gen ∷ X2-gen ∷ xs , at-head (axiom ax-X2-X1=X1-X2))
  p24-step (CX12-gen ∷ CX21-gen ∷ CX12-gen ∷ xs) = just (Swap12-gen ∷ xs , at-head (axiom ax-CX12-CX21-CX12=Swap12))
  p24-step (CX21-gen ∷ CX12-gen ∷ CX21-gen ∷ xs) = just (Swap12-gen ∷ xs , at-head (axiom ax-CX21-CX12-CX21=Swap12))
  p24-step (CX12-gen ∷ Swap12-gen ∷ xs) = just (CX21-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CX12-Swap12=CX21-CX12))
  p24-step (CX21-gen ∷ Swap12-gen ∷ xs) = just (CX12-gen ∷ CX21-gen ∷ xs , at-head (axiom ax-CX21-Swap12=CX12-CX21))
  p24-step _ = nothing

  module P24 = Rewriting.Step (step-cong p24-step)

  isP16 : Gate -> Bool
  isP16 CCX0-gen = true
  isP16 CX10-gen = true
  isP16 CX20-gen = true
  isP16 X0-gen = true
  isP16 _ = false

  isP24 : Gate -> Bool
  isP24 X1-gen = true
  isP24 X2-gen = true
  isP24 Swap12-gen = true
  isP24 CX12-gen = true
  isP24 CX21-gen = true
  isP24 _ = false

  nfp16 : NF Rel
  nfp16 = record { nf = f-of-listf (P16.multistep 1000) ; lemma-nf = lemma-f-of-listf (P16.lemma-multistep 1000) }

  nfp24 : NF Rel
  nfp24 = record { nf = f-of-listf (P24.multistep 1000) ; lemma-nf = lemma-f-of-listf (P24.lemma-multistep 1000) }


  p24-p16-conj : let X = Gate in let Γ = Rel in (h n : X) -> Maybe (∃ λ (n' : Word X) -> Γ ⊢ [ h ]ʷ • [ n ]ʷ === n' • [ h ]ʷ)
  p24-p16-conj X1-gen X0-gen = just ( X0 , axiom ax-X1-X0=X0-X1 )
  p24-p16-conj X1-gen CX10-gen = just ( X0 • CX10 , up-to-assoc auto (axiom ax-X1-CX10=X0-CX10-X1) )
  p24-p16-conj X1-gen CX20-gen = just ( CX20 , axiom ax-X1-CX20=CX20-X1 )
  p24-p16-conj X1-gen CCX0-gen = just ( CX20 • CCX0 , up-to-assoc auto (axiom ax-X1-CCX0=CX20-CCX0-X1) )
  p24-p16-conj X2-gen X0-gen = just ( X0 , axiom ax-X2-X0=X0-X2 )
  p24-p16-conj X2-gen CX10-gen = just ( CX10 , axiom ax-X2-CX10=CX10-X2 )
  p24-p16-conj X2-gen CX20-gen = just ( X0 • CX20 , up-to-assoc auto (axiom ax-X2-CX20=X0-CX20-X2) )
  p24-p16-conj X2-gen CCX0-gen = just ( CX10 • CCX0 , up-to-assoc auto (axiom ax-X2-CCX0=CX10-CCX0-X2) )
  p24-p16-conj CX12-gen X0-gen = just ( X0 , axiom ax-CX12-X0=X0-CX12 )
  p24-p16-conj CX12-gen CX10-gen = just ( CX10 , axiom ax-CX12-CX10=CX10-CX12 )
  p24-p16-conj CX12-gen CX20-gen = just ( CX10 • CX20 , up-to-assoc auto (axiom ax-CX12-CX20=CX10-CX20-CX12) )
  p24-p16-conj CX12-gen CCX0-gen = just ( CX10 • CCX0 , up-to-assoc auto (axiom ax-CX12-CCX0=CX10-CCX0-CX12) )
  p24-p16-conj CX21-gen X0-gen = just ( X0 , axiom ax-CX21-X0=X0-CX21 )
  p24-p16-conj CX21-gen CX10-gen = just ( CX10 • CX20 , up-to-assoc auto (axiom ax-CX21-CX10=CX10-CX20-CX21) )
  p24-p16-conj CX21-gen CX20-gen = just ( CX20 , axiom ax-CX21-CX20=CX20-CX21 )
  p24-p16-conj CX21-gen CCX0-gen = just ( CX20 • CCX0 , up-to-assoc auto (axiom ax-CX21-CCX0=CX20-CCX0-CX21) )
  p24-p16-conj Swap12-gen X0-gen = just ( X0 , axiom ax-Swap12-X0=X0-Swap12 )
  p24-p16-conj Swap12-gen CX10-gen = just ( CX20 , axiom ax-Swap12-CX10=CX20-Swap12 )
  p24-p16-conj Swap12-gen CX20-gen = just ( CX10 , axiom ax-Swap12-CX20=CX10-Swap12 )
  p24-p16-conj Swap12-gen CCX0-gen = just ( CCX0 , axiom ax-Swap12-CCX0=CCX0-Swap12 )
  p24-p16-conj _ _ = nothing

 

  module P384 = SemiDirect' isP24 isP16 nfp24 nfp16 group-like p24-p16-conj

  order-step : Step-Function Gate Rel
  order-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  order-step (CCX1-gen ∷ CCX1-gen ∷ xs) = just (xs , at-head (axiom ax-CCX1-CCX1=ε))
  order-step (CCX2-gen ∷ CCX2-gen ∷ xs) = just (xs , at-head (axiom ax-CCX2-CCX2=ε))
  order-step (CX01-gen ∷ CX01-gen ∷ xs) = just (xs , at-head (axiom ax-CX01-CX01=ε))
  order-step (CX10-gen ∷ CX10-gen ∷ xs) = just (xs , at-head (axiom ax-CX10-CX10=ε))
  order-step (CX12-gen ∷ CX12-gen ∷ xs) = just (xs , at-head (axiom ax-CX12-CX12=ε))
  order-step (CX21-gen ∷ CX21-gen ∷ xs) = just (xs , at-head (axiom ax-CX21-CX21=ε))
  order-step (CX02-gen ∷ CX02-gen ∷ xs) = just (xs , at-head (axiom ax-CX02-CX02=ε))
  order-step (CX20-gen ∷ CX20-gen ∷ xs) = just (xs , at-head (axiom ax-CX20-CX20=ε))
  order-step (X0-gen ∷ X0-gen ∷ xs) = just (xs , at-head (axiom ax-X0-X0=ε))
  order-step (X1-gen ∷ X1-gen ∷ xs) = just (xs , at-head (axiom ax-X1-X1=ε))
  order-step (X2-gen ∷ X2-gen ∷ xs) = just (xs , at-head (axiom ax-X2-X2=ε))
  order-step (Swap01-gen ∷ Swap01-gen ∷ xs) = just (xs , at-head (axiom ax-Swap01-Swap01=ε))
  order-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (axiom ax-Swap12-Swap12=ε))
  order-step (S0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs) = just (xs , at-head (axiom ax-S0-S0-S0-S0=ε))
  order-step (S1-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ xs) = just (xs , at-head (axiom ax-S1-S1-S1-S1=ε))
  order-step (S2-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ xs) = just (xs , at-head (axiom ax-S2-S2-S2-S2=ε))
  order-step (CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs) = just (xs , at-head (axiom ax-CS01-CS01-CS01-CS01=ε))
  order-step (CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ xs) = just (xs , at-head (axiom ax-CS12-CS12-CS12-CS12=ε))
  order-step (CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ xs) = just (xs , at-head (axiom ax-CS02-CS02-CS02-CS02=ε))
  order-step (CCZ-gen ∷ CCZ-gen ∷ xs) = just (xs , at-head (axiom ax-CCZ-CCZ=ε))
  order-step (iI-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs) = just (xs , at-head (axiom ax-iI-iI-iI-iI=ε))
  order-step (CCK'-gen ∷ CCK'-gen ∷ CCK'-gen ∷ xs) = just (CS12-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CCK'-CCK'-CCK'=CS12-CS12))
  order-step (CK10-gen ∷ CK10-gen ∷ xs) = just (S1-gen ∷ S1-gen ∷ S1-gen ∷ xs , at-head (axiom ax-CK10-CK10=S1-S1-S1))
  order-step (CK20-gen ∷ CK20-gen ∷ xs) = just (S2-gen ∷ S2-gen ∷ S2-gen ∷ xs , at-head (axiom ax-CK20-CK20=S2-S2-S2))
  order-step (K0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K0-K0=iI-iI-iI))
  order-step _ = nothing

  module Order = Rewriting.Step (step-cong order-step)

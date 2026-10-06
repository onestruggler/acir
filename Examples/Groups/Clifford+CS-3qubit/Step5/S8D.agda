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

open import Examples.Groups.Clifford+CS-3qubit.Step5.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step5.S8
open import Examples.Groups.Clifford+CS-3qubit.Step5.Comm
open import Examples.Groups.Clifford+CS-3qubit.Step5.Order
open import Examples.Groups.Clifford+CS-3qubit.Step5.Basis-Change

module Examples.Groups.Clifford+CS-3qubit.Step5.S8D where

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
  nfp16 : ListNF Rel
  nfp16 = record { listnf = P16.multistep 1000 ; lemma-listnf = P16.lemma-multistep 1000 }

  isP16 : Gate -> Bool
  isP16 CCX0-gen = true
  isP16 CX10-gen = true
  isP16 CX20-gen = true
  isP16 X0-gen = true
  isP16 _ = false


  p16d-step : Step-Function Gate Rel
  p16d-step (X0-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S0-gen ∷ S0-gen ∷ iI-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-S0=S0-S0-S0-iI-X0))
  p16d-step (X0-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-S1=S1-X0))
  p16d-step (X0-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-S2=S2-X0))
  p16d-step (X0-gen ∷ CS01-gen ∷ xs) = just (S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0))
  p16d-step (X0-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CS12=CS12-X0))
  p16d-step (X0-gen ∷ CS02-gen ∷ xs) = just (S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CS02=S2-CS02-CS02-CS02-X0))
  p16d-step (X0-gen ∷ CCZ-gen ∷ xs) = just (CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-CCZ=CS12-CS12-CCZ-X0))
  p16d-step (X0-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ X0-gen ∷ xs , at-head (axiom ax-X0-iI=iI-X0))
  p16d-step (CX10-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10))
  p16d-step (CX10-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-S1=S1-CX10))
  p16d-step (CX10-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-S2=S2-CX10))
  p16d-step (CX10-gen ∷ CS01-gen ∷ xs) = just (S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10))
  p16d-step (CX10-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-CS12=CS12-CX10))
  p16d-step (CX10-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10))
  p16d-step (CX10-gen ∷ CCZ-gen ∷ xs) = just (CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10))
  p16d-step (CX10-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-iI=iI-CX10))
  p16d-step (CX20-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-S0=S0-S2-CS02-CS02-CX20))
  p16d-step (CX20-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-S1=S1-CX20))
  p16d-step (CX20-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-S2=S2-CX20))
  p16d-step (CX20-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-CS01=CS01-CS12-CCZ-CX20))
  p16d-step (CX20-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-CS12=CS12-CX20))
  p16d-step (CX20-gen ∷ CS02-gen ∷ xs) = just (S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-CS02=S2-CS02-CS02-CS02-CX20))
  p16d-step (CX20-gen ∷ CCZ-gen ∷ xs) = just (CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-CCZ=CS12-CS12-CCZ-CX20))
  p16d-step (CX20-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-iI=iI-CX20))
  p16d-step (CCX0-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS12-gen ∷ CCZ-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-S0=S0-CS12-CCZ-CCX0))
  p16d-step (CCX0-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-S1=S1-CCX0))
  p16d-step (CCX0-gen ∷ S2-gen ∷ xs) = just (S2-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-S2=S2-CCX0))
  p16d-step (CCX0-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0))
  p16d-step (CCX0-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CS12=CS12-CCX0))
  p16d-step (CCX0-gen ∷ CS02-gen ∷ xs) = just (CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CS02=CS02-CS12-CCZ-CCX0))
  p16d-step (CCX0-gen ∷ CCZ-gen ∷ xs) = just (CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0))
  p16d-step (CCX0-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-iI=iI-CCX0))
  p16d-step _ = nothing


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
  mvI-step (iI-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-K0=K0-iI))
  mvI-step _ = nothing

  module mvI = Rewriting.Step (step-cong mvI-step)


  lemma-Swap01-K0-Swap01-Swap01-K0-Swap01=iI-iI-iI : Rel ⊢ (Swap01 • K0 • Swap01) • (Swap01 • K0 • Swap01) === iI • iI • iI
  lemma-Swap01-K0-Swap01-Swap01-K0-Swap01=iI-iI-iI =
    equational (Swap01 • K0 • Swap01) • (Swap01 • K0 • Swap01)
      by ListNF.listnfeq' nf-s7e auto
    equals Swap01 • (K0 • K0) • Swap01
      by right left axiom ax-K0-K0=iI-iI-iI
    equals Swap01 • (iI ^ 3) • Swap01
      by mvI.general-rewrite 100 auto
    equals (Swap01 • Swap01) • (iI ^ 3)
      by ListNF.listnfeq' nf-s7e auto
    equals iI • iI • iI

  lemma-Swap12-Swap01-K0-Swap01-Swap12-Swap12-Swap01-K0-Swap01-Swap12=iI-iI-iI : Rel ⊢ (Swap12 • Swap01 • K0 • Swap01 • Swap12) • (Swap12 • Swap01 • K0 • Swap01 • Swap12) === iI • iI • iI
  lemma-Swap12-Swap01-K0-Swap01-Swap12-Swap12-Swap01-K0-Swap01-Swap12=iI-iI-iI =
    equational (Swap12 • Swap01 • K0 • Swap01 • Swap12) • (Swap12 • Swap01 • K0 • Swap01 • Swap12)
      by ListNF.listnfeq' nf-s7e auto
    equals Swap12 • ((Swap01 • K0 • Swap01) • (Swap01 • K0 • Swap01)) • Swap12
      by right left lemma-Swap01-K0-Swap01-Swap01-K0-Swap01=iI-iI-iI
    equals Swap12 • (iI ^ 3) • Swap12
      by mvI.general-rewrite 100 auto
    equals Swap12 • Swap12 • (iI ^ 3)
      by ListNF.listnfeq' nf-s7e auto
    equals iI • iI • iI


  lemma-Swap01-K0-Swap01-iI-Swap01-K0-Swap01=ε : Rel ⊢ ((Swap01 • K0 • Swap01) • iI) • (Swap01 • K0 • Swap01) === ε
  lemma-Swap01-K0-Swap01-iI-Swap01-K0-Swap01=ε =
    equational ((Swap01 • K0 • Swap01) • iI) • (Swap01 • K0 • Swap01)
            by left mvI.general-rewrite 100 auto
        equals (iI • (Swap01 • K0 • Swap01)) • (Swap01 • K0 • Swap01)
            by assoc
        equals iI • (Swap01 • K0 • Swap01) • (Swap01 • K0 • Swap01)
            by right lemma-Swap01-K0-Swap01-Swap01-K0-Swap01=iI-iI-iI
        equals iI • iI • iI • iI
            by axiom ax-iI-iI-iI-iI=ε
        equals ε
        
  lemma-Swap12-Swap01-K0-Swap01-Swap12-iI-Swap12-Swap01-K0-Swap01-Swap12=ε : Rel ⊢ ((Swap12 • Swap01 • K0 • Swap01 • Swap12) • iI) • (Swap12 • Swap01 • K0 • Swap01 • Swap12) === ε
  lemma-Swap12-Swap01-K0-Swap01-Swap12-iI-Swap12-Swap01-K0-Swap01-Swap12=ε =
    equational ((Swap12 • Swap01 • K0 • Swap01 • Swap12) • iI) • (Swap12 • Swap01 • K0 • Swap01 • Swap12)
            by left mvI.general-rewrite 100 auto
        equals (iI • (Swap12 • Swap01 • K0 • Swap01 • Swap12)) • (Swap12 • Swap01 • K0 • Swap01 • Swap12)
            by assoc
        equals iI • (Swap12 • Swap01 • K0 • Swap01 • Swap12) • (Swap12 • Swap01 • K0 • Swap01 • Swap12)
            by right lemma-Swap12-Swap01-K0-Swap01-Swap12-Swap12-Swap01-K0-Swap01-Swap12=iI-iI-iI
        equals iI • iI • iI • iI
            by axiom ax-iI-iI-iI-iI=ε
        equals ε



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



  lemma-CS01-K0-CS01-K0-CS01-S1-S1-S1-iI-CS01-K0-CS01-K0-CS01-S1-S1-S1-iI=S1-S1-S1 : Rel ⊢ (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) • (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) === S1 • S1 • S1
  lemma-CS01-K0-CS01-K0-CS01-S1-S1-S1-iI-CS01-K0-CS01-K0-CS01-S1-S1-S1-iI=S1-S1-S1 =
    equational (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) • (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI)
            by general-comm auto
        equals (CS01 • K0 • CS01 • (K0 • CS01 • CS01 • K0 • iI) • S1 • S1 • S1 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI)
            by right right right left symm (axiom ax-CX10=K0-CS01-CS01-K0-iI)
        equals (CS01 • K0 • CS01 • CX10 • S1 • S1 • S1 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI)
            by general-comm auto
        equals (CS01 • K0 • CS01 • S1 • S1 • S1) • (CX10 • CS01) • K0 • CS01 • S1 • S1 • S1 • iI
            by right left axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10
        equals (CS01 • K0 • CS01 • S1 • S1 • S1) • (S1 • CS01 • CS01 • CS01 • CX10) • K0 • CS01 • S1 • S1 • S1 • iI
            by ListNF.listnfeq' nf-order auto
        equals CS01 • K0 • (CX10 • K0) • CS01 • S1 • S1 • S1 • iI
            by right right left axiom ax-CX10-K0=K0-CS01-CS01
        equals CS01 • K0 • (K0 • CS01 • CS01) • CS01 • S1 • S1 • S1 • iI
            by ListNF.listnfeq' nf-order-rep auto
        equals S1 • S1 • S1

  lemma-CS02-K0-CS02-K0-CS02-S2-S2-S2-iI-CS02-K0-CS02-K0-CS02-S2-S2-S2-iI=S2-S2-S2 : Rel ⊢ (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI) • (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI) === S2 • S2 • S2
  lemma-CS02-K0-CS02-K0-CS02-S2-S2-S2-iI-CS02-K0-CS02-K0-CS02-S2-S2-S2-iI=S2-S2-S2 =
    equational (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI) • (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI)
            by general-comm auto
        equals (CS02 • K0 • CS02 • (K0 • CS02 • CS02 • K0 • iI) • S2 • S2 • S2 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI)
            by right right right left symm (by-basis-change Swap12 Swap12 (axiom ax-CX10=K0-CS01-CS01-K0-iI) 100 auto)
        equals (CS02 • K0 • CS02 • CX20 • S2 • S2 • S2 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI)
            by general-comm auto
        equals (CS02 • K0 • CS02 • S2 • S2 • S2) • (CX20 • CS02) • K0 • CS02 • S2 • S2 • S2 • iI
            by right left axiom ax-CX20-CS02=S2-CS02-CS02-CS02-CX20
        equals (CS02 • K0 • CS02 • S2 • S2 • S2) • (S2 • CS02 • CS02 • CS02 • CX20) • K0 • CS02 • S2 • S2 • S2 • iI
            by ListNF.listnfeq' nf-order auto
        equals CS02 • K0 • (CX20 • K0) • CS02 • S2 • S2 • S2 • iI
            by right right left axiom ax-CX20-K0=K0-CS02-CS02
        equals CS02 • K0 • (K0 • CS02 • CS02) • CS02 • S2 • S2 • S2 • iI
            by ListNF.listnfeq' nf-order-rep auto
        equals S2 • S2 • S2

  lemma-CK10-S1-CK10=ε : Rel ⊢ (CK10 • S1) • CK10 === ε
  lemma-CK10-S1-CK10=ε =
    equational (CK10 • S1) • CK10
            by cong (left axiom ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI) (axiom ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI)
        equals ((CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) • S1) • (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI)
            by general-comm auto
        equals S1 • (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) • (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI)
            by right lemma-CS01-K0-CS01-K0-CS01-S1-S1-S1-iI-CS01-K0-CS01-K0-CS01-S1-S1-S1-iI=S1-S1-S1
        equals S1 • S1 • S1 • S1
            by axiom ax-S1-S1-S1-S1=ε
        equals ε


  lemma-CK20-S2-CK20=ε : Rel ⊢ (CK20 • S2) • CK20 === ε
  lemma-CK20-S2-CK20=ε =
    equational (CK20 • S2) • CK20
            by cong (left axiom ax-CK20=CS02-K0-CS02-K0-CS02-S2-S2-S2-iI) (axiom ax-CK20=CS02-K0-CS02-K0-CS02-S2-S2-S2-iI)
        equals ((CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI) • S2) • (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI)
            by general-comm auto
        equals S2 • (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI) • (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI)
            by right lemma-CS02-K0-CS02-K0-CS02-S2-S2-S2-iI-CS02-K0-CS02-K0-CS02-S2-S2-S2-iI=S2-S2-S2
        equals S2 • S2 • S2 • S2
            by axiom ax-S2-S2-S2-S2=ε
        equals ε

  lemma-iI-S0-K0=S0-K0-iI : Rel ⊢ iI • S0 • K0 === S0 • K0 • iI
  lemma-iI-S0-K0=S0-K0-iI =
    equational iI • S0 • K0
      by symm assoc
    equals (iI • S0) • K0
      by left axiom ax-iI-S0=S0-iI
    equals (S0 • iI) • K0
      by assoc
    equals S0 • iI • K0
      by cong refl (axiom ax-iI-K0=K0-iI)
    equals S0 • K0 • iI

  lemma-S1-S0-K0=S0-K0-S1 : Rel ⊢ S1 • S0 • K0 === S0 • K0 • S1
  lemma-S1-S0-K0=S0-K0-S1 =
    equational S1 • S0 • K0
      by symm assoc
    equals (S1 • S0) • K0
      by left axiom ax-S1-S0=S0-S1
    equals (S0 • S1) • K0
      by assoc
    equals S0 • S1 • K0
      by cong refl (axiom ax-S1-K0=K0-S1)
    equals S0 • K0 • S1


  lemma-S2-S0-K0=S0-K0-S2 : Rel ⊢ S2 • S0 • K0 === S0 • K0 • S2
  lemma-S2-S0-K0=S0-K0-S2 =
    equational S2 • S0 • K0
      by symm assoc
    equals (S2 • S0) • K0
      by left axiom ax-S2-S0=S0-S2
    equals (S0 • S2) • K0
      by assoc
    equals S0 • S2 • K0
      by cong refl (axiom ax-S2-K0=K0-S2)
    equals S0 • K0 • S2


  lemma-CS12-S0-K0=S0-K0-CS12 : Rel ⊢ CS12 • S0 • K0 === S0 • K0 • CS12
  lemma-CS12-S0-K0=S0-K0-CS12 =
    equational CS12 • S0 • K0
      by symm assoc
    equals (CS12 • S0) • K0
      by left axiom ax-CS12-S0=S0-CS12
    equals (S0 • CS12) • K0
      by assoc
    equals S0 • CS12 • K0
      by cong refl (axiom ax-CS12-K0=K0-CS12)
    equals S0 • K0 • CS12



  lemma-iI-CS01-K0=CS01-K0-iI : Rel ⊢ iI • CS01 • K0 === CS01 • K0 • iI
  lemma-iI-CS01-K0=CS01-K0-iI =
    equational iI • CS01 • K0
      by symm assoc
    equals (iI • CS01) • K0
      by left axiom ax-iI-CS01=CS01-iI
    equals (CS01 • iI) • K0
      by assoc
    equals CS01 • iI • K0
      by cong refl (axiom ax-iI-K0=K0-iI)
    equals CS01 • K0 • iI

  lemma-S1-CS01-K0=CS01-K0-S1 : Rel ⊢ S1 • CS01 • K0 === CS01 • K0 • S1
  lemma-S1-CS01-K0=CS01-K0-S1 =
    equational S1 • CS01 • K0
      by symm assoc
    equals (S1 • CS01) • K0
      by left symm (axiom ax-CS01-S1=S1-CS01)
    equals (CS01 • S1) • K0
      by assoc
    equals CS01 • S1 • K0
      by cong refl (axiom ax-S1-K0=K0-S1)
    equals CS01 • K0 • S1


  lemma-S2-CS01-K0=CS01-K0-S2 : Rel ⊢ S2 • CS01 • K0 === CS01 • K0 • S2
  lemma-S2-CS01-K0=CS01-K0-S2 =
    equational S2 • CS01 • K0
      by symm assoc
    equals (S2 • CS01) • K0
      by left symm (axiom ax-CS01-S2=S2-CS01)
    equals (CS01 • S2) • K0
      by assoc
    equals CS01 • S2 • K0
      by cong refl (axiom ax-S2-K0=K0-S2)
    equals CS01 • K0 • S2


  lemma-CS12-CS01-K0=CS01-K0-CS12 : Rel ⊢ CS12 • CS01 • K0 === CS01 • K0 • CS12
  lemma-CS12-CS01-K0=CS01-K0-CS12 =
    equational CS12 • CS01 • K0
      by symm assoc
    equals (CS12 • CS01) • K0
      by left axiom ax-CS12-CS01=CS01-CS12
    equals (CS01 • CS12) • K0
      by assoc
    equals CS01 • CS12 • K0
      by cong refl (axiom ax-CS12-K0=K0-CS12)
    equals CS01 • K0 • CS12


  lemma-iI-CS02-K0=CS02-K0-iI : Rel ⊢ iI • CS02 • K0 === CS02 • K0 • iI
  lemma-iI-CS02-K0=CS02-K0-iI =
    equational iI • CS02 • K0
      by symm assoc
    equals (iI • CS02) • K0
      by left axiom ax-iI-CS02=CS02-iI
    equals (CS02 • iI) • K0
      by assoc
    equals CS02 • iI • K0
      by cong refl (axiom ax-iI-K0=K0-iI)
    equals CS02 • K0 • iI

  lemma-S1-CS02-K0=CS02-K0-S1 : Rel ⊢ S1 • CS02 • K0 === CS02 • K0 • S1
  lemma-S1-CS02-K0=CS02-K0-S1 =
    equational S1 • CS02 • K0
      by symm assoc
    equals (S1 • CS02) • K0
      by left symm (axiom ax-CS02-S1=S1-CS02)
    equals (CS02 • S1) • K0
      by assoc
    equals CS02 • S1 • K0
      by cong refl (axiom ax-S1-K0=K0-S1)
    equals CS02 • K0 • S1


  lemma-S2-CS02-K0=CS02-K0-S2 : Rel ⊢ S2 • CS02 • K0 === CS02 • K0 • S2
  lemma-S2-CS02-K0=CS02-K0-S2 =
    equational S2 • CS02 • K0
      by symm assoc
    equals (S2 • CS02) • K0
      by left symm (axiom ax-CS02-S2=S2-CS02)
    equals (CS02 • S2) • K0
      by assoc
    equals CS02 • S2 • K0
      by cong refl (axiom ax-S2-K0=K0-S2)
    equals CS02 • K0 • S2


  lemma-CS12-CS02-K0=CS02-K0-CS12 : Rel ⊢ CS12 • CS02 • K0 === CS02 • K0 • CS12
  lemma-CS12-CS02-K0=CS02-K0-CS12 =
    equational CS12 • CS02 • K0
      by symm assoc
    equals (CS12 • CS02) • K0
      by left axiom ax-CS12-CS02=CS02-CS12
    equals (CS02 • CS12) • K0
      by assoc
    equals CS02 • CS12 • K0
      by cong refl (axiom ax-CS12-K0=K0-CS12)
    equals CS02 • K0 • CS12





  lemma-CS01-CS01-S0-K0=S0-K0-CX10 : Rel ⊢ CS01 • CS01 • S0 • K0 === S0 • K0 • CX10
  lemma-CS01-CS01-S0-K0=S0-K0-CX10 =
    equational CS01 • CS01 • S0 • K0
      by general-comm auto
    equals S0 • (CS01 • CS01 • K0)
      by right axiom ax-CS01-CS01-K0=K0-CX10
    equals S0 • K0 • CX10


  lemma-CS02-CS02-S0-K0=S0-K0-CX20 : Rel ⊢ CS02 • CS02 • S0 • K0 === S0 • K0 • CX20
  lemma-CS02-CS02-S0-K0=S0-K0-CX20 =
    equational CS02 • CS02 • S0 • K0
      by general-comm auto
    equals S0 • (CS02 • CS02 • K0)
      by right axiom ax-CS02-CS02-K0=K0-CX20
    equals S0 • K0 • CX20


  lemma-CCZ-S0-K0=S0-K0-CCX0 : Rel ⊢ CCZ • S0 • K0 === S0 • K0 • CCX0
  lemma-CCZ-S0-K0=S0-K0-CCX0 =
    equational CCZ • S0 • K0
      by symm assoc
    equals (CCZ • S0) • K0
      by left axiom ax-CCZ-S0=S0-CCZ
    equals (S0 • CCZ) • K0
      by assoc
    equals S0 • CCZ • K0
      by cong refl (axiom ax-CCZ-K0=K0-CCX0)
    equals S0 • K0 • CCX0


  lemma-CCZ-CS01-K0=CS01-K0-CCX0 : Rel ⊢ CCZ • CS01 • K0 === CS01 • K0 • CCX0
  lemma-CCZ-CS01-K0=CS01-K0-CCX0 =
    equational CCZ • CS01 • K0
      by symm assoc
    equals (CCZ • CS01) • K0
      by left axiom ax-CCZ-CS01=CS01-CCZ
    equals (CS01 • CCZ) • K0
      by assoc
    equals CS01 • CCZ • K0
      by cong refl (axiom ax-CCZ-K0=K0-CCX0)
    equals CS01 • K0 • CCX0


  lemma-CCZ-CS02-K0=CS02-K0-CCX0 : Rel ⊢ CCZ • CS02 • K0 === CS02 • K0 • CCX0
  lemma-CCZ-CS02-K0=CS02-K0-CCX0 =
    equational CCZ • CS02 • K0
      by symm assoc
    equals (CCZ • CS02) • K0
      by left axiom ax-CCZ-CS02=CS02-CCZ
    equals (CS02 • CCZ) • K0
      by assoc
    equals CS02 • CCZ • K0
      by cong refl (axiom ax-CCZ-K0=K0-CCX0)
    equals CS02 • K0 • CCX0




  lemma-S0-S0-CS01-K0=CS01-K0-X0 : Rel ⊢ S0 • S0 • CS01 • K0 === CS01 • K0 • X0
  lemma-S0-S0-CS01-K0=CS01-K0-X0 =
    equational S0 • S0 • CS01 • K0
      by general-comm auto
    equals CS01 • S0 • S0 • K0
      by right axiom ax-S0-S0-K0=K0-X0
    equals CS01 • K0 • X0


  lemma-CS02-CS02-CS01-K0=CS01-K0-CX20 : Rel ⊢ CS02 • CS02 • CS01 • K0 === CS01 • K0 • CX20
  lemma-CS02-CS02-CS01-K0=CS01-K0-CX20 =
    equational CS02 • CS02 • CS01 • K0
      by general-comm auto
    equals CS01 • CS02 • CS02 • K0
      by right axiom ax-CS02-CS02-K0=K0-CX20
    equals CS01 • K0 • CX20

  lemma-S0-S0-CS02-K0=CS02-K0-X0 : Rel ⊢ S0 • S0 • CS02 • K0 === CS02 • K0 • X0
  lemma-S0-S0-CS02-K0=CS02-K0-X0 =
    equational S0 • S0 • CS02 • K0
      by general-comm auto
    equals CS02 • S0 • S0 • K0
      by right axiom ax-S0-S0-K0=K0-X0
    equals CS02 • K0 • X0


  lemma-CS01-CS01-CS02-K0=CS02-K0-CX10 : Rel ⊢ CS01 • CS01 • CS02 • K0 === CS02 • K0 • CX10
  lemma-CS01-CS01-CS02-K0=CS02-K0-CX10 =
    equational CS01 • CS01 • CS02 • K0
      by general-comm auto
    equals CS02 • CS01 • CS01 • K0
      by right axiom ax-CS01-CS01-K0=K0-CX10
    equals CS02 • K0 • CX10


  lemma-iI-CS01-CS02-K0=CS01-CS02-K0-iI : Rel ⊢ iI • CS01 • CS02 • K0 === CS01 • CS02 • K0 • iI
  lemma-iI-CS01-CS02-K0=CS01-CS02-K0-iI =
    equational iI • CS01 • CS02 • K0
      by general-comm auto
    equals CS01 • CS02 • iI • K0
      by right right axiom ax-iI-K0=K0-iI
    equals CS01 • CS02 • K0 • iI

  lemma-S1-CS01-CS02-K0=CS01-CS02-K0-S1 : Rel ⊢ S1 • CS01 • CS02 • K0 === CS01 • CS02 • K0 • S1
  lemma-S1-CS01-CS02-K0=CS01-CS02-K0-S1 =
    equational S1 • CS01 • CS02 • K0
      by general-comm auto
    equals CS01 • CS02 • S1 • K0
      by right right axiom ax-S1-K0=K0-S1
    equals CS01 • CS02 • K0 • S1


  lemma-S2-CS01-CS02-K0=CS01-CS02-K0-S2 : Rel ⊢ S2 • CS01 • CS02 • K0 === CS01 • CS02 • K0 • S2
  lemma-S2-CS01-CS02-K0=CS01-CS02-K0-S2 =
    equational S2 • CS01 • CS02 • K0
      by general-comm auto
    equals CS01 • CS02 • S2 • K0
      by right right axiom ax-S2-K0=K0-S2
    equals CS01 • CS02 • K0 • S2


  lemma-CS12-CS01-CS02-K0=CS01-CS02-K0-CS12 : Rel ⊢ CS12 • CS01 • CS02 • K0 === CS01 • CS02 • K0 • CS12
  lemma-CS12-CS01-CS02-K0=CS01-CS02-K0-CS12 =
    equational CS12 • CS01 • CS02 • K0
      by general-comm auto
    equals CS01 • CS02 • CS12 • K0
      by right right axiom ax-CS12-K0=K0-CS12
    equals CS01 • CS02 • K0 • CS12

  
  lemma-S0-S0-CS01-CS02-K0=CS01-CS02-K0-X0 : Rel ⊢ S0 • S0 • CS01 • CS02 • K0 === CS01 • CS02 • K0 • X0
  lemma-S0-S0-CS01-CS02-K0=CS01-CS02-K0-X0 =
    equational S0 • S0 • CS01 • CS02 • K0
      by general-comm auto
    equals CS01 • CS02 • S0 • S0 • K0
      by right right axiom ax-S0-S0-K0=K0-X0
    equals CS01 • CS02 • K0 • X0

  lemma-CCZ-CS01-CS02-K0=CS01-CS02-K0-CCX0 : Rel ⊢ CCZ • CS01 • CS02 • K0 === CS01 • CS02 • K0 • CCX0
  lemma-CCZ-CS01-CS02-K0=CS01-CS02-K0-CCX0 =
    equational CCZ • CS01 • CS02 • K0
      by general-comm auto
    equals CS01 • CS02 • CCZ • K0
      by right right axiom ax-CCZ-K0=K0-CCX0
    equals CS01 • CS02 • K0 • CCX0



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

  module DK = Rewriting.Step (step-cong (order-step then d-step then p16-step))
  module DK2 = Rewriting.Step (step-cong (order-step then d-step then p16-step then p16d-step))


  lemma-K0-S0-K0=S0-K0-X0-S0-S0-S0 : Rel ⊢ K0 • S0 • K0 === S0 • K0 • X0 • S0 • S0 • S0
  lemma-K0-S0-K0=S0-K0-X0-S0-S0-S0 = 
    equational K0 • S0 • K0
      by mvI.general-rewrite 100 auto
    equals (iI ^ 3) • K0 • (S0 • K0) • iI
      by Diag.general-rewrite 100 auto
    equals (S0 • S0 • S0) • (iI ^ 3) • (S0 • K0) ^ 2 • iI
      by right left symm (axiom ax-K0-K0=iI-iI-iI)
    equals (S0 • S0 • S0) • (K0 • K0) • (S0 • K0) ^ 2 • iI
      by general-assoc auto
    equals (S0 • S0 • S0 • K0) • K0 • (S0 • K0) ^ 2 • iI
      by Diag.general-rewrite 100 auto
    equals (S0 • S0 • S0 • K0 • S0 • S0 • S0) • (S0 • K0) ^ 3 • iI
      by right left axiom ax-S0-K0-S0-K0-S0-K0=iI-iI-iI
    equals (S0 • S0 • S0 • K0 • S0 • S0 • S0) • iI ^ 3 • iI
      by mvI.general-rewrite 100 auto
    equals S0 • (S0 • S0 • K0) • S0 • S0 • S0
      by right left axiom ax-S0-S0-K0=K0-X0
    equals S0 • (K0 • X0) • S0 • S0 • S0
      by general-assoc auto
    equals S0 • K0 • X0 • S0 • S0 • S0



  lemma-CS01-K0-CS01-K0=S0-K0-CS01-K0-CS01-S0-S0-S0 : Rel ⊢ CS01 • K0 • CS01 • K0 === S0 • K0 • CS01 • K0 • CS01 • S0 • S0 • S0
  lemma-CS01-K0-CS01-K0=S0-K0-CS01-K0-CS01-S0-S0-S0 =
    equational CS01 • K0 • CS01 • K0
      by Diag.general-rewrite 100 auto
    equals (CS01 • K0 • CS01 • K0 • S0) • S0 ^ 3
      by left axiom ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01
    equals (S0 • K0 • CS01 • K0 • CS01) • S0 ^ 3
      by general-assoc auto
    equals S0 • K0 • CS01 • K0 • CS01 • S0 • S0 • S0

  lemma-CS01-CS02-K0-CS01-K0=S0-CS02-K0-CS01-K0-CS01-S0-S0-S0 : Rel ⊢ CS01 • CS02 • K0 • CS01 • K0 === S0 • CS02 • K0 • CS01 • K0 • CS01 • S0 • S0 • S0
  lemma-CS01-CS02-K0-CS01-K0=S0-CS02-K0-CS01-K0-CS01-S0-S0-S0 =
    equational CS01 • CS02 • K0 • CS01 • K0
      by general-comm auto
    equals CS02 • CS01 • K0 • CS01 • K0
      by right lemma-CS01-K0-CS01-K0=S0-K0-CS01-K0-CS01-S0-S0-S0
    equals CS02 • S0 • K0 • CS01 • K0 • CS01 • S0 • S0 • S0
      by general-comm auto
    equals S0 • CS02 • K0 • CS01 • K0 • CS01 • S0 • S0 • S0


  lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0 : Rel ⊢ CS02 • K0 • CS02 • K0 === S0 • K0 • CS02 • K0 • CS02 • S0 • S0 • S0
  lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0 =
    equational CS02 • K0 • CS02 • K0
      by by-basis-change Swap12 Swap12 (lemma-CS01-K0-CS01-K0=S0-K0-CS01-K0-CS01-S0-S0-S0) 100 auto
    equals S0 • K0 • CS02 • K0 • CS02 • S0 • S0 • S0




  lemma-CS01-K0-S0-CS01-K0-CS01=K0-S0-CS01-K0-S1 : Rel ⊢ CS01 • K0 • S0 • CS01 • K0 • CS01 === K0 • S0 • CS01 • K0 • S1
  lemma-CS01-K0-S0-CS01-K0-CS01=K0-S0-CS01-K0-S1 =
    equational CS01 • K0 • S0 • CS01 • K0 • CS01
      by DK.general-rewrite 100 auto
    equals (CS01 • K0 • CS01) • (S0 • K0 • CS01 • K0 • CS01) • CS01 ^ 3 • K0 • iI
      by right left symm (axiom ax-CS01-K0-CS01-K0-S0=S0-K0-CS01-K0-CS01)
    equals (CS01 • K0 • CS01) • (CS01 • K0 • CS01 • K0 • S0) • CS01 ^ 3 • K0 • iI
      by general-assoc auto
    equals (CS01 • K0) • (CS01 • CS01 • K0) • CS01 • K0 • S0 • CS01 ^ 3 • K0 • iI
      by right left axiom ax-CS01-CS01-K0=K0-CX10
    equals (CS01 • K0) • (K0 • CX10) • CS01 • K0 • S0 • CS01 ^ 3 • K0 • iI
      by general-assoc auto
    equals CS01 • (K0 • K0) • CX10 • CS01 • K0 • S0 • CS01 ^ 3 • K0 • iI
      by right left axiom ax-K0-K0=iI-iI-iI
    equals CS01 • (iI ^ 3) • CX10 • CS01 • K0 • S0 • CS01 ^ 3 • K0 • iI
      by mvI.general-rewrite 100 auto
    equals CS01 • (CX10 • CS01) • K0 • S0 • CS01 ^ 3 • K0
      by right left axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10
    equals CS01 • (S1 • CS01 • CS01 • CS01 • CX10) • K0 • S0 • CS01 ^ 3 • K0
      by Diag.general-rewrite 200 auto
    equals S1 • (CX10 • K0) • S0 • CS01 ^ 3 • K0
      by right left axiom ax-CX10-K0=K0-CS01-CS01
    equals S1 • (K0 • CS01 • CS01) • S0 • CS01 ^ 3 • K0
      by Diag.general-rewrite 200 auto
    equals (S1 • K0) • S0 • CS01 • K0
      by general-comm auto
    equals K0 • S0 • CS01 • K0 • S1



  lemma-CS01-K0-S0-CS01-K0=K0-S0-CS01-K0-S1-CS01-CS01-CS01 : Rel ⊢ CS01 • K0 • S0 • CS01 • K0 === K0 • S0 • CS01 • K0 • S1 • CS01 • CS01 • CS01
  lemma-CS01-K0-S0-CS01-K0=K0-S0-CS01-K0-S1-CS01-CS01-CS01 =
    equational CS01 • K0 • S0 • CS01 • K0
      by Diag.general-rewrite 100 auto
    equals (CS01 • K0 • S0 • CS01 • K0 • CS01) • CS01 ^ 3
      by left lemma-CS01-K0-S0-CS01-K0-CS01=K0-S0-CS01-K0-S1
    equals (K0 • S0 • CS01 • K0 • S1) • CS01 ^ 3
      by general-assoc auto
    equals K0 • S0 • CS01 • K0 • S1 • CS01 • CS01 • CS01


  lemma-CS02-K0-S0-CS02-K0=K0-S0-CS02-K0-S2-CS02-CS02-CS02 : Rel ⊢ CS02 • K0 • S0 • CS02 • K0 === K0 • S0 • CS02 • K0 • S2 • CS02 • CS02 • CS02
  lemma-CS02-K0-S0-CS02-K0=K0-S0-CS02-K0-S2-CS02-CS02-CS02 = by-basis-change Swap12 Swap12 (lemma-CS01-K0-S0-CS01-K0=K0-S0-CS01-K0-S1-CS01-CS01-CS01) 100 auto


  lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ : Rel ⊢ CS01 • CS02 • K0 • CS01 • CS02 • K0 === S0 • K0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ
  lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ =
    equational CS01 • CS02 • K0 • CS01 • CS02 • K0
      by Diag.general-rewrite 100 auto
    equals (CS01 • CS02 • K0 • CS01 • CS02 • K0 • S0) • S0 ^ 3
      by left axiom ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ
    equals (S0 • K0 • CS01 • CS02 • K0 • CS01 • CS02 • CS12 • CCZ) • S0 ^ 3
      by Diag.general-rewrite 100 auto
    equals S0 • K0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ



  mvKL-step : Step-Function Gate Rel
  mvKL-step (K0-gen ∷ K0-gen ∷ xs) = just (iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (axiom ax-K0-K0=iI-iI-iI))
  mvKL-step (iI-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ iI-gen ∷ xs , at-head (axiom ax-iI-K0=K0-iI))
  mvKL-step (S1-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-K0=K0-S1))
  mvKL-step (S2-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-K0=K0-S2))
  mvKL-step (X1-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ X1-gen ∷ xs , at-head (axiom ax-X1-K0=K0-X1))
  mvKL-step (X2-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ X2-gen ∷ xs , at-head (axiom ax-X2-K0=K0-X2))
  mvKL-step (CS12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-K0=K0-CS12))
  mvKL-step (CX12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CX12-K0=K0-CX12))
  mvKL-step (CX21-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CX21-gen ∷ xs , at-head (axiom ax-CX21-K0=K0-CX21))
  mvKL-step (Swap12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-K0=K0-Swap12))
  mvKL-step (S0-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ X0-gen ∷ xs , at-head (axiom ax-S0-S0-K0=K0-X0))
  mvKL-step (CS01-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CS01-CS01-K0=K0-CX10))
  mvKL-step (CS02-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CS02-CS02-K0=K0-CX20))
  mvKL-step (CCZ-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCZ-K0=K0-CCX0))
  mvKL-step (X0-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S0-gen ∷ S0-gen ∷ xs , at-head (axiom ax-X0-K0=K0-S0-S0))
  mvKL-step (CX10-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS01-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CX10-K0=K0-CS01-CS01))
  mvKL-step (CX20-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS02-gen ∷ CS02-gen ∷ xs , at-head (axiom ax-CX20-K0=K0-CS02-CS02))
  mvKL-step (CCX0-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CCZ-gen ∷ xs , at-head (axiom ax-CCX0-K0=K0-CCZ))
  mvKL-step (CS01-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS01-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs , at-head (lemma-CS01-K0-CS01-K0=S0-K0-CS01-K0-CS01-S0-S0-S0))
  mvKL-step (CS02-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS02-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs , at-head (lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0))
  mvKL-step (iI-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-S0-K0=S0-K0-iI))
  mvKL-step (S1-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ S1-gen ∷ xs , at-head (lemma-S1-S0-K0=S0-K0-S1))
  mvKL-step (S2-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ S2-gen ∷ xs , at-head (lemma-S2-S0-K0=S0-K0-S2))
  mvKL-step (CS12-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS12-gen ∷ xs , at-head (lemma-CS12-S0-K0=S0-K0-CS12))
  mvKL-step (CS01-gen ∷ CS01-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CX10-gen ∷ xs , at-head (lemma-CS01-CS01-S0-K0=S0-K0-CX10))
  mvKL-step (CS02-gen ∷ CS02-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CX20-gen ∷ xs , at-head (lemma-CS02-CS02-S0-K0=S0-K0-CX20))
  mvKL-step (CCZ-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCZ-S0-K0=S0-K0-CCX0))
  mvKL-step (iI-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-CS01-K0=CS01-K0-iI))
  mvKL-step (S1-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ S1-gen ∷ xs , at-head (lemma-S1-CS01-K0=CS01-K0-S1))
  mvKL-step (S2-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ S2-gen ∷ xs , at-head (lemma-S2-CS01-K0=CS01-K0-S2))
  mvKL-step (CS12-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ CS12-gen ∷ xs , at-head (lemma-CS12-CS01-K0=CS01-K0-CS12))
  mvKL-step (S0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ X0-gen ∷ xs , at-head (lemma-S0-S0-CS01-K0=CS01-K0-X0))
  mvKL-step (CS02-gen ∷ CS02-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ CX20-gen ∷ xs , at-head (lemma-CS02-CS02-CS01-K0=CS01-K0-CX20))
  mvKL-step (CCZ-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCZ-CS01-K0=CS01-K0-CCX0))
  mvKL-step (iI-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS02-gen ∷ K0-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-CS02-K0=CS02-K0-iI))
  mvKL-step (S1-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS02-gen ∷ K0-gen ∷ S1-gen ∷ xs , at-head (lemma-S1-CS02-K0=CS02-K0-S1))
  mvKL-step (S2-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS02-gen ∷ K0-gen ∷ S2-gen ∷ xs , at-head (lemma-S2-CS02-K0=CS02-K0-S2))
  mvKL-step (CS12-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS02-gen ∷ K0-gen ∷ CS12-gen ∷ xs , at-head (lemma-CS12-CS02-K0=CS02-K0-CS12))
  mvKL-step (S0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS02-gen ∷ K0-gen ∷ X0-gen ∷ xs , at-head (lemma-S0-S0-CS02-K0=CS02-K0-X0))
  mvKL-step (CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS02-gen ∷ K0-gen ∷ CX10-gen ∷ xs , at-head (lemma-CS01-CS01-CS02-K0=CS02-K0-CX10))
  mvKL-step (CCZ-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS02-gen ∷ K0-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCZ-CS02-K0=CS02-K0-CCX0))
  mvKL-step (K0-gen ∷ S0-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ X0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs , at-head (lemma-K0-S0-K0=S0-K0-X0-S0-S0-S0))
  mvKL-step (CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ xs , at-head (lemma-CS01-K0-S0-CS01-K0=K0-S0-CS01-K0-S1-CS01-CS01-CS01))
  mvKL-step (CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ xs , at-head (lemma-CS02-K0-S0-CS02-K0=K0-S0-CS02-K0-S2-CS02-CS02-CS02))
  mvKL-step (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ xs , at-head (lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ))
  mvKL-step (iI-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ iI-gen ∷ xs , at-head (lemma-iI-CS01-CS02-K0=CS01-CS02-K0-iI))
  mvKL-step (S1-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ S1-gen ∷ xs , at-head (lemma-S1-CS01-CS02-K0=CS01-CS02-K0-S1))
  mvKL-step (S2-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ S2-gen ∷ xs , at-head (lemma-S2-CS01-CS02-K0=CS01-CS02-K0-S2))
  mvKL-step (CS12-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ CS12-gen ∷ xs , at-head (lemma-CS12-CS01-CS02-K0=CS01-CS02-K0-CS12))
  mvKL-step (S0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ X0-gen ∷ xs , at-head (lemma-S0-S0-CS01-CS02-K0=CS01-CS02-K0-X0))
  mvKL-step (CCZ-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ CCX0-gen ∷ xs , at-head (lemma-CCZ-CS01-CS02-K0=CS01-CS02-K0-CCX0))
  mvKL-step (CS01-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS01-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ xs , at-head (lemma-CS01-CS02-K0-CS01-K0=S0-CS02-K0-CS01-K0-CS01-S0-S0-S0))

  mvKL-step _ = nothing

  module mvKL = Rewriting.Step (step-cong mvKL-step)



  module mvKL2 = Rewriting.Step (step-cong (mvKL-step then order-K0-step))


  module P16DK = Rewriting.Step (step-cong (order-step then mvKL-step then p16d-step then d-step then p16-step))

  lemma-KS : Rel ⊢ K0 • S0 === S0 • S0 • S0 • K0 • S0 • S0 • S0 • K0 • iI
  lemma-KS =
    equational K0 • S0
      by P16DK.general-rewrite 100 auto
    equals (S0 • S0) • (S0 • K0 • S0 • K0 • S0 • K0) • K0 • S0 ^ 3 • X0 • iI ^ 2
      by P16DK.general-rewrite 100 auto
    equals (S0 • S0) • (S0 • K0) • S0 • (K0 • X0) • iI
      by right right right left symm (axiom ax-S0-S0-K0=K0-X0)
    equals (S0 • S0) • (S0 • K0) • S0 • (S0 • S0 • K0) • iI
      by general-assoc auto
    equals S0 • S0 • S0 • K0 • S0 • S0 • S0 • K0 • iI


  lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02 : Rel ⊢ CS02 • K0 • S0 • CS01 • CS02 • K0 === CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
  lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02 =
    equational CS02 • K0 • S0 • CS01 • CS02 • K0
      by general-assoc auto
    equals CS02 • (K0 • S0) • CS01 • CS02 • K0
      by right left lemma-KS
    equals CS02 • (S0 • S0 • S0 • K0 • S0 • S0 • S0 • K0 • iI) • CS01 • CS02 • K0
      by P16DK.general-rewrite 200 auto
    equals (CS02 • S0 • S0 • S0 • K0 • S0 • S0) • (S0 • K0 • CS01 • CS02 • K0 • CS01 • CS02 • CS12 • CCZ) • CS01 ^ 3 • CS02 ^ 3 • CS12 ^ 3 • CCZ • iI
      by right left symm (axiom ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ)
    equals (CS02 • S0 • S0 • S0 • K0 • S0 • S0) • (CS01 • CS02 • K0 • CS01 • CS02 • K0 • S0) • CS01 ^ 3 • CS02 ^ 3 • CS12 ^ 3 • CCZ • iI
      by P16DK.general-rewrite 2000 auto
    equals (CS02 • X0) • (S0 • K0 • CS01 • CS02 • K0 • CS01 • CS02 • CS12 • CCZ) • CS12 ^ 3 • CCZ • K0 • S0 • CS01 ^ 3 • CS02 ^ 3 • CS12 ^ 3 • CCZ
      by right left symm (axiom ax-CS01-CS02-K0-CS01-CS02-K0-S0=S0-K0-CS01-CS02-K0-CS01-CS02-CS12-CCZ)
    equals (CS02 • X0) • (CS01 • CS02 • K0 • CS01 • CS02 • K0 • S0) • CS12 ^ 3 • CCZ • K0 • S0 • CS01 ^ 3 • CS02 ^ 3 • CS12 ^ 3 • CCZ
      by P16DK.general-rewrite 1000 auto
    equals CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02


  lemma-CS01-K0-S0-CS01-CS02-K0=CS02-K0-S0-CS01-CS02-K0-S2-S2-S2-S1-CS01-CS02-CS01-CS01 : Rel ⊢ CS01 • K0 • S0 • CS01 • CS02 • K0 === CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
  lemma-CS01-K0-S0-CS01-CS02-K0=CS02-K0-S0-CS01-CS02-K0-S2-S2-S2-S1-CS01-CS02-CS01-CS01 =
    equational CS01 • K0 • S0 • CS01 • CS02 • K0
      by Diag.general-rewrite 100 auto
    equals (CS02 • CS02 • CS01 • CS02) • (CS02 • K0 • S0 • CS01 • CS02 • K0)
      by right lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02
    equals (CS02 • CS02 • CS01 • CS02) • (CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02)
      by Diag.general-rewrite 100 auto
    equals (CS02 • CS02 • CS02 • CS01) • (CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02)
      by mvKL.general-rewrite 100 auto
    equals CS02 • K0 • CX20 • CX10 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by P16DK.general-rewrite 200 auto
    equals CS02 • K0 • S0 • S1 • S1 • S2 • S2 • CS01 • CS02 • CX10 • CX20 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by mvKL.general-rewrite 100 auto
    equals CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S2 • S2 • CS01 • CS01 • CS02 • CS02 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by Diag.general-rewrite 100 auto
    equals CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02


  lemma-CS02-K0-CS01-K0-CS02-K0=CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-CX10-CX20 : Rel ⊢ CS02 • K0 • CS01 • K0 • CS02 • K0 === CS01 • K0 • CS02 • K0 • CS01 • K0 • S1 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • CX10 • CX20
  lemma-CS02-K0-CS01-K0-CS02-K0=CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-CX10-CX20 =
    equational CS02 • K0 • CS01 • K0 • CS02 • K0
      by Diag.general-rewrite 100 auto
    equals (CS02 • CS01 ^ 3) • (CS01 • K0 • CS01 • K0) • CS02 • K0
      by right left lemma-CS01-K0-CS01-K0=S0-K0-CS01-K0-CS01-S0-S0-S0
    equals (CS02 • CS01 ^ 3) • (S0 • K0 • CS01 • K0 • CS01 • S0 • S0 • S0) • CS02 • K0
      by P16DK.general-rewrite 500 auto
    equals (CS01 • CS02 • S0 • K0) • CS01 •  K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • CS01 • CS01 • CS12 • CS12 • CS12 • X0 • CX10 • CCX0
      by P16DK.general-rewrite 500 auto
    equals (CS01 • CS02 • S0 • K0) • (CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02) • S2 • S2 • S2 • CS01 • CS02 • CS12 • CS12 • CS12 • X0 • CX10 • CCX0
      by right left symm (lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02)
    equals (CS01 • CS02 • S0 • K0) • (CS02 • K0 • S0 • CS01 • CS02 • K0) • S2 • S2 • S2 • CS01 • CS02 • CS12 • CS12 • CS12 • X0 • CX10 • CCX0
      by P16DK.general-rewrite 500 auto
    equals (CS01 • CS02 ^ 3) • (S0 • K0 • CS02 • K0 • CS02 • S0 • S0 • S0) • CS01 • K0 • S1 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • CX10 • CX20
      by right left symm (lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0)
    equals (CS01 • CS02 ^ 3) • (CS02 • K0 • CS02 • K0) • CS01 • K0 • S1 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • CX10 • CX20
      by P16DK.general-rewrite 100 auto
    equals CS01 • K0 • CS02 • K0 • CS01 • K0 • S1 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • CX10 • CX20

  lemma-nice4 : Rel ⊢ S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0 === K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02
  lemma-nice4 =
    equational S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0
      by general-assoc auto
    equals (S0 • CS01 • K0) • (CS02 • K0 • CS01 • K0 • CS02 • K0) • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0
      by right left lemma-CS02-K0-CS01-K0-CS02-K0=CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-CX10-CX20
    equals (S0 • CS01 • K0) • (CS01 • K0 • CS02 • K0 • CS01 • K0 • S1 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • CX10 • CX20) • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0
      by P16DK.general-rewrite 500 auto
    equals K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02

  lemma-K0-CS01-K0-CS02-K0-CS01-K0-CS02=S0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-S0-S0-S0-S2-CS01-CS01-CCZ-CX10-CX20-CCX0 : Rel ⊢ K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 === S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0
  lemma-K0-CS01-K0-CS02-K0-CS01-K0-CS02=S0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-S0-S0-S0-S2-CS01-CS01-CCZ-CX10-CX20-CCX0 = symm lemma-nice4


  lemma-CCK'^3 : Rel ⊢ (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI) • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI) • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI) === CS12 ^ 2
  lemma-CCK'^3 =
    equational (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI) • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI) • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI)
      by P16DK.general-rewrite 2000 auto
    equals (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02) • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • CS02 • CS02 • CCZ • iI • iI • CCX0 • CX10
      by left lemma-K0-CS01-K0-CS02-K0-CS01-K0-CS02=S0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-S0-S0-S0-S2-CS01-CS01-CCZ-CX10-CX20-CCX0
    equals (S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0) • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • CS02 • CS02 • CCZ • iI • iI • CCX0 • CX10
      by P16DK.general-rewrite 2000 auto
    equals (S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • S0 • CS02 • K0 • S0 • CS01 • K0 • CS02) • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02) • K0 • CS01 • K0 • S2 • S2 • S2 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • CX10 • CX20 • CX10
      by right left lemma-K0-CS01-K0-CS02-K0-CS01-K0-CS02=S0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-S0-S0-S0-S2-CS01-CS01-CCZ-CX10-CX20-CCX0
    equals (S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • S0 • CS02 • K0 • S0 • CS01 • K0 • CS02) • (S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0) • K0 • CS01 • K0 • S2 • S2 • S2 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • CX10 • CX20 • CX10
      by P16DK.general-rewrite 4000 auto
    equals S0 • (CS01 • K0 • S0 • CS01 • CS02 • K0) • S0 • CS01 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • CS01 • CS01 • CS02 • CS12 • CCZ • iI • iI • CX20 • CX10
      by right left lemma-CS01-K0-S0-CS01-CS02-K0=CS02-K0-S0-CS01-CS02-K0-S2-S2-S2-S1-CS01-CS02-CS01-CS01
    equals S0 • (CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02) • S0 • CS01 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • CS01 • CS01 • CS02 • CS12 • CCZ • iI • iI • CX20 • CX10
      by P16DK.general-rewrite 2000 auto
    equals CS12 ^ 2




  lemma-CCK'-CCK'-CS12-CS12-CCK'=ε : Rel ⊢ CCK' • CCK' • CS12 • CS12 • CCK' === ε
  lemma-CCK'-CCK'-CS12-CS12-CCK'=ε =
    equational CCK' • CCK' • CS12 • CS12 • CCK'
            by cong (axiom ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI) (cong (axiom ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI) (right right axiom ax-CCK'=K0-CS01-K0-CS02-K0-CS01-K0-CCX0-CX10-CS12-CS12-CS12-CS02-CS02-CS02-iI-iI))
        equals ((K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI)) • ((K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI)) • CS12 • CS12 • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI)
            by (general-comm auto)
        equals (((K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI)) • ((K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI)) • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI)) • CS12 • CS12
            by left lemma-CCK'^3
        equals CS12 ^ 2 • CS12 • CS12
          by general-assoc auto
        equals CS12 • CS12 • CS12 • CS12
            by axiom ax-CS12-CS12-CS12-CS12=ε
        equals ε

  lemma-iI-CCK'=CCK'-iI : Rel ⊢ iI • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI === (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI) • iI
  lemma-iI-CCK'=CCK'-iI =
    equational iI • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by general-comm auto
    equals (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI) • iI

  lemma-iI-CK10=CK10-iI : Rel ⊢ iI • CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI === (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) • iI
  lemma-iI-CK10=CK10-iI =
    equational iI • CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI
      by general-comm auto
    equals (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) • iI

  lemma-iI-CK20=CK20-iI : Rel ⊢ iI • CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI === (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI) • iI
  lemma-iI-CK20=CK20-iI =
    equational iI • CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI
      by general-comm auto
    equals (CS02 • K0 • CS02 • K0 • CS02 • S2 • S2 • S2 • iI) • iI



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

  nf-dk : ListNF Rel
  nf-dk = nf-pde ∘ record { listnf = P16DK.multistep 2000 ; lemma-listnf = P16DK.lemma-multistep 2000 }

  nf-dk-rep : ListNF Rel
  nf-dk-rep = rep 5 nf-dk


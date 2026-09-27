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

open import Examples.Groups.Clifford+CS-3qubit.Step4.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8D
open import Examples.Groups.Clifford+CS-3qubit.Step4.KD

module Examples.Groups.Clifford+CS-3qubit.Step4.Lemmas where

  lemma-CS01-K2=K2-CS01 : Rel ⊢ CS01 • K2 === K2 • CS01
  lemma-CS01-K2=K2-CS01 =
    equational CS01 • K2
      by right axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12
    equals CS01 • Swap12 • Swap01 • K0 • Swap01 • Swap12
      by ListNF.listnfeq' nf-pde auto
    equals Swap12 • Swap01 • CS12 • K0 • Swap01 • Swap12
      by general-assoc auto
    equals Swap12 • Swap01 • (CS12 • K0) • Swap01 • Swap12
      by right right left ListNF.listnfeq' nf-e4e auto
    equals Swap12 • Swap01 • (K0 • CS12) • Swap01 • Swap12
      by right right (ListNF.listnfeq' nf-pde auto)
    equals Swap12 • Swap01 • (K0) • Swap01 • Swap12 • CS01
      by general-assoc auto
    equals (Swap12 • Swap01 • K0 • Swap01 • Swap12) • CS01
      by left symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals K2 • CS01

  lemma-S1-K2=K2-S1 : Rel ⊢ S1 • K2 === K2 • S1
  lemma-S1-K2=K2-S1 =
    equational S1 • K2
      by right axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12
    equals S1 • Swap12 • Swap01 • K0 • Swap01 • Swap12
      by ListNF.listnfeq' nf-pde auto
    equals Swap12 • Swap01 • S2 • K0 • Swap01 • Swap12
      by general-assoc auto
    equals Swap12 • Swap01 • (S2 • K0) • Swap01 • Swap12
      by right right left ListNF.listnfeq' nf-e4e auto
    equals Swap12 • Swap01 • (K0 • S2) • Swap01 • Swap12
      by right right (ListNF.listnfeq' nf-pde auto)
    equals Swap12 • Swap01 • (K0) • Swap01 • Swap12 • S1
      by general-assoc auto
    equals (Swap12 • Swap01 • K0 • Swap01 • Swap12) • S1
      by left symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals K2 • S1

  lemma-K2-K0=K0-K2 : Rel ⊢ K2 • K0 === K0 • K2
  lemma-K2-K0=K0-K2 =
    equational K2 • K0
      by left axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12
    equals (Swap12 • Swap01 • K0 • Swap01 • Swap12) • K0
      by general-assoc auto
    equals Swap12 • (Swap01 • K0 • Swap01) • (Swap12 • K0)
      by right cong (symm (axiom ax-K1=Swap01-K0-Swap01)) ( ListNF.listnfeq' nf-p24k0d  auto)
    equals Swap12 • K1 • (K0 • Swap12)
      by symm (cong refl assoc)
    equals Swap12 • (K1 • K0) • Swap12
      by right left axiom ax-K1-K0=K0-K1
    equals Swap12 • (K0 • K1) • Swap12
      by general-assoc auto
    equals (Swap12 • K0) • K1 • Swap12
      by left ListNF.listnfeq' nf-p24k0d  auto
    equals (K0 • Swap12) • K1 • Swap12
      by right left axiom ax-K1=Swap01-K0-Swap01
    equals (K0 • Swap12) • (Swap01 • K0 • Swap01) • Swap12
      by general-assoc auto
    equals K0 • Swap12 • Swap01 • K0 • Swap01 • Swap12
      by right symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals K0 • K2


  mvK2-step : Step-Function Gate Rel
  mvK2-step (K2-gen ∷ iI-gen ∷ xs) = just (iI-gen ∷ K2-gen ∷ xs , at-head (symm (lemma-iI-K2=K2-iI)))
  mvK2-step (K2-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ K2-gen ∷ xs , at-head (lemma-K2-K0=K0-K2))
  mvK2-step (K2-gen ∷ CS01-gen ∷ xs) = just (CS01-gen ∷ K2-gen ∷ xs , at-head (symm lemma-CS01-K2=K2-CS01))
  mvK2-step (K2-gen ∷ S1-gen ∷ xs) = just (S1-gen ∷ K2-gen ∷ xs , at-head (symm lemma-S1-K2=K2-S1))
  mvK2-step _ = nothing

  module mvK2 = Rewriting.Step (step-cong mvK2-step)

  lemma-K2-CK10=CK10-K2 : Rel ⊢ K2 • CK10 === CK10 • K2
  lemma-K2-CK10=CK10-K2 =
    equational K2 • CK10
      by right (ListNF.listnfeq' nf-e4 auto)
    equals K2 • CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI
      by mvK2.general-rewrite 100 auto
    equals (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) • K2
      by left symm ((ListNF.listnfeq' nf-e4 auto))
    equals CK10 • K2


  lemma-CX01-K2=K2-CX01 : Rel ⊢ CX01 • K2 === K2 • CX01
  lemma-CX01-K2=K2-CX01 =
    equational CX01 • K2
      by right axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12
    equals CX01 • Swap12 • Swap01 • K0 • Swap01 • Swap12
      by ListNF.listnfeq' nf-pde auto
    equals Swap12 • Swap01 • CX12 • K0 • Swap01 • Swap12
      by general-assoc auto
    equals Swap12 • Swap01 • (CX12 • K0) • Swap01 • Swap12
      by right right left ListNF.listnfeq' nf-p24k0d auto
    equals Swap12 • Swap01 • (K0 • CX12) • Swap01 • Swap12
      by right right (ListNF.listnfeq' nf-pde auto)
    equals Swap12 • Swap01 • (K0) • Swap01 • Swap12 • CX01
      by general-assoc auto
    equals (Swap12 • Swap01 • K0 • Swap01 • Swap12) • CX01
      by left symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals K2 • CX01

  lemma-CX10-K2=K2-CX10 : Rel ⊢ CX10 • K2 === K2 • CX10
  lemma-CX10-K2=K2-CX10 =
    equational CX10 • K2
      by left  ListNF.listnfeq' nf-e4 auto
    equals (K0 • CS01 • CS01 • K0 • iI) • K2
      by mvK2.general-rewrite 100 auto
    equals K2 • (K0 • CS01 • CS01 • K0 • iI)
      by right ListNF.listnfeq' nf-e4 auto
    equals K2 • CX10

  lemma-Swap01-K2=K2-Swap01 : Rel ⊢ Swap01 • K2 === K2 • Swap01
  lemma-Swap01-K2=K2-Swap01 =
    equational Swap01 • K2
      by ListNF.listnfeq' nf-s8e auto
    equals CX01 • CX10 • (CX01 • K2)
      by right right lemma-CX01-K2=K2-CX01
    equals CX01 • CX10 • (K2 • CX01)
      by general-assoc auto
    equals CX01 • (CX10 • K2) • CX01
      by right left lemma-CX10-K2=K2-CX10
    equals CX01 • (K2 • CX10) • CX01
      by general-assoc auto
    equals (CX01 • K2) • CX10 • CX01
      by left lemma-CX01-K2=K2-CX01
    equals (K2 • CX01) • CX10 • CX01
      by general-assoc auto
    equals K2 • CX01 • CX10 • CX01
      by right ListNF.listnfeq' nf-s8e auto
    equals K2 • Swap01



  lemma-K2-K1=K1-K2 : Rel ⊢ K2 • K1 === K1 • K2
  lemma-K2-K1=K1-K2 =
    equational K2 • K1
      by right axiom ax-K1=Swap01-K0-Swap01
    equals K2 • Swap01 • K0 • Swap01
      by symm assoc
    equals (K2 • Swap01) • K0 • Swap01
      by left symm lemma-Swap01-K2=K2-Swap01
    equals (Swap01 • K2) • K0 • Swap01
      by general-assoc auto
    equals Swap01 • (K2 • K0) • Swap01
      by right left lemma-K2-K0=K0-K2
    equals Swap01 • (K0 • K2) • Swap01
      by cong refl assoc
    equals Swap01 • K0 • (K2 • Swap01)
      by right right lemma-Swap01-K2=K2-Swap01 reversed
    equals Swap01 • K0 • (Swap01 • K2)
      by general-assoc auto
    equals (Swap01 • K0 • Swap01) • K2
      by left symm (axiom ax-K1=Swap01-K0-Swap01)
    equals K1 • K2


  lemma-CCX2 : Rel ⊢ CCX2 === K2 • CCZ • K2 • iI
  lemma-CCX2 =
    equational CCX2
      by ListNF.listnfeq' nf-s7e auto
    equals Swap12 • Swap01 • CCX0 • Swap01 • Swap12
      by right right left ListNF.listnfeq' nf-e4e auto
    equals Swap12 • Swap01 • (K0 • CCZ • K0 • iI) • Swap01 • Swap12
      by ListNF.listnfeq' nf-s7e auto
    equals Swap12 • Swap01 • K0  • Swap01 • Swap12  • Swap12 • Swap01 • CCZ • K0 • iI • Swap01 • Swap12
      by mvI.general-rewrite 50 auto
    equals (Swap12 • Swap01 • K0  • Swap01 • Swap12)  • (Swap12 • Swap01 • CCZ • K0 • Swap01 • Swap12) • iI
      by left symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals K2  • (Swap12 • Swap01 • CCZ • K0 • Swap01 • Swap12) • iI
      by right left  (ListNF.listnfeq' nf-pde auto)
    equals K2  • (CCZ • Swap12 • Swap01 • K0 • Swap01 • Swap12) • iI
      by right left right symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals K2  • (CCZ • K2) • iI
      by general-assoc auto
    equals K2 • CCZ • K2 • iI

  lemma-CX02 : Rel ⊢ CX02 === K2 • CS02 • CS02 • K2 • iI
  lemma-CX02 =
    equational CX02
      by ListNF.listnfeq' nf-s7e auto
    equals Swap01 • Swap12 • Swap01 • CX20 • Swap01 • Swap12 • Swap01
      by right right right left ListNF.listnfeq' nf-e4e auto
    equals Swap01 • Swap12 • Swap01 • (K0 • CS02 • CS02 • K0 • iI) • Swap01 • Swap12 • Swap01
      by ListNF.listnfeq' nf-s7e auto
    equals Swap01 • Swap12 • Swap01 • K0  • Swap01 • Swap12  • Swap12 • Swap01 • CS02 • CS02 • K0 • iI • Swap01 • Swap12 • Swap01
      by mvI.general-rewrite 50 auto
    equals Swap01 • (Swap12 • Swap01 • K0  • Swap01 • Swap12)  • (Swap12 • Swap01 • CS02 • CS02 • K0 • Swap01 • Swap12 • Swap01) • iI
      by right left symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals Swap01 • K2  • (Swap12 • Swap01 • CS02 • CS02 • K0 • Swap01 • Swap12 • Swap01) • iI
      by right right left  (ListNF.listnfeq' nf-pde auto)
    equals Swap01 • K2  • (CS12 • CS12 • Swap12 • Swap01 • K0 • Swap01 • Swap12 • Swap01) • iI
      by general-assoc auto
    equals Swap01 • K2  • (CS12 • CS12 • Swap12 • Swap01 • K0 • Swap01 • Swap12) • Swap01 • iI
      by right right left right right symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
    equals Swap01 • K2  • (CS12 • CS12 • K2) • Swap01 • iI
      by general-assoc auto
    equals (Swap01 • K2)  • (CS12 • CS12) • (K2 • Swap01) • iI
      by left lemma-Swap01-K2=K2-Swap01
    equals (K2 • Swap01) • (CS12 • CS12) • (K2 • Swap01) • iI
      by right right left symm (lemma-Swap01-K2=K2-Swap01)
    equals (K2 • Swap01) • (CS12 • CS12) • (Swap01 • K2) • iI
      by ListNF.listnfeq' nf-pde auto
    equals K2 • CS02 • CS02 • K2 • iI

  lemma-CX01 : Rel ⊢ CX01 === K1 • CS01 • CS01 • K1 • iI
  lemma-CX01 =
    equational CX01
      by ListNF.listnfeq' nf-s7e auto
    equals Swap01 • CX10 • Swap01
      by right left ListNF.listnfeq' nf-e4e auto
    equals Swap01 • (K0 • CS01 • CS01 • K0 • iI) • Swap01
      by ListNF.listnfeq' nf-s7e auto
    equals (Swap01 • K0 • Swap01) • (Swap01 • CS01 • CS01 • Swap01) • (Swap01 • K0 • Swap01) • Swap01 • iI • Swap01
      by cong (symm (axiom ax-K1=Swap01-K0-Swap01)) (right left symm (axiom ax-K1=Swap01-K0-Swap01))
    equals (K1) • (Swap01 • CS01 • CS01 • Swap01) • (K1) • Swap01 • iI • Swap01
      by ListNF.listnfeq' nf-pde auto
    equals K1 • CS01 • CS01 • K1 • iI


  lemma-CX12 : Rel ⊢ CX12 === K2 • CS12 • CS12 • K2 • iI
  lemma-CX12 =
    equational CX12
      by ListNF.listnfeq' nf-s7e auto
    equals Swap01 • CX02 • Swap01
      by right left lemma-CX02
    equals Swap01 • (K2 • CS02 • CS02 • K2 • iI) • Swap01
      by mvI.general-rewrite 100 auto
    equals (Swap01 • K2) • CS02 • CS02 • (K2 • Swap01) • iI
      by cong (lemma-Swap01-K2=K2-Swap01) (right right left symm (lemma-Swap01-K2=K2-Swap01))
    equals (K2 • Swap01) • CS02 • CS02 • (Swap01 • K2) • iI
      by general-assoc auto
    equals K2 • (Swap01 • CS02 • CS02 • Swap01) • K2 • iI
      by right left ListNF.listnfeq' nf-pd auto
    equals K2 • (CS12 • CS12) • K2 • iI
      by general-assoc auto
    equals K2 • CS12 • CS12 • K2 • iI


  lemma-CCX2-K0-CK10=K0-CK10-CCX2 : Rel ⊢ CCX2 • K0 • CK10 === K0 • CK10 • CCX2
  lemma-CCX2-K0-CK10=K0-CK10-CCX2 =
    equational CCX2 • K0 • CK10
      by left lemma-CCX2
    equals (K2 • CCZ • K2 • iI) • K0 • CK10
      by left right right symm (lemma-iI-K2=K2-iI)
    equals (K2 • CCZ • iI • K2) • K0 • CK10
      by general-assoc auto
    equals (K2 • CCZ • iI) • (K2 • K0) • CK10
      by right left lemma-K2-K0=K0-K2
    equals (K2 • CCZ • iI) • (K0 • K2) • CK10
      by general-assoc auto
    equals (K2 • CCZ • iI) • K0 • K2 • CK10
      by right right lemma-K2-CK10=CK10-K2
    equals (K2 • CCZ • iI) • K0 • CK10 • K2
      by ListNF.listnfeq' nf-e4e auto
    equals (K2 • K0) • CK10 • CCZ • (iI • K2)
      by cong (lemma-K2-K0=K0-K2) (right right lemma-iI-K2=K2-iI)
    equals (K0 • K2) • CK10 • CCZ • (K2 • iI)
      by general-assoc auto
    equals K0 • (K2 • CK10) • CCZ • (K2 • iI)
      by right left lemma-K2-CK10=CK10-K2
    equals K0 • (CK10 • K2) • CCZ • (K2 • iI)
      by general-assoc auto
    equals K0 • CK10 • (K2 • CCZ • K2 • iI)
      by right right symm lemma-CCX2
    equals K0 • CK10 • CCX2

  lemma-CCX2-CX02 : Rel ⊢ CCX2 • CX02 === K2 • CCZ • CS02 • CS02 • K2 • iI
  lemma-CCX2-CX02 =
    equational CCX2 • CX02
      by cong lemma-CCX2 lemma-CX02
    equals (K2 • CCZ • K2 • iI) • (K2 • CS02 • CS02 • K2 • iI)
      by general-assoc auto
    equals (K2 • CCZ) • ((K2 • iI) • K2) • CS02 • CS02 • K2 • iI
      by right left lemma-K2-iI-K2=ε
    equals (K2 • CCZ) • (ε) • CS02 • CS02 • K2 • iI
      by general-assoc auto
    equals K2 • CCZ • CS02 • CS02 • K2 • iI


  lemma-CCX2-CX12 : Rel ⊢ CCX2 • CX12 === K2 • CCZ • CS12 • CS12 • K2 • iI
  lemma-CCX2-CX12 =
    equational CCX2 • CX12
      by cong lemma-CCX2 lemma-CX12
    equals (K2 • CCZ • K2 • iI) • (K2 • CS12 • CS12 • K2 • iI)
      by general-assoc auto
    equals (K2 • CCZ) • ((K2 • iI) • K2) • CS12 • CS12 • K2 • iI
      by right left lemma-K2-iI-K2=ε
    equals (K2 • CCZ) • (ε) • CS12 • CS12 • K2 • iI
      by general-assoc auto
    equals K2 • CCZ • CS12 • CS12 • K2 • iI


  lemma-CCX2-CX02-CK10=CK10-CCX2-CX02 : Rel ⊢ CCX2 • CX02 • CK10 === CK10 • CCX2 • CX02
  lemma-CCX2-CX02-CK10=CK10-CCX2-CX02 =
    equational CCX2 • CX02 • CK10
      by symm assoc
    equals (CCX2 • CX02) • CK10
      by left lemma-CCX2-CX02
    equals (K2 • CCZ • CS02 • CS02 • K2 • iI) • CK10
      by mvI.general-rewrite 50 auto
    equals (K2 • CCZ • CS02 • CS02) • (K2 • CK10) • iI
      by right left lemma-K2-CK10=CK10-K2
    equals (K2 • CCZ • CS02 • CS02) • (CK10 • K2) • iI
      by general-assoc auto
    equals K2 • (CCZ • CS02 • CS02 • CK10) • K2 • iI
      by right left ListNF.listnfeq' nf-e4e auto
    equals K2 • (CK10 • CCZ • CS02 • CS02) • K2 • iI
      by general-assoc auto
    equals (K2 • CK10) • (CCZ • CS02 • CS02) • K2 • iI
      by left lemma-K2-CK10=CK10-K2
    equals (CK10 • K2) • (CCZ • CS02 • CS02) • K2 • iI
      by general-assoc auto
    equals CK10 • (K2 • CCZ • CS02 • CS02 • K2 • iI)
      by right lemma-CCX2-CX02 reversed
    equals CK10 • CCX2 • CX02

  lemma-CCX2-K0-CCX2-K0=K0-CCX2-K0-CCX2-CX12 : Rel ⊢ CCX2 • K0 • CCX2 • K0 === K0 • CCX2 • K0 • CCX2 • CX12
  lemma-CCX2-K0-CCX2-K0=K0-CCX2-K0-CCX2-CX12 =
    equational CCX2 • K0 • CCX2 • K0
      by cong lemma-CCX2 (right left lemma-CCX2)
    equals (K2 • CCZ • K2 • iI) • K0 • (K2 • CCZ • K2 • iI) • K0
      by mvI.general-rewrite 100 auto
    equals (K2 • CCZ) • (K2 • K0) • (K2 • CCZ • K2) • K0 • iI • iI
      by right left lemma-K2-K0=K0-K2
    equals (K2 • CCZ) • (K0 • K2) • (K2 • CCZ • K2) • K0 • iI • iI
      by general-assoc auto
    equals (K2 • CCZ) • K0 • (K2 • K2) • CCZ • K2 • K0 • iI • iI
      by right right left lemma-K2-K2=iI-iI-iI
    equals (K2 • CCZ) • K0 • (iI ^ 3) • CCZ • K2 • K0 • iI • iI
      by general-assoc auto
    equals ((K2 • CCZ) • K0 • (iI ^ 3) • CCZ) • (K2 • K0) • iI • iI
      by right left lemma-K2-K0=K0-K2
    equals ((K2 • CCZ) • K0 • (iI ^ 3) • CCZ) • (K0 • K2) • iI • iI
      by mvI.general-rewrite 100 auto
    equals K2 • (CCZ • K0 • iI ^ 3 • CCZ • K0 • iI) • K2 • iI
      by right left ListNF.listnfeq' nf-e4e auto
    equals K2 • (K0 • CCZ • K0 • CCZ • CS12 • CS12) • K2 • iI
      by general-assoc auto
    equals (K2 • K0) • (CCZ • K0 • CCZ • CS12 • CS12) • K2 • iI
      by left lemma-K2-K0=K0-K2
    equals (K0 • K2) • (CCZ • K0 • CCZ • CS12 • CS12) • K2 • iI
      by general-assoc auto
    equals K0 • K2 • CCZ • ε • K0 • CCZ • CS12 • CS12 • K2 • iI
      by right right right left symm lemma-K2-iI-K2=ε
    equals K0 • K2 • CCZ • ((K2 • iI) • K2) • K0 • CCZ • CS12 • CS12 • K2 • iI
      by general-assoc auto
    equals K0 • (K2 • CCZ • K2 • iI) • (K2 • K0) • CCZ • CS12 • CS12 • K2 • iI
      by right right left lemma-K2-K0=K0-K2
    equals K0 • (K2 • CCZ • K2 • iI) • (K0 • K2) • CCZ • CS12 • CS12 • K2 • iI
      by general-assoc auto
    equals K0 • (K2 • CCZ • K2 • iI) • K0 • (K2 • CCZ • CS12 • CS12 • K2 • iI)
      by right left lemma-CCX2 reversed
    equals K0 • CCX2 • K0 • (K2 • CCZ • CS12 • CS12 • K2 • iI)
      by right right right lemma-CCX2-CX12 reversed
    equals K0 • CCX2 • K0 • CCX2 • CX12

  lemma-CCX2-CX02-K0-CS01-K0=K0-CS01-K0-CCX2-CX02 : Rel ⊢ CCX2 • CX02 • K0 • CS01 • K0 === K0 • CS01 • K0 • CCX2 • CX02
  lemma-CCX2-CX02-K0-CS01-K0=K0-CS01-K0-CCX2-CX02 =
    equational CCX2 • CX02 • K0 • CS01 • K0
      by general-assoc auto
    equals (CCX2 • CX02) • K0 • CS01 • K0
      by left lemma-CCX2-CX02
    equals (K2 • CCZ • CS02 • CS02 • K2 • iI) • K0 • CS01 • K0
      by mvI.general-rewrite 100 auto
    equals (K2 • CCZ • CS02 • CS02) • (K2 • K0) • CS01 • K0 • iI
      by right left lemma-K2-K0=K0-K2
    equals (K2 • CCZ • CS02 • CS02) • (K0 • K2) • CS01 • K0 • iI
      by general-assoc auto
    equals (K2 • CCZ • CS02 • CS02) • K0 • (K2 • CS01) • K0 • iI
      by right right left symm (lemma-CS01-K2=K2-CS01)
    equals (K2 • CCZ • CS02 • CS02) • K0 • (CS01 • K2) • K0 • iI
      by general-assoc auto
    equals (K2 • CCZ • CS02 • CS02) • K0 • CS01 • (K2 • K0) • iI
      by right right right left lemma-K2-K0=K0-K2
    equals (K2 • CCZ • CS02 • CS02) • K0 • CS01 • (K0 • K2) • iI
      by general-assoc auto
    equals K2 • (CCZ • CS02 • CS02 • K0 • CS01 • K0) • K2 • iI
      by right left ListNF.listnfeq' nf-e4e auto
    equals K2 • (K0 • CS01 • K0 • CCZ • CS02 • CS02) • K2 • iI
      by general-assoc auto
    equals (K2 • K0) • (CS01 • K0 • CCZ • CS02 • CS02) • K2 • iI
      by left lemma-K2-K0=K0-K2
    equals (K0 • K2) • (CS01 • K0 • CCZ • CS02 • CS02) • K2 • iI
      by general-assoc auto
    equals K0 • (K2 • CS01) • (K0 • CCZ • CS02 • CS02) • K2 • iI
      by right left symm (lemma-CS01-K2=K2-CS01)
    equals K0 • (CS01 • K2) • (K0 • CCZ • CS02 • CS02) • K2 • iI
      by general-assoc auto
    equals K0 • CS01 • (K2 • K0) • (CCZ • CS02 • CS02) • K2 • iI
      by right right left lemma-K2-K0=K0-K2
    equals K0 • CS01 • (K0 • K2) • (CCZ • CS02 • CS02) • K2 • iI
      by general-assoc auto
    equals K0 • CS01 • K0 • K2 • CCZ • CS02 • CS02 • K2 • iI
      by right right right lemma-CCX2-CX02 reversed
    equals K0 • CS01 • K0 • CCX2 • CX02


  




  lemma-Swap12-CCX2=CCX1-Swap12 : Rel ⊢ Swap12 • CCX2 === CCX1 • Swap12
  lemma-Swap12-CCX2=CCX1-Swap12 = ListNF.listnfeq' nf-s7e auto

  lemma-Swap12-CCX1=CCX2-Swap12 : Rel ⊢ Swap12 • CCX1 === CCX2 • Swap12
  lemma-Swap12-CCX1=CCX2-Swap12 = ListNF.listnfeq' nf-s7e auto

  lemma-Swap12-CX01=CX02-Swap12 : Rel ⊢ Swap12 • CX01 === CX02 • Swap12
  lemma-Swap12-CX01=CX02-Swap12 = ListNF.listnfeq' nf-s7e auto
  
  lemma-Swap12-CX02=CX01-Swap12 : Rel ⊢ Swap12 • CX02 === CX01 • Swap12
  lemma-Swap12-CX02=CX01-Swap12 = ListNF.listnfeq' nf-s7e auto
  
  mvSwap12-step : Step-Function Gate Rel
  mvSwap12-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (axiom ax-Swap12-Swap12=ε))
  mvSwap12-step (Swap12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-K0=K0-Swap12))
  mvSwap12-step (Swap12-gen ∷ CK10-gen ∷ xs) = just (CK20-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CK10=CK20-Swap12))
  mvSwap12-step (Swap12-gen ∷ CK20-gen ∷ xs) = just (CK10-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CK20=CK10-Swap12))
  mvSwap12-step (Swap12-gen ∷ CCK'-gen ∷ xs) = just (CCK'-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CCK'=CCK'-Swap12))
  mvSwap12-step (Swap12-gen ∷ CCX0-gen ∷ xs) = just (CCX0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CCX0=CCX0-Swap12))
  mvSwap12-step (Swap12-gen ∷ CCX2-gen ∷ xs) = just (CCX1-gen ∷ Swap12-gen ∷ xs , at-head lemma-Swap12-CCX2=CCX1-Swap12)
  mvSwap12-step (Swap12-gen ∷ CCX1-gen ∷ xs) = just (CCX2-gen ∷ Swap12-gen ∷ xs , at-head lemma-Swap12-CCX1=CCX2-Swap12)
  mvSwap12-step (Swap12-gen ∷ CS01-gen ∷ xs) = just (CS02-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CS01=CS02-Swap12))
  mvSwap12-step (Swap12-gen ∷ CS12-gen ∷ xs) = just (CS12-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CS12=CS12-Swap12))
  mvSwap12-step (Swap12-gen ∷ CS02-gen ∷ xs) = just (CS01-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CS02=CS01-Swap12))
  mvSwap12-step (Swap12-gen ∷ CX01-gen ∷ xs) = just (CX02-gen ∷ Swap12-gen ∷ xs , at-head lemma-Swap12-CX01=CX02-Swap12)
  mvSwap12-step (Swap12-gen ∷ CX02-gen ∷ xs) = just (CX01-gen ∷ Swap12-gen ∷ xs , at-head lemma-Swap12-CX02=CX01-Swap12)
  mvSwap12-step (Swap12-gen ∷ CX10-gen ∷ xs) = just (CX20-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX10=CX20-Swap12))
  mvSwap12-step (Swap12-gen ∷ CX20-gen ∷ xs) = just (CX10-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX20=CX10-Swap12))
  mvSwap12-step (Swap12-gen ∷ CX12-gen ∷ xs) = just (CX21-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX12=CX21-Swap12))
  mvSwap12-step (Swap12-gen ∷ CX21-gen ∷ xs) = just (CX12-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX21=CX12-Swap12))
  mvSwap12-step _ = nothing

  module MvSwap12 = Rewriting.Step (step-cong mvSwap12-step)

  open Basis-Change group-like mvSwap12-step

  lemma-12' : Rel ⊢ CCX2 • CX02 • K0 • CCX2 • CX02 • K0 === K0 • CCX2 • CX02 • K0 • CCX2 • CX02 • CX12 • X2
  lemma-12' =
    equational CCX2 • CX02 • K0 • CCX2 • CX02 • K0
      by ListNF.listnfeq' nf-s8e auto
    equals X1 • CCX2 • (X1 • K0 • X1) • CCX2 • X1 • K0
      by right right left ListNF.listnfeq' nf-p24k0d auto
    equals X1 • CCX2 • K0 • CCX2 • X1 • K0
      by right right right right ListNF.listnfeq' nf-p24k0d auto
    equals X1 • CCX2 • K0 • CCX2 • K0 • X1
      by general-assoc auto
    equals X1 • (CCX2 • K0 • CCX2 • K0) • X1
      by right left lemma-CCX2-K0-CCX2-K0=K0-CCX2-K0-CCX2-CX12
    equals X1 • (K0 • CCX2 • K0 • CCX2 • CX12) • X1
      by general-assoc auto
    equals (X1 • K0) • CCX2 • K0 • CCX2 • CX12 • X1
      by left ListNF.listnfeq' nf-p24k0d auto
    equals (K0 • X1) • CCX2 • K0 • CCX2 • CX12 • X1
      by right right left ListNF.listnfeq' nf-p24k0d auto
    equals (K0 • X1) • CCX2 • (X1 • K0 • X1) • CCX2 • CX12 • X1
      by ListNF.listnfeq' nf-s8e auto
    equals K0 • CCX2 • CX02 • K0 • CCX2 • CX02 • CX12 • X2


  lemma-CCX2-CX02-CCK'=CCK'-CCX2-CX02 : Rel ⊢ CCX2 • CX02 • CCK' === CCK' • CCX2 • CX02
  lemma-CCX2-CX02-CCK'=CCK'-CCX2-CX02 =
    equational CCX2 • CX02 • CCK'
      by right (right (ListNF.listnfeq' nf-e4 auto))
    equals CCX2 • CX02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by general-assoc auto
    equals (CCX2 • CX02 • K0 • CS01 • K0) • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by left (lemma-CCX2-CX02-K0-CS01-K0=K0-CS01-K0-CCX2-CX02)
    equals (K0 • CS01 • K0 • CCX2 • CX02) • CS02 • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by general-assoc auto
    equals (K0 • CS01 • K0) • (CCX2 • CX02 • CS02) • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by right left ListNF.listnfeq' nf-pd auto
    equals (K0 • CS01 • K0) • (S0 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ • CCX2 • CX02) • K0 • CS01 • K0 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by general-assoc auto
    equals (K0 • CS01 • K0 • S0 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ) • (CCX2 • CX02 • K0 • CS01 • K0) • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by right left (lemma-CCX2-CX02-K0-CS01-K0=K0-CS01-K0-CCX2-CX02)
    equals (K0 • CS01 • K0 • S0 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ) • (K0 • CS01 • K0 • CCX2 • CX02) • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by general-assoc auto
    equals (K0 • CS01 • K0 • S0 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ • K0 • CS01 • K0) • CCX2 • CX02 • CCX0 • CX10 • CS12 • CS12 • CS12 • CS02 • CS02 • CS02 • iI • iI
      by right ListNF.listnfeq' nf-pd auto
    equals (K0 • CS01 • K0 • S0 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ • K0 • CS01 • K0) • (CCX0 • CX10 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI) • CCX2 • CX02
      by general-assoc auto
    equals (K0 • CS01 • K0 • S0 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ • K0 • CS01 • K0 • CCX0 • CX10 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI) • CCX2 • CX02
      by left ListNF.listnfeq' nf-e4e auto
    equals CCK' • CCX2 • CX02

  lemma-7' : Rel ⊢  CCX1 • CX01 • CCK' === CCK' • CCX1 • CX01
  lemma-7' = (by-basis-change Swap12 (lemma-CCX2-CX02-CCK'=CCK'-CCX2-CX02) 50 auto)

  lemma-CCX1-CK10-CCK'=CK10-CCK'-CCX1-CS02-CS02 : Rel ⊢ CCX1 • CK10 • CCK' === CK10 • CCK' • CCX1 • CS02 • CS02
  lemma-CCX1-CK10-CCK'=CK10-CCK'-CCX1-CS02-CS02 =
    equational CCX1 • CK10 • CCK'
      by right ListNF.listnfeq' nf-p24k0d auto
    equals CCX1 • X2 • CCK' • X2 • CS01 • CS12 • CS12 • CS12 • CCZ
      by general-assoc auto
    equals (CCX1 • X2) • CCK' • X2 • CS01 • CS12 • CS12 • CS12 • CCZ
      by left ListNF.listnfeq' nf-s8e auto
    equals (X2 • CCX1 • CX01) • CCK' • X2 • CS01 • CS12 • CS12 • CS12 • CCZ
      by general-assoc auto
    equals X2 • (CCX1 • CX01 • CCK') • X2 • CS01 • CS12 • CS12 • CS12 • CCZ
      by right left lemma-7'
    equals X2 • (CCK' • CCX1 • CX01) • X2 • CS01 • CS12 • CS12 • CS12 • CCZ
      by general-assoc auto
    equals X2 • CCK' • CCX1 • CX01 • X2 • CS01 • CS12 • CS12 • CS12 • CCZ
      by right right ListNF.listnfeq' nf-pd auto
    equals X2 • CCK' • X2 • CS01 • CS12 • CS12 • CS12 • CCZ • CCX1 • CS02 • CS02
      by general-assoc auto
    equals (X2 • CCK' • X2 • CS01 • CS12 • CS12 • CS12 • CCZ) • CCX1 • CS02 • CS02
      by left ListNF.listnfeq' nf-p24k0d auto
    equals (CK10 • CCK') • CCX1 • CS02 • CS02
      by general-assoc auto
    equals CK10 • CCK' • CCX1 • CS02 • CS02

  lemma-9' : Rel ⊢ CCX2 • Swap01 • CK20 • CCK' === Swap01 • CK20 • CCK' • CCX2 • CS01 • CS01
  lemma-9' =
    equational CCX2 • Swap01 • CK20 • CCK'
      by ListNF.listnfeq' nf-s8e auto
    equals CCX2 • (CX01 • CX10 • CX01) • CK20 • CCK'
      by ListNF.listnfeq' nf-s7e auto
    equals (CX01 • CX10 • CX01) • (CCX2 • CK20 • CCK')
      by right (by-basis-change Swap12 (lemma-CCX1-CK10-CCK'=CK10-CCK'-CCX1-CS02-CS02) 50 auto)
    equals (CX01 • CX10 • CX01) • (CK20 • CCK' • CCX2 • CS01 • CS01)
      by general-assoc auto
    equals (CX01 • CX10 • CX01) • CK20 • CCK' • CCX2 • CS01 • CS01
      by ListNF.listnfeq' nf-s7e auto
    equals Swap01 • CK20 • CCK' • CCX2 • CS01 • CS01


  lemma-7b : Rel ⊢  CCX2 • CX02 • CCK' === CCK' • CCX2 • CX02
  lemma-7b = by-basis-change Swap12 lemma-7' 50 auto


  lemma-8' : Rel ⊢ CCX2 • CCX1 • CX02 • CCK' === CCK' • CCX2 • CCX1 • CX02
  lemma-8' =
    equational CCX2 • CCX1 • CX02 • CCK'
      by ListNF.listnfeq' nf-s8e auto
    equals CCX2 • CX02 • CCX1 • CX01 • CCK'
      by right right lemma-7'
    equals CCX2 • CX02 • CCK' • CCX1 • CX01
      by general-assoc auto
    equals (CCX2 • CX02 • CCK') • CCX1 • CX01
      by left lemma-7b
    equals (CCK' • CCX2 • CX02) • CCX1 • CX01
      by ListNF.listnfeq' nf-s8e auto
    equals CCK' • CCX2 • CCX1 • CX02



  lemma-4' : Rel ⊢  CCX2 • K0 • CK20 • CK10 • CCK' === K0 • CK20 • CK10 • CCK' • CCX2 • CS01 • CS01
  lemma-4' =
    equational CCX2 • K0 • CK20 • CK10 • CCK'
      by ListNF.listnfeq' nf-e3e auto
    equals (CCX2 • K0 • CK10) • CK20 • CCK'
      by left lemma-CCX2-K0-CK10=K0-CK10-CCX2
    equals (K0 • CK10 • CCX2) • CK20 • CCK'
      by general-assoc auto
    equals K0 • CK10 • (CCX2 • CK20 • CCK')
      by right right (by-basis-change Swap12 (lemma-CCX1-CK10-CCK'=CK10-CCK'-CCX1-CS02-CS02) 100 auto) -- ax-CCX2-CK20-CCK'=CK20-CCK'-CCX2-CS01-CS01
    equals K0 • CK10 • (CK20 • CCK' • CCX2 • CS01 • CS01)
      by ListNF.listnfeq' nf-e3e auto
    equals K0 • CK20 • CK10 • CCK' • CCX2 • CS01 • CS01

  lemma-5' : Rel ⊢  CCX1 • K0 • CK20 • CK10 • CCK' === K0 • CK20 • CK10 • CCK' • CCX1 • CS02 • CS02
  lemma-5' =
    equational CCX1 • K0 • CK20 • CK10 • CCK'
      by ListNF.listnfeq' nf-e3e auto
    equals CCX1 • K0 • CK10 • CK20 • CCK'
      by by-basis-change Swap12 lemma-4' 100 auto
    equals K0 • CK10 • CK20 • CCK' • CCX1 • CS02 • CS02
      by ListNF.listnfeq' nf-e3e auto
    equals K0 • CK20 • CK10 • CCK' • CCX1 • CS02 • CS02



  lemma-10' : Rel ⊢  CCX1 • CX01 • CK20 === CK20 • CCX1 • CX01
  lemma-10' = by-basis-change Swap12 (lemma-CCX2-CX02-CK10=CK10-CCX2-CX02) 100 auto

  lemma-13' : Rel ⊢  CCX2 • CX02 • CK10 === CK10 • CCX2 • CX02
  lemma-13' = by-basis-change Swap12 lemma-10' 50 auto


  lemma-2' : Rel ⊢  CCX2 • CK20 • CCK' === CK20 • CCK' • CCX2 • CS01 • CS01
  lemma-2' = by-basis-change Swap12 (lemma-CCX1-CK10-CCK'=CK10-CCK'-CCX1-CS02-CS02) 100 auto

  lemma-3' : Rel ⊢  CCX1 • CK10 • CCK' === CK10 • CCK' • CCX1 • CS02 • CS02
  lemma-3' = by-basis-change Swap12 lemma-2' 50 auto

  lemma-6' : Rel ⊢  CCX2 • CX02 • K0 • CK10 === CK10 • CCX2 • CX02 • K0
  lemma-6' =
    equational CCX2 • CX02 • K0 • CK10
      by ListNF.listnfeq' nf-e4e auto
    equals (CCX2 • CX02 • CK10) • K0
      by left lemma-13'
    equals (CK10 • CCX2 • CX02) • K0
      by general-assoc auto
    equals CK10 • CCX2 • CX02 • K0


  lemma-14' : Rel ⊢ CK10 • CCK' • CCX1 • CK20 • CCK' === CCX1 • CK20 • CK10 • CX20 • CCX0 • CS12 • CS12 • CS12
  lemma-14' =
    equational CK10 • CCK' • CCX1 • CK20 • CCK'
      by ListNF.listnfeq' nf-de auto
    equals (CK10 • CCK' • CCX1 • CS02 • CS02 • CS02 • CS02) • CK20 • CCK'
      by general-assoc auto
    equals (CK10 • CCK' • CCX1 • CS02 • CS02) • CS02 • CS02 • CK20 • CCK'
      by left symm lemma-3'
    equals (CCX1 • CK10 • CCK') • CS02 • CS02 • CK20 • CCK'
      by general-assoc auto
    equals CCX1 • CK10 • CCK' • CS02 • CS02 • CK20 • CCK'
      by right ListNF.listnfeq' nf-e3 auto
    equals CCX1 • CK20 • CK10 • CX20 • CCX0 • CS12 • CS12 • CS12


  lemma-p-CK20 : Rel ⊢ CX01 • CCX0 • Swap01 • CK20 === CK20 • CX01 • CCX0 • Swap01 • CCX0 • CCZ
  lemma-p-CK20 =
    equational CX01 • CCX0 • Swap01 • CK20
      by ListNF.listnfeq' ((extend-nf isPD nf-pd)) auto
    equals CX10 • CCX1 • CX01 • CK20
      by right by-basis-change Swap12 (lemma-CCX2-CX02-CK10=CK10-CCX2-CX02) 100 auto
    equals CX10 • CK20 • CCX1 • CX01
      by ListNF.listnfeq' ((extend-nf isk0spd nf-e4)) auto
    equals CK20 • CX10 • CCX0 • CCZ • CCX1 • CX01
      by right ListNF.listnfeq' ((extend-nf isPD nf-pd)) auto
    equals CK20 • CX01 • CCX0 • Swap01 • CCX0 • CCZ

  lemma-p-CCK' : Rel ⊢ CX01 • CCX0 • Swap01 • CCK' === CCK' • CX01 • CCX0 • Swap01 • CCX0 • CCZ
  lemma-p-CCK' =
    equational CX01 • CCX0 • Swap01 • CCK'
      by ListNF.listnfeq' ((extend-nf isPD nf-pd)) auto
    equals CX10 • CCX1 • CX01 • CCK'
      by right by-basis-change Swap12 (lemma-CCX2-CX02-CCK'=CCK'-CCX2-CX02) 100 auto
    equals CX10 • CCK' • CCX1 • CX01
      by ListNF.listnfeq' ((extend-nf isk0spd nf-e4)) auto
    equals CCK' • CX10 • CCX0 • CCZ • CCX1 • CX01
      by right ListNF.listnfeq' ((extend-nf isPD nf-pd)) auto
    equals CCK' • CX01 • CCX0 • Swap01 • CCX0 • CCZ

  
  lemma-15' : Rel ⊢ K0 • CK20 • CK10 • CCK' • CX01 • CCX0 • Swap01 • CK20 • CCK' === K0 • CK10 • CX01 • CCX0 • Swap01 • S2 • S2 • S2 • CS12 • CS12
  lemma-15' =
    equational K0 • CK20 • CK10 • CCK' • CX01 • CCX0 • Swap01 • CK20 • CCK'
      by general-assoc auto
    equals (K0 • CK20 • CK10 • CCK') • (CX01 • CCX0 • Swap01 • CK20) • CCK'
      by right left lemma-p-CK20
    equals (K0 • CK20 • CK10 • CCK') • (CK20 • CX01 • CCX0 • Swap01 • CCX0 • CCZ) • CCK'
      by right ListNF.listnfeq' ((extend-nf isk0spd nf-e4)) auto
    equals (K0 • CK20 • CK10 • CCK') • (CK20 • CX01 • CCX0 • Swap01 • CCK') • CCX0 • CS12 • CS12 • CS12 
      by general-assoc auto
    equals (K0 • CK20 • CK10 • CCK' • CK20) • (CX01 • CCX0 • Swap01 • CCK') • CCX0 • CS12 • CS12 • CS12 
      by right left lemma-p-CCK'
    equals (K0 • CK20 • CK10 • CCK' • CK20) • (CCK' • CX01 • CCX0 • Swap01 • CCX0 • CCZ) • CCX0 • CS12 • CS12 • CS12 
      by general-assoc auto
    equals (K0 • CK20 • CK10 • CCK' • CK20 • CCK') • CX01 • CCX0 • Swap01 • CCX0 • CCZ • CCX0 • CS12 • CS12 • CS12 
      by left ListNF.listnfeq' nf-e4 auto
    equals (K0 • CK10 • S2 ^ 3 • CS12 ^ 3 • CCZ) • CX01 • CCX0 • Swap01 • CCX0 • CCZ • CCX0 • CS12 • CS12 • CS12 
      by general-assoc auto
    equals (K0 • CK10) • S2 ^ 3 • CS12 ^ 3 • CCZ • CX01 • CCX0 • Swap01 • CCX0 • CCZ • CCX0 • CS12 • CS12 • CS12 
      by right ListNF.listnfeq' nf-pd auto
    equals (K0 • CK10) • CX01 • CCX0 • Swap01 • S2 • S2 • S2 • CS12 • CS12
      by general-assoc auto
    equals K0 • CK10 • CX01 • CCX0 • Swap01 • S2 • S2 • S2 • CS12 • CS12


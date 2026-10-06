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

open import Examples.Groups.Clifford+CS-3qubit.Step5.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step5.S8
open import Examples.Groups.Clifford+CS-3qubit.Step5.Comm
open import Examples.Groups.Clifford+CS-3qubit.Step5.Order
open import Examples.Groups.Clifford+CS-3qubit.Step5.Basis-Change
open import Examples.Groups.Clifford+CS-3qubit.Step5.S8D
open import Examples.Groups.Clifford+CS-3qubit.Step5.KD

module Examples.Groups.Clifford+CS-3qubit.Step5.Lemmas where

  lemma-CS01-K2=K2-CS01 : Rel ⊢ CS01 • K2 === K2 • CS01
  lemma-CS01-K2=K2-CS01 =
    equational CS01 • K2
      by right axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12
    equals CS01 • Swap12 • Swap01 • K0 • Swap01 • Swap12
      by ListNF.listnfeq' nf-pde auto
    equals Swap12 • Swap01 • CS12 • K0 • Swap01 • Swap12
      by general-assoc auto
    equals Swap12 • Swap01 • (CS12 • K0) • Swap01 • Swap12
      by right right left axiom ax-CS12-K0=K0-CS12
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
      by right right left axiom ax-S2-K0=K0-S2
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
      by right right axiom ax-Swap12-K0=K0-Swap12
    equals Swap12 • (Swap01 • K0 • Swap01) • (K0 • Swap12)
      by general-assoc auto
    equals Swap12 • (Swap01 • K0 • Swap01 • K0) • Swap12
      by right left axiom ax-Swap01-K0-Swap01-K0=K0-Swap01-K0-Swap01
    equals Swap12 • (K0 • Swap01 • K0 • Swap01) • Swap12
      by general-assoc auto
    equals (Swap12 • K0) • Swap01 • K0 • Swap01 • Swap12
      by left axiom ax-Swap12-K0=K0-Swap12
    equals (K0 • Swap12) • Swap01 • K0 • Swap01 • Swap12
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
      by right axiom ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI
    equals K2 • CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI
      by mvK2.general-rewrite 100 auto
    equals (CS01 • K0 • CS01 • K0 • CS01 • S1 • S1 • S1 • iI) • K2
      by left symm (axiom ax-CK10=CS01-K0-CS01-K0-CS01-S1-S1-S1-iI)
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
      by right right left axiom ax-CX12-K0=K0-CX12
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
      by left  axiom ax-CX10=K0-CS01-CS01-K0-iI
    equals (K0 • CS01 • CS01 • K0 • iI) • K2
      by mvK2.general-rewrite 100 auto
    equals K2 • (K0 • CS01 • CS01 • K0 • iI)
      by right symm (axiom ax-CX10=K0-CS01-CS01-K0-iI)
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
      by right right left (P16DK.general-rewrite 100 auto)
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
      by right right right left (P16DK.general-rewrite 100 auto)
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
      by right left (P16DK.general-rewrite 100 auto)
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

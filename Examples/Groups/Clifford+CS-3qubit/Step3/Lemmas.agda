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
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD3
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD4
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD5
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD6
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD7

module Examples.Groups.Clifford+CS-3qubit.Step3.Lemmas where

lemma-K1 : Rel ⊢
    (((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
      (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
     •
     (X1 • CCX2 • X1) •
     (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1)
    •
    (((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
      ((X0 • CCX2 • X0) •
       ((X0 • CX21 • CCX2 • CX21 • X0) •
        (Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12) •
        S1 •
        S1 •
        S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
       • X0 • CCX2 • X0)
      • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
     •
     ((X1 • CCX2 • X1) •
      ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
       ((X0 • CCX2 • X0) •
        ((X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1) •
         ((S1 •
           S1 •
           S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
          •
          (Swap12 •
           Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12)
          • X0 • CX21 • CCX2 • CX21 • X0)
         • X1 • X0 • CCX2 • X0 • X1)
        • X0 • CCX2 • X0)
       • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
      • X1 • CCX2 • X1)
     •
     ((CX21 • CCX2 • CX21) •
      ((X1 • CCX2 • X1) •
       ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
        ((X0 • CX21 • CCX2 • CX21 • X0) •
         ((X1 • X0 • CCX2 • X0 • X1) •
          ((X0 • CCX2 • X0) •
           ((X0 • CX21 • CCX2 • CX21 • X0) •
            (Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12) •
            S1 •
            S1 •
            S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
           • X0 • CCX2 • X0)
          • X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1)
         •
         S1 •
         S1 •
         S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
        • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
       • X1 • CCX2 • X1)
      • CX21 • CCX2 • CX21)
     •
     CCX2 •
     ((CX21 • CCX2 • CX21) •
      ((X1 • CCX2 • X1) •
       ((X0 • CCX2 • X0) •
        ((S1 •
          S1 •
          S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
         •
         ((X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1) •
          ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
           ((X0 • CCX2 • X0) •
            ((S1 •
              S1 •
              S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
             •
             (Swap12 •
              Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12)
             • X0 • CX21 • CCX2 • CX21 • X0)
            • X0 • CCX2 • X0)
           • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
          • X1 • X0 • CCX2 • X0 • X1)
         • X0 • CX21 • CCX2 • CX21 • X0)
        • X0 • CCX2 • X0)
       • X1 • CCX2 • X1)
      • CX21 • CCX2 • CX21)
     • CCX2)
    •
    ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
     (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
    •
    (X1 • CCX2 • X1) •
    (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1
    === [ K1-gen ]ʷ
    
lemma-K1 =
  equational (((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
      (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
     •
     (X1 • CCX2 • X1) •
     (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1)
    •
    (((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
      ((X0 • CCX2 • X0) •
       ((X0 • CX21 • CCX2 • CX21 • X0) •
        (Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12) •
        S1 •
        S1 •
        S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
       • X0 • CCX2 • X0)
      • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
     •
     ((X1 • CCX2 • X1) •
      ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
       ((X0 • CCX2 • X0) •
        ((X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1) •
         ((S1 •
           S1 •
           S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
          •
          (Swap12 •
           Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12)
          • X0 • CX21 • CCX2 • CX21 • X0)
         • X1 • X0 • CCX2 • X0 • X1)
        • X0 • CCX2 • X0)
       • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
      • X1 • CCX2 • X1)
     •
     ((CX21 • CCX2 • CX21) •
      ((X1 • CCX2 • X1) •
       ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
        ((X0 • CX21 • CCX2 • CX21 • X0) •
         ((X1 • X0 • CCX2 • X0 • X1) •
          ((X0 • CCX2 • X0) •
           ((X0 • CX21 • CCX2 • CX21 • X0) •
            (Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12) •
            S1 •
            S1 •
            S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
           • X0 • CCX2 • X0)
          • X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1)
         •
         S1 •
         S1 •
         S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
        • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
       • X1 • CCX2 • X1)
      • CX21 • CCX2 • CX21)
     •
     CCX2 •
     ((CX21 • CCX2 • CX21) •
      ((X1 • CCX2 • X1) •
       ((X0 • CCX2 • X0) •
        ((S1 •
          S1 •
          S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
         •
         ((X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1) •
          ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
           ((X0 • CCX2 • X0) •
            ((S1 •
              S1 •
              S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
             •
             (Swap12 •
              Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12)
             • X0 • CX21 • CCX2 • CX21 • X0)
            • X0 • CCX2 • X0)
           • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
          • X1 • X0 • CCX2 • X0 • X1)
         • X0 • CX21 • CCX2 • CX21 • X0)
        • X0 • CCX2 • X0)
       • X1 • CCX2 • X1)
      • CX21 • CCX2 • CX21)
     • CCX2)
    •
    ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
     (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
    •
    (X1 • CCX2 • X1) •
    (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1
    by right left ListNF.listnfeq' ANF auto
    
  equals (((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
      (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
     •
     (X1 • CCX2 • X1) •
     (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1)
    • K0
    •
    ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
     (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
    •
    (X1 • CCX2 • X1) •
    (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1
    by left PD.nfeq auto
    
  equals Swap01
    • K0
    •
    ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
     (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
    •
    (X1 • CCX2 • X1) •
    (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1
    by right right PD.nfeq auto
    
  equals Swap01
    • K0
    • Swap01
    by symm (axiom ax-K1=Swap01-K0-Swap01)

  equals K1
  

lemma-K2 : Rel ⊢
    ((X0 • CX21 • CCX2 • CX21 • X0) • CX21 • CCX2 • CX21) •
    ((((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
       (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
      •
      (X1 • CCX2 • X1) •
      (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1)
     •
     (((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
       ((X0 • CCX2 • X0) •
        ((X0 • CX21 • CCX2 • CX21 • X0) •
         (Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12) •
         S1 •
         S1 •
         S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
        • X0 • CCX2 • X0)
       • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
      •
      ((X1 • CCX2 • X1) •
       ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
        ((X0 • CCX2 • X0) •
         ((X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1) •
          ((S1 •
            S1 •
            S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
           •
           (Swap12 •
            Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12)
           • X0 • CX21 • CCX2 • CX21 • X0)
          • X1 • X0 • CCX2 • X0 • X1)
         • X0 • CCX2 • X0)
        • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
       • X1 • CCX2 • X1)
      •
      ((CX21 • CCX2 • CX21) •
       ((X1 • CCX2 • X1) •
        ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
         ((X0 • CX21 • CCX2 • CX21 • X0) •
          ((X1 • X0 • CCX2 • X0 • X1) •
           ((X0 • CCX2 • X0) •
            ((X0 • CX21 • CCX2 • CX21 • X0) •
             (Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12) •
             S1 •
             S1 •
             S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
            • X0 • CCX2 • X0)
           • X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1)
          •
          S1 •
          S1 •
          S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
         • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
        • X1 • CCX2 • X1)
       • CX21 • CCX2 • CX21)
      •
      CCX2 •
      ((CX21 • CCX2 • CX21) •
       ((X1 • CCX2 • X1) •
        ((X0 • CCX2 • X0) •
         ((S1 •
           S1 •
           S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
          •
          ((X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1) •
           ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
            ((X0 • CCX2 • X0) •
             ((S1 •
               S1 •
               S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
              •
              (Swap12 •
               Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12)
              • X0 • CX21 • CCX2 • CX21 • X0)
             • X0 • CCX2 • X0)
            • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
           • X1 • X0 • CCX2 • X0 • X1)
          • X0 • CX21 • CCX2 • CX21 • X0)
         • X0 • CCX2 • X0)
        • X1 • CCX2 • X1)
       • CX21 • CCX2 • CX21)
      • CCX2)
     •
     ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
      (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
     •
     (X1 • CCX2 • X1) •
     (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1)
    • (X0 • CX21 • CCX2 • CX21 • X0) • CX21 • CCX2 • CX21
    === [ K2-gen ]ʷ

lemma-K2 =
  equational     ((X0 • CX21 • CCX2 • CX21 • X0) • CX21 • CCX2 • CX21) •
    ((((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
       (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
      •
      (X1 • CCX2 • X1) •
      (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1)
     •
     (((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
       ((X0 • CCX2 • X0) •
        ((X0 • CX21 • CCX2 • CX21 • X0) •
         (Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12) •
         S1 •
         S1 •
         S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
        • X0 • CCX2 • X0)
       • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
      •
      ((X1 • CCX2 • X1) •
       ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
        ((X0 • CCX2 • X0) •
         ((X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1) •
          ((S1 •
            S1 •
            S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
           •
           (Swap12 •
            Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12)
           • X0 • CX21 • CCX2 • CX21 • X0)
          • X1 • X0 • CCX2 • X0 • X1)
         • X0 • CCX2 • X0)
        • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
       • X1 • CCX2 • X1)
      •
      ((CX21 • CCX2 • CX21) •
       ((X1 • CCX2 • X1) •
        ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
         ((X0 • CX21 • CCX2 • CX21 • X0) •
          ((X1 • X0 • CCX2 • X0 • X1) •
           ((X0 • CCX2 • X0) •
            ((X0 • CX21 • CCX2 • CX21 • X0) •
             (Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12) •
             S1 •
             S1 •
             S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
            • X0 • CCX2 • X0)
           • X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1)
          •
          S1 •
          S1 •
          S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
         • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
        • X1 • CCX2 • X1)
       • CX21 • CCX2 • CX21)
      •
      CCX2 •
      ((CX21 • CCX2 • CX21) •
       ((X1 • CCX2 • X1) •
        ((X0 • CCX2 • X0) •
         ((S1 •
           S1 •
           S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
          •
          ((X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1) •
           ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
            ((X0 • CCX2 • X0) •
             ((S1 •
               S1 •
               S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12)
              •
              (Swap12 •
               Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12)
              • X0 • CX21 • CCX2 • CX21 • X0)
             • X0 • CCX2 • X0)
            • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
           • X1 • X0 • CCX2 • X0 • X1)
          • X0 • CX21 • CCX2 • CX21 • X0)
         • X0 • CCX2 • X0)
        • X1 • CCX2 • X1)
       • CX21 • CCX2 • CX21)
      • CCX2)
     •
     ((X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) •
      (X0 • CCX2 • X0) • X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2)
     •
     (X1 • CCX2 • X1) •
     (X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2) • X1 • CCX2 • X1)
    • (X0 • CX21 • CCX2 • CX21 • X0) • CX21 • CCX2 • CX21
      by right left lemma-K1
      
  equals     ((X0 • CX21 • CCX2 • CX21 • X0) • CX21 • CCX2 • CX21) •
    (K1)
    • (X0 • CX21 • CCX2 • CX21 • X0) • CX21 • CCX2 • CX21
      by left PD.nfeq auto
      
  equals Swap12 • 
    (K1)
    • (X0 • CX21 • CCX2 • CX21 • X0) • CX21 • CCX2 • CX21
      by right right PD.nfeq auto
      
  equals Swap12 • 
    (K1)
    • Swap12
      by right left axiom ax-K1=Swap01-K0-Swap01
      
  equals Swap12 • 
    (Swap01 • K0 • Swap01)
    • Swap12
      by general-assoc auto
      
  equals Swap12 • 
    Swap01 • K0 • Swap01
    • Swap12
      by symm (axiom ax-K2=Swap12-Swap01-K0-Swap01-Swap12)
      
    equals K2


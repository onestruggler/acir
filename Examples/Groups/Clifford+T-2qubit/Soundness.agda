------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness: the translation f of Clifford+T words into Greylyn's
-- generators respects the relations: every Clifford+T relation of
-- Figure 1 translates to a consequence of Greylyn's relations.  Ported
-- from the Agda code accompanying Bian and Selinger, "Generators and
-- relations for 2-qubit Clifford+T operators" (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Soundness where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _∸_ ; _*_)
open import Data.Nat.Properties using (_≤?_ ; _≟_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Relation.Nullary using (¬_ ; Dec ; yes ; no ; does)
open import Presentation.Tactics.Equality as Eq using (_≡_)

open import Notations using (auto)
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open import Presentation.Tactics.Lists
open import Presentation.Tactics.Words
open import Examples.Groups.Clifford+T-2qubit.Generator as Generator
open import Examples.Groups.Clifford+T-2qubit.Greylyn-Lemmas as Greylyn-Lemmas

open Clifford+T
open Greylyn
open Monoid-Equational
open Associative
open Commuting-Greylyn
open Inverse-Greylyn
open Greylyn-Rewrite-Twolevel

-- ----------------------------------------------------------------------
-- * Some lemmas

-- These lemmas are required to complete the "rel-C" case of
-- soundness.

-- A lemma about the translation of CH0 • H0 • T0 • CH0 into 1- and
-- 2-level generators.
lemma-CH0-H0-T0-CH0 : Greylyn.Rel ⊢ (f ʷ) (CH0 • H0 • T0 • CH0) === ω ₃ • H ₁₃ • H ₀₂ • ω ₂
lemma-CH0-H0-T0-CH0 = rewrite-twolevel 60 auto

-- A lemma about the translation of CH1 • H1 • T1 • CH1 into 1- and
-- 2-level generators.
lemma-CH1-H1-T1-CH1 : Greylyn.Rel ⊢ (f ʷ) (CH1 • H1 • T1 • CH1) === ω ₃ • H ₂₃ • H ₀₁ • ω ₁
lemma-CH1-H1-T1-CH1 = rewrite-twolevel 60 auto

-- The soundness of the translation of rel-C.
lemma-soundness-rel-C : Greylyn.Rel ⊢ (f ʷ) (CH1 • H1 • T1 • CH1 • CH0 • H0 • T0 • CH0) === (f ʷ) (CH0 • H0 • T0 • CH0 • CH1 • H1 • T1 • CH1)
lemma-soundness-rel-C =
    equational (f ʷ) (CH1 • H1 • T1 • CH1 • CH0 • H0 • T0 • CH0)
            by general-assoc auto
        equals (f ʷ) (CH1 • H1 • T1 • CH1) • (f ʷ) (CH0 • H0 • T0 • CH0)
            by cong lemma-CH1-H1-T1-CH1 lemma-CH0-H0-T0-CH0
        equals (ω ₃ • H ₂₃ • H ₀₁ • ω ₁) • (ω ₃ • H ₁₃ • H ₀₂ • ω ₂)
            by general-comm auto
        equals (ω ₃ • H ₀₁ • H ₂₃ • H ₀₂) • (ω ₁ • ω ₃ • H ₁₃) • ω ₂
            by  right left axiom [17]
        equals (ω ₃ • H ₀₁ • H ₂₃ • H ₀₂) • (H ₁₃ • ω ₁ • ω ₃) • ω ₂
            by general-comm auto
        equals ω ₃ • (H ₀₁ • H ₂₃ • H ₀₂ • H ₁₃) • ω ₁ • ω ₃ • ω ₂
            by right left axiom ([20] {kl = ₁₂})
        equals ω ₃ • (H ₀₂ •  H ₁₃ • H ₀₁ • H ₂₃) • ω ₁ • ω ₃ • ω ₂
            by general-comm auto
        equals (ω ₃ • H ₁₃ • H ₀₂ • H ₀₁) • (H ₂₃ •  ω ₂ • ω ₃) • ω ₁
            by right left axiom [17] reversed
        equals (ω ₃ • H ₁₃ • H ₀₂ • H ₀₁) • (ω ₂ • ω ₃ • H ₂₃) • ω ₁
            by general-comm auto
        equals (ω ₃ • H ₁₃ • H ₀₂ • ω ₂) • (ω ₃ • H ₂₃ • H ₀₁ • ω ₁)
            by cong lemma-CH0-H0-T0-CH0 lemma-CH1-H1-T1-CH1 reversed
        equals (f ʷ) (CH0 • H0 • T0 • CH0) • (f ʷ) (CH1 • H1 • T1 • CH1)
            by general-assoc auto
        equals (f ʷ) (CH0 • H0 • T0 • CH0 • CH1 • H1 • T1 • CH1)

-- Base case of the soundness theorem: The translation of every
-- basic Clifford+T relation is sound.
soundness-base : ∀ {w v} -> w === v ∈ Clifford+T.Rel -> Greylyn.Rel ⊢ (f ʷ) w === (f ʷ) v
soundness-base (comm-W W-gen) = refl
soundness-base (comm-W H0-gen) = rewrite-twolevel 30 auto
soundness-base (comm-W H1-gen) = rewrite-twolevel 30 auto
soundness-base (comm-W S0-gen) = rewrite-twolevel 10 auto
soundness-base (comm-W S1-gen) = rewrite-twolevel 10 auto
soundness-base (comm-W T0-gen) = rewrite-twolevel 10 auto
soundness-base (comm-W T1-gen) = rewrite-twolevel 10 auto
soundness-base (comm-W CZ-gen) = rewrite-twolevel 10 auto

soundness-base comm-H0-H1 =
    equational (H ₁₃ • H ₀₂) • (H ₂₃ • H ₀₁)
            by general-assoc auto
        equals H ₁₃ • H ₀₂ • H ₂₃ • H ₀₁
            by inverse-eq (axiom ([20] {kl = ₁₂}))
        equals H ₂₃ • H ₀₁ • H ₁₃ • H ₀₂
            by general-assoc auto
        equals (H ₂₃ • H ₀₁) • (H ₁₃ • H ₀₂)
            
soundness-base comm-H0-S1 = rewrite-twolevel 20 auto
soundness-base comm-H0-T1 = rewrite-twolevel 20 auto
soundness-base comm-S0-H1 = rewrite-twolevel 20 auto
soundness-base comm-S0-S1 = rewrite-twolevel 10 auto
soundness-base comm-S0-T1 = rewrite-twolevel 10 auto
soundness-base comm-T0-H1 = rewrite-twolevel 20 auto
soundness-base comm-T0-S1 = rewrite-twolevel 10 auto
soundness-base comm-T0-T1 = rewrite-twolevel 10 auto
soundness-base order-W  = rewrite-twolevel 10 auto
soundness-base order-H0 = rewrite-twolevel 10 auto
soundness-base order-H1 = rewrite-twolevel 10 auto
soundness-base order-S0 = rewrite-twolevel 10 auto
soundness-base order-S1 = rewrite-twolevel 10 auto
soundness-base order-S0H0 = rewrite-twolevel 80 auto 
soundness-base order-S1H1 = rewrite-twolevel 80 auto 
soundness-base order-CZ = rewrite-twolevel 10 auto
soundness-base comm-S0-CZ = rewrite-twolevel 10 auto
soundness-base comm-S1-CZ = rewrite-twolevel 10 auto
soundness-base rel-X0-CZ = rewrite-twolevel 20 auto 
soundness-base rel-X1-CZ = rewrite-twolevel 20 auto
soundness-base rel-CZ-H0-CZ = rewrite-twolevel 70 auto
soundness-base rel-CZ-H1-CZ = rewrite-twolevel 70 auto
soundness-base square-T0 = rewrite-twolevel 10 auto
soundness-base square-T1 = rewrite-twolevel 10 auto
soundness-base lemma-order-T0X0 = rewrite-twolevel 50 auto
soundness-base lemma-order-T1X1 = rewrite-twolevel 50 auto
soundness-base comm-T0-CZ = rewrite-twolevel 10 auto

soundness-base swap-T0 =
    equational (H ₂₃ • H ₀₁) • ω ₃ ^ 4 • (H ₁₃ • H ₀₂) • (H ₂₃ • H ₀₁) • ω ₃ ^ 4 • (H ₁₃ • H ₀₂) • ω ₂ • ω ₃
            by general-comm auto
        equals (H ₂₃ • H ₀₁ • ω ₃ ^ 4) • (H ₀₂ • H ₁₃ • H ₀₁ • H ₂₃) • (ω ₃ ^ 4 • H ₁₃ • H ₀₂ • ω ₂ • ω ₃)
            by right left axiom ([20] {kl = ₁₂}) reversed
        equals (H ₂₃ • H ₀₁ • ω ₃ ^ 4) • (H ₀₁ • H ₂₃ • H ₀₂ • H ₁₃) • (ω ₃ ^ 4 • H ₁₃ • H ₀₂ • ω ₂ • ω ₃)
            by rewrite-twolevel 30 auto
        equals (ω ₃ • ω ₁ • H ₂₃ • H ₀₁ • ω ₃ ^ 4) • (H ₀₁ • H ₂₃ • H ₀₂ • H ₁₃) • (ω ₃ ^ 4 • H ₁₃ • H ₀₂)
            by right (left axiom ([20] {kl = ₁₂}))
        equals (ω ₃ • ω ₁ • H ₂₃ • H ₀₁ • ω ₃ ^ 4) • (H ₀₂ • H ₁₃ • H ₀₁ • H ₂₃) • (ω ₃ ^ 4 • H ₁₃ • H ₀₂)
            by general-comm auto
        equals (ω ₁ • ω ₃) • (H ₂₃ • H ₀₁) • ω ₃ ^ 4 • (H ₁₃ • H ₀₂) • (H ₂₃ • H ₀₁) • ω ₃ ^ 4 • H ₁₃ • H ₀₂

soundness-base rel-A = rewrite-twolevel 30 auto
soundness-base rel-B = rewrite-twolevel 30 auto
soundness-base rel-C = lemma-soundness-rel-C

-- Proof of the soundness theorem: All the work was done in the base
-- cases. The rest is just an obvious induction.
soundness : soundness-property
soundness (axiom x) = soundness-base x
soundness refl = refl
soundness (symm deriv) = symm (soundness deriv)
soundness (trans deriv deriv₁) = trans (soundness deriv) (soundness deriv₁)
soundness (cong deriv deriv₁) = cong (soundness deriv) (soundness deriv₁)
soundness assoc = assoc
soundness left-unit = left-unit
soundness right-unit = right-unit

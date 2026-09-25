------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness: a relation between Clifford+T words that holds after
-- translation into Greylyn's generators holds in the Clifford+T relations.
-- First relative to Greylyn's simplified relations, by the Reidemeister-
-- Schreier theorem with the two cosets of the Clifford+T group in
-- U₄(ℤ[1/√2,i]) (8 + 2·19 = 46 equations, in Equations), then for
-- Greylyn's relations.  Ported from the Agda code accompanying Bian and
-- Selinger, "Generators and relations for 2-qubit Clifford+T operators"
-- (CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit.Completeness where

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
open import Presentation.Tactics.Reidemeister-Schreier hiding (lemma-*-*)
open import Examples.Groups.Clifford+T-2qubit.Greylyn-Simplified as Greylyn-Simplified
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation1
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation2
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation3
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation4
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation5
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation6
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation7
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation8
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation9
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation10
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation11
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation12
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation13
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation14
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation15
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation16
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation17
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation18
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation19
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation20
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation21
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation22
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation23
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation24
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation25
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation26
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation27
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation28
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation29
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation30
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation31
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation32
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation33
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation34
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation35
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation36
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation37
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation38
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation39
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation40
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation41
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation42
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation43
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation44
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation45
open import Examples.Groups.Clifford+T-2qubit.Equations.Equation46

-- ----------------------------------------------------------------------
-- * Step 1: Completeness w.r.t. Greylyn's simplified relations

module Step1 where

  -- Here, we prove completeness of the 2-qubit Clifford+T generators
  -- with respect to Greylyn's simplified generators and relations.
  -- With all the work we have already done, this is now a simple
  -- application of the Reidemeister-Schreier theorem.

  open Clifford+T
  open Associative
  open Reidemeister-Schreier-Full

  -- The cosets for the Reidemeister-Schreier theorem. Since the
  -- 2-qubit Clifford+T group is a subgroup of U₄(ℤ[1/√2, i]) of index
  -- 2, there are exactly 2 cosets. We use 1 and ω as the coset
  -- representatives.
  data Cosets : Set where
    I : Cosets
    Ω : Cosets

  -- The main translation function from Greylyn's simplified
  -- generators to the Clifford+T generators. Since the latter don't
  -- span the former, the translation needs to keep track of cosets.
  h : Cosets -> Greylyn-Simplified.Generator -> Word Clifford+T.Generator × Cosets
  h I ω₀-gen = (T0⁻¹ • T1⁻¹ • W , Ω)
  h I X₀₁-gen = (X1 • CX1 , I)
  h I X₁₂-gen = (Swap , I)
  h I X₂₃-gen = (CX1 , I)
  h I H₀₁-gen = (X0 • CH1 • X0 , I)
  h Ω ω₀-gen = (X0 • CX0 • T0 • CX0 • X0 , I)
  h Ω X₀₁-gen = (X1 • CX1 , Ω)
  h Ω X₁₂-gen = (Swap , Ω)
  h Ω X₂₃-gen = (T1 • CX1 • T1⁻¹ , Ω)
  h Ω H₀₁-gen = (X0 • CH1 • X0 , Ω)

  -- The main translation function f' from the Clifford+T generators
  -- to Greylyn's simplified generators. Recall that a translation f
  -- from the Clifford+T generators to Greylyn's original generators
  -- was already defined prior to the statement of the completeness
  -- theorem in Generator.agda. The translation f' is simply the
  -- composition of f with the function simple-of-greylyn.
  f' : Clifford+T.Generator -> Word Greylyn-Simplified.Generator
  f' x = simple-of-greylyn (f x)

  -- Hypothesis (a) of the Reidemeister-Schreier theorem. It requires
  -- one equation to be proved for each Clifford+T generator.
  hypA : ∀ (x : Clifford+T.Generator) -> Clifford+T.Rel ⊢ₚ (h ᵗ) I (f' x) === ([ x ]ʷ , I)
  hypA W-gen = (up-to-assoc auto (symm eqn1) , auto)
  hypA H0-gen = (up-to-assoc auto (symm eqn2) , auto)
  hypA H1-gen = (up-to-assoc auto (symm eqn3) , auto)
  hypA S0-gen = (up-to-assoc auto (symm eqn4) , auto)
  hypA S1-gen = (up-to-assoc auto (symm eqn5) , auto)
  hypA T0-gen = (up-to-assoc auto (symm eqn6) , auto)
  hypA T1-gen = (up-to-assoc auto (symm eqn7) , auto)
  hypA CZ-gen = (up-to-assoc auto (symm eqn8) , auto)

  -- Hypothesis (b) of the Reidemeister-Schreier theorem. It requires
  -- one equation to be proved for each pair of a coset and a
  -- simplified Greylyn relation.
  hypB : ∀ (c : Cosets) {u t : Word Greylyn-Simplified.Generator} -> u === t ∈ Greylyn-Simplified.Rel -> Clifford+T.Rel ⊢ₚ (h ᵗ) c u === (h ᵗ) c t
  hypB I [S1] = (up-to-assoc auto eqn9 , auto)
  hypB Ω [S1] = (up-to-assoc auto eqn10 , auto)
  hypB I [S2] = (up-to-assoc auto eqn11 , auto)
  hypB Ω [S2] = (up-to-assoc auto eqn12 , auto)
  hypB I [S3] = (up-to-assoc auto eqn13 , auto)
  hypB Ω [S3] = (up-to-assoc auto eqn14 , auto)
  hypB I [S4] = (up-to-assoc auto eqn15 , auto)
  hypB Ω [S4] = (up-to-assoc auto eqn16 , auto)
  hypB I [S5] = (up-to-assoc auto eqn17 , auto)
  hypB Ω [S5] = (up-to-assoc auto eqn18 , auto)
  hypB I [S6] = (up-to-assoc auto eqn19 , auto)
  hypB Ω [S6] = (up-to-assoc auto eqn20 , auto)
  hypB I [S7] = (up-to-assoc auto eqn21 , auto)
  hypB Ω [S7] = (up-to-assoc auto eqn22 , auto)
  hypB I [S8] = (up-to-assoc auto eqn23 , auto)
  hypB Ω [S8] = (up-to-assoc auto eqn24 , auto)
  hypB I [S9] = (up-to-assoc auto eqn25 , auto)
  hypB Ω [S9] = (up-to-assoc auto eqn26 , auto)
  hypB I [S10] = (up-to-assoc auto eqn27 , auto)
  hypB Ω [S10] = (up-to-assoc auto eqn28 , auto)
  hypB I [S11] = (up-to-assoc auto eqn29 , auto)
  hypB Ω [S11] = (up-to-assoc auto eqn30 , auto)
  hypB I [S12] = (up-to-assoc auto eqn31 , auto)
  hypB Ω [S12] = (up-to-assoc auto eqn32 , auto)
  hypB I [S13] = (up-to-assoc auto eqn33 , auto)
  hypB Ω [S13] = (up-to-assoc auto eqn34 , auto)
  hypB I [S14] = (up-to-assoc auto eqn35 , auto)
  hypB Ω [S14] = (up-to-assoc auto eqn36 , auto)
  hypB I [S15] = (up-to-assoc auto eqn37 , auto)
  hypB Ω [S15] = (up-to-assoc auto eqn38 , auto)
  hypB I [S16] = (up-to-assoc auto eqn39 , auto)
  hypB Ω [S16] = (up-to-assoc auto eqn40 , auto)
  hypB I [S17] = (up-to-assoc auto eqn41 , auto)
  hypB Ω [S17] = (up-to-assoc auto eqn42 , auto)
  hypB I [S18] = (up-to-assoc auto eqn43 , auto)
  hypB Ω [S18] = (up-to-assoc auto eqn44 , auto)
  hypB I [S19] = (up-to-assoc auto eqn45 , auto)
  hypB Ω [S19] = (up-to-assoc auto eqn46 , auto)

  -- The completeness theorem for the 2-qubit Clifford+T group,
  -- relative to completeness for Greylyn's simplified relations.
  completeness-simple : ∀ {w v} -> Greylyn-Simplified.Rel ⊢ (f' ʷ) w === (f' ʷ) v -> Clifford+T.Rel ⊢ w === v
  completeness-simple {w} {v} hyp = reidemeister-schreier Cosets I f' h hypA hypB w v hyp 

-- ----------------------------------------------------------------------
module Step2 where

  -- The proof of the main completeness theorem for the 2-qubit
  -- Clifford+T generators, relative to the known completeness result
  -- for Greylyn's generators and relations for U₄(ℤ[1/√2, i]).

  open Step1
  open Monoid-Equational

  -- This lemma states that when we compose two translations from
  -- generators to words, the composition behaves as expected, i.e.,
  --
  -- g* ∘ f* = (g* ∘ f)*.
  lemma-*-* : ∀ {X Y Z : Set} -> (f : X -> Word Y) -> (g : Y -> Word Z) -> ∀ (w : Word X) -> (g ʷ) ((f ʷ) w) ≡ ((\y -> (g ʷ) (f y)) ʷ) w
  lemma-*-* f g ([ x ]ʷ) = Eq.refl
  lemma-*-* f g ε = Eq.refl
  lemma-*-* f g (w • w') = Eq.cong₂ _•_ (lemma-*-* f g w) (lemma-*-* f g w')

  -- The lemma states that f'* is just the composition of
  -- simple-of-greylyn and f*.
  lemma-simple-of-greylyn : ∀ (w : Word Clifford+T.Generator) -> simple-of-greylyn ((f ʷ) w) ≡ (f' ʷ) w
  lemma-simple-of-greylyn w = lemma-*-* f simple-of-greylyn-gen w

  -- The completeness theorem for the 2-qubit Clifford+T group.
  -- This is now an easy consequence of completeness-simple.
  completeness : completeness-property
  completeness {w} {v} hyp = completeness-simple hyp'
    where
      hyp' : Greylyn-Simplified.Rel ⊢ (f' ʷ) w === (f' ʷ) v
      hyp' =
        equational (f' ʷ) w
                by refl' (lemma-simple-of-greylyn w) reversed
            equals simple-of-greylyn ((f ʷ) w)
                by theorem-simple-of-greylyn hyp
            equals simple-of-greylyn ((f ʷ) v)
                by refl' (lemma-simple-of-greylyn v)
            equals (f' ʷ) v

open Step1 public
open Step2 public

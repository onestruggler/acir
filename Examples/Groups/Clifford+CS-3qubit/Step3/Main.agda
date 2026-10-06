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
open import Presentation.Tactics.Reidemeister-Schreier

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
open import Examples.Groups.Clifford+CS-3qubit.Step3.Lemmas

open import Examples.Groups.Clifford+CS-3qubit.Step2.Theorem using (module TwoLevel-Simplified)
open TwoLevel-Simplified hiding (Rel)

module Examples.Groups.Clifford+CS-3qubit.Step3.Main where

  -- Translation from Gate to simplified TwoLevel
  simple-of-gate-gen : Gate -> Word Gen
  simple-of-gate-gen CCX0-gen = X₃₇
  simple-of-gate-gen CCX1-gen = X₅₇
  simple-of-gate-gen CCX2-gen = X₆₇
  simple-of-gate-gen CX01-gen = X₄₆ • X₅₇
  simple-of-gate-gen CX10-gen = X₂₆ • X₃₇
  simple-of-gate-gen CX12-gen = X₂₃ • X₆₇
  simple-of-gate-gen CX21-gen = X₁₃ • X₅₇
  simple-of-gate-gen CX02-gen = X₄₅ • X₆₇
  simple-of-gate-gen CX20-gen = X₁₅ • X₃₇
  simple-of-gate-gen X0-gen = X₀₄ • X₁₅ • X₂₆ • X₃₇
  simple-of-gate-gen X1-gen =  X₀₂ • X₁₃ • X₄₆ • X₅₇
  simple-of-gate-gen X2-gen = X₀₁ • X₂₃ • X₄₅ • X₆₇
  simple-of-gate-gen Swap01-gen = X₂₄ • X₃₅
  simple-of-gate-gen Swap12-gen = X₁₂ • X₅₆
  simple-of-gate-gen S0-gen = i₄ • i₅ • i₆ • i₇
  simple-of-gate-gen S1-gen = i₂ • i₃ • i₆ • i₇
  simple-of-gate-gen S2-gen = i₁ • i₃ • i₅ • i₇
  simple-of-gate-gen CS01-gen = i₆ • i₇
  simple-of-gate-gen CS12-gen = i₃ • i₇
  simple-of-gate-gen CS02-gen = i₅ • i₇
  simple-of-gate-gen CCZ-gen = i₇ • i₇
  simple-of-gate-gen iI-gen = i₀ • i₁ • i₂ • i₃ • i₄ • i₅ • i₆ • i₇
  simple-of-gate-gen CCK'-gen = K₃₇ • i₇ • i₇ • i₇
  simple-of-gate-gen CK10-gen = K₂₆ • K₃₇
  simple-of-gate-gen CK20-gen = K₁₅ • K₃₇
  simple-of-gate-gen K0-gen = K₀₄ • K₁₅ • K₂₆ • K₃₇
  simple-of-gate-gen K1-gen = (X₂₄ • X₃₅) • (K₀₄ • K₁₅ • K₂₆ • K₃₇) • (X₂₄ • X₃₅)
  simple-of-gate-gen K2-gen = (X₁₂ • X₅₆) • ((X₂₄ • X₃₅) • (K₀₄ • K₁₅ • K₂₆ • K₃₇) • (X₂₄ • X₃₅)) • (X₁₂ • X₅₆)

  data Cosets : Set where
    I : Cosets
    I₁ : Cosets

  -- Translation from simplified TwoLevel to Gate.
  h : Cosets -> Gen -> Word Gate × Cosets
  h I i₀-gen = X1 • X0 • CS01 • CCZ • X0 • X1 , I₁
  h I K₀₁-gen = Swap12 • Swap01 • X1 • X2 • CCK' • X2 • X1 • Swap01 • Swap12 , I₁
  h I X₀₁-gen = X1 • X0 • CCX2 • X0 • X1 , I
  h I X₁₂-gen = X0 • CX21 • CCX2 • CX21 • X0 , I
  h I X₂₃-gen = X0 • CCX2 • X0 , I
  h I X₃₄-gen = X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2 , I
  h I X₄₅-gen = X1 • CCX2 • X1 , I
  h I X₅₆-gen = CX21 • CCX2 • CX21 , I
  h I X₆₇-gen = CCX2 , I
  h I₁ i₀-gen = X1 • X0 • CS01 • X0 • X1 , I
  h I₁ K₀₁-gen = Swap12 • Swap01 • X1 • X2 • CCK' • CS12 • CCK' • X2 • X1 • Swap01 • Swap12 , I
  h I₁ X₀₁-gen = X1 • X0 • CCX2 • CS01 • CCZ • X0 • X1 , I₁
  h I₁ X₁₂-gen = S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02 • CX12 • CCX1 • CX21 • CX12 , I₁
  h I₁ X₂₃-gen = X0 • CCX2 • X0 , I₁
  h I₁ X₃₄-gen = X2 • CX10 • CX21 • CCX2 • CX21 • CX10 • X2 , I₁
  h I₁ X₄₅-gen = X1 • CCX2 • X1 , I₁
  h I₁ X₅₆-gen = CX21 • CCX2 • CX21 , I₁
  h I₁ X₆₇-gen = CCX2 , I₁

  f' = simple-of-gate-gen

  open Group-Lemmas Gate Rel group-like

  hypA : ∀ (x : Gate) -> Rel ⊢ₚ (h ᵗ) I (f' x) === ([ x ]ʷ , I)
  hypA CCX0-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CCX1-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CCX2-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CX01-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CX10-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CX12-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CX21-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CX02-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CX20-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA X0-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA X1-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA X2-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA Swap01-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA Swap12-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA S0-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA S1-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA S2-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CS01-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CS12-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CS02-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CCZ-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA iI-gen = lemma-one-sided (PD.nfeq auto) , auto
  hypA CCK'-gen = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypA CK10-gen = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypA CK20-gen = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypA K0-gen = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypA K1-gen = lemma-K1 , auto
  hypA K2-gen = lemma-K2 , auto

  hypB : ∀ (c : Cosets) {u t : Word Gen} -> u === t ∈ TwoLevel-Simplified.Rel -> Rel ⊢ₚ (h ᵗ) c u === (h ᵗ) c t
  hypB I [S1] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S3a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S3b] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S3c] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S3d] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S3e] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S3f] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S3g] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S4a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S4b] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S5a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S5b] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S5c] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S5d] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S5e] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S5f] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S6] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S7a] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S7b] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S7c] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S7d] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S7e] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S8a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8b] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8c] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8d] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8e] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8f] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8g] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8h] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8i] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8j] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8k] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8l] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8m] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8n] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S8o] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S9a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S9b] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S9c] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S9d] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S9e] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S9f] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I [S10] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S11] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S12] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S14] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I [S15] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S1] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S3a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S3b] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S3c] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S3d] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S3e] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S3f] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S3g] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S4a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S4b] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S5a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S5b] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S5c] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S5d] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S5e] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S5f] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S6] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S7a] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S7b] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S7c] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S7d] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S7e] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S8a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8b] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8c] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8d] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8e] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8f] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8g] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8h] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8i] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8j] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8k] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8l] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8m] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8n] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S8o] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S9a] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S9b] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S9c] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S9d] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S9e] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S9f] = lemma-one-sided (PD.nfeq auto) , auto
  hypB I₁ [S10] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S11] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S12] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S14] = lemma-one-sided (ListNF.listnfeq' ANF auto) , auto
  hypB I₁ [S15] = symm (lemma-one-sided (ListNF.listnfeq' ANF auto)) , auto

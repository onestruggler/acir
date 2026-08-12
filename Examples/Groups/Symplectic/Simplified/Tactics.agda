------------------------------------------------------------------------
-- Presentations of groups
--
-- Word tactics for the simplified generators
--
-- The commutation table and generator ordering feeding
-- Presentation.Tactic.Rewriting, plus the rewriting step function
-- step-sym0 and its closure rewrite-sim.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.PropositionalEquality using (_≡_ ; inspect ; setoid ; module ≡-Reasoning ; _≢_) renaming ([_] to [_]')
open import Relation.Nullary.Decidable using (yes ; no)



open import Data.Product using (_,_ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
import Data.Nat as Nat
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Bool
open import Data.List hiding ([_])


open import Data.Maybe

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Normalization.Reidemeister-Schreier as RS
open import Notations
module RSF = RS.Star-Injective-Full.Reidemeister-Schreier-Full
open import Presentation.Tactic.Rewriting



open import Data.Nat.Primality
open import Data.Nat.GCD
open Bézout
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Symplectic.Simplified.Tactics
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime as NSym
open Symplectic hiding (_QRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; lemma-cong↑ ; order-S ; order-H ; semi-MS ; semi-M↑CZ ; semi-M↓CZ ; order-CZ ; comm-CZ-S↓ ; comm-CZ-S↑ ; selinger-c10 ; selinger-c11 ; selinger-c12 ; selinger-c13 ; selinger-c14 ; selinger-c15)

open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
open import Examples.Groups.Symplectic.Simplified.Lemmas p-2 p-prime g* g-gen

-- ----------------------------------------------------------------------
-- * Data required for applying word tactics to Symplectic generators

module CommData-Sim where
  variable
    n : ℕ

  open Simplified-Relations
  open Lemmas-Sim
  
  
  -- Commutativity.
  commute : (x y : Gen (₂₊ n)) → let open PB ((₂₊ n) QRel,_===_) in Maybe (([ x ]ʷ • [ y ]ʷ) ≈ ([ y ]ʷ • [ x ]ʷ))
  commute {n} H-gen (y ↥) = just (PB.sym (PB.axiom (comm₁ H-gate _)))
  commute {n} (x ↥) H-gen = just (PB.axiom (comm₁ H-gate _))
  commute {n} S-gen (y ↥) = just (PB.sym (PB.axiom (comm₁ S-gate _)))
  commute {n} (x ↥) S-gen = just (PB.axiom (comm₁ S-gate _))
  commute {n} S-gen CZ-gen = just (PB.sym (PB.axiom (srel comm-CZ-S↓)))
  commute {n} CZ-gen S-gen = just (PB.axiom (srel comm-CZ-S↓))
  commute {n} (S-gen ↥) CZ-gen = just (PB.sym (PB.axiom (srel comm-CZ-S↑)))
  commute {n} CZ-gen (S-gen ↥) = just (PB.axiom (srel comm-CZ-S↑))
  
  commute {n@(₁₊ n')} CZ-gen (CZ-gen ↥) = just (PB.sym (PB.axiom (srel selinger-c12)))
  commute {n} (CZ-gen ↥) CZ-gen = just (PB.axiom (srel selinger-c12))
  
  commute {n@(₁₊ n')} CZ-gen ((y ↥) ↥) = just (PB.sym (PB.axiom (comm₂ CZ-gate _)))
  commute {n@(₁₊ n')} ((x ↥) ↥) CZ-gen = just (PB.axiom (comm₂ CZ-gate _))
  
  commute {n@(₁₊ n')} (x ↥) (y ↥) with commute x y
  ... | nothing = nothing
  ... | just eq = just (lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) eq)

  commute {n} _ _ = nothing


  -- We number the generators for the purpose of ordering them.
  ord : Gen (₁₊ n) → ℕ
  ord {n}(S-gen) = 0
  ord {n} (H-gen) = 1
  ord {₁₊ n} (CZ-gen) = 2
  -- On one wire the only thing under a shift is gate₀, which ord cannot
  -- be applied to (it wants a non-zero width), so this case is constant
  -- rather than recursive.
  ord {₀} (g ↥) = 3
  ord {₁₊ n} (g ↥) = 3 Nat.+ ord g


  -- Ordering of generators.
  les : Gen (₂₊ n) → Gen (₂₊ n) → Bool
  les x y with ord x Nat.<? ord y
  les x y | yes _ = true
  les x y | no _ = false

module Commuting-Symplectic-Sim (n : ℕ) where
  open Simplified-Relations
  open CommData-Sim hiding (n)
  open Commuting (((₂₊ n) QRel,_===_) ) commute les public


module Rewriting-Sim where

  open Rewriting
  open Simplified-Relations
  variable
    n : ℕ

  
  
  step-sym0 : let open PB ((₁₊ n) QRel,_===_) hiding (_===_) in Step-Function (Gen (₁₊ n))  ((₁₊ n) QRel,_===_)

  -- Order of generators.
  step-sym0 {n} ((H-gen) ∷ (H-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (lemma-order-H))
    where
    open Lemmas1 n
  step-sym0 {₁₊ n} ((H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ lemma-order-H))
    where
    open Lemmas1 n
    open Lemmas-Sim
  step-sym0 {₂₊ n} ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ (lemma-cong↑ _ _ lemma-order-H)))
    where
    open Lemmas1 n
    open Lemmas-Sim

  step-sym0 {n} ((S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ (S-gen) ∷ (H-gen) ∷ xs) = just (xs , at-head (lemma-order-SH))
    where
    open Lemmas1 n
  step-sym0 {₁₊ n} ((S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ (H-gen ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ lemma-order-SH))
    where
    open Lemmas1 n
    open Lemmas-Sim
  step-sym0 {₂₊ n} ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just (xs , at-head (lemma-cong↑ _ _ (lemma-cong↑ _ _ lemma-order-SH)))
    where
    open Lemmas1 n
    open Lemmas-Sim

  -- Commuting of generators.
  step-sym0 ((S-gen) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (PB.axiom (srel comm-CZ-S↓))))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (srel comm-CZ-S↑))))
  step-sym0 ((S-gen ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ (srel comm-CZ-S↓)))))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen ↥) ∷ xs) = just ((CZ-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (PB.axiom (cong↑ (srel comm-CZ-S↑)))))

  step-sym0 ((H-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom (comm₂ CZ-gate _)))
  step-sym0 ((S-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom (comm₂ CZ-gate _)))

  step-sym0 ((S-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom (comm₁ S-gate _))))
  step-sym0 ((S-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ (comm₁ S-gate _)))))
  step-sym0 ((S-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom (comm₁ S-gate _)))
  step-sym0 ((S-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥) ∷ xs , at-head ((PB.axiom (comm₁ H-gate _))))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ (comm₁ H-gate _)))))
  step-sym0 ((S-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.axiom (comm₁ H-gate _)))
  step-sym0 ((H-gen ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom (comm₁ H-gate _))))
  step-sym0 ((H-gen ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥) ∷ xs , at-head ((PB.axiom (comm₁ S-gate _))))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ (comm₁ H-gate _)))))
  step-sym0 ((H-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom (comm₁ H-gate _)))
  step-sym0 ((H-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (H-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ (comm₁ S-gate _)))))
  step-sym0 ((H-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (H-gen ↥ ↥) ∷ xs , at-head (PB.axiom (comm₁ S-gate _)))

  step-sym0 ((CZ-gen ↥ ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ (comm₁ H-gate _)))))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom (comm₁ H-gate _)))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (S-gen ↥) ∷ xs) = just ((S-gen ↥) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (cong↑ (comm₁ S-gate _)))))
  step-sym0 ((CZ-gen ↥ ↥) ∷ (S-gen) ∷ xs) = just ((S-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head (PB.axiom (comm₁ S-gate _)))

  step-sym0 ((CZ-gen ↥ ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥ ↥) ∷ xs , at-head ((PB.axiom (comm₂ CZ-gate _))))
  step-sym0 ((CZ-gen ↥) ∷ (CZ-gen) ∷ xs) = just ((CZ-gen) ∷ (CZ-gen ↥) ∷ xs , at-head ((PB.axiom (srel selinger-c12))))

  step-sym0 {n} ((S-gen) ∷ (H-gen) ∷ (H-gen) ∷ xs) = just ((H-gen) ∷ (H-gen) ∷ (S-gen) ∷ xs , at-head (PB.sym (lemma-comm-HHS)))
    where
    open Lemmas1b n
    open Lemmas-Sim
  step-sym0 {₁₊ n} ((S-gen ↥) ∷ (H-gen ↥) ∷ (H-gen ↥) ∷ xs) = just ((H-gen ↥) ∷ (H-gen ↥) ∷ (S-gen ↥) ∷ xs , at-head (PB.sym (lemma-cong↑ _ _ lemma-comm-HHS)))
    where
    open Lemmas1b n
    open Lemmas-Sim
  step-sym0 {₂₊ n} ((S-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ xs) = just ((H-gen ↥ ↥) ∷ (H-gen ↥ ↥) ∷ (S-gen ↥ ↥) ∷ xs , at-head (PB.sym (lemma-cong↑ _ _ (lemma-cong↑ _ _ lemma-comm-HHS))))
    where
    open Lemmas1b n
    open Lemmas-Sim

  -- Catch-all
  step-sym0 _ = nothing

module Sim-Rewriting (n : ℕ) where
  open Rewriting
  open Rewriting-Sim hiding (n)
  open Rewriting.Step (step-cong (step-sym0 {n})) renaming (general-rewrite to rewrite-sim) public

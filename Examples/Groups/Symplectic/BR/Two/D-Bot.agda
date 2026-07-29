{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Pushing a bottom gate (H-gen or S-gen) through a D box.
--
-- This is the dual of BR.Two.B-Top.lemma-B-br: where B-Top pushes a top
-- gate (gate₁ x₁ ↥) through a B box and leaves the residual on the
-- bottom wire (dir ↓ᵏ 1), D-Bot pushes a bottom gate (gate₁ x₁) through
-- a D box and leaves the residual on the top wire (dir ↑).
--
-- Unlike B-Top no `dual` bridge is needed: BR.Two.D.lemma-D-br already
-- emits the residual on the top wire, and for a bottom single-qubit gate
-- the bottom phase is S^ ₀ ↓ = ε, which left-unit discards.
------------------------------------------------------------------------

open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Nat hiding (_^_ ; _+_ ; _*_)

open import Word.Base as WB hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Data.Nat.Primality
open import Notations

module Examples.Groups.Symplectic.BR.Two.D-Bot (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
import Examples.Groups.Symplectic.BR.Two.D p-2 p-prime as DD

open PB (₂ QRel,_===_)
open PP (₂ QRel,_===_)
open SR word-setoid

-- The updated box: the same update as B-Top's b'-of (H sends (a,b) to
-- (b,-a); S sends (a,b) to (a, b-a)), matching D.d'-of on gate₁ x₁.
d'-of : ∀ (d : D) (x₁ : SympGate 1) -> D
d'-of (a , b) H-gate = b , - a
d'-of (a , b) S-gate = a , b + - a

-- The top-wire residual: proj₂ of D.dir-of on the bottom gate gate₁ x₁.
dir-of : ∀ (d : D) (x₁ : SympGate 1) -> Word (Gen 1)
dir-of (₀ , ₀)                 H-gate = H
dir-of (₀ , ₁₊ b)              H-gate = ε
dir-of (₁₊ a , ₀)              H-gate = H ^ 2
dir-of (a@(₁₊ _) , b@(₁₊ _))   H-gate = ZM a/b • S^ b/a
  where
  a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
  b/a = b * a⁻¹
  a/b = (a , λ ()) *' (b , λ ()) ⁻¹
dir-of (₀ , b)                 S-gate = S
dir-of (₁₊ a , b)              S-gate = ε

-- The dual of B-Top.lemma-B-br.
lemma-D-br : ∀ (d : D) (x₁ : SympGate 1) ->
  let
  dir = dir-of d x₁
  d' = d'-of d x₁
  in

  [ d ]ᵈ • [ gate₁ x₁ ]ʷ ≈ (dir ↑) • [ d' ]ᵈ

lemma-D-br d@(₀ , ₀)         H-gate = trans (DD.lemma-D-br d H-gen (λ ())) left-unit
lemma-D-br d@(₀ , ₁₊ _)      H-gate = trans (DD.lemma-D-br d H-gen (λ ())) left-unit
lemma-D-br d@(₁₊ _ , ₀)      H-gate = trans (DD.lemma-D-br d H-gen (λ ())) left-unit
lemma-D-br d@(₁₊ _ , ₁₊ _)   H-gate = trans (DD.lemma-D-br d H-gen (λ ())) left-unit
lemma-D-br d@(₀ , ₀)         S-gate = trans (DD.lemma-D-br d S-gen (λ ())) left-unit
lemma-D-br d@(₀ , ₁₊ _)      S-gate = trans (DD.lemma-D-br d S-gen (λ ())) left-unit
lemma-D-br d@(₁₊ _ , ₀)      S-gate = trans (DD.lemma-D-br d S-gen (λ ())) left-unit
lemma-D-br d@(₁₊ _ , ₁₊ _)   S-gate = trans (DD.lemma-D-br d S-gen (λ ())) left-unit

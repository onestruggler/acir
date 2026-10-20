------------------------------------------------------------------------
-- Presentations of groups
--
-- The three five-wire equations of Lambda.Split, from four-wire
-- completeness
--
-- Each CS of the bottom four wires is its two halves controlled by
-- wire 4, λ⁰(CS) λ¹(CS), the S-box of Lambda in λ¹: the derivations
-- Five.D (scratchpad/joint/f5.py, lowered and emitted by
-- scratchpad/five), from four-wire windows only — the box calculus
-- they rest on is scratchpad/joint/box.py.  So g ≡ λ⁰(g) λ¹(g) holds for
-- every generator at every width from five on, given completeness on
-- four wires (`split₅`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.F5 where

open import Data.Nat using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using ([_]ʷ ; _•_)

open import Notations using (₄ ; ₄₊)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.Lambda using (Xᵗ ; λ⁰ ; λ¹)
open import Examples.Groups.Clifford+CS.Lambda.Split using (F5 ; split)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Flat using (by-flat)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F5-01 ; lem-F5-12 ; lem-F5-23)

f5 : Ws → F5
f5 c4 = record
  { cs₀₁ = sym (trans (by-flat Eq.refl) (lem-F5-01 c4))
  ; cs₁₂ = sym (trans (by-flat Eq.refl) (lem-F5-12 c4))
  ; cs₂₃ = sym (trans (by-flat Eq.refl) (lem-F5-23 c4))
  }

-- The λ-calculus (ii) at every width from five on.
split₅ : Ws → ∀ {n} (g : Gen (₄₊ n)) → (suc (₄₊ n)) ⊢ₓ top [ g ]ʷ ≈ λ⁰ g • λ¹ g
split₅ c4 = split (f5 c4)

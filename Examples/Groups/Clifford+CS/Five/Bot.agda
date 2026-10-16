------------------------------------------------------------------------
-- Presentations of groups
--
-- Affine circuits on the bottom wires
--
-- A four-wire affine circuit widened by one idle wire on top (`bot`,
-- Circuit.Base's _↓ᵏ_ for Blake's gates) is the same circuit of
-- Clifford+CS gates widened (`τ-bot`), and its action on bits leaves
-- the top bit alone (`bm-bot`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Bot where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (prime[2])
open import Data.Vec using ([] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Semantics using (Bits)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit ; _↑ ; _↓ᵏ_)
open import Examples.Groups.Clifford+CS.Five.Affine using (τg ; τ)
open import Examples.Groups.Clifford+CS.Five.Sem.Aff using (bm ; bmg)

import Examples.Groups.Qupit-Phase-Affine.Syntactics 0 prime[2] 0 as B

private
  variable
    n : ℕ

bot : B.Circuit n → B.Circuit (n Data.Nat.+ 1)
bot w = w B.↓ᵏ 1

------------------------------------------------------------------------
-- The gates

-- Shifting up and widening commute.
↑-↓ : (w : Circuit n) → (w ↑) ↓ᵏ 1 ≡ (w ↓ᵏ 1) ↑
↑-↓ [ g ]ʷ  = refl
↑-↓ ε       = refl
↑-↓ (u • v) = Eq.cong₂ _•_ (↑-↓ u) (↑-↓ v)

τg-bot : (g : B.Gen n) → τg (g B.↧ᵏ 1) ≡ τg g ↓ᵏ 1
τg-bot (B.gate₀ _)                 = refl
τg-bot (B.gate₁ B.X-gate)          = refl
τg-bot (B.gate₁ (B.M-gate _ _))    = refl
τg-bot (B.gate₁ (B.Z-gate _))      = refl
τg-bot (B.gate₁ (B.S-gate _))      = refl
τg-bot (B.gate₁ (B.T-gate _))      = refl
τg-bot (B.gate₂ B.CX-gate)         = refl
τg-bot (B.gate₂ B.SWAP-gate)       = refl
τg-bot (g B.↥)                     = Eq.trans (Eq.cong _↑ (τg-bot g)) (Eq.sym (↑-↓ (τg g)))

τ-bot : (w : B.Circuit n) → τ (bot w) ≡ τ w ↓ᵏ 1
τ-bot [ g ]ʷ  = τg-bot g
τ-bot ε       = refl
τ-bot (u • v) = Eq.cong₂ _•_ (τ-bot u) (τ-bot v)

------------------------------------------------------------------------
-- The action on bits

private
  bmg-bot : (g : B.Gen n) (x : Bits n) (b : Bool) → bmg (g B.↧ᵏ 1) (x ++ (b ∷ [])) ≡ bmg g x ++ (b ∷ [])
  bmg-bot (B.gate₀ _)               x           b = refl
  bmg-bot (B.gate₁ B.X-gate)        (a ∷ x)     b = refl
  bmg-bot (B.gate₁ (B.M-gate _ _))  x           b = refl
  bmg-bot (B.gate₁ (B.Z-gate _))    x           b = refl
  bmg-bot (B.gate₁ (B.S-gate _))    x           b = refl
  bmg-bot (B.gate₁ (B.T-gate _))    x           b = refl
  bmg-bot (B.gate₂ B.CX-gate)       (a ∷ c ∷ x) b = refl
  bmg-bot (B.gate₂ B.SWAP-gate)     (a ∷ c ∷ x) b = refl
  bmg-bot (g B.↥)                   (a ∷ x)     b = Eq.cong (a ∷_) (bmg-bot g x b)

bm-bot : (w : B.Circuit n) (x : Bits n) (b : Bool) → bm (bot w) (x ++ (b ∷ [])) ≡ bm w x ++ (b ∷ [])
bm-bot [ g ]ʷ  x b = bmg-bot g x b
bm-bot ε       x b = refl
bm-bot (u • v) x b = Eq.trans (Eq.cong (bm (bot u)) (bm-bot v x b)) (bm-bot u (bm v x) b)

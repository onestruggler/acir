------------------------------------------------------------------------
-- Presentations of groups
--
-- Pushing a power of S through an M box, by iterating push-M-S.
--
--   [ m ]ᵐ • S ^ j  ≈  dir • [ m' ]ᵐ
--
-- This is the "push the dirty gate through M" step for the S-power
-- dirties.  Its relevance: when a generator (S, H, CZ) is pushed through
-- an L box, the bottom A box turns it into a *power of S* (never an H —
-- see BR.One.A.dir-and-A'-of: every A-box direction is ε or S^k).  So the
-- dirty gate that then has to traverse the M column is, at the A-box
-- level, exactly an S^j — handled here — which sidesteps the hard
-- H-through-M rule entirely.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
{-# OPTIONS --termination-depth=2 #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.PushMSn (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Data.Product using (_,_ ; ∃ ; proj₁ ; proj₂)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)
open import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.PushM p-2 p-prime using (push-M-S)

open import Notations
open import Word.Base using (Word ; _•_ ; ε ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

------------------------------------------------------------------------
-- Pushing S ^ j through an M box.

push-M-Sⁿ : ∀ {n} (j : ℕ) (m : M (₁₊ n)) →
  let open PB ((₁₊ n) QRel,_===_) in
  ∃ λ (dir : Word (Gen (₁₊ n))) → ∃ λ (m' : M (₁₊ n)) → [ m ]ᵐ • (S ^ j) ≈ dir • [ m' ]ᵐ

push-M-Sⁿ {n} ₀ m = ε , m , trans right-unit (sym left-unit)
  where open PB ((₁₊ n) QRel,_===_) ; open PP ((₁₊ n) QRel,_===_)

-- S ^ 1 = S : a single push.
push-M-Sⁿ {n} (₁₊ ₀) m = push-M-S m

-- S ^ (2 + j) = S • S ^ (1 + j) : push one S, recurse on the rest.
push-M-Sⁿ {n} (₂₊ j) m = (dir₁ • dir') , m' , claim
  where
  open PB ((₁₊ n) QRel,_===_) ; open PP ((₁₊ n) QRel,_===_) ; open SR word-setoid
  r₁   = push-M-S m
  dir₁ = proj₁ r₁ ;  m₁ = proj₁ (proj₂ r₁) ;  eq₁ = proj₂ (proj₂ r₁)
  r'   = push-M-Sⁿ (₁₊ j) m₁
  dir' = proj₁ r' ;  m' = proj₁ (proj₂ r') ;  eq' = proj₂ (proj₂ r')
  claim : [ m ]ᵐ • (S ^ (₂₊ j)) ≈ (dir₁ • dir') • [ m' ]ᵐ
  claim = begin
    [ m ]ᵐ • (S • S ^ (₁₊ j))       ≈⟨ sym assoc ⟩
    ([ m ]ᵐ • S) • S ^ (₁₊ j)       ≈⟨ cleft eq₁ ⟩
    (dir₁ • [ m₁ ]ᵐ) • S ^ (₁₊ j)   ≈⟨ assoc ⟩
    dir₁ • ([ m₁ ]ᵐ • S ^ (₁₊ j))   ≈⟨ cright eq' ⟩
    dir₁ • (dir' • [ m' ]ᵐ)         ≈⟨ sym assoc ⟩
    (dir₁ • dir') • [ m' ]ᵐ         ∎

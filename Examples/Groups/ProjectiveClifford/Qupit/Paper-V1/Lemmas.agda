{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- What the Paper-V1 rules give, on one wire.
--
-- Paper-V1's job is to be Paper-V0 with the multiplier respelled, and
-- Iso proves exactly that.  So this library only has to reach the four
-- facts Iso needs — order-SH as a theorem, and the bridge between the R-
-- and S-spellings of the multiplier at -1, at g and at g ^ k — and every
-- rule Paper-V0 derives is then a Paper-V1 theorem by transport.
--
-- That is why there is no Ex-conjugation or three-wire layer here.  An
-- earlier version carried one, ported wholesale from Paper-V0: 4255 lines
-- deriving the swap calculus, the lower-wire rules and Selinger's
-- c10–c15 natively.  None of it was reachable from Presentation, because
-- the isomorphism already transports all of it, so it is gone.  Look in
-- Paper-V0.Lemmas for those derivations; they are live there, since
-- Paper-V0.Iso proves Simplified-V1 ⟺ Paper-V0 the long way round and
-- genuinely consumes them.
--
-- This file is a façade over Lemmas/, in dependency order:
--
--   OneWire     multiplier arithmetic on one wire, and lemma-order-SH
--   GroupLike   group-likeness, and powers modulo p
--   XZ          Pauli conjugation past H and past S, the ℤₚ
--               half-exponent arithmetic (where X • Z ≈ Z • X lives),
--               and the bridge between the two spellings
--
-- Clients should keep importing this module: the names Iso.agda and
-- Presentation.agda use are the ones below, and they are unchanged.
------------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Notations
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import ForStdlib.Data.Fin.Mod

module Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.OneWire
  p-3 p-prime g* g-gen public
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.GroupLike
  p-3 p-prime g* g-gen public
open import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Lemmas.XZ
  p-3 p-prime g* g-gen public

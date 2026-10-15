------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary A.5 decoded: K-free words with the same phased permutation
-- decode to equal circuits
--
-- Given the consecutive facts at a width (Lemma88.KFree), the decoding
-- respects every K-free rule of P′, hence the congruence they generate
-- (`d-≈`; `d ʷ` is a monoid homomorphism on the nose), and the
-- fragment's Corollary A.5 (Auxiliary.Unique.A5) carries over (`dA5`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Clifford+CS.Lemma88.FreeA5 (m : ℕ) where

open import Word.Base using (Word ; _ʷ)

import Presentation.Base as PB

open import Notations using (₄₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Numbering (₄₊ m) using (N ; N′)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_)
open import Examples.Groups.Clifford+CS.Auxiliary.NF N′ using (KFreeʷ)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm N using (sp ; _≐_)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique N′ using (A5)
open import Examples.Groups.Clifford+CS.Decoding m using (d)
open import Examples.Groups.Clifford+CS.Lemma88.KFree m using (Facts ; k-free)

open Tools ((₄₊ m) VRel,_===_)

module _ (fs : Facts) where

  -- The decoding respects the K-free congruence.
  d-≈ : ∀ {u t : Word (GenP N)} → PB._≈_ (N F,_===_) u t → (d ʷ) u ≈ (d ʷ) t
  d-≈ PB.refl         = refl
  d-≈ (PB.sym e)      = sym (d-≈ e)
  d-≈ (PB.trans e e′) = trans (d-≈ e) (d-≈ e′)
  d-≈ (PB.cong e e′)  = cong (d-≈ e) (d-≈ e′)
  d-≈ PB.assoc        = assoc
  d-≈ PB.left-unit    = left-unit
  d-≈ PB.right-unit   = right-unit
  d-≈ (PB.axiom a)    = k-free fs a

  -- Corollary A.5, decoded.
  dA5 : ∀ {u v : Word (GenP N)} → KFreeʷ u → KFreeʷ v → sp u ≐ sp v → (d ʷ) u ≈ (d ʷ) v
  dA5 ku kv e = d-≈ (A5 ku kv e)

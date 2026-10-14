------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness at every width, by induction on the width (the analogue
-- of Clément's Theorem 8.9)
--
-- Up to three wires completeness is proved outright (Completeness).
-- From four wires on it is the back-and-forth argument of Section8,
-- whose two circuit-side hypotheses at a width are the analogues of
-- Clément's Lemmas 8.7 and 8.8 — the decoding inverts the encoding,
-- and respects the rules of P′ — and those, as in the paper, are
-- proved with completeness one width down as a black box (Lemma 5.1,
-- in Place and Idle).  This module states the two hypotheses in that
-- form and assembles the induction: given them at every width,
-- completeness holds at every width.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.CompletenessInduction where

open import Data.Nat using (ℕ)
open import Word.Base using (Word ; [_]ʷ ; _ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Completeness
  using (Complete ; complete₀ ; complete₁ ; complete₂ ; complete₃)
open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (_R,_===_)
import Examples.Groups.Clifford+CS.Numbering as Numbering
import Examples.Groups.Clifford+CS.Encoding as Encoding
import Examples.Groups.Clifford+CS.Decoding as Decoding
import Examples.Groups.Clifford+CS.Section8 as Section8

------------------------------------------------------------------------
-- The two hypotheses at a width 4 + m

-- Lemma 8.7: the decoding inverts the encoding.
D∘E : ℕ → Set
D∘E m = ∀ (g : Gen (₄₊ m)) → (₄₊ m) ⊢ [ g ]ʷ ≈ (Decoding.d m ʷ) (Encoding.e m g)

-- Lemma 8.8: the decoding respects the rules of P′.
DWD : ℕ → Set
DWD m = ∀ {u t : Word (GenP (Numbering.N (₄₊ m)))} → Numbering.N (₄₊ m) R, u === t →
        (₄₊ m) ⊢ (Decoding.d m ʷ) u ≈ (Decoding.d m ʷ) t

------------------------------------------------------------------------
-- The induction

module Theorem
  (lemma-8-7 : ∀ m → Complete (₃₊ m) → D∘E m)
  (lemma-8-8 : ∀ m → Complete (₃₊ m) → DWD m)
  where

  complete : ∀ n → Complete n
  complete ₀      = complete₀
  complete ₁      = complete₁
  complete ₂      = complete₂
  complete ₃      = complete₃
  complete (₄₊ m) =
    Section8.Complete′.complete m (Decoding.d m)
      (lemma-8-8 m (complete (₃₊ m))) (lemma-8-7 m (complete (₃₊ m)))

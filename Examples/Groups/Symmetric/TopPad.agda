------------------------------------------------------------------------
-- Presentations of groups
--
-- Sₙ's rules on their own wires, padded by Circuit.TopPad, give the
-- same congruence as Syntactics' rules at every width, lifted by
-- Circuit.Base's Lift-Relation
--
-- An instance of Circuit.TopPad.Equivalence: Syntactics states order
-- and yang-baxter at every width (₂₊ n and ₃₊ n: the rule on the bottom
-- wires of any wider circuit), here they are stated on their own wires
-- only (2 and 3), and the two have the same rules — a rule at width
-- ₂₊ n is the rule on its own wires with n idle wires on top (order↓,
-- yang-baxter↓); a rule on its own wires is the rule at n = 0; and a
-- rule's words are closed, so ⇓'d it is the same rule one wire wider.
-- So the congruences coincide (lr⇒tp, tp⇒lr), and the identity is a
-- group isomorphism of the two word groups (lr≅tp).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.TopPad where

open import Data.Nat using (ℕ)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Word.Base using (WRel ; ε ; _•_)

import Circuit.TopPad
import Circuit.TopPad.Equivalence
import Presentation.Base as PB

open import Examples.Groups.Symmetric.Syntactics

open Circuit.TopPad Gate using (_⇓)

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The rules on their own wires, padded by Top-Pad

infix 4 _Base,_===_
data _Base,_===_ : (n : ℕ) → WRel (Gen n) where
  order₀       : 2 Base, σ • σ === ε
  yang-baxter₀ : 3 Base, σ • σ ↑ • σ === σ ↑ • σ • σ ↑

module TP = Circuit.TopPad.Top-Pad Gate _Base,_===_
module E  = Circuit.TopPad.Equivalence.Lift≅Top-Pad Gate _SRel,_===_ _Base,_===_

open E public using (_TRel,_===_ ; _⊢ᵀ_≈_ ; _⊢ᴸ_≈_)

-- Each rule on the bottom wires of every wider circuit: a closed word
-- one wire wider is the same word (σ ⇓ is σ).
order↓ : (₂₊ n) TRel, σ • σ === ε
order↓ {0}    = TP.srel order₀
order↓ {₁₊ n} = TP.cong↓ order↓

yang-baxter↓ : (₃₊ n) TRel, σ • σ ↑ • σ === σ ↑ • σ • σ ↑
yang-baxter↓ {0}    = TP.srel yang-baxter₀
yang-baxter↓ {₁₊ n} = TP.cong↓ yang-baxter↓

------------------------------------------------------------------------
-- The two have the same rules

same : E.SameRules
same = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
  where
  pad : n SRel, w === v → n ⊢ᵀ w ≈ v
  pad order       = PB.axiom order↓
  pad yang-baxter = PB.axiom yang-baxter↓

  unpad : n Base, w === v → n ⊢ᴸ w ≈ v
  unpad order₀       = PB.axiom (srel order)
  unpad yang-baxter₀ = PB.axiom (srel yang-baxter)

  srel-⇓ : n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
  srel-⇓ order       = PB.axiom (srel order)
  srel-⇓ yang-baxter = PB.axiom (srel yang-baxter)

------------------------------------------------------------------------
-- So the congruences coincide, and the identity is a group isomorphism

open E.Equivalent same public using (lr⇒tp ; tp⇒lr)
open E.Equivalent.Iso same grouplike public using (glᵀ ; lr≅tp)

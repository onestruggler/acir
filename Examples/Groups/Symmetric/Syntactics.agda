------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ: gate type, circuit generators, and the
-- group-specific relations (order and yang-baxter).
-- Syntactic framework only; no coset enumeration or normal form.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Syntactics where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Notations using (auto ; ₂₊ ; ₃₊ ; ₁₊)
open import Presentation.GroupLike using (Grouplike)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

import Circuit.Base
import Circuit.TopPad
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Gate type

-- The one generating gate of Sₙ: the transposition of two adjacent
-- wires.
data Gate : ℕ → Set where
  σ-gate : Gate 2

------------------------------------------------------------------------
-- Syntactic framework

private module SC = Circuit.Base Gate

-- gate₀ is exported so clients can discharge it: this gate set has no
-- 0-ary gate, so every gate₀ case is the absurd `gate₀ ()`.
open SC public
  using ( Gen ; gate₀ ; gate₁ ; gate₂ ; Circuit
        ; _↥ ; _↑ ; _↓ ; _↥ᵏ_ ; _↑ᵏ_ )

pattern σ-gen = gate₂ σ-gate

-- The transposition as a one-letter circuit.
σ : Word (Gen (₂₊ n))
σ = [ σ-gen ]ʷ

------------------------------------------------------------------------
-- Group-specific relations: order and braid only, each on its own
-- wires; no structural rules

infix 4 _SRel,_===_
data _SRel,_===_ : (n : ℕ) → WRel (Gen n) where
  order       : 2 SRel, σ • σ === ε
  yang-baxter : 3 SRel, σ • σ ↑ • σ === σ ↑ • σ • σ ↑

------------------------------------------------------------------------
-- Full relation via Top-Pad: each rule closed under an idle wire on
-- top (cong↓), and the structural rules cong↑, comm₁, comm₂ on top of
-- that

private module LR = Circuit.TopPad.Top-Pad Gate _SRel,_===_
-- ω↑=ω is the 0-ary gate's structural rule.  This gate set has no
-- 0-ary gate, so it is never inhabited here — but it still has to be
-- re-exported, or a client cannot name it to discharge it when it
-- cases on the relation.
open LR public
  using ( base ; cong↓ ; srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω ; lemma-cong↑
        ; comm-gate₂-w↑↑ ; _TopPad,_===_ ; _VRel,_===_
        ; Padded ; padded ; padded₂ ; padded₃ ; top-view )

-- Each rule on the bottom wires of every wider circuit: a closed word
-- one wire wider is the same word (σ ⇓ is σ).
order↓ : (₂₊ n) TopPad, σ • σ === ε
order↓ {0}     = base order
order↓ {₁₊ n}  = cong↓ order↓

yang-baxter↓ : (₃₊ n) TopPad, σ • σ ↑ • σ === σ ↑ • σ • σ ↑
yang-baxter↓ {0}     = base yang-baxter
yang-baxter↓ {₁₊ n}  = cong↓ yang-baxter↓

------------------------------------------------------------------------
-- Grouplike (each generator has a two-sided inverse)

grouplike : Grouplike (_VRel,_===_ n)
grouplike {₂₊ k} (gate₂ σ-gate) = σ , PB.axiom (srel order↓)
grouplike {₁₊ n} (g ↥) with grouplike {n} g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf

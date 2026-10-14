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
open import Relation.Nullary using (¬_)
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
-- Full relation via Top-Pad: the rules, closed under an idle wire on
-- top (cong↓) and under the structural rules cong↑, comm₁, comm₂ — one
-- relation

private module LR = Circuit.TopPad.Top-Pad Gate _SRel,_===_
-- ω↑=ω is the 0-ary gate's structural rule.  This gate set has no
-- 0-ary gate, so it is never inhabited here — but it still has to be
-- re-exported, or a client cannot name it to discharge it when it
-- cases on the relation.
open LR public
  using ( srel ; cong↓ ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω ; lemma-cong↑
        ; lemma-cong↓ ; comm-gate₂-w↑↑ ; _VRel,_===_ )
open Circuit.TopPad Gate public
  using ( _↧ ; _⇓ ; ↑⇓ ; TopWire ; below ; top ; top-wire )

-- Each rule on the bottom wires of every wider circuit: a closed word
-- one wire wider is the same word (σ ⇓ is σ).
order↓ : (₂₊ n) VRel, σ • σ === ε
order↓ {0}     = srel order
order↓ {₁₊ n}  = cong↓ order↓

yang-baxter↓ : (₃₊ n) VRel, σ • σ ↑ • σ === σ ↑ • σ • σ ↑
yang-baxter↓ {0}     = srel yang-baxter
yang-baxter↓ {₁₊ n}  = cong↓ yang-baxter↓

-- No rule holds on fewer than two wires.
no-rel₀ : {w v : Circuit 0} → ¬ (0 VRel, w === v)
no-rel₀ (srel ())

no-rel₁ : {w v : Circuit 1} → ¬ (1 VRel, w === v)
no-rel₁ (srel ())
no-rel₁ (cong↓ x)   = no-rel₀ x
no-rel₁ (cong↑ x)   = no-rel₀ x
no-rel₁ (comm₁ () _)
no-rel₁ (ω↑=ω ())

------------------------------------------------------------------------
-- Grouplike (each generator has a two-sided inverse)

grouplike : Grouplike (_VRel,_===_ n)
grouplike {₂₊ k} (gate₂ σ-gate) = σ , PB.axiom order↓
grouplike {₁₊ n} (g ↥) with grouplike {n} g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf

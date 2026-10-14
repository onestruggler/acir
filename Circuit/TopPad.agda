------------------------------------------------------------------------
-- Presentations of groups
--
-- Relations stated on exact widths, closed under idle wires on top
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; _≤_ ; z≤n ; s≤s)

module Circuit.TopPad (Gate : ℕ → Set) where

open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base
open import Circuit.Base Gate

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- One idle wire on top
--
-- The dual of _↥ and _↑, which put one below.  A gate keeps its wires
-- and only the width grows, so a closed word, ⇓'d, is the same word
-- read one wire wider (σ ⇓ is σ).

infixl 8 _↧
_↧ : Gen n → Gen (₁₊ n)
gate₀ h ↧ = gate₀ h
gate₁ h ↧ = gate₁ h
gate₂ h ↧ = gate₂ h
gate₃ h ↧ = gate₃ h
(g ↥)   ↧ = (g ↧) ↥

_⇓ : Circuit n → Circuit (₁₊ n)
w ⇓ = wmap _↧ w

------------------------------------------------------------------------
-- A generator, and a circuit, on the bottom m of n ≥ m wires

infixl 8 _↧≤_
_↧≤_ : {m : ℕ} → Gen m → m ≤ n → Gen n
gate₀ h ↧≤ p                     = gate₀ h
gate₁ h ↧≤ s≤s p                 = gate₁ h
gate₂ h ↧≤ s≤s (s≤s p)           = gate₂ h
gate₃ h ↧≤ s≤s (s≤s (s≤s p))     = gate₃ h
(g ↥)   ↧≤ s≤s p                 = (g ↧≤ p) ↥

infixl 7 _↓≤_
_↓≤_ : {m : ℕ} → Circuit m → m ≤ n → Circuit n
w ↓≤ p = wmap (_↧≤ p) w

private
  -- One more idle wire on top of a witness.
  _⁺ : {m : ℕ} → m ≤ n → m ≤ ₁₊ n
  z≤n   ⁺ = z≤n
  s≤s p ⁺ = s≤s (p ⁺)

  ↧≤-refl : (g : Gen n) → g ↧≤ ≤-refl ≡ g
  ↧≤-refl (gate₀ h) = Eq.refl
  ↧≤-refl (gate₁ h) = Eq.refl
  ↧≤-refl (gate₂ h) = Eq.refl
  ↧≤-refl (gate₃ h) = Eq.refl
  ↧≤-refl (g ↥)     = Eq.cong _↥ (↧≤-refl g)

  ↧-↧≤ : {m : ℕ} (g : Gen m) (p : m ≤ n) → g ↧≤ (p ⁺) ≡ (g ↧≤ p) ↧
  ↧-↧≤ (gate₀ h) p                     = Eq.refl
  ↧-↧≤ (gate₁ h) (s≤s p)               = Eq.refl
  ↧-↧≤ (gate₂ h) (s≤s (s≤s p))         = Eq.refl
  ↧-↧≤ (gate₃ h) (s≤s (s≤s (s≤s p)))   = Eq.refl
  ↧-↧≤ (g ↥)     (s≤s p)               = Eq.cong _↥ (↧-↧≤ g p)

  ↓≤-refl : (w : Circuit n) → w ↓≤ ≤-refl ≡ w
  ↓≤-refl [ g ]ʷ  = Eq.cong [_]ʷ (↧≤-refl g)
  ↓≤-refl ε       = Eq.refl
  ↓≤-refl (u • t) = Eq.cong₂ _•_ (↓≤-refl u) (↓≤-refl t)

  ⇓-↓≤ : {m : ℕ} (w : Circuit m) (p : m ≤ n) → w ↓≤ (p ⁺) ≡ (w ↓≤ p) ⇓
  ⇓-↓≤ [ g ]ʷ  p = Eq.cong [_]ʷ (↧-↧≤ g p)
  ⇓-↓≤ ε       p = Eq.refl
  ⇓-↓≤ (u • t) p = Eq.cong₂ _•_ (⇓-↓≤ u p) (⇓-↓≤ t p)

------------------------------------------------------------------------
-- Top-Pad
--
-- A relation on exact widths: each rule between circuits on its own
-- wires, n Base, w === v, with no parameter for wider circuits.
-- _TopPad,_===_ closes it under one more idle wire on top (cong↓, the
-- dual of Lift-Relation's cong↑, which puts one below), so that a rule
-- holds on the bottom wires of every wider circuit, and Lift-Relation
-- over _TopPad,_===_ adds the structural rules.  Since a closed word,
-- ⇓'d, is the same word one wire wider, the rule
-- 3 Base, σ • σ ↑ • σ === σ ↑ • σ • σ ↑ gives, by recursion on k,
-- (₃₊ k) TopPad, σ • σ ↑ • σ === σ ↑ • σ • σ ↑.
--
-- An instance at a width like ₂₊ n is cong↓ applied an unknown number
-- of times, so a function at that width cannot match on it directly.
-- top-view reads it as a rule on the bottom wires (Padded): the rule
-- and a witness p : m ≤ n, whose constructors fix the width (padded₀ …
-- padded₄) — match on top-view x.
--
-- Usage: state the group-specific relation on exact widths and open
-- Top-Pad in place of Lift-Relation.

module Top-Pad (_Base,_===_ : (n : ℕ) → CRel n) where

  infix 4 _TopPad,_===_
  data _TopPad,_===_ : (n : ℕ) → CRel n where
    base  : n Base, w === v → n TopPad, w === v
    cong↓ : n TopPad, w === v → (₁₊ n) TopPad, w ⇓ === v ⇓

  open Lift-Relation _TopPad,_===_ public

  -- An instance read as a rule on the bottom m of the n wires.
  data Padded : (n : ℕ) → CRel n where
    padded : {m : ℕ} {w v : Circuit m} (p : m ≤ n) → m Base, w === v →
             Padded n (w ↓≤ p) (v ↓≤ p)

  pattern padded₀ r = padded z≤n r
  pattern padded₁ r = padded (s≤s z≤n) r
  pattern padded₂ r = padded (s≤s (s≤s z≤n)) r
  pattern padded₃ r = padded (s≤s (s≤s (s≤s z≤n))) r
  pattern padded₄ r = padded (s≤s (s≤s (s≤s (s≤s z≤n)))) r

  top-view : n TopPad, w === v → Padded n w v
  top-view (base {w = w} {v} r) =
    Eq.subst₂ (Padded _) (↓≤-refl w) (↓≤-refl v) (padded ≤-refl r)
  top-view (cong↓ x) = up (top-view x)
    where
      up : Padded n w v → Padded (₁₊ n) (w ⇓) (v ⇓)
      up (padded {w = w} {v} p r) =
        Eq.subst₂ (Padded _) (⇓-↓≤ w p) (⇓-↓≤ v p) (padded (p ⁺) r)

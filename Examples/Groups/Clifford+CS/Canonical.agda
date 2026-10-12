------------------------------------------------------------------------
-- Presentations of groups
--
-- Canonical spellings of the scalar
--
-- The scalar iI is a 0-ary gate, available at every width, but shifting
-- a circuit relabels it: (iI) ↑ is the letter (I-gen ↥), a different
-- letter that the structural rule ω↑=ω identifies with iI.  A rule
-- lifted by cong↑ therefore mentions the shifted spelling wherever the
-- rule mentions iI, while a word written at the higher width directly
-- mentions iI.
--
-- `can` replaces every shifted spelling of the scalar by the scalar,
-- letter by letter, and `can-≈` says that changes nothing in the theory.
-- So an equation between canonical words follows from one between any
-- spellings of them (`via-can`), which is how lifted rules are used at
-- the higher width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Canonical where

open import Data.Nat using (ℕ)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
open import Notations using (₁₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The canonical spelling of a generator

-- Shift a generator up one wire, except that the scalar stays the
-- scalar.
up : Gen n → Gen (₁₊ n)
up (gate₀ h) = gate₀ h
up g         = g ↥

canG : Gen n → Gen n
canG (g ↥) = up (canG g)
canG g     = g

can : Circuit n → Circuit n
can = wmap canG

------------------------------------------------------------------------
-- It changes nothing

private
  up-≈ : (g : Gen n) → (₁₊ n) ⊢ [ g ↥ ]ʷ ≈ [ up g ]ʷ
  up-≈ (gate₀ h) = PB.axiom (ω↑=ω h)
  up-≈ (gate₁ h) = PB.refl
  up-≈ (gate₂ h) = PB.refl
  up-≈ (g ↥)     = PB.refl

canG-≈ : (g : Gen n) → n ⊢ [ g ]ʷ ≈ [ canG g ]ʷ
canG-≈ (gate₀ h) = PB.refl
canG-≈ (gate₁ h) = PB.refl
canG-≈ (gate₂ h) = PB.refl
canG-≈ (g ↥)     = PB.trans (lemma-cong↑ [ g ]ʷ [ canG g ]ʷ (canG-≈ g)) (up-≈ (canG g))

can-≈ : (w : Circuit n) → n ⊢ w ≈ can w
can-≈ [ g ]ʷ  = canG-≈ g
can-≈ ε       = PB.refl
can-≈ (w • v) = PB.cong (can-≈ w) (can-≈ v)

-- An equation between any spellings is one between canonical ones.
via-can : {w v : Circuit n} → n ⊢ w ≈ v → n ⊢ can w ≈ can v
via-can {w = w} {v} e = PB.trans (PB.sym (can-≈ w)) (PB.trans e (can-≈ v))

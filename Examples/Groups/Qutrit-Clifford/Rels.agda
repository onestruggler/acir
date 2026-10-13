------------------------------------------------------------------------
-- Presentations of groups
--
-- The box relations available on n wires
--
-- Normalisation on n wires uses the box relations on at most n qutrits
-- only.  The supplement's proof is an induction on that number: the
-- relations on two qutrits are derived given completeness on one, and
-- those on three given completeness on two.  So the pushes and the
-- normalisation take their relations as an argument of type Rels n,
-- and Rels 1 does not mention the relations on two or three qutrits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Rels where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_)
open import Data.Unit.Base using (⊤ ; tt)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Qutrit-Clifford.Tables
  using (BoxRelations₁ ; BoxRelations₂ ; BoxRelations₃)

private
  variable
    m : ℕ

Rels : ℕ → Set
Rels 0         = ⊤
Rels 1         = BoxRelations₁
Rels 2         = BoxRelations₁ × BoxRelations₂
Rels (₃₊ _)    = BoxRelations₁ × BoxRelations₂ × BoxRelations₃

-- The relations on one wire fewer.
down : Rels (₁₊ m) → Rels m
down {0}       _                = tt
down {1}       (r₁ , _)         = r₁
down {2}       (r₁ , r₂ , _)    = r₁ , r₂
down {₃₊ _}    rs               = rs

-- The relations of each size, where they are available.
rel₁ : Rels (₁₊ m) → BoxRelations₁
rel₁ {0}    r₁            = r₁
rel₁ {1}    (r₁ , _)      = r₁
rel₁ {₂₊ _} (r₁ , _ , _)  = r₁

rel₂ : Rels (₂₊ m) → BoxRelations₂
rel₂ {0}    (_ , r₂)      = r₂
rel₂ {₁₊ _} (_ , r₂ , _)  = r₂

rel₃ : Rels (₃₊ m) → BoxRelations₃
rel₃ (_ , _ , r₃) = r₃

-- All of them make relations on every number of wires.
rels : BoxRelations₁ → BoxRelations₂ → BoxRelations₃ → (n : ℕ) → Rels n
rels r₁ r₂ r₃ 0        = tt
rels r₁ r₂ r₃ 1        = r₁
rels r₁ r₂ r₃ 2        = r₁ , r₂
rels r₁ r₂ r₃ (₃₊ _)   = r₁ , r₂ , r₃

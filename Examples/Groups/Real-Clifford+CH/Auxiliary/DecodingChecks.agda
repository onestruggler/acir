------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding of Definition 8.3 on three qubits: checks that a decoded
-- letter has the matrix of the letter
--
-- D(p) is a circuit of multi-controlled gates read off the Gray codes
-- of the indices of p (Decoding, MultiControlled).  Here its stored
-- matrix is compared with that of p: for every sign pair and every
-- signed exchange on eight indices (`zz-all`, and `zx-all₀` … `zx-all₇`
-- by the index of the sign, each in a module of its own,
-- DecodingChecks.ZX0 … ZX7), and on samples of the exchange pairs and
-- of the Hadamard pairs, on and off the H-pattern and with repeated
-- indices.  The circuit is read by row operations and compared by one
-- boolean (DecodingChecks.Base: Evaluation, Semantics.Decide); read as
-- a dense product and compared by `mat-dec`, as this module first did,
-- a decoded letter cost about 1.27ⁿ in its n gates and only the five
-- letters under 43 gates were within reach, where a Hadamard pair off
-- the H-pattern has some 1800.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks where

open import Data.Bool using (true)
open import Data.Bool.ListAction using (all)
open import Data.List using (allFin)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; xx ; hh)
open import Examples.Groups.Real-Clifford+CH.Decoding using () renaming (d to D)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.Base
  using (⟦_⟧Y ; decideD-sound ; check)

------------------------------------------------------------------------
-- The letters checked
--
-- The Gray codes of 0 … 7, top wire first: 000, 001, 011, 010, 110,
-- 111, 101, 100.

-- Every sign pair (−1)_[a] (−1)_[b]: boxes on every wire, and chains of
-- up to seven of them.
zz-all : all (λ a → all (λ b → check (zz a b)) (allFin 8)) (allFin 8) ≡ true
zz-all = Eq.refl

-- Every signed exchange (−1)_[c] X_[a,b]: on its own pair, in either
-- order of the pair, and with the sign elsewhere.
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX0 public using (zx-all₀)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX1 public using (zx-all₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX2 public using (zx-all₂)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX3 public using (zx-all₃)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX4 public using (zx-all₄)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX5 public using (zx-all₅)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX6 public using (zx-all₆)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DecodingChecks.ZX7 public using (zx-all₇)

-- Exchange pairs X_[a,b] X_[c,d].
xx-0123 : check (xx ₀ ₁ ₂ ₃) ≡ true
xx-0123 = Eq.refl

xx-0725 : check (xx ₀ ₇ ₂ ₅) ≡ true
xx-0725 = Eq.refl

xx-6134 : check (xx ₆ ₁ ₃ ₄) ≡ true
xx-6134 = Eq.refl

-- Hadamard pairs of the H-pattern: the all-white gate, a black
-- control, and the other order of the two varying wires.
hh-0132 : check (hh ₀ ₁ ₃ ₂) ≡ true
hh-0132 = Eq.refl

hh-7645 : check (hh ₇ ₆ ₄ ₅) ≡ true
hh-7645 = Eq.refl

hh-0312 : check (hh ₀ ₃ ₁ ₂) ≡ true
hh-0312 = Eq.refl

-- Off the H-pattern: Definition E.1's words around the gadget.
hh-0246 : check (hh ₀ ₂ ₄ ₆) ≡ true
hh-0246 = Eq.refl

hh-1527 : check (hh ₁ ₅ ₂ ₇) ≡ true
hh-1527 = Eq.refl

-- Repeated indices: the pair is split over two fresh ones.
hh-0102 : check (hh ₀ ₁ ₀ ₂) ≡ true
hh-0102 = Eq.refl

-- As statements about the semantics.
D-zz-01 : ⟦ (D ʷ) (zz ₀ ₁) ⟧ ~ ⟦ zz ₀ ₁ ⟧Y
D-zz-01 = decideD-sound ((D ʷ) (zz ₀ ₁)) (zz ₀ ₁) Eq.refl

D-hh-0132 : ⟦ (D ʷ) (hh ₀ ₁ ₃ ₂) ⟧ ~ ⟦ hh ₀ ₁ ₃ ₂ ⟧Y
D-hh-0132 = decideD-sound ((D ʷ) (hh ₀ ₁ ₃ ₂)) (hh ₀ ₁ ₃ ₂) hh-0132

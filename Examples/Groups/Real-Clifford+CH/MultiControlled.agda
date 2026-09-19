------------------------------------------------------------------------
-- Presentations of groups
--
-- Multi-controlled gates with parametrised controls anywhere on the
-- wires (Clément, Definition 2.4 and Section 2.2)
--
-- Definition 2.4 gives the k-controlled box, ZX, XZ and H gates with
-- their controls on the top wires and the target at the bottom
-- (Syntactics' Λ□, ΛZX, ΛXZ, and ΛH here).  The paper then places
-- them anywhere by conjugating with swaps — "the permutation that
-- preserves the vertical order of the controls" — and negates a
-- control by conjugating its wire with X; a control parametrised by a
-- bit is black for 1 and white for 0.
--
-- Here a gate is described by a LAYOUT: one slot per wire, either a
-- parametrised control or a target.  The circuit is the base gate
-- conjugated by the network that cycles the target wire(s) down to
-- the bottom, and by X on the wires of the white controls.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.MultiControlled where

open import Data.Bool using (Bool ; true ; false ; if_then_else_ ; _∧_ ; not)
open import Data.Nat using (ℕ ; zero ; suc ; _<ᵇ_)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Gates at a wire, by the wire's number

-- X on wire i (ε when there is no such wire).
Xat : ℕ → Circuit n
Xat {₁₊ n} zero    = X
Xat {₁₊ n} (suc i) = Xat i ↑
Xat {₀}    _       = ε

-- The swap of wires i and i + 1 (ε when there are no such wires).
swapAt : ℕ → Circuit n
swapAt {₂₊ n} zero    = Ex
swapAt {₁₊ n} (suc i) = swapAt i ↑
swapAt {₀}    _       = ε
swapAt {₁}    zero    = ε

-- Moving wire t down to wire 0, the wires below it each up by one;
-- and back.
shiftDown shiftUp : ℕ → Circuit n
shiftDown zero    = ε
shiftDown (suc j) = swapAt j • shiftDown j
shiftUp zero    = ε
shiftUp (suc j) = shiftUp j • swapAt j

-- Moving wire u down to wire 1, and back (the same one wire up).
shiftDown₁ shiftUp₁ : ℕ → Circuit n
shiftDown₁ {₁₊ n} (suc u) = shiftDown u ↑
shiftDown₁ _              = ε
shiftUp₁ {₁₊ n} (suc u) = shiftUp u ↑
shiftUp₁ _              = ε

------------------------------------------------------------------------
-- The multi-controlled H (Definition 2.4)
--
-- ΛH k has k controls on wires 2 … k + 1, the H on wire 1 and the
-- dashed box on wire 0: with no control it is H; with one it is CH;
-- with two or more it is the (k + 1)-controlled box, the extra control
-- being wire 1, conjugated by P ⊗ P on wires 1 and 0.

ΛH : (k : ℕ) → Circuit (₂₊ k)
ΛH 0      = H ↑
ΛH 1      = CH ↑
ΛH (₂₊ k) = PP ↓ • Λ□ (₃₊ k) • PP ↓

------------------------------------------------------------------------
-- Layouts

data Slot : Set where
  ctrl : Bool → Slot     -- a control, black (true) or white (false)
  tgt  : Slot            -- the target wire, or the dashed box of an H gate
  tgtH : Slot            -- the H wire of an H gate

Layout : ℕ → Set
Layout n = Vec Slot n

-- The wire of the first slot satisfying a predicate, counting from
-- wire 0 (the width when there is none).
private
  find : (Slot → Bool) → Layout n → ℕ
  find p []       = zero
  find p (s ∷ L) = if p s then zero else suc (find p L)

  isTgt isTgtH : Slot → Bool
  isTgt tgt = true
  isTgt _   = false
  isTgtH tgtH = true
  isTgtH _    = false

-- The wires of the target and of the H.
tgtWire hWire₀ : Layout n → ℕ
tgtWire = find isTgt
hWire₀  = find isTgtH

-- X on every white control.
negs : Layout n → Circuit n
negs []             = ε
negs (ctrl false ∷ L) = X • negs L ↑
negs (_ ∷ L)          = negs L ↑

-- Conjugation by the placement network and the negations, for a gate
-- with one target: the target wire goes down to wire 0.
conj₁ : Layout n → Circuit n → Circuit n
conj₁ L g = negs L • shiftDown (tgtWire L) • g • shiftUp (tgtWire L) • negs L

-- With two targets: the box wire goes down to wire 0, then the H wire
-- (one higher than it was if it sat below the box) down to wire 1.
hWire : Layout n → ℕ
hWire L = let t = tgtWire L ; h = hWire₀ L in
          if h <ᵇ t then suc h else h

conj₂ : Layout n → Circuit n → Circuit n
conj₂ L g = negs L • shiftDown (tgtWire L) • shiftDown₁ (hWire L) • g •
            shiftUp₁ (hWire L) • shiftUp (tgtWire L) • negs L

------------------------------------------------------------------------
-- The gates: every wire is a control or a target, so the base gate
-- has exactly the width

-- The multi-controlled box, ZX and XZ (one target), on n + 1 wires.
mc□ mcZX mcXZ : Layout (₁₊ n) → Circuit (₁₊ n)
mc□  {n} L = conj₁ L (Λ□ n)
mcZX {n} L = conj₁ L (ΛZX n)
mcXZ {n} L = conj₁ L (ΛXZ n)

-- (−1)^β ZX and (−1)^β XZ, Definition 2.4's parametrised targets:
-- (−1)^β XZ is XZ for β = 0 and ZX for β = 1, and dually.
mc±XZ mc±ZX : Bool → Layout (₁₊ n) → Circuit (₁₊ n)
mc±XZ false L = mcXZ L
mc±XZ true  L = mcZX L
mc±ZX false L = mcZX L
mc±ZX true  L = mcXZ L

-- The multi-controlled H (an H wire and a box wire), on n + 2 wires.
mcH : Layout (₂₊ n) → Circuit (₂₊ n)
mcH {n} L = conj₂ L (ΛH n)

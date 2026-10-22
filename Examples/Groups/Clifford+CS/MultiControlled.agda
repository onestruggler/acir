------------------------------------------------------------------------
-- Presentations of groups
--
-- Multi-controlled gates for the decoding from four wires on
--
-- The letters of P′ decode to multi-controlled gates, and no
-- multi-controlled phase or K gate with every other wire controlling
-- is a circuit on its own (determinant i); the determinant-one
-- combinations the letters denote are, as split-control commutators
-- L_{C1 ∪ C2}([A, B]) = L_{C1}(A) L_{C2}(B) L_{C1}(A)⁻¹ L_{C2}(B)⁻¹
-- (scratchpad/dec.py, checked at n = 4 and 5):
--
--   * Clément's box Λ□ k, the k-controlled −1 with its box wire 0, by
--     his recursion W B V B through the Toffoli-like CCZX;
--   * the S-box and the K-box, L^m(S) and L^m(K) with two idle wires,
--     by borrowed-wire recursions: L^m(S) = Zbox · [L_{C1}X_A, L_{C2+A}S_T]
--     and L^m(K) = L_C(S_A)³ · [L_{C1}X_A, L_{C2+A}K_T], from the identity
--     [L_{C2+a}G_t, L_{C1}X_a] = L_C(G_t)⁻¹ · L_{C+a}(G²_t) at G = S, K;
--     each is defined in a fixed frame of its wires (below), its child
--     placed by one transposition at distance two, as Clément's τ₀₂;
--   * the three base gadgets, on target 0 with every other wire a black
--     control: the phase gadget L^{n−1}(iZ) = [Toff, L_{3..}(S_0)], the
--     rotation L^{n−1}(XZ) = [CK, box] and the hybrid gadget
--     L^{n−1}(X K X · diag(1, −i)) = [L_{1,2}(V²), L_{3..}(K_0)] with
--     V = S² K S, where L_{1,2}(V²) is Barenco's word of two-wire gates.
--
-- A gate is placed anywhere by a LAYOUT, as in Clément's Definition 2.4
-- (Real-Clifford+CH.MultiControlled): the target wire is cycled down to
-- wire 0 by swaps, a white control is conjugated by X, and the
-- orientation of the gate on its target is X on the target.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.MultiControlled where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₀ ; ₁ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- One more wire on top (Real-Clifford+CH.TopWeakening)

-- The same gate at the next width.
infixl 8 _↧
_↧ : Gen n → Gen (₁₊ n)
gate₀ h ↧ = gate₀ h
gate₁ h ↧ = gate₁ h
gate₂ h ↧ = gate₂ h
(g ↥)   ↧ = (g ↧) ↥

top : Circuit n → Circuit (₁₊ n)
top = wmap _↧

------------------------------------------------------------------------
-- Two-wire shortcuts

-- CZ, and the controlled K with its control on wire 0 (CK₀₁) or on wire
-- 1 (CK₁₀), Bian and Selinger's words (TwoQubit).
CZ CK₀₁ CK₁₀ : Circuit (₂₊ n)
CZ   = CS • CS
CK₀₁ = CK
CK₁₀ = CS • K • CS • K • CS • S ↑ • S ↑ • S ↑ • iI

------------------------------------------------------------------------
-- Three-wire gates, on wires 0, 1, 2

-- The Toffoli with its target on wire 2 (Toffᵗ; Toff, on wire 0, is
-- Syntactics'):
-- K on the target around Syntactics' CCZ.
Toffᵗ CCZX CCXZ : Circuit (₃₊ n)
Toffᵗ = K ↑ ↑ • CCZ • K ↑ ↑ • iI
CCZX  = CCZ • Toff
CCXZ  = Toff • CCZ

-- The transposition of wires 0 and 2, and conjugation by it.
τ₀₂ : Circuit (₃₊ n)
τ₀₂ = Swap • Swap ↑ • Swap

τ₀₂-conj : Circuit (₃₊ n) → Circuit (₃₊ n)
τ₀₂-conj w = τ₀₂ • w • τ₀₂

------------------------------------------------------------------------
-- The box (Clément, Definition 2.4)

-- Λ□ k is −1 when the wires 1 … k are set, wire 0 idle.
Λ□ : (k : ℕ) → Circuit (₁₊ k)
Λ□ 0      = iI • iI
Λ□ 1      = Z ↑
Λ□ 2      = CZ ↑
Λ□ (₃₊ k) = CCZX • τ₀₂-conj (Λ□ (₂₊ k) ↑) • CCXZ • τ₀₂-conj (Λ□ (₂₊ k) ↑)

------------------------------------------------------------------------
-- The rotation: XZ on wire 0 controlled by the wires 1 … k

-- [CK, B] with B the box on the wires 0, 2 … k and box wire 1, and
-- CK⁻¹ = S on the control times CK.
ΛXZ : (k : ℕ) → Circuit (₁₊ k)
ΛXZ 0      = X • Z
ΛXZ (₁₊ k) = CK₁₀ • B • S ↑ • CK₁₀ • B
  where B = Swap • Λ□ (₁₊ k) • Swap

------------------------------------------------------------------------
-- The S-box and the K-box
--
-- Frames, at width m + 3 (U the box wire of the Z-box, T the target, A
-- the borrowed wire, c the controls):
--
--   Sbox m   [U = 0, T = 1, c = 2 … m + 1, A = m + 2]
--   Kbox m   [U = 0, A = 1, c = 2 … m + 1, T = m + 2]
--
-- The S recursion acts at the top: the Toffoli on the wires m, m + 1
-- (its controls) and m + 2 (its target, the borrowed wire), and the
-- child one idle wire up, conjugated by the transposition of the wires
-- m and m + 2.  The K recursion acts at the bottom: the Toffoli on the
-- wires 2, 3 and 1, the child one wire up conjugated by the
-- transposition of the wires 1 and 3, and the correction L_C(S_A)³ is
-- the S-box in its own frame.  The inverses are defined alongside, so
-- that a word's size stays 2ᵐ.

-- The Toffoli with its target on top, and τ₀₂, on the top three wires.
topToff topτ : (m : ℕ) → Circuit (₃₊ m)
topToff zero    = Toffᵗ
topToff (suc m) = topToff m ↑
topτ zero    = τ₀₂
topτ (suc m) = topτ m ↑

Sbox Sbox⁻¹ : (m : ℕ) → Circuit (₃₊ m)
Sbox 0      = S ↑
Sbox 1      = CS ↑
Sbox (₂₊ j) =
  let Ch   = topτ (₂₊ j) • top (Sbox (₁₊ j)) • topτ (₂₊ j)
      Ch⁻¹ = topτ (₂₊ j) • top (Sbox⁻¹ (₁₊ j)) • topτ (₂₊ j)
  in Λ□ (₄₊ j) • topToff (₂₊ j) • Ch • topToff (₂₊ j) • Ch⁻¹
Sbox⁻¹ 0      = S ↑ • S ↑ • S ↑
Sbox⁻¹ 1      = CS ↑ • CS ↑ • CS ↑
Sbox⁻¹ (₂₊ j) =
  let Ch   = topτ (₂₊ j) • top (Sbox (₁₊ j)) • topτ (₂₊ j)
      Ch⁻¹ = topτ (₂₊ j) • top (Sbox⁻¹ (₁₊ j)) • topτ (₂₊ j)
  in Ch • topToff (₂₊ j) • Ch⁻¹ • topToff (₂₊ j) • Λ□ (₄₊ j)

Kbox Kbox⁻¹ : (m : ℕ) → Circuit (₃₊ m)
Kbox 0      = K ↑ ↑
Kbox 1      = CK₀₁ ↑ ↑
Kbox (₂₊ j) =
  let Ch   = τ₀₂ ↑ • Kbox (₁₊ j) ↑ • τ₀₂ ↑
      Ch⁻¹ = τ₀₂ ↑ • Kbox⁻¹ (₁₊ j) ↑ • τ₀₂ ↑
  in Sbox⁻¹ (₂₊ j) • Toff ↑ • Ch • Toff ↑ • Ch⁻¹
Kbox⁻¹ 0      = K ↑ ↑ • iI
Kbox⁻¹ 1      = (S • CK₀₁) ↑ ↑
Kbox⁻¹ (₂₊ j) =
  let Ch   = τ₀₂ ↑ • Kbox (₁₊ j) ↑ • τ₀₂ ↑
      Ch⁻¹ = τ₀₂ ↑ • Kbox⁻¹ (₁₊ j) ↑ • τ₀₂ ↑
  in Ch • Toff ↑ • Ch⁻¹ • Toff ↑ • Sbox (₂₊ j)

------------------------------------------------------------------------
-- Networks

-- The swap of wires i and i + 1 (ε when there are no such wires).
swapAt : ℕ → Circuit n
swapAt {₂₊ n} zero    = Swap
swapAt {₁₊ n} (suc i) = swapAt i ↑
swapAt {₀}    _       = ε
swapAt {₁}    zero    = ε

-- The cycle of the bottom k + 1 wires that carries wire 0 up to wire k,
-- the wires 1 … k each down one, and its inverse (Clément's cyc):
-- conjugating by cyc k … cyc⁻¹ k carries a gate's wires 0 … k − 1 up
-- one and its wire k down to 0.
cyc cyc⁻¹ : (k : ℕ) → Circuit (₁₊ k)
cyc zero      = ε
cyc (suc k)   = Swap • cyc k ↑
cyc⁻¹ zero    = ε
cyc⁻¹ (suc k) = cyc⁻¹ k ↑ • Swap

------------------------------------------------------------------------
-- The base gadgets, at width m + 3: target 0, controls 1 … m + 2

-- The controlled functor on one qubit (S ↦ CS, K ↦ CK, i ↦ S on the
-- control) at V = S² K S and V⁻¹ = S³ K⁻¹ S³ S³, the control on wire 1.
C₁₀V C₁₀V⁻¹ : Circuit (₂₊ n)
C₁₀V   = CS • CS • CK₁₀ • CS
C₁₀V⁻¹ = CS • CS • CS • CK₁₀ • S ↑ • CS • CS • CS • CS • CS • CS

-- Barenco's words for L_{1,2}(V²) and L_{1,2}(V⁻²):
-- C₁(V) CX₁₂ C₂(V⁻¹) CX₁₂ C₂(V), the wire-2 controls through the swap
-- of wires 1 and 2.
Bar Bar⁻¹ : Circuit (₃₊ n)
Bar   = C₁₀V • CX₁₂ • (Swap ↑ • C₁₀V⁻¹ • Swap ↑) • CX₁₂ • (Swap ↑ • C₁₀V • Swap ↑)
Bar⁻¹ = C₁₀V⁻¹ • CX₁₂ • (Swap ↑ • C₁₀V • Swap ↑) • CX₁₂ • (Swap ↑ • C₁₀V⁻¹ • Swap ↑)

-- The S-box re-framed to target 0, controls 3 … m + 2, idle wires 1, 2:
-- its frame [0, 1, 2 … m + 1, m + 2] goes to [1, 0, 3 … m + 2, 2], the
-- swap of wires 0, 1 and the cycle of the wires 2 … m + 2.
reS reS⁻¹ : (m : ℕ) → Circuit (₃₊ m)
reS   m = (Swap • cyc m ↑ ↑) • Sbox m • (cyc⁻¹ m ↑ ↑ • Swap)
reS⁻¹ m = (Swap • cyc m ↑ ↑) • Sbox⁻¹ m • (cyc⁻¹ m ↑ ↑ • Swap)

-- The K-box re-framed to target 0, controls 3 … m + 2, idle wires 1, 2:
-- its frame [0, 1, 2 … m + 1, m + 2] goes to [1, 2, 3 … m + 2, 0], the
-- cycle of all the wires.
reK reK⁻¹ : (m : ℕ) → Circuit (₃₊ m)
reK   m = cyc (₂₊ m) • Kbox m • cyc⁻¹ (₂₊ m)
reK⁻¹ m = cyc (₂₊ m) • Kbox⁻¹ m • cyc⁻¹ (₂₊ m)

-- The phase gadget L^{m+2}(iZ) (i at bit 0 of the target), the rotation
-- L^{m+2}(XZ), and the hybrid gadget L^{m+2}(X K X · diag(1, −i)).
G-pp G-rot G-ki : (m : ℕ) → Circuit (₃₊ m)
G-pp  m = Toff • reS m • Toff • reS⁻¹ m
G-rot m = ΛXZ (₂₊ m)
G-ki  m = Bar • reK m • Bar⁻¹ • reK⁻¹ m

------------------------------------------------------------------------
-- Layouts (Clément, Definition 2.4)

data Slot : Set where
  ctrl : Bool → Slot     -- a control, black (true) or white (false)
  tgt  : Slot            -- the target wire

Layout : ℕ → Set
Layout n = Vec Slot n

-- The wire of the target, counting from wire 0 (the width when there
-- is none).
tgtWire : Layout n → ℕ
tgtWire []           = zero
tgtWire (tgt ∷ L)    = zero
tgtWire (ctrl _ ∷ L) = suc (tgtWire L)

-- X on every white control.
negs : Layout n → Circuit n
negs []               = ε
negs (ctrl false ∷ L) = X • negs L ↑
negs (_ ∷ L)          = negs L ↑

-- Moving wire t down to wire 0, the wires below it each up by one; and
-- back.
shiftDown shiftUp : ℕ → Circuit n
shiftDown zero    = ε
shiftDown (suc j) = swapAt j • shiftDown j
shiftUp zero    = ε
shiftUp (suc j) = shiftUp j • swapAt j

-- A gate with target 0 placed by a layout: the target wire goes down to
-- wire 0, the white controls are conjugated by X.
conj₁ : Layout n → Circuit n → Circuit n
conj₁ L g = negs L • shiftDown (tgtWire L) • g • shiftUp (tgtWire L) • negs L

-- With its orientation: X on the target when the bit is set.
mc : Bool → Layout (₁₊ n) → Circuit (₁₊ n) → Circuit (₁₊ n)
mc false L g = conj₁ L g
mc true  L g = conj₁ L (X • g • X)

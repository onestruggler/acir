------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled functor: a circuit on n ≥ 4 wires under a control on
-- a new top wire
--
-- The completeness proof from five wires on (the joint paper's
-- stability theorem, scratchpad/five-qubit-plan.md) compares circuits
-- on n wires with their controlled versions on n + 1, letter by letter:
--
--     λ¹(i) = S_t,  λ¹(S_v) = CS(v, t),  λ¹(K_v) = CK(t → v),
--     λ¹(CS(x, y)) = Σ(x; t, y | u, A),
--
-- t the new top wire and Σ the doubly controlled S with two borrowed
-- wires u, A of the circuit (the joint paper's Definition 2.x): the
-- box Λ(−I; u) on the wires x, t, y, A times the commutator
-- [Toff(A; t, y), CS(x, A)].  λ⁰ is λ¹ with the control white, X on
-- the top wire around each letter.  Every letter acts on its own wires
-- and t, so a gate one wire up has its image one wire up:
-- λ¹(g ↥) = λ¹(g) ↑.  A gate on the bottom wires has its control
-- carried up by `stretch` — the control of a circuit is its top wire,
-- and stretching inserts an idle wire just below it, by `top` and the
-- exchange of the top two wires — and the borrowed wires of a CS on the
-- wires 0, 1 are 2, 3.  A CS near the top of a four-wire domain borrows
-- from below: on the wires 1, 2 it borrows 0, 3, on 2, 3 it borrows
-- 0, 1.  The three S-boxes are the joint paper's spellings
-- (Five.Letters: Sb u-x-ty-A), so that the five-wire derivations speak
-- of the same words.
--
-- Semantics (Lambda.Semantics): ⟦ λ¹ʷ w ⟧ is ⟦ w ⟧ controlled by the
-- top wire, and ⟦ λ⁰ʷ w ⟧ the same with the control white.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Lambda where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; CK₁₀)
open import Examples.Groups.Clifford+CS.Five.Letters
  using (b-Sb2-0-41-3 ; b-Sb0-1-42-3 ; b-Sb0-2-43-1)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Gates at the top

-- S and X on the top wire.
Sᵗ Xᵗ : (k : ℕ) → Circuit (₁₊ k)
Sᵗ zero    = S
Sᵗ (suc k) = Sᵗ k ↑
Xᵗ zero    = X
Xᵗ (suc k) = Xᵗ k ↑

-- The exchange of the top two wires.
Swᵗ : (k : ℕ) → Circuit (₂₊ k)
Swᵗ zero    = Swap
Swᵗ (suc k) = Swᵗ k ↑

-- An idle wire inserted just below the top wire.
stretch : Circuit (₂₊ k) → Circuit (₃₊ k)
stretch {k} c = Swᵗ (suc k) • top c • Swᵗ (suc k)

------------------------------------------------------------------------
-- The letters on the bottom wires

-- CS of wire 0 and the top wire, and K on wire 0 controlled by the top
-- wire.
CSᵗ CKᵗ : (k : ℕ) → Circuit (₂₊ k)
CSᵗ zero    = CS
CSᵗ (suc k) = stretch (CSᵗ k)
CKᵗ zero    = CK₁₀
CKᵗ (suc k) = stretch (CKᵗ k)

-- Σ(0; t, 1 | 2, 3): CS of the wires 0, 1 controlled by the top wire t,
-- borrowing the wires 2 and 3.
Σᵗ : (k : ℕ) → Circuit (suc (₄₊ k))
Σᵗ zero    = b-Sb2-0-41-3
Σᵗ (suc k) = stretch (Σᵗ k)

------------------------------------------------------------------------
-- The functor on generators

-- A four-wire domain, the generators above wire 0: on the wires 1, 2 the
-- CS borrows 0 and 3, on the wires 2, 3 it borrows 0 and 1.
private
  λ₁ : Gen 1 → Circuit 5
  λ₁ I-gen        = Sᵗ ₄
  λ₁ S-gen        = CSᵗ ₀ ↑ ↑ ↑
  λ₁ K-gen        = CKᵗ ₀ ↑ ↑ ↑
  λ₁ (I-gen ↥)    = Sᵗ ₄

  λ₂ : Gen 2 → Circuit 5
  λ₂ I-gen  = Sᵗ ₄
  λ₂ S-gen  = CSᵗ ₁ ↑ ↑
  λ₂ K-gen  = CKᵗ ₁ ↑ ↑
  λ₂ CS-gen = b-Sb0-2-43-1
  λ₂ (g ↥)  = λ₁ g

  λ₃ : Gen 3 → Circuit 5
  λ₃ I-gen  = Sᵗ ₄
  λ₃ S-gen  = CSᵗ ₂ ↑
  λ₃ K-gen  = CKᵗ ₂ ↑
  λ₃ CS-gen = b-Sb0-1-42-3
  λ₃ (g ↥)  = λ₂ g

λ¹ : Gen (₄₊ n) → Circuit (suc (₄₊ n))
λ¹ {n}     I-gen  = Sᵗ (₄₊ n)
λ¹ {n}     S-gen  = CSᵗ (₃₊ n)
λ¹ {n}     K-gen  = CKᵗ (₃₊ n)
λ¹ {n}     CS-gen = Σᵗ n
λ¹ {suc n} (g ↥)  = λ¹ g ↑
λ¹ {zero}  (g ↥)  = λ₃ g

-- The same with the control white.
λ⁰ : Gen (₄₊ n) → Circuit (suc (₄₊ n))
λ⁰ {n} g = Xᵗ (₄₊ n) • λ¹ g • Xᵗ (₄₊ n)

------------------------------------------------------------------------
-- On circuits, letter by letter

λ¹ʷ λ⁰ʷ : Circuit (₄₊ n) → Circuit (suc (₄₊ n))
λ¹ʷ = λ¹ ʷ
λ⁰ʷ = λ⁰ ʷ

-- The iterates: k controls on the k top wires, the innermost lowest.
λ¹ᵏ : (k : ℕ) → Circuit (₄₊ n) → Circuit (₄₊ (k +ℕ n))
λ¹ᵏ zero    w = w
λ¹ᵏ (suc k) w = λ¹ʷ (λ¹ᵏ k w)

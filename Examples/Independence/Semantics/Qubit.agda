------------------------------------------------------------------------
-- Presentations of groups
--
-- The qubit gates of Section 3.1, as scaled matrices over ℤ[ω]
--
-- ℤ[ω] is ℤ[x]/(x⁴ + 1), ω = x = e^{iπ/4}; √2 = ω − ω³, so a gate's
-- matrix is (√2)^{−h} M with M over ℤ[ω].  The gates of the common
-- signature Σ(2): the scalars ω and −1, H, Z, S, T, X, CNOT (control on
-- wire 1, target on wire 0) and CS, and the swap.  A matrix is indexed
-- by (output , input) basis vectors, wire 0 first.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Semantics.Qubit where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

import Examples.Independence.Semantics.Quartic as Quartic
import Examples.Independence.Semantics.Circuits

------------------------------------------------------------------------
-- ℤ[ω]

module ZΩ = Quartic (+ 0) (-[1+ 0 ])

√2 : ZΩ.Q
√2 = ZΩ.⟨ + 0 , + 1 , + 0 , -[1+ 0 ] ⟩

√2-cancel : ∀ {a b} → √2 ZΩ.* a ≡ √2 ZΩ.* b → a ≡ b
√2-cancel = ZΩ.cancel √2 (+ 2) refl

ω⁸≡1 : ZΩ._^_ ZΩ.x 8 ≡ ZΩ.1q
ω⁸≡1 = refl

open import Examples.Independence.Semantics.Scaled 2 (+ 0) (-[1+ 0 ]) √2 √2-cancel 7 ω⁸≡1 public

-- The semantics of circuits over a qubit gate set, from its valuation.
module Circuits {Gate : ℕ → Set} =
  Examples.Independence.Semantics.Circuits 2 (+ 0) (-[1+ 0 ]) √2 √2-cancel 7 ω⁸≡1 {Gate}

------------------------------------------------------------------------
-- The gates

private
  -- 1 if the two bits agree, 0 otherwise.
  δ : Fin 2 → Fin 2 → Q
  δ = δ₁

  xor : Fin 2 → Fin 2 → Fin 2
  xor zero    b    = b
  xor (suc zero) zero       = suc zero
  xor (suc zero) (suc zero) = zero

  and : Fin 2 → Fin 2 → Fin 2
  and zero _ = zero
  and (suc zero) b = b

  one : Fin 2
  one = suc zero

-- ω^{k b} on the bit b.
phase : ℕ → Fin 2 → Q
phase k zero       = 1#
phase k (suc zero) = x ^ k

-- A diagonal one-qubit gate, from its phase on |1⟩.
diag₁ : Q → Mat 1
diag₁ c = matOf λ { (a ∷ []) (b ∷ []) → δ a b * dg a }
  where
  dg : Fin 2 → Q
  dg zero       = 1#
  dg (suc zero) = c

ωᵍ −1ᵍ : Sc 0
ωᵍ  = 0 , mat x
−1ᵍ = 0 , mat (- 1#)

Hᵍ Zᵍ Sᵍ Tᵍ Xᵍ : Sc 1
Hᵍ  = 1 , matOf λ { (a ∷ []) (b ∷ []) → h a b }
  where
  h : Fin 2 → Fin 2 → Q
  h (suc zero) (suc zero) = - 1#
  h _          _          = 1#
Zᵍ  = 0 , diag₁ (- 1#)
Sᵍ  = 0 , diag₁ (x ^ 2)
Tᵍ  = 0 , diag₁ x
Xᵍ  = 0 , matOf λ { (a ∷ []) (b ∷ []) → δ a (xor b one) }

-- CNOT |b₀ , b₁⟩ ↦ |b₀ ⊕ b₁ , b₁⟩, CS = diag(1, 1, 1, i), and the swap.
CXᵍ CSᵍ SWᵍ : Sc 2
CXᵍ = 0 , matOf λ { (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []) → δ a₁ b₁ * δ a₀ (xor b₀ b₁) }
CSᵍ = 0 , matOf λ { (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []) →
                      (δ a₀ b₀ * δ a₁ b₁) * phase 2 (and b₀ b₁) }
SWᵍ = 0 , matOf swapₒ

-- The swap reads as the swap, which is all the swap rules need
-- (Circuits' Symmetry).
SWᵍ-ok : ix (proj₂ SWᵍ) ≐ swapₒ
SWᵍ-ok = ix-matOf swapₒ

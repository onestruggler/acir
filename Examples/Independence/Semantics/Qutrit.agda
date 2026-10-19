------------------------------------------------------------------------
-- Presentations of groups
--
-- The qutrit gates of Section 3.2, as scaled matrices over ℤ[ζ]
--
-- ℤ[ζ] is ℤ[x]/(x⁴ − x² + 1), ζ = x = e^{iπ/6}, so ω₃ = e^{2πi/3} is
-- ζ⁴; √3 = 2ζ − ζ³, so a gate's matrix is (√3)^{−h} M with M over
-- ℤ[ζ].  The gates: the scalar ω₁₂ = ζ, H|x⟩ = Σₖ ω₃^{xk}|k⟩/√3,
-- S|x⟩ = e^{iπ x(x−1)/3}|x⟩ = diag(1, 1, ω₃), the qutrit CNOT
-- |b₀ , b₁⟩ ↦ |b₀ + b₁ , b₁⟩ (control on wire 1) and the swap.  A
-- matrix is indexed by (output , input) basis vectors, wire 0 first.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Independence.Semantics.Qutrit where

open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

import Examples.Independence.Semantics.Quartic as Quartic
import Examples.Independence.Semantics.Circuits

------------------------------------------------------------------------
-- ℤ[ζ]

module Zζ = Quartic (+ 1) (-[1+ 0 ])

√3 : Zζ.Q
√3 = Zζ.⟨ + 0 , + 2 , + 0 , -[1+ 0 ] ⟩

√3-cancel : ∀ {a b} → √3 Zζ.* a ≡ √3 Zζ.* b → a ≡ b
√3-cancel = Zζ.cancel √3 (+ 3) refl

ζ¹²≡1 : Zζ._^_ Zζ.x 12 ≡ Zζ.1q
ζ¹²≡1 = refl

open import Examples.Independence.Semantics.Scaled 3 (+ 1) (-[1+ 0 ]) √3 √3-cancel 11 ζ¹²≡1 public

-- The semantics of circuits over a qutrit gate set, from its valuation.
module Circuits {Gate : ℕ → Set} =
  Examples.Independence.Semantics.Circuits 3 (+ 1) (-[1+ 0 ]) √3 √3-cancel 11 ζ¹²≡1 {Gate}

------------------------------------------------------------------------
-- The gates

private
  δ : Fin 3 → Fin 3 → Q
  δ = δ₁

  -- Addition and multiplication modulo 3.
  _⊞_ : Fin 3 → Fin 3 → Fin 3
  zero          ⊞ b             = b
  suc zero      ⊞ zero          = suc zero
  suc zero      ⊞ suc zero      = suc (suc zero)
  suc zero      ⊞ suc (suc zero) = zero
  suc (suc zero) ⊞ zero          = suc (suc zero)
  suc (suc zero) ⊞ suc zero      = zero
  suc (suc zero) ⊞ suc (suc zero) = suc zero

  _⊠_ : Fin 3 → Fin 3 → Fin 3
  zero           ⊠ _ = zero
  suc zero       ⊠ b = b
  suc (suc zero) ⊠ b = b ⊞ b

  -- ω₃^j = ζ^{4 j}.
  ω₃^ : Fin 3 → Q
  ω₃^ zero           = 1#
  ω₃^ (suc zero)     = x ^ 4
  ω₃^ (suc (suc zero)) = x ^ 8

  -- The phase of S on |b⟩.
  sph : Fin 3 → Q
  sph (suc (suc zero)) = x ^ 4
  sph _                = 1#

ωᵍ : Sc 0
ωᵍ = 0 , mat x

Hᵍ Sᵍ : Sc 1
Hᵍ = 1 , matOf λ { (a ∷ []) (b ∷ []) → ω₃^ (a ⊠ b) }
Sᵍ = 0 , matOf λ { (a ∷ []) (b ∷ []) → δ a b * sph b }

CXᵍ SWᵍ : Sc 2
CXᵍ = 0 , matOf λ { (a₀ ∷ a₁ ∷ []) (b₀ ∷ b₁ ∷ []) → δ a₁ b₁ * δ a₀ (b₀ ⊞ b₁) }
SWᵍ = 0 , matOf swapₒ

-- The swap reads as the swap, which is all the swap rules need
-- (Circuits' Symmetry).
SWᵍ-ok : ix (proj₂ SWᵍ) ≐ swapₒ
SWᵍ-ok = ix-matOf swapₒ

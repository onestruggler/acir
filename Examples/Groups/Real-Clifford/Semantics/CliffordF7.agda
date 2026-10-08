------------------------------------------------------------------------
-- Presentations of groups
--
-- Corollary 4.16 over F₇
--
-- The hypotheses of Semantics.Clifford are those of ℝ: a nontrivial
-- commutative ring with s s + s s = 1 whose only square roots of 1
-- are 1 and −1.  Agda has no ℝ, so this module checks that they can be
-- met, in the field F₇, where 1/2 = 4 = 2 · 2 has the square root 2.
-- There the orthogonal matrices that normalise the Pauli group are
-- again exactly 2 · ∏ᵢ₌₁ⁿ (4ⁱ + 2ⁱ − 2)(2 · 4ⁱ⁻¹) in number.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Semantics.CliffordF7 where

open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime ; prime?)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Function.Bundles using (Inverse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (from-yes)

open import Typeclasses using (SemiRing ; Ring)

open import Examples.Groups.Real-Clifford.Count using (order)
import Examples.Groups.Qupit-Phase-Affine.Field as Field
import Examples.Groups.Real-Clifford.Semantics.Clifford as Clifford

------------------------------------------------------------------------
-- The field F₇

7-prime : Prime 7
7-prime = from-yes (prime? 7)

open Field 5 7-prime using (F ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; _-_ ; isCommutativeRing-F ; module FR ; cancel ; solve ; _:+_ ; _:*_ ; _:-_ ; _:=_ ; con)

instance
  semiRing-F : SemiRing F
  semiRing-F = record { _+_ = _+_ ; _*_ = _*_ ; 0# = 0F ; 1# = 1F ; fromℕ = λ _ → 0F }

  ring-F : Ring F
  ring-F = record { -_ = -_ }

------------------------------------------------------------------------
-- The hypotheses

opaque
  unfolding _+_ _*_

  -- 2 · 2 + 2 · 2 = 8 = 1.
  s-half : 2F * 2F + 2F * 2F ≡ 1F
  s-half = refl

1≢0 : 1F ≢ 0F
1≢0 ()

-- c² = 1 gives (c − 1)(c + 1) = 0, and F₇ has no zero divisors.
±1 : (c : F) → c * c ≡ 1F → c ≡ 1F ⊎ c ≡ - 1F
±1 c e with (c - 1F) ≟ 0F
... | yes c-1≡0 = inj₁ (begin
  c                   ≡⟨ solve 1 (λ c → c := (c :- con (+ 1)) :+ con (+ 1)) refl c ⟩
  (c - 1F) + 1F       ≡⟨ Eq.cong (_+ 1F) c-1≡0 ⟩
  0F + 1F             ≡⟨ FR.+-identityˡ 1F ⟩
  1F                  ∎)
  where open Eq.≡-Reasoning
... | no  c-1≢0 = inj₂ (begin
  c                   ≡⟨ solve 1 (λ c → c := (c :+ con (+ 1)) :- con (+ 1)) refl c ⟩
  (c + 1F) - 1F       ≡⟨ Eq.cong (_- 1F) c+1≡0 ⟩
  0F - 1F             ≡⟨ FR.+-identityˡ (- 1F) ⟩
  - 1F                ∎)
  where
  open Eq.≡-Reasoning
  c+1≡0 : c + 1F ≡ 0F
  c+1≡0 = cancel (c - 1F) c-1≢0 (begin
    (c - 1F) * (c + 1F)   ≡⟨ solve 1 (λ c → (c :- con (+ 1)) :* (c :+ con (+ 1)) := c :* c :- con (+ 1)) refl c ⟩
    c * c - 1F            ≡⟨ Eq.cong (_- 1F) e ⟩
    1F - 1F               ≡⟨ FR.-‿inverseʳ 1F ⟩
    0F                    ≡⟨ FR.zeroʳ (c - 1F) ⟨
    (c - 1F) * 0F         ∎)

------------------------------------------------------------------------
-- Corollary 4.16 over F₇

open Clifford {A = F} isCommutativeRing-F 2F s-half 1≢0 ±1 public
  using (Clifford ; Clifford-setoid ; corollary-4-16)

_ : {n : ℕ} → Inverse (Clifford-setoid n) (Eq.setoid (Fin (order n)))
_ = corollary-4-16

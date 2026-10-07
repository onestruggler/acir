------------------------------------------------------------------------
-- Presentations of groups
--
-- Linear diagonal expressions
--
-- From level 1 on, ω ^ s • Zc c has phase s + c · x.  These words
-- multiply by adding their data (ld-add), take iterates by scaling it
-- (ld-^ᶠ), are diagonal, and Z conjugated by a linear word is one of
-- them (Z-conj): the column of the first row of the word.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.LinearDE
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 1 ≤ lv) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; 0F ; 1F ; _+_ ; _*_ ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Commute p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (↑ᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv using (_⋆ᴿ*_)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Linear p-2 p-prime lv h

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The expressions

LD : ℕ → Set
LD n = F × Vec F n

⟦_⟧ˡ : LD n → Circuit n
⟦ s , c ⟧ˡ = ω h ^ᶠ s • Zc c

_+ˡ_ : LD n → LD n → LD n
(s , c) +ˡ (s' , c') = s + s' , zipWith _+_ c c'

_·ˡ_ : F → LD n → LD n
k ·ˡ (s , c) = s * k , map (_* k) c

ld₀ : LD n
ld₀ = 0F , 0ᵛ

------------------------------------------------------------------------
-- Their algebra

private
  module OW {n : ℕ} = Pow.Order n {ω h} ω-order

-- Columns take iterates entrywise.
Zc-^ᶠ : (c : Vec F n) (k : F) → n ⊢ Zc c ^ᶠ k ≈ Zc (map (_* k) c)
Zc-^ᶠ {n} [] k = Pow.pow-ε n (toℕ k)
Zc-^ᶠ {suc n} (a ∷ c) k = begin
  (Z h ^ᶠ a • Zc c ↑) ^ᶠ k                  ≈⟨ Pow.pow-• (₁₊ n) (toℕ k) (Zᶠ-up a (Zc c)) ⟩
  (Z h ^ᶠ a) ^ᶠ k • (Zc c ↑) ^ᶠ k           ≈⟨ cong (Pow.Order.^ᶠ-* (₁₊ n) Z-order a k)
                                                     (trans (refl' (Eq.sym (↑ᶠ (Zc c) k))) (lift (Zc-^ᶠ c k))) ⟩
  Z h ^ᶠ (a * k) • Zc (map (_* k) c) ↑      ∎
  where open Width (₁₊ n)

ld-add : (e e' : LD n) → n ⊢ ⟦ e ⟧ˡ • ⟦ e' ⟧ˡ ≈ ⟦ e +ˡ e' ⟧ˡ
ld-add {n} (s , c) (s' , c') = begin
  (ω h ^ᶠ s • Zc c) • ω h ^ᶠ s' • Zc c'      ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  ω h ^ᶠ s • (Zc c • ω h ^ᶠ s') • Zc c'      ≈⟨ back _ (front _ (sym (ωᶠ-comm s' (Zc c)))) ⟩
  ω h ^ᶠ s • (ω h ^ᶠ s' • Zc c) • Zc c'      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (ω h ^ᶠ s • ω h ^ᶠ s') • Zc c • Zc c'      ≈⟨ cong (OW.^ᶠ-+ s s') (Zc-add c c') ⟩
  ω h ^ᶠ (s + s') • Zc (zipWith _+_ c c')    ∎
  where open Width n

ld-^ᶠ : (e : LD n) (k : F) → n ⊢ ⟦ e ⟧ˡ ^ᶠ k ≈ ⟦ k ·ˡ e ⟧ˡ
ld-^ᶠ {n} (s , c) k = begin
  (ω h ^ᶠ s • Zc c) ^ᶠ k                    ≈⟨ Pow.pow-• n (toℕ k) (ωᶠ-comm s (Zc c)) ⟩
  (ω h ^ᶠ s) ^ᶠ k • Zc c ^ᶠ k               ≈⟨ cong (OW.^ᶠ-* s k) (Zc-^ᶠ c k) ⟩
  ω h ^ᶠ (s * k) • Zc (map (_* k) c)        ∎
  where open Width n

ld-zero : n ⊢ ⟦ ld₀ {n} ⟧ˡ ≈ ε
ld-zero {n} = Width.trans Width.left-unit Zc-zero

------------------------------------------------------------------------
-- Z conjugated by a linear word

Z-conj : (L : Word (LGen (₁₊ n))) → (₁₊ n) ⊢ ⌊ L ⌋ ⁻¹ • Z h • ⌊ L ⌋ ≈ ⟦ 0F , (1F ∷ 0ᵛ) ⋆ᴿ* L ⟧ˡ
Z-conj {n} L = begin
  ⌊ L ⌋ ⁻¹ • Z h • ⌊ L ⌋                      ≈⟨ back _ (front _ Z≈) ⟩
  ⌊ L ⌋ ⁻¹ • Zc (1F ∷ 0ᵛ) • ⌊ L ⌋             ≈⟨ back _ (Z-push* L (1F ∷ 0ᵛ)) ⟩
  ⌊ L ⌋ ⁻¹ • ⌊ L ⌋ • Zc ((1F ∷ 0ᵛ) ⋆ᴿ* L)     ≈⟨ trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ n))) left-unit) ⟩
  Zc ((1F ∷ 0ᵛ) ⋆ᴿ* L)                        ≈⟨ sym left-unit ⟩
  ε • Zc ((1F ∷ 0ᵛ) ⋆ᴿ* L)                    ∎
  where
  open Width (₁₊ n)
  Z≈ : (₁₊ n) ⊢ Z h ≈ Zc (1F ∷ 0ᵛ)
  Z≈ = sym (trans (back _ (lift Zc-zero)) right-unit)

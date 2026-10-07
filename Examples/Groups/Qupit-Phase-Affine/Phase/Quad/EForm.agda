------------------------------------------------------------------------
-- Presentations of groups
--
-- Diagonal circuits, and the wire-0 forms at level 2
--
-- A circuit is diagonal (Diag) when it equals a diagonal expression
-- (Phase.Quad.Diag); diagonal circuits commute (diag∥), and products,
-- iterates, lifts and SWAP-conjugates of diagonal circuits are
-- diagonal, as are ω, Z, S, P and CZ.
--
-- On ₁₊ n wires the part of a quadratic phase that involves x₀ is
--
--     d (x₀ choose 2) + c x₀ + x₀ (α · x'),
--
-- and its canonical circuit is E (d , c , α) = S^d • Z^c • K α, where
-- the fan K α puts CZ^a on wires (0, 1) and the rest one wire up with
-- wire 0 swapped past wire 1.  These forms are diagonal, so they add
-- (E-add) and take iterates (E-^ᶠ) by their data, and a multiplier on
-- wire 0 scales the fan (K-M), CZ's on the way scaling by rule (28)'s
-- consequence CZ-M₀.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Quad.EForm
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 2 ≤ lv) (odd : 1 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (Fin ; zero ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; F* ; 0F ; 1F ; _+_ ; _*_ ; -_ ; 1* ; _×ᶠ_ ; ×ᶠ-toℕ ; module FR
        ; solve ; _:+_ ; _:*_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invʳ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (sM ; sM↑ ; slideᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; conjᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv using (R-e₀)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.Diag p-2 p-prime lv h odd public

private
  variable
    n : ℕ

  h₁ : 1 ≤ lv
  h₁ = lin₂ h

------------------------------------------------------------------------
-- Diagonal circuits

Diag : (n : ℕ) → Circuit n → Set
Diag n w = Σ (DE n) (λ d → n ⊢ w ≈ ⟦ d ⟧ᴰ)

module _ {n : ℕ} where

  open Width n

  diag∥ : {w v : Circuit n} → Diag n w → Diag n v → n ⊢ w ∥ v
  diag∥ (d , e) (d' , e') = trans (cong e e') (trans (de∥ d d') (sym (cong e' e)))

  Diag-≈ : {w v : Circuit n} → n ⊢ w ≈ v → Diag n v → Diag n w
  Diag-≈ e (d , e') = d , trans e e'

  Diag-• : {w v : Circuit n} → Diag n w → Diag n v → Diag n (w • v)
  Diag-• (d , e) (d' , e') = d ⊕ d' , trans (cong e e') (⊕-sound d d')

  Diag-ε : Diag n ε
  Diag-ε = de 0F 0ᵛ [] , sym (trans left-unit (trans right-unit Zc-zero))

  Diag-^ : {w : Circuit n} → Diag n w → (k : ℕ) → Diag n (w ^ k)
  Diag-^ D zero          = Diag-ε
  Diag-^ D (suc zero)    = D
  Diag-^ D (suc (suc k)) = Diag-• D (Diag-^ D (suc k))

  Diag-^ᶠ : {w : Circuit n} → Diag n w → (k : F) → Diag n (w ^ᶠ k)
  Diag-^ᶠ D k = Diag-^ D (toℕ k)

  Diag-ω : Diag n (ω h₁)
  Diag-ω = de 1F 0ᵛ [] , sym (trans (back _ (trans right-unit Zc-zero)) right-unit)

  Diag-Zc : (c : Vec F n) → Diag n (Zc c)
  Diag-Zc c = de 0F c [] , sym (trans left-unit right-unit)

  Diag-atom : (ℓ : NZ n) → Diag n (atom ℓ)
  Diag-atom ℓ = de 0F 0ᵛ ((ℓ , 1F) ∷ []) , sym (trans left-unit (trans (front _ Zc-zero) (trans left-unit right-unit)))

Diag-↑ : {w : Circuit n} → Diag n w → Diag (₁₊ n) (w ↑)
Diag-↑ (d , e) = lift-d d , Width.trans (lift e) (lift-sound d)

Diag-SWAP : {w : Circuit (₂₊ n)} → Diag (₂₊ n) w → Diag (₂₊ n) (SWAP • w • SWAP)
Diag-SWAP {n} {w} (d , e) = d ⋆ˡ sw , (begin
  SWAP • w • SWAP                    ≈⟨ back _ (trans (front _ e) (⋆ˡ-sound d sw)) ⟩
  SWAP • SWAP • ⟦ d ⋆ˡ sw ⟧ᴰ         ≈⟨ trans (sym assoc) (trans (front _ (ax swap-order)) left-unit) ⟩
  ⟦ d ⋆ˡ sw ⟧ᴰ                       ∎)
  where open Width (₂₊ n)

Diag-S : Diag (₁₊ n) (S h)
Diag-S = Diag-≈ (S-e zero) (Diag-atom (eᴺ zero))

Diag-Z : Diag (₁₊ n) (Z h₁)
Diag-Z = Diag-≈ (Z-e zero) (Diag-Zc _)

Diag-SZ : (q b : F) → Diag (₁₊ n) (SZ q b)
Diag-SZ q b = Diag-• (Diag-^ᶠ Diag-S q) (Diag-^ᶠ Diag-Z b)

-- P is the atom of x₀ + x₁.
e₀₁ : NZ (₂₊ n)
e₀₁ = big 1* (1F ∷ 0ᵛ)

P-atom : (₂₊ n) ⊢ P ≈ atom (e₀₁ {n})
P-atom {n} = sym (trans (cong (Inv.⁻¹-cong (₂₊ n) r≈) (back _ r≈)) (front _ CX⁻¹≈))
  where
  open Width (₂₊ n)
  r≈ : (₂₊ n) ⊢ r (e₀₁ {n}) ≈ CX
  r≈ = trans (back _ (ax ax1)) (trans right-unit R-e₀)
  CX⁻¹≈ : (₂₊ n) ⊢ CX ⁻¹ ≈ CX ^ᶠ (- 1F)
  CX⁻¹≈ = sym (Inv.inverseʳ-unique (₂₊ n) (CX-invʳ 1F))

Diag-P : Diag (₂₊ n) P
Diag-P {n} = Diag-≈ P-atom (Diag-atom (e₀₁ {n}))

Diag-CZ : Diag (₂₊ n) (CZ h)
Diag-CZ = Diag-• (Diag-^ᶠ Diag-S (- 1F)) (Diag-• (Diag-↑ (Diag-^ᶠ Diag-S (- 1F))) Diag-P)

------------------------------------------------------------------------
-- The fan of CZ's from wire 0

K : Vec F n → Circuit (₁₊ n)
K []      = ε
K (a ∷ α) = CZ h ^ᶠ a • SWAP • K α ↑ • SWAP

Diag-K : (α : Vec F n) → Diag (₁₊ n) (K α)
Diag-K []      = Diag-ε
Diag-K (a ∷ α) = Diag-• (Diag-^ᶠ Diag-CZ a) (Diag-SWAP (Diag-↑ (Diag-K α)))

private
  module OCZ {n : ℕ} = Pow.Order (₂₊ n) {CZ h} CZ-order

  ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
  ss = ax swap-order

K-zero : (₁₊ n) ⊢ K (0ᵛ {n}) ≈ ε
K-zero {zero}  = Width.refl
K-zero {suc n} = trans left-unit (trans (back _ (trans (front _ (lift K-zero)) left-unit)) ss)
  where open Width (₂₊ n)

K-add : (α β : Vec F n) → (₁₊ n) ⊢ K α • K β ≈ K (zipWith _+_ α β)
K-add [] [] = Width.left-unit
K-add {suc n} (a ∷ α) (b ∷ β) = begin
  (CZ h ^ᶠ a • K₀ α) • CZ h ^ᶠ b • K₀ β
    ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  CZ h ^ᶠ a • (K₀ α • CZ h ^ᶠ b) • K₀ β
    ≈⟨ back _ (front _ (diag∥ (Diag-SWAP (Diag-↑ (Diag-K α))) (Diag-^ᶠ Diag-CZ b))) ⟩
  CZ h ^ᶠ a • (CZ h ^ᶠ b • K₀ α) • K₀ β
    ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (CZ h ^ᶠ a • CZ h ^ᶠ b) • K₀ α • K₀ β
    ≈⟨ cong (OCZ.^ᶠ-+ a b) K₀-add ⟩
  CZ h ^ᶠ (a + b) • K₀ (zipWith _+_ α β) ∎
  where
  open Width (₂₊ n)
  K₀ : Vec F n → Circuit (₂₊ n)
  K₀ γ = SWAP • K γ ↑ • SWAP
  K₀-add : (₂₊ n) ⊢ K₀ α • K₀ β ≈ K₀ (zipWith _+_ α β)
  K₀-add = begin
    (SWAP • K α ↑ • SWAP) • SWAP • K β ↑ • SWAP
      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    SWAP • K α ↑ • (SWAP • SWAP) • K β ↑ • SWAP
      ≈⟨ back _ (back _ (trans (front _ ss) left-unit)) ⟩
    SWAP • K α ↑ • K β ↑ • SWAP
      ≈⟨ back _ (trans (sym assoc) (front _ (lift (K-add α β)))) ⟩
    SWAP • K (zipWith _+_ α β) ↑ • SWAP ∎

-- Scaling a vector.
sc : F → Vec F n → Vec F n
sc k []      = []
sc k (a ∷ α) = k * a ∷ sc k α

private
  sc-0 : (α : Vec F n) → sc 0F α ≡ 0ᵛ
  sc-0 []      = Eq.refl
  sc-0 (a ∷ α) = Eq.cong₂ _∷_ (FR.zeroˡ a) (sc-0 α)

  sc-suc : (m : F) (α : Vec F n) → zipWith _+_ α (sc m α) ≡ sc (1F + m) α
  sc-suc m []      = Eq.refl
  sc-suc m (a ∷ α) = Eq.cong₂ _∷_ (solve 2 (λ a m → a :+ m :* a := (con (ℤ.+ 1) :+ m) :* a) Eq.refl a m) (sc-suc m α)

  sc-1 : (α : Vec F n) → sc 1F α ≡ α
  sc-1 []      = Eq.refl
  sc-1 (a ∷ α) = Eq.cong₂ _∷_ (FR.*-identityˡ a) (sc-1 α)

-- Iterates of a fan.
K-^ : (α : Vec F n) (m : ℕ) → (₁₊ n) ⊢ K α ^ m ≈ K (sc (m ×ᶠ 1F) α)
K-^ {n} α zero          = sym (trans (refl' (Eq.cong K (sc-0 α))) K-zero)
  where open Width (₁₊ n)
K-^ {n} α (suc zero)    = sym (refl' (Eq.cong K (Eq.trans (Eq.cong (λ t → sc t α) (FR.+-identityʳ 1F)) (sc-1 α))))
  where open Width (₁₊ n)
K-^ {n} α (suc (suc m)) = begin
  K α • K α ^ suc m                    ≈⟨ back _ (K-^ α (suc m)) ⟩
  K α • K (sc (suc m ×ᶠ 1F) α)         ≈⟨ K-add α _ ⟩
  K (zipWith _+_ α (sc (suc m ×ᶠ 1F) α)) ≈⟨ refl' (Eq.cong K (sc-suc _ α)) ⟩
  K (sc (suc (suc m) ×ᶠ 1F) α)         ∎
  where open Width (₁₊ n)

K-^ᶠ : (α : Vec F n) (k : F) → (₁₊ n) ⊢ K α ^ᶠ k ≈ K (sc k α)
K-^ᶠ {n} α k = Width.trans (K-^ α (toℕ k))
  (Width.refl' (₁₊ n) (Eq.cong (λ t → K (sc t α)) (Eq.trans (×ᶠ-toℕ k 1F) (FR.*-identityʳ k))))

-- A multiplier on wire 0 scales the fan.
CZᶠ-M₀ : (k : F) (x : F*) → (₂₊ n) ⊢ CZ h ^ᶠ k • M⟨ x ⟩ ≈ M⟨ x ⟩ • CZ h ^ᶠ (proj₁ x * k)
CZᶠ-M₀ {n} k x = trans (sym (slideᶠ k (sym (CZ-M₀ x)))) (back _ (OCZ.^ᶠ-* (proj₁ x) k))
  where open Width (₂₊ n)

K-M : (x : F*) (α : Vec F n) → (₁₊ n) ⊢ K α • M⟨ x ⟩ ≈ M⟨ x ⟩ • K (sc (proj₁ x) α)
K-M {n} x [] = Width.trans Width.left-unit (Width.sym Width.right-unit)
K-M {suc n} x (a ∷ α) = begin
  (CZ h ^ᶠ a • SWAP • K α ↑ • SWAP) • M⟨ x ⟩
    ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
  CZ h ^ᶠ a • SWAP • K α ↑ • SWAP • M⟨ x ⟩
    ≈⟨ back _ (back _ (back _ (sM x))) ⟩
  CZ h ^ᶠ a • SWAP • K α ↑ • M⟨ x ⟩ ↑ • SWAP
    ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (lift (K-M x α))) assoc))) ⟩
  CZ h ^ᶠ a • SWAP • M⟨ x ⟩ ↑ • K (sc (proj₁ x) α) ↑ • SWAP
    ≈⟨ back _ (trans (sym assoc) (trans (front _ (sM↑ x)) assoc)) ⟩
  CZ h ^ᶠ a • M⟨ x ⟩ • SWAP • K (sc (proj₁ x) α) ↑ • SWAP
    ≈⟨ trans (sym assoc) (trans (front _ (CZᶠ-M₀ a x)) assoc) ⟩
  M⟨ x ⟩ • CZ h ^ᶠ (proj₁ x * a) • SWAP • K (sc (proj₁ x) α) ↑ • SWAP ∎
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- The wire-0 forms

EData : ℕ → Set
EData n = F × F × Vec F n

E : EData n → Circuit (₁₊ n)
E (d , c , α) = SZ d c • K α

Diag-E : (e : EData n) → Diag (₁₊ n) (E e)
Diag-E (d , c , α) = Diag-• (Diag-SZ d c) (Diag-K α)

e₀ᴱ : EData n
e₀ᴱ = 0F , 0F , 0ᵛ

E-zero : (₁₊ n) ⊢ E (e₀ᴱ {n}) ≈ ε
E-zero {n} = trans (cong SZ-zero K-zero) left-unit
  where open Width (₁₊ n)

infixl 6 _+ᴱ_
_+ᴱ_ : EData n → EData n → EData n
(d , c , α) +ᴱ (d' , c' , α') = d + d' , c + c' , zipWith _+_ α α'

E-add : (e e' : EData n) → (₁₊ n) ⊢ E e • E e' ≈ E (e +ᴱ e')
E-add {n} (d , c , α) (d' , c' , α') = begin
  (SZ d c • K α) • SZ d' c' • K α'       ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
  SZ d c • (K α • SZ d' c') • K α'       ≈⟨ back _ (front _ (diag∥ (Diag-K α) (Diag-SZ d' c'))) ⟩
  SZ d c • (SZ d' c' • K α) • K α'       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
  (SZ d c • SZ d' c') • K α • K α'       ≈⟨ cong (SZ-add d c d' c') (K-add α α') ⟩
  SZ (d + d') (c + c') • K (zipWith _+_ α α') ∎
  where open Width (₁₊ n)

infixl 7 _·ᴱ_
_·ᴱ_ : F → EData n → EData n
k ·ᴱ (d , c , α) = d * k , c * k , sc k α

E-^ᶠ : (e : EData n) (k : F) → (₁₊ n) ⊢ E e ^ᶠ k ≈ E (k ·ᴱ e)
E-^ᶠ {n} (d , c , α) k = begin
  (SZ d c • K α) ^ᶠ k                    ≈⟨ Pow.pow-• (₁₊ n) (toℕ k) (diag∥ (Diag-SZ d c) (Diag-K α)) ⟩
  SZ d c ^ᶠ k • K α ^ᶠ k                 ≈⟨ cong (SZ-^ᶠ d c k) (K-^ᶠ α k) ⟩
  SZ (d * k) (c * k) • K (sc k α)        ∎
  where open Width (₁₊ n)

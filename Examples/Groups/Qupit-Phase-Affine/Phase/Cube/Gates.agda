------------------------------------------------------------------------
-- Presentations of groups
--
-- CS, SC and the gadget of T
--
-- CS (Definition 17) is a product of atoms of T and gates on wire 1:
--
--     CS = Aᵀ(x₀ - x₁)^(-½) Aᵀ(x₀ + x₁)^½ (S⁻¹ T⁻¹ Z^(-½)) ↑ CZ^½,
--
-- and SC = SWAP CS SWAP, the controlled square with the roles of the
-- wires exchanged (x₀ (x₁ choose 2)), is the same with the rows
-- swapped (CS-atoms, SC-atoms); both are diagonal.  Rule (32) at -1
-- negates a row: the atom of T at -ℓ is the inverse of that at ℓ times
-- atoms of S and Z (neg-T), and with it CS • SC is the gadget PT of T
-- with T on both wires taken out (PT-dec):
--
--     PT = T • T ↑ • CS • SC.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Gates
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (Fin ; zero ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; F* ; p ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; 1* ; -1* ; binom2 ; binom3 ; half ; _×ᶠ_ ; ×ᶠ-toℕ
        ; big⇒odd ; module FR ; module Odd ; module Big ; solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invʳ ; CX-invˡ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv using (↑ᶠ ; slideᶠ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; ⌊^⌋)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Phase.Cube.Diag p-2 p-prime lv h gt3 public

private
  variable
    n : ℕ

  h₂ : 2 ≤ lv
  h₂ = quad₃ h

  h₁ : 1 ≤ lv
  h₁ = lin₃ h

  odd : 1 ≤ p-2
  odd = big⇒odd gt3

------------------------------------------------------------------------
-- Atoms of T: order, rows, conjugation

atomᵀ-order : (ℓ : NZ n) → n ⊢ atomᵀ ℓ ^ p ≈ ε
atomᵀ-order {suc n} ℓ = begin
  AT.A ℓ ^ p                   ≈⟨ AT.A-^ ℓ p ⟩
  r ℓ ⁻¹ • T h ^ p • r ℓ       ≈⟨ back _ (trans (front _ T-order) left-unit) ⟩
  r ℓ ⁻¹ • r ℓ                 ≈⟨ Inv.inverseˡ (₁₊ n) ⟩
  ε                            ∎
  where open Width (₁₊ n)

module OAT {n : ℕ} (ℓ : NZ n) = Pow.Order n {atomᵀ ℓ} (atomᵀ-order ℓ)

atomᵀ-≡ : (ℓ ℓ' : NZ n) → row ℓ ≡ row ℓ' → n ⊢ atomᵀ ℓ ≈ atomᵀ ℓ'
atomᵀ-≡ {suc n} ℓ ℓ' e = AT.A-≡ e

atomᵀ-≡ᶠ : (ℓ ℓ' : NZ n) (k : F) → row ℓ ≡ row ℓ' → n ⊢ atomᵀ ℓ ^ᶠ k ≈ atomᵀ ℓ' ^ᶠ k
atomᵀ-≡ᶠ {n} ℓ ℓ' k e = Pow.pow-cong n (toℕ k) (atomᵀ-≡ ℓ ℓ' e)

atomᵀ-conj : (ℓ : NZ n) (L : Word (LGen n)) → n ⊢ ⌊ L ⌋ ⁻¹ • atomᵀ ℓ • ⌊ L ⌋ ≈ atomᵀ (ℓ ⋆* L)
atomᵀ-conj {suc n} ℓ L = AT.A-conj ℓ L

atomᵀ-conjᶠ : (ℓ : NZ n) (L : Word (LGen n)) (k : F) →
              n ⊢ ⌊ L ⌋ ⁻¹ • atomᵀ ℓ ^ᶠ k • ⌊ L ⌋ ≈ atomᵀ (ℓ ⋆* L) ^ᶠ k
atomᵀ-conjᶠ {n} ℓ L k = Width.trans (conj-^ᶠ ⌊ L ⌋ (atomᵀ ℓ) k) (Pow.pow-cong n (toℕ k) (atomᵀ-conj ℓ L))

-- A word undoing ⌊ L ⌋ on its left is its inverse.
undo-conj : {g X : Circuit n} (L : Word (LGen n)) → n ⊢ g • ⌊ L ⌋ ≈ ε → n ⊢ g • X • ⌊ L ⌋ ≈ ⌊ L ⌋ ⁻¹ • X • ⌊ L ⌋
undo-conj {n} L gL = Width.front n _ (Inv.inverseˡ-unique n gL)

-- T is the atom of e₀.
T≈ : (₁₊ n) ⊢ T h ≈ atomᵀ (e0 {n})
T≈ = T-e zero

T↑≈ : (₂₊ n) ⊢ T h ↑ ≈ atomᵀ (e1 {n})
T↑≈ = Width.trans (lift T≈) (Width.sym (AT.A-small e0))

------------------------------------------------------------------------
-- CS and SC

-- The rows x₀ - x₁ and -x₀ + x₁.
e0m1 : NZ (₂₊ n)
e0m1 = big 1* (- 1F ∷ 0ᵛ)

em1 : NZ (₂₊ n)
em1 = big -1* (1F ∷ 0ᵛ)

private
  Q₁ : Circuit (₂₊ n)
  Q₁ = (S h₂ ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • (Z h₁ ^ᶠ (- half)) ↑ • CZ h₂ ^ᶠ half

  Q₀ : Circuit (₂₊ n)
  Q₀ = S h₂ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • Z h₁ ^ᶠ (- half) • CZ h₂ ^ᶠ half

  -- The two conjugates in the definition of CS.
  L₁ L₂ : Word (LGen (₂₊ n))
  L₁ = [ cx ]ʷ ^ toℕ (- 1F)
  L₂ = [ cx ]ʷ

  ⌊L₁⌋ : (₂₊ n) ⊢ ⌊ L₁ {n} ⌋ ≈ CX ^ᶠ (- 1F)
  ⌊L₁⌋ = Width.refl' _ (⌊^⌋ [ cx ]ʷ (toℕ (- 1F)))

  row-L₁ : row ((e0 {₁₊ n}) ⋆* L₁) ≡ row (e0m1 {n})
  row-L₁ = Eq.trans (row-⋆* e0 L₁) (Eq.trans (cx-pow 1F 0F 0ᵛ (toℕ (- 1F)))
             (Eq.cong (λ t → 1F ∷ t ∷ 0ᵛ) (Eq.trans (FR.+-identityˡ _) (Eq.trans (×ᶠ-toℕ (- 1F) 1F) (FR.*-identityʳ _)))))

  row-L₂ : row ((e0 {₁₊ n}) ⋆* L₂) ≡ row (e₀₁ {n})
  row-L₂ = Eq.cong (λ t → 1F ∷ t ∷ 0ᵛ) (FR.+-identityˡ 1F)

CS-atoms : (₂₊ n) ⊢ CS h ≈ atomᵀ e0m1 ^ᶠ (- half) • atomᵀ e₀₁ ^ᶠ half • Q₁
CS-atoms {n} = begin
  CX • T h ^ᶠ (- half) • CX ^ᶠ (- 1F) • CX ^ᶠ (- 1F) • T h ^ᶠ half • CX • Q₁
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □) ((□ • □ • □) • (□ • □ • □) • □) Eq.refl ⟩
  (CX • T h ^ᶠ (- half) • CX ^ᶠ (- 1F)) • (CX ^ᶠ (- 1F) • T h ^ᶠ half • CX) • Q₁
    ≈⟨ cong first (front _ second) ⟩
  atomᵀ e0m1 ^ᶠ (- half) • atomᵀ e₀₁ ^ᶠ half • Q₁ ∎
  where
  open Width (₂₊ n)
  first : (₂₊ n) ⊢ CX • T h ^ᶠ (- half) • CX ^ᶠ (- 1F) ≈ atomᵀ e0m1 ^ᶠ (- half)
  first = begin
    CX • T h ^ᶠ (- half) • CX ^ᶠ (- 1F)
      ≈⟨ back _ (back _ (sym ⌊L₁⌋)) ⟩
    CX • T h ^ᶠ (- half) • ⌊ L₁ ⌋
      ≈⟨ undo-conj L₁ (trans (back _ ⌊L₁⌋) (CX-invʳ 1F)) ⟩
    ⌊ L₁ ⌋ ⁻¹ • T h ^ᶠ (- half) • ⌊ L₁ ⌋
      ≈⟨ back _ (front _ (Pow.pow-cong (₂₊ n) (toℕ (- half)) T≈)) ⟩
    ⌊ L₁ ⌋ ⁻¹ • atomᵀ e0 ^ᶠ (- half) • ⌊ L₁ ⌋
      ≈⟨ atomᵀ-conjᶠ e0 L₁ (- half) ⟩
    atomᵀ (e0 ⋆* L₁) ^ᶠ (- half)
      ≈⟨ atomᵀ-≡ᶠ (e0 ⋆* L₁) e0m1 (- half) row-L₁ ⟩
    atomᵀ e0m1 ^ᶠ (- half) ∎
  second : (₂₊ n) ⊢ CX ^ᶠ (- 1F) • T h ^ᶠ half • CX ≈ atomᵀ e₀₁ ^ᶠ half
  second = begin
    CX ^ᶠ (- 1F) • T h ^ᶠ half • CX
      ≈⟨ undo-conj L₂ (CX-invˡ 1F) ⟩
    ⌊ L₂ ⌋ ⁻¹ • T h ^ᶠ half • ⌊ L₂ ⌋
      ≈⟨ back _ (front _ (Pow.pow-cong (₂₊ n) (toℕ half) T≈)) ⟩
    ⌊ L₂ ⌋ ⁻¹ • atomᵀ e0 ^ᶠ half • ⌊ L₂ ⌋
      ≈⟨ atomᵀ-conjᶠ e0 L₂ half ⟩
    atomᵀ (e0 ⋆* L₂) ^ᶠ half
      ≈⟨ atomᵀ-≡ᶠ (e0 ⋆* L₂) e₀₁ half row-L₂ ⟩
    atomᵀ e₀₁ ^ᶠ half ∎

-- The controlled square with the wires exchanged: x₀ (x₁ choose 2).
SC : Circuit (₂₊ n)
SC = SWAP • CS h • SWAP

SC-atoms : (₂₊ n) ⊢ SC ≈ atomᵀ em1 ^ᶠ (- half) • atomᵀ e₀₁ ^ᶠ half • Q₀
SC-atoms {n} = begin
  SWAP • CS h • SWAP
    ≈⟨ back _ (front _ CS-atoms) ⟩
  SWAP • (atomᵀ e0m1 ^ᶠ (- half) • atomᵀ e₀₁ ^ᶠ half • Q₁) • SWAP
    ≈⟨ trans (conj-• SWAP _ _) (back _ (conj-• SWAP _ _)) ⟩
  (SWAP • atomᵀ e0m1 ^ᶠ (- half) • SWAP) • (SWAP • atomᵀ e₀₁ ^ᶠ half • SWAP) • (SWAP • Q₁ • SWAP)
    ≈⟨ cong (trans (atomᵀ-conjᶠ e0m1 [ sw ]ʷ (- half)) (atomᵀ-≡ᶠ (e0m1 ⋆ sw) em1 (- half) (row-⋆ e0m1 sw)))
            (cong (trans (atomᵀ-conjᶠ e₀₁ [ sw ]ʷ half) (atomᵀ-≡ᶠ (e₀₁ ⋆ sw) e₀₁ half (row-⋆ e₀₁ sw))) Q₁≈) ⟩
  atomᵀ em1 ^ᶠ (- half) • atomᵀ e₀₁ ^ᶠ half • Q₀ ∎
  where
  open Width (₂₊ n)
  Q₁≈ : (₂₊ n) ⊢ SWAP • Q₁ • SWAP ≈ Q₀
  Q₁≈ = begin
    SWAP • ((S h₂ ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • (Z h₁ ^ᶠ (- half)) ↑ • CZ h₂ ^ᶠ half) • SWAP
      ≈⟨ back _ (by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl) ⟩
    SWAP • (S h₂ ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • (Z h₁ ^ᶠ (- half)) ↑ • CZ h₂ ^ᶠ half • SWAP
      ≈⟨ back _ (back _ (back _ (back _ (sym (conjᶠ′ half))))) ⟩
    SWAP • (S h₂ ^ᶠ (- 1F)) ↑ • (T h ^ᶠ (- 1F)) ↑ • (Z h₁ ^ᶠ (- half)) ↑ • SWAP • CZ h₂ ^ᶠ half
      ≈⟨ trans (sym assoc) (trans (front _ (sS↑ᶠ (- 1F))) assoc) ⟩
    S h₂ ^ᶠ (- 1F) • SWAP • (T h ^ᶠ (- 1F)) ↑ • (Z h₁ ^ᶠ (- half)) ↑ • SWAP • CZ h₂ ^ᶠ half
      ≈⟨ back _ (trans (sym assoc) (trans (front _ sT↑ᶠ) assoc)) ⟩
    S h₂ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • SWAP • (Z h₁ ^ᶠ (- half)) ↑ • SWAP • CZ h₂ ^ᶠ half
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (sym (Zᶠ-SWAP (- half)))) assoc))) ⟩
    S h₂ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • Z h₁ ^ᶠ (- half) • SWAP • SWAP • CZ h₂ ^ᶠ half
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (trans (front _ (ax swap-order)) left-unit)))) ⟩
    S h₂ ^ᶠ (- 1F) • T h ^ᶠ (- 1F) • Z h₁ ^ᶠ (- half) • CZ h₂ ^ᶠ half ∎
    where
    -- SWAP fixes iterates of CZ.
    conjᶠ′ : (k : F) → (₂₊ n) ⊢ SWAP • CZ h₂ ^ᶠ k ≈ CZ h₂ ^ᶠ k • SWAP
    conjᶠ′ k = slideᶠ k CZ-sym
    sT↑ᶠ : (₂₊ n) ⊢ SWAP • (T h ^ᶠ (- 1F)) ↑ ≈ T h ^ᶠ (- 1F) • SWAP
    sT↑ᶠ = trans (back _ (refl' (↑ᶠ (T h) (- 1F)))) (slideᶠ (- 1F) sT↑)

------------------------------------------------------------------------
-- The gates are diagonal

Diag₃-Q₁ : Diag₃ (₂₊ n) Q₁
Diag₃-Q₁ = Diag₃-• (Diag₃-↑ (Diag₃-2 (Diag-^ᶠ Diag-S (- 1F))))
           (Diag₃-• (Diag₃-↑ (Diag₃-^ᶠ Diag₃-T (- 1F)))
           (Diag₃-• (Diag₃-↑ (Diag₃-2 (Diag-^ᶠ Diag-Z (- half)))) (Diag₃-2 (Diag-^ᶠ Diag-CZ half))))

Diag₃-CS : Diag₃ (₂₊ n) (CS h)
Diag₃-CS = Diag₃-≈ CS-atoms (Diag₃-• (Diag₃-^ᶠ (Diag₃-atomᵀ e0m1) (- half))
                            (Diag₃-• (Diag₃-^ᶠ (Diag₃-atomᵀ e₀₁) half) Diag₃-Q₁))

Diag₃-SC : Diag₃ (₂₊ n) SC
Diag₃-SC = Diag₃-SWAP Diag₃-CS

------------------------------------------------------------------------
-- Negating a row: rule (32) at -1

neg-T : (ℓ : NZ (₁₊ n)) →
        (₁₊ n) ⊢ atomᵀ (e0 ⋆* ([ mul -1* ]ʷ • rL ℓ)) ≈
                 atom ℓ ^ᶠ (2F * - 1F * binom2 (- 1F)) • Zc ((binom3 (- 1F) ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • atomᵀ ℓ ^ᶠ (- 1F * - 1F * - 1F)
neg-T {n} ℓ = begin
  atomᵀ (e0 ⋆* L)
    ≈⟨ sym (atomᵀ-conj e0 L) ⟩
  ⌊ L ⌋ ⁻¹ • atomᵀ e0 • ⌊ L ⌋
    ≈⟨ back _ (front _ (sym T≈)) ⟩
  (ρ ⁻¹ • Mn ⁻¹) • T h • Mn • ρ
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  ρ ⁻¹ • (Mn ⁻¹ • T h • Mn) • ρ
    ≈⟨ back _ (front _ MTM) ⟩
  ρ ⁻¹ • (S h₂ ^ᶠ q • Z h₁ ^ᶠ b • T h ^ᶠ t) • ρ
    ≈⟨ trans (conj-• ρ _ _) (back _ (conj-• ρ _ _)) ⟩
  (ρ ⁻¹ • S h₂ ^ᶠ q • ρ) • (ρ ⁻¹ • Z h₁ ^ᶠ b • ρ) • (ρ ⁻¹ • T h ^ᶠ t • ρ)
    ≈⟨ cong (trans (conjρ _) (sym (A-^ ℓ (toℕ q)))) (cong (trans (conjρ _) Zpart) (trans (conjρ _) (sym (AT.A-^ ℓ (toℕ t))))) ⟩
  atom ℓ ^ᶠ q • Zc ((b ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • atomᵀ ℓ ^ᶠ t ∎
  where
  open Width (₁₊ n)
  q b t : F
  q = 2F * - 1F * binom2 (- 1F)
  b = binom3 (- 1F)
  t = - 1F * - 1F * - 1F
  L : Word (LGen (₁₊ n))
  L = [ mul -1* ]ʷ • rL ℓ
  Mn ρ : Circuit (₁₊ n)
  Mn = M⟨ -1* ⟩
  ρ = ⌊ rL ℓ ⌋
  -- ρ is the representative.
  conjρ : (X : Circuit (₁₊ n)) → (₁₊ n) ⊢ ρ ⁻¹ • X • ρ ≈ r ℓ ⁻¹ • X • r ℓ
  conjρ X = refl' (Eq.cong (λ q → q ⁻¹ • X • q) (⌊rL⌋ ℓ))
  MTM : (₁₊ n) ⊢ Mn ⁻¹ • T h • Mn ≈ S h₂ ^ᶠ q • Z h₁ ^ᶠ b • T h ^ᶠ t
  MTM = trans (back _ (T-M -1*)) (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ n))) left-unit))
  Zpart : (₁₊ n) ⊢ r ℓ ⁻¹ • Z h₁ ^ᶠ b • r ℓ ≈ Zc ((b ∷ 0ᵛ) ⋆ᴿ* rL ℓ)
  Zpart = trans (back _ (front _ (sym (trans (back _ (lift Zc-zero)) right-unit)))) (Zc-rconj ℓ (b ∷ 0ᵛ))

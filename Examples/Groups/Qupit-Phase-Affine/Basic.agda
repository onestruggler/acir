------------------------------------------------------------------------
-- Presentations of groups
--
-- Inverses of the generators
--
-- The orders of X and CX are not rules: X^d = id comes from (3) at
-- x = 1, which reads X · X^(-1) = id once M_1 = id (1) is used, and
-- CX^d = id likewise from (5) (the paper's Lemma 17).  M_a has the
-- inverse M_(a⁻¹) by (2) and (1); the phases have order p by (19),
-- (20), (24), (31); SWAP is an involution.  So every generator has a
-- left inverse and the presented monoid is a group (grouplike).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Basic
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Empty using (⊥-elim-irr)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

import Presentation.Base as PB
open import Presentation.GroupLike using (Grouplike)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; _*_ ; -_ ; _⁻¹ᶠ ; _⁻¹* ; 1* ; ⁻¹ᶠ-inverseʳ ; ⁻¹ᶠ-inverseˡ ; toℕ-1)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Multipliers

-- M depends on its label alone.
M-≡ : {a b : F} .{na : a ≢ 0F} .{nb : b ≢ 0F} → a ≡ b → M {n} a na ≡ M b nb
M-≡ refl = refl

-- A label with an irrelevant proof of a ≢ 0 is a unit.
unit : (a : F) → .(a ≢ 0F) → F*
unit a na = a , λ e → ⊥-elim-irr (na e)

M-inverseˡ : (a : F*) → (₁₊ n) ⊢ M⟨ a ⁻¹* ⟩ • M⟨ a ⟩ ≈ ε
M-inverseˡ {n} (a , na) =
  trans (ax (ax2 (a , na) ((a , na) ⁻¹*)))
    (trans (refl' (M-≡ (⁻¹ᶠ-inverseʳ a na))) (ax ax1))
  where open Width (₁₊ n)

M-inverseʳ : (a : F*) → (₁₊ n) ⊢ M⟨ a ⟩ • M⟨ a ⁻¹* ⟩ ≈ ε
M-inverseʳ {n} (a , na) =
  trans (ax (ax2 ((a , na) ⁻¹*) (a , na)))
    (trans (refl' (M-≡ (⁻¹ᶠ-inverseˡ a na))) (ax ax1))
  where open Width (₁₊ n)

------------------------------------------------------------------------
-- The orders of X and CX (Lemma 17)

X-order : (₁₊ n) ⊢ X ^ p ≈ ε
X-order {n} = begin
  X • X ^ suc p-2                          ≈⟨ back X (sym left-unit) ⟩
  X • ε • X ^ suc p-2                      ≈⟨ back X (front _ (sym (ax ax1))) ⟩
  X • M⟨ 1* ⟩ • X ^ suc p-2                ≈⟨ back X (back M⟨ 1* ⟩ (refl' (Eq.cong (X ^_) (Eq.sym toℕ-1)))) ⟩
  X ^ᶠ 1F • M⟨ 1* ⟩ • X ^ᶠ (- 1F)          ≈⟨ ax (ax3 1*) ⟩
  M⟨ 1* ⟩                                  ≈⟨ ax ax1 ⟩
  ε                                        ∎
  where open Width (₁₊ n)

CX-inverseˡ : (₂₊ n) ⊢ CX ^ᶠ (- 1F) • CX ≈ ε
CX-inverseˡ {n} = begin
  CX ^ᶠ (- 1F) • CX                        ≈⟨ back _ (sym left-unit) ⟩
  CX ^ᶠ (- 1F) • ε • CX                    ≈⟨ back _ (front CX (sym (ax ax1))) ⟩
  CX ^ᶠ (- 1F) • M⟨ 1* ⟩ • CX              ≈⟨ ax (ax5 1*) ⟩
  M⟨ 1* ⟩                                  ≈⟨ ax ax1 ⟩
  ε                                        ∎
  where open Width (₂₊ n)

CX-order : (₂₊ n) ⊢ CX ^ p ≈ ε
CX-order {n} = begin
  CX • CX ^ suc p-2                        ≈⟨ sym (Pow.pow-comm (₂₊ n) (suc p-2) refl) ⟩
  CX ^ suc p-2 • CX                        ≈⟨ front CX (refl' (Eq.cong (CX ^_) (Eq.sym toℕ-1))) ⟩
  CX ^ᶠ (- 1F) • CX                        ≈⟨ CX-inverseˡ ⟩
  ε                                        ∎
  where open Width (₂₊ n)

------------------------------------------------------------------------
-- Every generator has a left inverse

grouplike : Grouplike (n VRel,_===_)
grouplike {n} (gate₀ (ω-gate h)) =
  ω h ^ᶠ (- 1F) , Pow.Order.inverseˡ n (ax (ax19 h))
grouplike (gate₁ X-gate) = X ^ᶠ (- 1F) , Pow.Order.inverseˡ _ X-order
grouplike {suc n} (gate₁ (M-gate a na)) = M⟨ unit a na ⁻¹* ⟩ , M-inverseˡ (unit a na)
grouplike (gate₁ (Z-gate h)) = Z h ^ᶠ (- 1F) , Pow.Order.inverseˡ _ (ax (ax20 h))
grouplike (gate₁ (S-gate h)) = S h ^ᶠ (- 1F) , Pow.Order.inverseˡ _ (ax (ax24 h))
grouplike (gate₁ (T-gate h)) = T h ^ᶠ (- 1F) , Pow.Order.inverseˡ _ (ax (ax31 h))
grouplike (gate₂ CX-gate)    = CX ^ᶠ (- 1F) , CX-inverseˡ
grouplike (gate₂ SWAP-gate)  = SWAP , ax swap-order
grouplike (g ↥) with grouplike g
... | ig , prf = ig ↑ , lemma-cong↑ (ig • [ g ]ʷ) ε prf

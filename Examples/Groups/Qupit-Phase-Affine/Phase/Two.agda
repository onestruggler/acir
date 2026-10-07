------------------------------------------------------------------------
-- Presentations of groups
--
-- Two-wire words
--
-- A word on wire 0 only, or on wires 0 and 1 only, is given by a code
-- (One, Two) read at every width.  A one-wire word commutes with
-- everything one wire up and SWAP carries it there; a two-wire word
-- commutes with everything two wires up (two∥), and the cycle
-- σ = SWAP • SWAP ↑ (wire 0 to 1, 1 to 2, 2 to 0) carries it one wire
-- up (two-σ).  So its placement on wires 0 and 2 can be made by either
-- swap (two-place):
--
--     SWAP ↑ • w • SWAP ↑ ≈ SWAP • w ↑ • SWAP.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Two
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Nat.Base using (zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv using (↑-pow)
open import Examples.Groups.Qupit-Phase-Affine.Commute p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (SWAP↑²)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
  using (slide^ ; unslide ; σCX ; sW)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Codes

infixr 7 _⊙¹_ _⊙²_
infix  8 _^¹_ _^²_

-- Words on wire 0.
data One : Set where
  o0   : Gate 0 → One
  o1   : Gate 1 → One
  oε   : One
  _⊙¹_ : One → One → One
  _^¹_ : One → ℕ → One

⟦_⟧¹ : One → Circuit (₁₊ n)
⟦ o0 g ⟧¹    = [ gate₀ g ]ʷ
⟦ o1 g ⟧¹    = [ gate₁ g ]ʷ
⟦ oε ⟧¹      = ε
⟦ a ⊙¹ b ⟧¹  = ⟦ a ⟧¹ • ⟦ b ⟧¹
⟦ a ^¹ m ⟧¹  = ⟦ a ⟧¹ ^ m

-- Words on wires 0 and 1.
data Two : Set where
  t0   : One → Two
  t1   : One → Two
  t2   : Gate 2 → Two
  tε   : Two
  _⊙²_ : Two → Two → Two
  _^²_ : Two → ℕ → Two

⟦_⟧² : Two → Circuit (₂₊ n)
⟦ t0 a ⟧²    = ⟦ a ⟧¹
⟦ t1 a ⟧²    = ⟦ a ⟧¹ ↑
⟦ t2 g ⟧²    = [ gate₂ g ]ʷ
⟦ tε ⟧²      = ε
⟦ a ⊙² b ⟧²  = ⟦ a ⟧² • ⟦ b ⟧²
⟦ a ^² m ⟧²  = ⟦ a ⟧² ^ m

------------------------------------------------------------------------
-- Commuting with words further up

private
  ∥-ε : {w : Circuit n} → n ⊢ ε ∥ w
  ∥-ε = Width.trans Width.left-unit (Width.sym Width.right-unit)

one∥ : (a : One) (w : Circuit n) → (₁₊ n) ⊢ ⟦ a ⟧¹ ∥ (w ↑)
one∥ (o0 g)   w = Width.sym (comm-gate₀-w g (w ↑))
one∥ (o1 g)   w = Width.sym (comm-gate₁-w↑ g w)
one∥ oε       w = ∥-ε
one∥ (a ⊙¹ b) w = •-∥ (one∥ a w) (one∥ b w)
one∥ (a ^¹ m) w = ∥-^ m (one∥ a w)

two∥ : (c : Two) (w : Circuit n) → (₂₊ n) ⊢ ⟦ c ⟧² ∥ (w ↑ ↑)
two∥ (t0 a)   w = one∥ a (w ↑)
two∥ (t1 a)   w = lift (one∥ a w)
two∥ (t2 g)   w = Width.sym (comm-gate₂-w↑↑ g w)
two∥ tε       w = ∥-ε
two∥ (a ⊙² b) w = •-∥ (two∥ a w) (two∥ b w)
two∥ (a ^² m) w = ∥-^ m (two∥ a w)

------------------------------------------------------------------------
-- SWAP and σ carry them up

-- The naturality of SWAP for the gates on wire 0.
swap-gate₁ : (g : Gate 1) → (₂₊ n) ⊢ SWAP • [ gate₁ g ]ʷ ≈ [ gate₁ g ↥ ]ʷ • SWAP
swap-gate₁ {n} g = unslide (ax swap-order) (Width.sym (nat g))
  where
  nat : (g : Gate 1) → (₂₊ n) ⊢ [ gate₁ g ]ʷ • SWAP ≈ SWAP • [ gate₁ g ↥ ]ʷ
  nat X-gate       = ax swap-X
  nat (M-gate a z) = ax (swap-M a z)
  nat (Z-gate h)   = ax (swap-Z h)
  nat (S-gate h)   = ax (swap-S h)
  nat (T-gate h)   = ax (swap-T h)

one-swap : (a : One) → (₂₊ n) ⊢ SWAP • ⟦ a ⟧¹ ≈ ⟦ a ⟧¹ ↑ • SWAP
one-swap {n} (o0 g)   = Width.trans (comm-gate₀-w g SWAP) (Width.front (₂₊ n) SWAP (Width.sym (ax' (ω↑=ω g))))
one-swap (o1 g)       = swap-gate₁ g
one-swap {n} oε       = Width.slide-ε (₂₊ n)
one-swap {n} (a ⊙¹ b) = Width.slide (₂₊ n) (one-swap a) (one-swap b)
one-swap {n} (a ^¹ m) = Width.trans (slide^ m (one-swap a)) (Width.front (₂₊ n) SWAP (Width.refl' (₂₊ n) (Eq.sym (↑-pow ⟦ a ⟧¹ m))))

module _ {n : ℕ} where

  open Width (₃₊ n)

  -- σ = SWAP • SWAP ↑ moves wire 0 to 1, 1 to 2 and 2 to 0.
  σ : Circuit (₃₊ n)
  σ = SWAP • SWAP ↑

  σ⁻ : Circuit (₃₊ n)
  σ⁻ = SWAP ↑ • SWAP

  σσ⁻ : (₃₊ n) ⊢ σ • σ⁻ ≈ ε
  σσ⁻ = trans (by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl)
          (trans (back _ (trans (front _ SWAP↑²) left-unit)) (ax swap-order))

  σ⁻σ : (₃₊ n) ⊢ σ⁻ • σ ≈ ε
  σ⁻σ = trans (by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl)
          (trans (back _ (trans (front _ (ax swap-order)) left-unit)) SWAP↑²)

  private
    σSWAP : (₃₊ n) ⊢ σ • SWAP ≈ SWAP ↑ • σ
    σSWAP = begin
      (SWAP • SWAP ↑) • SWAP      ≈⟨ trans assoc (ax swap-braid) ⟩
      SWAP ↑ • SWAP • SWAP ↑      ∎

  two-σ : (c : Two) → (₃₊ n) ⊢ σ • ⟦ c ⟧² ≈ ⟦ c ⟧² ↑ • σ
  two-σ (t0 a) = begin
    (SWAP • SWAP ↑) • ⟦ a ⟧¹      ≈⟨ trans assoc (back _ (sym (one∥ a SWAP))) ⟩
    SWAP • ⟦ a ⟧¹ • SWAP ↑        ≈⟨ trans (sym assoc) (front _ (one-swap a)) ⟩
    (⟦ a ⟧¹ ↑ • SWAP) • SWAP ↑    ≈⟨ assoc ⟩
    ⟦ a ⟧¹ ↑ • SWAP • SWAP ↑      ∎
  two-σ (t1 a) = begin
    (SWAP • SWAP ↑) • ⟦ a ⟧¹ ↑    ≈⟨ trans assoc (back _ (lift (one-swap a))) ⟩
    SWAP • ⟦ a ⟧¹ ↑ ↑ • SWAP ↑    ≈⟨ trans (sym assoc) (front _ (sW (⟦ a ⟧¹))) ⟩
    (⟦ a ⟧¹ ↑ ↑ • SWAP) • SWAP ↑  ≈⟨ assoc ⟩
    ⟦ a ⟧¹ ↑ ↑ • SWAP • SWAP ↑    ∎
  two-σ (t2 CX-gate)   = σCX
  two-σ (t2 SWAP-gate) = σSWAP
  two-σ tε       = slide-ε
  two-σ (a ⊙² b) = slide (two-σ a) (two-σ b)
  two-σ (a ^² m) = trans (slide^ m (two-σ a)) (front σ (refl' (Eq.sym (↑-pow ⟦ a ⟧² m))))

  -- The placement on wires 0 and 2, by either swap.
  two-place : (c : Two) → (₃₊ n) ⊢ SWAP ↑ • ⟦ c ⟧² • SWAP ↑ ≈ SWAP • ⟦ c ⟧² ↑ • SWAP
  two-place c = begin
    SWAP ↑ • ⟦ c ⟧² • SWAP ↑
      ≈⟨ sym (cancel-in (ax swap-order) _) ⟩
    SWAP • SWAP • SWAP ↑ • ⟦ c ⟧² • SWAP ↑
      ≈⟨ back _ (trans (sym (cancel-at (ax swap-order) _))
                        (by-passoc ((□ • □ • □ • □) • □ • □) ((□ • □) • □ • □ • □ • □) Eq.refl)) ⟩
    SWAP • (SWAP • SWAP ↑) • ⟦ c ⟧² • SWAP ↑ • SWAP • SWAP
      ≈⟨ back _ (trans (sym assoc) (front _ (two-σ c))) ⟩
    SWAP • (⟦ c ⟧² ↑ • SWAP • SWAP ↑) • SWAP ↑ • SWAP • SWAP
      ≈⟨ back _ (by-passoc ((□ • (□ • □)) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl) ⟩
    SWAP • ⟦ c ⟧² ↑ • SWAP • (SWAP ↑ • SWAP ↑) • SWAP • SWAP
      ≈⟨ back _ (back _ (back _ (trans (front _ SWAP↑²) left-unit))) ⟩
    SWAP • ⟦ c ⟧² ↑ • SWAP • SWAP • SWAP
      ≈⟨ back _ (back _ (cancel-in (ax swap-order) _)) ⟩
    SWAP • ⟦ c ⟧² ↑ • SWAP ∎

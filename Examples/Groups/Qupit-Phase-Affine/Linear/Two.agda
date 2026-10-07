------------------------------------------------------------------------
-- Presentations of groups
--
-- Linear circuits on two wires: the multipliers past the reversed
-- controlled addition, and the swap in the big cell
--
-- Writing x(s) = CX ^ᶠ s (x₀ += s x₁), y(s) = CXʳ ^ᶠ s (x₁ += s x₀)
-- and m₀, m₁ for the multipliers on wires 0 and 1:
--
-- * a multiplier scales the label of an addition it meets on the
--   target (M-CXᶠ, M↑-CXʳᶠ) or the control (CXᶠ-M↑, CXʳᶠ-M), and the
--   inverse label the other way round (M-CXʳᶠ, M↑-CXᶠ);
-- * rule (7), SWAP = m₁(-1) y(-1) x(1) y(-1), conjugated by SWAP and
--   then by m₀(-c), is the Weyl relation
--
--     x(c) y(-c⁻¹) x(c) = m₀(c) m₁(-c⁻¹) SWAP              (weyl)
--
--   and with it x(c) m₀(a) SWAP, an element of the big cell, factors
--   as y(c⁻¹) m₁(-a c⁻¹) x(a) m₀(c)                         (bruhat)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Linear.Two
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

import Data.Integer.Base as ℤ
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; F* ; 0F ; 1F ; _+_ ; _*_ ; -_ ; _⁻¹ᶠ ; _⁻¹* ; _⊛_ ; 1* ; -1*
        ; ⁻¹ᶠ-inverseʳ ; ⁻¹ᶠ-inverseˡ ; cancel ; module FR
        ; solve ; _:+_ ; _:*_ ; :-_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv

------------------------------------------------------------------------
-- Labels

private
  -1F : F
  -1F = - 1F

  -- An inverse is unique.
  inv-unique : (c : F) → c ≢ 0F → {d : F} → c * d ≡ 1F → d ≡ c ⁻¹ᶠ
  inv-unique c nc e = cancel c nc (Eq.trans e (Eq.sym (⁻¹ᶠ-inverseʳ c nc)))

  -- s c⁻¹ c = s.
  undo⁻¹ : (s : F) (t : F*) → (s * proj₁ (t ⁻¹*)) * proj₁ t ≡ s
  undo⁻¹ s (t , nt) = begin
    (s * t ⁻¹ᶠ) * t     ≡⟨ FR.*-assoc s (t ⁻¹ᶠ) t ⟩
    s * (t ⁻¹ᶠ * t)     ≡⟨ Eq.cong (s *_) (⁻¹ᶠ-inverseˡ t nt) ⟩
    s * 1F              ≡⟨ FR.*-identityʳ s ⟩
    s                   ∎
    where open Eq.≡-Reasoning

  -- The labels of the Weyl relation.
  neg1² : -1F * -1F ≡ 1F
  neg1² = solve 0 ((:- con (ℤ.+ 1)) :* (:- con (ℤ.+ 1)) := con (ℤ.+ 1)) Eq.refl

  neg-neg : (c : F) → -1F * (-1F * c) ≡ c
  neg-neg c = solve 1 (λ c → (:- con (ℤ.+ 1)) :* ((:- con (ℤ.+ 1)) :* c) := c) Eq.refl c

  -- c i = 1 makes (-c)(-i) = 1, a (-c)(-i) = a, ...
  module _ (c i : F) (ci : c * i ≡ 1F) where

    negs-inv : (-1F * c) * (-1F * i) ≡ 1F
    negs-inv = Eq.trans
      (solve 2 (λ c i → ((:- con (ℤ.+ 1)) :* c) :* ((:- con (ℤ.+ 1)) :* i) := c :* i) Eq.refl c i) ci

    neg-scale : (a : F) → (- c) * (a * (-1F * i)) ≡ a
    neg-scale a = begin
      (- c) * (a * (-1F * i))   ≡⟨ solve 3 (λ c i a → (:- c) :* (a :* ((:- con (ℤ.+ 1)) :* i)) := a :* (c :* i))
                                         Eq.refl c i a ⟩
      a * (c * i)               ≡⟨ Eq.cong (a *_) ci ⟩
      a * 1F                    ≡⟨ FR.*-identityʳ a ⟩
      a                         ∎
      where open Eq.≡-Reasoning

  -- The inverse of -c.
  inv-neg : (c : F*) → 1F * proj₁ ((-1* ⊛ c) ⁻¹*) ≡ - (proj₁ c ⁻¹ᶠ)
  inv-neg (c , nc) = Eq.trans (FR.*-identityˡ _) (Eq.sym (inv-unique (-1F * c) (proj₂ (-1* ⊛ (c , nc)))
    (Eq.trans (solve 2 (λ c i → ((:- con (ℤ.+ 1)) :* c) :* (:- i) := c :* i) Eq.refl c (c ⁻¹ᶠ))
              (⁻¹ᶠ-inverseʳ c nc))))

------------------------------------------------------------------------
-- Multipliers past the additions

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    module OA = Pow.Order (₂₊ n) {CX} CX-order
    module OR = Pow.Order (₂₊ n) {CXʳ} CXʳ-order

  M↑-CXʳᶠ : (t : F*) (s : F) → (₂₊ n) ⊢ M⟨ t ⟩ ↑ • CXʳ ^ᶠ s ≈ CXʳ ^ᶠ (s * proj₁ t) • M⟨ t ⟩ ↑
  M↑-CXʳᶠ t s =
    across (slide (sM t) (slideᶠ s sCX)) (slide (slideᶠ (s * proj₁ t) sCX) (sM t)) (M-CXᶠ t s)

  CXʳᶠ-M : (t : F*) (s : F) → (₂₊ n) ⊢ CXʳ ^ᶠ s • M⟨ t ⟩ ≈ M⟨ t ⟩ • CXʳ ^ᶠ (s * proj₁ t)
  CXʳᶠ-M t s =
    across (slide (slideᶠ s sCX) (sM↑ t)) (slide (sM↑ t) (slideᶠ (s * proj₁ t) sCX)) (CXᶠ-M↑ t s)

  M-CXʳᶠ : (t : F*) (s : F) → (₂₊ n) ⊢ M⟨ t ⟩ • CXʳ ^ᶠ s ≈ CXʳ ^ᶠ (s * proj₁ (t ⁻¹*)) • M⟨ t ⟩
  M-CXʳᶠ t s = sym (trans (CXʳᶠ-M t (s * proj₁ (t ⁻¹*))) (back _ (OR.^ᶠ-≡ (undo⁻¹ s t))))

  M↑-CXᶠ : (t : F*) (s : F) → (₂₊ n) ⊢ M⟨ t ⟩ ↑ • CX ^ᶠ s ≈ CX ^ᶠ (s * proj₁ (t ⁻¹*)) • M⟨ t ⟩ ↑
  M↑-CXᶠ t s = sym (trans (CXᶠ-M↑ t (s * proj₁ (t ⁻¹*))) (back _ (OA.^ᶠ-≡ (undo⁻¹ s t))))

  -- Multipliers on different wires commute, and on one wire multiply.
  M-M↑ : (a b : F*) → (₂₊ n) ⊢ M⟨ a ⟩ • M⟨ b ⟩ ↑ ≈ M⟨ b ⟩ ↑ • M⟨ a ⟩
  M-M↑ a b = sym (comm-gate₁-w↑ (M-gate (proj₁ a) (proj₂ a)) M⟨ b ⟩)

  M↑-M↑ : (a b : F*) → (₂₊ n) ⊢ M⟨ b ⟩ ↑ • M⟨ a ⟩ ↑ ≈ M⟨ a ⊛ b ⟩ ↑
  M↑-M↑ a b = lift (ax (ax2 a b))

  -- A multiplier by a label equal to 1.
  M-one : {a : F*} → proj₁ a ≡ 1F → (₂₊ n) ⊢ M⟨ a ⟩ ↑ ≈ ε
  M-one e = lift (W.trans (W.refl' (M-≡ e)) (ax ax1))
    where module W = Width (₁₊ n)

  ----------------------------------------------------------------------
  -- The Weyl relation

  -- Rule (7) conjugated by SWAP.
  swap-xyx : (₂₊ n) ⊢ SWAP ≈ M⟨ -1* ⟩ • CX ^ᶠ -1F • CXʳ • CX ^ᶠ -1F
  swap-xyx = across refl (slide (sM↑ -1*) (slide sY (slide sCX sY))) (ax ax7)
    where
    sY : (₂₊ n) ⊢ SWAP • (SWAP • CX ^ᶠ -1F • SWAP) ≈ CX ^ᶠ -1F • SWAP
    sY = cancel-in (ax swap-order) _

  weyl : (c : F*) →
    (₂₊ n) ⊢ CX ^ᶠ proj₁ c • CXʳ ^ᶠ (- (proj₁ c ⁻¹ᶠ)) • CX ^ᶠ proj₁ c
           ≈ M⟨ c ⟩ • M⟨ -1* ⊛ c ⁻¹* ⟩ ↑ • SWAP
  weyl c = begin
    CX ^ᶠ proj₁ c • CXʳ ^ᶠ (- (proj₁ c ⁻¹ᶠ)) • CX ^ᶠ proj₁ c
      ≈⟨ cong (OA.^ᶠ-≡ (Eq.sym (neg-neg (proj₁ c))))
              (cong (OR.^ᶠ-≡ (Eq.sym (inv-neg c))) (OA.^ᶠ-≡ (Eq.sym (neg-neg (proj₁ c))))) ⟩
    CX ^ᶠ (-1F * proj₁ t) • CXʳ ^ᶠ (1F * proj₁ (t ⁻¹*)) • CX ^ᶠ (-1F * proj₁ t)
      ≈⟨ across (slide (M-CXᶠ t -1F) (slide (M-CXʳᶠ t 1F) (M-CXᶠ t -1F))) conj-rhs xyx ⟩
    M⟨ c ⟩ • M⟨ -1* ⊛ c ⁻¹* ⟩ ↑ • SWAP ∎
    where
    t : F*
    t = -1* ⊛ c
    v : F*
    v = -1* ⊛ c ⁻¹*

    mm : (₂₊ n) ⊢ M⟨ -1* ⟩ • M⟨ -1* ⟩ ≈ ε
    mm = trans (ax (ax2 -1* -1*)) (trans (refl' (M-≡ neg1²)) (ax ax1))

    -- x(-1) y(1) x(-1) = m₀(-1) SWAP.
    xyx : (₂₊ n) ⊢ CX ^ᶠ -1F • CXʳ • CX ^ᶠ -1F ≈ M⟨ -1* ⟩ • SWAP
    xyx = sym (begin
      M⟨ -1* ⟩ • SWAP                                          ≈⟨ back _ swap-xyx ⟩
      M⟨ -1* ⟩ • M⟨ -1* ⟩ • CX ^ᶠ -1F • CXʳ • CX ^ᶠ -1F         ≈⟨ cancel-in mm _ ⟩
      CX ^ᶠ -1F • CXʳ • CX ^ᶠ -1F                              ∎)

    -- Both sides of the conjugated relation are m₀(c) SWAP.
    conj-rhs : (₂₊ n) ⊢ M⟨ t ⟩ • M⟨ -1* ⟩ • SWAP ≈ (M⟨ c ⟩ • M⟨ v ⟩ ↑ • SWAP) • M⟨ t ⟩
    conj-rhs = begin
      M⟨ t ⟩ • M⟨ -1* ⟩ • SWAP                    ≈⟨ trans (sym assoc) (front _ (ax (ax2 -1* t))) ⟩
      M⟨ -1* ⊛ t ⟩ • SWAP                         ≈⟨ front _ (refl' (M-≡ (neg-neg (proj₁ c)))) ⟩
      M⟨ c ⟩ • SWAP                               ≈⟨ back _ (sym left-unit) ⟩
      M⟨ c ⟩ • ε • SWAP                           ≈⟨ back _ (front _ (sym (M-one {t ⊛ v} tv))) ⟩
      M⟨ c ⟩ • M⟨ t ⊛ v ⟩ ↑ • SWAP                ≈⟨ back _ (front _ (sym (M↑-M↑ t v))) ⟩
      M⟨ c ⟩ • (M⟨ v ⟩ ↑ • M⟨ t ⟩ ↑) • SWAP       ≈⟨ back _ (trans assoc (back _ (sym (sM t)))) ⟩
      M⟨ c ⟩ • M⟨ v ⟩ ↑ • SWAP • M⟨ t ⟩           ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
      (M⟨ c ⟩ • M⟨ v ⟩ ↑ • SWAP) • M⟨ t ⟩         ∎
      where
      tv : proj₁ (t ⊛ v) ≡ 1F
      tv = negs-inv (proj₁ c) (proj₁ c ⁻¹ᶠ) (⁻¹ᶠ-inverseʳ (proj₁ c) (proj₂ c))

  -- The big cell: x(c) m₀(a) SWAP = y(c⁻¹) m₁(-a c⁻¹) x(a) m₀(c).
  bruhat : (c a : F*) →
    (₂₊ n) ⊢ CX ^ᶠ proj₁ c • M⟨ a ⟩ • SWAP
           ≈ CXʳ ^ᶠ (proj₁ c ⁻¹ᶠ) • M⟨ a ⊛ (-1* ⊛ c ⁻¹*) ⟩ ↑ • CX ^ᶠ proj₁ a • M⟨ c ⟩
  bruhat c a = begin
    CX ^ᶠ k • M⟨ a ⟩ • SWAP
      ≈⟨ sym (cancel-in (OR.^ᶠ-inverseʳ i) _) ⟩
    CXʳ ^ᶠ i • CXʳ ^ᶠ (- i) • CX ^ᶠ k • M⟨ a ⟩ • SWAP
      ≈⟨ back _ (sym (cancel-in (OA.^ᶠ-inverseˡ k) _)) ⟩
    CXʳ ^ᶠ i • CX ^ᶠ (- k) • CX ^ᶠ k • CXʳ ^ᶠ (- i) • CX ^ᶠ k • M⟨ a ⟩ • SWAP
      ≈⟨ back _ (back _ (by-passoc (□ • □ • □ • □ • □) ((□ • □ • □) • □ • □) Eq.refl)) ⟩
    CXʳ ^ᶠ i • CX ^ᶠ (- k) • (CX ^ᶠ k • CXʳ ^ᶠ (- i) • CX ^ᶠ k) • M⟨ a ⟩ • SWAP
      ≈⟨ back _ (back _ (front _ (weyl c))) ⟩
    CXʳ ^ᶠ i • CX ^ᶠ (- k) • (M⟨ c ⟩ • M⟨ v ⟩ ↑ • SWAP) • M⟨ a ⟩ • SWAP
      ≈⟨ back _ (back _ (by-passoc ((□ • □ • □) • □ • □) (□ • □ • (□ • □ • □)) Eq.refl)) ⟩
    CXʳ ^ᶠ i • CX ^ᶠ (- k) • M⟨ c ⟩ • M⟨ v ⟩ ↑ • (SWAP • M⟨ a ⟩ • SWAP)
      ≈⟨ back _ (back _ (back _ (back _ (Involution.conj← (ax swap-order) (sM a))))) ⟩
    CXʳ ^ᶠ i • CX ^ᶠ (- k) • M⟨ c ⟩ • M⟨ v ⟩ ↑ • M⟨ a ⟩ ↑
      ≈⟨ back _ (back _ (back _ (M↑-M↑ a v))) ⟩
    CXʳ ^ᶠ i • CX ^ᶠ (- k) • M⟨ c ⟩ • M⟨ u ⟩ ↑
      ≈⟨ back _ (back _ (M-M↑ c u)) ⟩
    CXʳ ^ᶠ i • CX ^ᶠ (- k) • M⟨ u ⟩ ↑ • M⟨ c ⟩
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (CXᶠ-M↑ u (- k))) assoc)) ⟩
    CXʳ ^ᶠ i • M⟨ u ⟩ ↑ • CX ^ᶠ (- k * proj₁ u) • M⟨ c ⟩
      ≈⟨ back _ (back _ (front _ (OA.^ᶠ-≡ (neg-scale k i (⁻¹ᶠ-inverseʳ k (proj₂ c)) (proj₁ a))))) ⟩
    CXʳ ^ᶠ i • M⟨ u ⟩ ↑ • CX ^ᶠ proj₁ a • M⟨ c ⟩ ∎
    where
    k = proj₁ c
    i = proj₁ c ⁻¹ᶠ
    v = -1* ⊛ c ⁻¹*
    u = a ⊛ v

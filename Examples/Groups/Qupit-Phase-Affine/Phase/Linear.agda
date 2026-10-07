------------------------------------------------------------------------
-- Presentations of groups
--
-- Linear phases: ω, Z, and the columns of Z's
--
-- From level 1 on there is the scalar ω, central and of order p, and
-- Z, of order p (rules (19), (20)).  Z moves past the affine
-- generators by substituting into its phase x₀:
--
-- * a multiplier scales it (rule (22), Zᶠ-M);
-- * X shifts it, leaving a scalar (rule (23), Zᶠ-Xᶠ);
-- * on the target of CX it picks up Z on the control (rule (21));
-- * on the control of CX it commutes with it (Z↑-CX, the paper's
--   ZC-control): conjugating by M₋₁ on the control inverts both CX
--   (rule (4)) and Z (rule (22)), which turns rule (21) around;
-- * SWAP moves it a wire.
--
-- A column Zc c = Z^(c₀) on wire 0, Z^(c₁) on wire 1, … has phase c · x;
-- a linear generator turns it into the column of c Y (Z-push), a
-- translation by v leaves the scalar ω^(c · v) (Zc-Xc), and columns add.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Linear
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 1 ≤ lv) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Nat.DivMod using (_%_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; F* ; p ; 0F ; 1F ; _+_ ; _*_ ; -_ ; -1* ; toℕ-* ; module FR
        ; solve ; _:+_ ; _:*_ ; :-_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Two p-2 p-prime lv using (M↑-M↑)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; pass)
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv using (Xc)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Semantics p-2 p-prime lv
  using () renaming (dot to dot′)

private
  variable
    n : ℕ

  -- A word sliding leftwards past iterates.
  slideʳ^ : ∀ {m} {g a b : Circuit m} (k : ℕ) → m ⊢ a • g ≈ g • b → m ⊢ a ^ k • g ≈ g • b ^ k
  slideʳ^ {m} k e = W.sym (slide^ k (W.sym e))
    where module W = Width m

------------------------------------------------------------------------
-- The scalar

module _ {n : ℕ} where

  open Width n

  ω-comm : (w : Circuit n) → n ⊢ ω h • w ≈ w • ω h
  ω-comm w = sym (comm-gate₀-w (ω-gate h) w)

  ω-order : n ⊢ ω h ^ p ≈ ε
  ω-order = ax (ax19 h)

  ωᶠ-comm : (s : F) (w : Circuit n) → n ⊢ ω h ^ᶠ s • w ≈ w • ω h ^ᶠ s
  ωᶠ-comm s w = Pow.pow-comm n (toℕ s) (ω-comm w)

  ω^-comm : (k : ℕ) (w : Circuit n) → n ⊢ ω h ^ k • w ≈ w • ω h ^ k
  ω^-comm k w = Pow.pow-comm n k (ω-comm w)

ω↑ : (₁₊ n) ⊢ (ω h) ↑ ≈ ω h
ω↑ = ax' (ω↑=ω (ω-gate h))

ωᶠ↑ : (s : F) → (₁₊ n) ⊢ (ω h ^ᶠ s) ↑ ≈ ω h ^ᶠ s
ωᶠ↑ {n} s = trans (refl' (↑ᶠ (ω h) s)) (Pow.pow-cong (₁₊ n) (toℕ s) ω↑)
  where open Width (₁₊ n)

------------------------------------------------------------------------
-- Z on one wire

module _ {n : ℕ} where

  open Width (₁₊ n)

  Z-order : (₁₊ n) ⊢ Z h ^ p ≈ ε
  Z-order = ax (ax20 h)

  private
    module OZ = Pow.Order (₁₊ n) {Z h} Z-order
    module OW = Pow.Order (₁₊ n) {ω h} ω-order
    module OX = Pow.Order (₁₊ n) {X} X-order

  -- Rule (22): a multiplier scales Z.
  Zᶠ-M : (c : F) (x : F*) → (₁₊ n) ⊢ Z h ^ᶠ c • M⟨ x ⟩ ≈ M⟨ x ⟩ • Z h ^ᶠ (c * proj₁ x)
  Zᶠ-M c x = trans (slideʳ^ (toℕ c) (ax (ax22 h x)))
                   (back _ (trans (OZ.^ᶠ-* (proj₁ x) c) (OZ.^ᶠ-≡ (FR.*-comm _ c))))

  -- Rule (23): X shifts Z, leaving the scalar.
  Z-X : (₁₊ n) ⊢ Z h • X ≈ X • Z h • ω h
  Z-X = trans (ax (ax23 h)) (trans (ω-comm _) assoc)

  private
    Z-X^ : (m : ℕ) → (₁₊ n) ⊢ Z h • X ^ m ≈ X ^ m • Z h • ω h ^ m
    Z-X^ zero    = trans right-unit (sym (trans left-unit right-unit))
    Z-X^ (suc m) = begin
      Z h • X ^ suc m                        ≈⟨ back _ (Pow.pow-suc (₁₊ n) X m) ⟩
      Z h • X • X ^ m                        ≈⟨ trans (sym assoc) (front _ Z-X) ⟩
      (X • Z h • ω h) • X ^ m                ≈⟨ trans assoc (back _ (trans assoc (back _ (ω-comm _)))) ⟩
      X • Z h • X ^ m • ω h                  ≈⟨ back _ (trans (sym assoc) (front _ (Z-X^ m))) ⟩
      X • (X ^ m • Z h • ω h ^ m) • ω h      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
      (X • X ^ m) • Z h • ω h ^ m • ω h      ≈⟨ cong (sym (Pow.pow-suc (₁₊ n) X m))
                                                   (back _ (trans (ω^-comm m (ω h)) (sym (Pow.pow-suc (₁₊ n) (ω h) m)))) ⟩
      X ^ suc m • Z h • ω h ^ suc m          ∎

    Z^-X^ : (k m : ℕ) → (₁₊ n) ⊢ Z h ^ k • X ^ m ≈ X ^ m • Z h ^ k • ω h ^ (k ℕ.* m)
    Z^-X^ zero    m = trans left-unit (sym (trans (back _ left-unit) right-unit))
    Z^-X^ (suc k) m = begin
      Z h ^ suc k • X ^ m                                ≈⟨ front _ (Pow.pow-suc (₁₊ n) (Z h) k) ⟩
      (Z h • Z h ^ k) • X ^ m                            ≈⟨ trans assoc (back _ (Z^-X^ k m)) ⟩
      Z h • X ^ m • Z h ^ k • ω h ^ (k ℕ.* m)            ≈⟨ trans (sym assoc) (front _ (Z-X^ m)) ⟩
      (X ^ m • Z h • ω h ^ m) • Z h ^ k • ω h ^ (k ℕ.* m)
        ≈⟨ by-passoc ((□ • □ • □) • □ • □) (□ • □ • (□ • □) • □) Eq.refl ⟩
      X ^ m • Z h • (ω h ^ m • Z h ^ k) • ω h ^ (k ℕ.* m)
        ≈⟨ back _ (back _ (front _ (ω^-comm m _))) ⟩
      X ^ m • Z h • (Z h ^ k • ω h ^ m) • ω h ^ (k ℕ.* m)
        ≈⟨ back _ (by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl) ⟩
      X ^ m • (Z h • Z h ^ k) • ω h ^ m • ω h ^ (k ℕ.* m)
        ≈⟨ back _ (cong (sym (Pow.pow-suc (₁₊ n) (Z h) k)) (sym (Pow.pow-+ (₁₊ n) (ω h) m (k ℕ.* m)))) ⟩
      X ^ m • Z h ^ suc k • ω h ^ (m ℕ.+ k ℕ.* m)        ∎

  Zᶠ-Xᶠ : (c d : F) → (₁₊ n) ⊢ Z h ^ᶠ c • X ^ᶠ d ≈ X ^ᶠ d • Z h ^ᶠ c • ω h ^ᶠ (c * d)
  Zᶠ-Xᶠ c d = trans (Z^-X^ (toℕ c) (toℕ d))
    (back _ (back _ (trans (OW.pow-mod (toℕ c ℕ.* toℕ d)) (refl' (Eq.cong (ω h ^_) (Eq.sym (toℕ-* c d)))))))

  -- Z on wire 0 commutes with everything one wire up.
  Zᶠ-up : (c : F) (w : Circuit n) → (₁₊ n) ⊢ Z h ^ᶠ c • w ↑ ≈ w ↑ • Z h ^ᶠ c
  Zᶠ-up c w = Pow.pow-comm (₁₊ n) (toℕ c) (sym (comm-gate₁-w↑ (Z-gate h) w))

------------------------------------------------------------------------
-- Z and the two-wire gates

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    module OZ = Pow.Order (₁₊ n) {Z h} Z-order
    m C : Circuit (₂₊ n)
    m = M⟨ -1* ⟩ ↑
    C = CX

    mm : (₂₊ n) ⊢ m • m ≈ ε
    mm = trans (lift (ax (ax2 -1* -1*))) (lift (W1.trans (W1.refl' (M-≡ neg1²)) (ax ax1)))
      where
      module W1 = Width (₁₊ n)
      neg1² : - 1F * - 1F ≡ 1F
      neg1² = solve 0 ((:- con (ℤ.+ 1)) :* (:- con (ℤ.+ 1)) := con (ℤ.+ 1)) Eq.refl

    -- Rule (4) at -1: M₋₁ on the control inverts CX.
    Cm : (₂₊ n) ⊢ C • m ≈ m • CX ^ᶠ (- 1F)
    Cm = ax (ax4 -1*)

    mCm : (₂₊ n) ⊢ m • C • m ≈ CX ^ᶠ (- 1F)
    mCm = trans (back _ Cm) (cancel-in mm _)

    Ci-m : (₂₊ n) ⊢ CX ^ᶠ (- 1F) • m ≈ m • C
    Ci-m = begin
      CX ^ᶠ (- 1F) • m          ≈⟨ front _ (sym mCm) ⟩
      (m • C • m) • m           ≈⟨ trans assoc (back _ (trans assoc (back _ mm))) ⟩
      m • C • ε                 ≈⟨ back _ right-unit ⟩
      m • C                     ∎

    -- Rule (22) at -1, one wire up: m Z↑ m = Z↑⁻¹.
    Zi↑ : (₂₊ n) ⊢ (Z h ^ᶠ (- 1F)) ↑ ≈ m • Z h ↑ • m
    Zi↑ = sym (trans (back _ (lift (ax (ax22 h -1*)))) (cancel-in mm _))

    -- Rule (21), read as C Z = Z C Z↑⁻¹.
    CZ₀ : (₂₊ n) ⊢ C • Z h ≈ Z h • C • (Z h ^ᶠ (- 1F)) ↑
    CZ₀ = begin
      C • Z h                                ≈⟨ back _ (sym right-unit) ⟩
      C • Z h • ε                            ≈⟨ back _ (back _ (sym (lift (OZ.^ᶠ-inverseʳ 1F)))) ⟩
      C • Z h • Z h ↑ • (Z h ^ᶠ (- 1F)) ↑    ≈⟨ trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl)
                                                     (front _ (ax (ax21 h))) ⟩
      (Z h • C) • (Z h ^ᶠ (- 1F)) ↑          ≈⟨ assoc ⟩
      Z h • C • (Z h ^ᶠ (- 1F)) ↑            ∎

    Z∥Z↑ : (₂₊ n) ⊢ Z h • Z h ↑ ≈ Z h ↑ • Z h
    Z∥Z↑ = sym (comm-gate₁-w↑ (Z-gate h) (Z h))

    m∥Z : (₂₊ n) ⊢ m • Z h ≈ Z h • m
    m∥Z = comm-gate₁-w↑ (Z-gate h) M⟨ -1* ⟩

  -- The paper's ZC-control: Z on the control of CX commutes with it.
  Z↑-CX : (₂₊ n) ⊢ CX • Z h ↑ ≈ Z h ↑ • CX
  Z↑-CX = begin
    C • Z₁
      ≈⟨ back _ (sym (trans (back _ inv₀) right-unit)) ⟩
    C • Z₁ • Z₀ • Zi₀
      ≈⟨ trans (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) (front _ t21) ⟩
    (Z₀ • C) • Zi₀
      ≈⟨ trans assoc (sym (trans (front _ pre) left-unit)) ⟩
    (Z₁ • C • Ci • Zi₁) • Z₀ • C • Zi₀
      ≈⟨ by-passoc ((□ • □ • □ • □) • □ • □ • □) (□ • □ • □ • □ • □ • □ • □) Eq.refl ⟩
    Z₁ • C • Ci • Zi₁ • Z₀ • C • Zi₀
      ≈⟨ back _ (back _ (back _ (front _ Zi↑))) ⟩
    Z₁ • C • Ci • (m • Z₁ • m) • Z₀ • C • Zi₀
      ≈⟨ by-passoc (□ • □ • □ • (□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □ • □ • □ • □) Eq.refl ⟩
    Z₁ • C • (Ci • m) • Z₁ • m • Z₀ • C • Zi₀
      ≈⟨ back _ (back _ (front _ Ci-m)) ⟩
    Z₁ • C • (m • C) • Z₁ • m • Z₀ • C • Zi₀
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □ • □ • □ • □) (□ • □ • □ • □ • □ • (□ • □) • □ • □) Eq.refl ⟩
    Z₁ • C • m • C • Z₁ • (m • Z₀) • C • Zi₀
      ≈⟨ back _ (back _ (back _ (back _ (back _ (front _ m∥Z))))) ⟩
    Z₁ • C • m • C • Z₁ • (Z₀ • m) • C • Zi₀
      ≈⟨ by-passoc (□ • □ • □ • □ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □ • □) • □ • □ • □) Eq.refl ⟩
    Z₁ • C • m • (C • Z₁ • Z₀) • m • C • Zi₀
      ≈⟨ back _ (back _ (back _ (front _ t21))) ⟩
    Z₁ • C • m • (Z₀ • C) • m • C • Zi₀
      ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □ • □ • □) Eq.refl ⟩
    Z₁ • C • (m • Z₀) • C • m • C • Zi₀
      ≈⟨ back _ (back _ (front _ m∥Z)) ⟩
    Z₁ • C • (Z₀ • m) • C • m • C • Zi₀
      ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □ • □ • □) (□ • □ • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
    Z₁ • C • Z₀ • (m • C • m) • C • Zi₀
      ≈⟨ back _ (back _ (back _ (front _ mCm))) ⟩
    Z₁ • C • Z₀ • Ci • C • Zi₀
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (trans (front _ (CX-invˡ 1F)) left-unit)))) ⟩
    Z₁ • C • Z₀ • Zi₀
      ≈⟨ back _ (back _ inv₀) ⟩
    Z₁ • C • ε
      ≈⟨ back _ right-unit ⟩
    Z₁ • C ∎
    where
    module OZ' = Pow.Order (₂₊ n) {Z h} Z-order
    Z₀ Z₁ Zi₀ Zi₁ Ci : Circuit (₂₊ n)
    Z₀ = Z h
    Z₁ = Z h ↑
    Zi₀ = Z h ^ᶠ (- 1F)
    Zi₁ = (Z h ^ᶠ (- 1F)) ↑
    Ci = CX ^ᶠ (- 1F)
    inv₀ : (₂₊ n) ⊢ Z₀ • Zi₀ ≈ ε
    inv₀ = OZ'.^ᶠ-inverseʳ 1F
    -- Rule (21) with the Z's in either order.
    t21 : (₂₊ n) ⊢ C • Z₁ • Z₀ ≈ Z₀ • C
    t21 = trans (back _ (sym Z∥Z↑)) (ax (ax21 h))
    pre : (₂₊ n) ⊢ Z₁ • C • Ci • Zi₁ ≈ ε
    pre = begin
      Z₁ • C • Ci • Zi₁       ≈⟨ back _ (trans (sym assoc) (trans (front _ (CX-invʳ 1F)) left-unit)) ⟩
      Z₁ • Zi₁                ≈⟨ lift (OZ.^ᶠ-inverseʳ 1F) ⟩
      ε                       ∎

------------------------------------------------------------------------
-- Presentations of groups
--
-- Atoms of S: S on a linear form of the labels
--
-- A ℓ = (r ℓ)⁻¹ • S • r ℓ multiplies |x⟩ by ω^(ℓ·x choose 2)
-- (Phase.Atom).  S commutes with every atom (S∥A): the atom of a row
-- without x₀ lives one wire up, and for ℓ = (a, w) the fan-in R w is
-- CX conjugated by the representative of w one wire up (CX-r), so the
-- atom is P = CX⁻¹ S CX conjugated by that representative and by M_a,
-- and S and Z pass all three (M_a turning S into S and Z, rule (27)).
-- So any two atoms commute (A∥A), as do atoms and columns of Z's
-- (Zc∥A).  An iterate of an atom passes a translation, leaving a column
-- of Z's and a power of ω (A-Xc): rule (25) iterated (S-Xᶠ), conjugated.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Quad.Atom
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 2 ≤ lv) (odd : 1 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; head)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; F* ; 0F ; 1F ; _+_ ; _-_ ; _*_ ; -_ ; _⁻¹* ; binom2 ; half ; _×ᶠ_ ; ×ᶠ-toℕ ; module FR ; module Odd
        ; solve ; _:+_ ; _:*_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv using (_⁻¹ ; module Inv ; M-inverseʳ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Base p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv using (CX-invʳ)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Fan p-2 p-prime lv using (0ᵛ ; R-zero)
open import Examples.Groups.Qupit-Phase-Affine.Linear.Rows p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Affine p-2 p-prime lv using (Xc ; _⋆ˣ*_)
open import Examples.Groups.Qupit-Phase-Affine.Phase.Atom p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.CZ p-2 p-prime lv h odd public

open Atoms (S-gate h) S∥CXʳ (ax (swap-S h)) public

private
  variable
    n : ℕ

  h₁ : 1 ≤ lv
  h₁ = lin₂ h

module _ {m : ℕ} where

  open Width m

  -- Commuting with a word equal to X.
  via : {a X X' : Circuit m} → m ⊢ X ≈ X' → m ⊢ a ∥ X' → m ⊢ a ∥ X
  via e c = trans (back _ e) (trans c (front _ (sym e)))

------------------------------------------------------------------------
-- S past a multiplier, the other way

-- The exponents rule (27) gives at a⁻¹.
sq⁻ β⁻ : F* → F
sq⁻ a = 1F * (proj₁ (a ⁻¹*) * proj₁ (a ⁻¹*))
β⁻ a = 1F * binom2 (proj₁ (a ⁻¹*))

module _ {n : ℕ} where

  open Width (₁₊ n)

  M⁻¹≈ : (a : F*) → (₁₊ n) ⊢ M⟨ a ⟩ ⁻¹ ≈ M⟨ a ⁻¹* ⟩
  M⁻¹≈ a = sym (Inv.inverseʳ-unique (₁₊ n) (M-inverseʳ a))

  S-M⁻¹ : (a : F*) → (₁₊ n) ⊢ S h • M⟨ a ⟩ ⁻¹ ≈ M⟨ a ⟩ ⁻¹ • SZ (sq⁻ a) (β⁻ a)
  S-M⁻¹ a = begin
    S h • M⟨ a ⟩ ⁻¹                            ≈⟨ back _ (M⁻¹≈ a) ⟩
    S h • M⟨ a ⁻¹* ⟩                           ≈⟨ Sᶠ-M 1F (a ⁻¹*) ⟩
    M⟨ a ⁻¹* ⟩ • Z h₁ ^ᶠ β⁻ a • S h ^ᶠ sq⁻ a   ≈⟨ cong (sym (M⁻¹≈ a)) (sym (Sᶠ∥Zᶠ (sq⁻ a) (β⁻ a))) ⟩
    M⟨ a ⟩ ⁻¹ • SZ (sq⁻ a) (β⁻ a)              ∎

  M-S : (a : F*) → (₁₊ n) ⊢ M⟨ a ⟩ • S h ≈ SZ (sq⁻ a) (β⁻ a) • M⟨ a ⟩
  M-S a = trans (front _ (sym (Inv.⁻¹-involutive (₁₊ n))))
            (trans (flip⁻¹ (S-M⁻¹ a)) (back _ (Inv.⁻¹-involutive (₁₊ n))))

  -- S and Z on wire 0 pass whatever is one wire up, and S.
  SZ-up : (q b : F) (w : Circuit n) → (₁₊ n) ⊢ SZ q b ∥ (w ↑)
  SZ-up q b w = •-∥ (Sᶠ-up q w) (Zᶠ-up b w)

  SZ∥S : (q b : F) → (₁₊ n) ⊢ SZ q b ∥ S h
  SZ∥S q b = •-∥ (∥-^ᶠ q refl) (∥-^ᶠ b (∥-sym S∥Z))

module _ {n : ℕ} where

  SZ∥P : (q b : F) → (₂₊ n) ⊢ SZ q b ∥ P
  SZ∥P q b = •-∥ (∥-^ᶠ q S∥P) (∥-^ᶠ b Z∥P)

------------------------------------------------------------------------
-- S commutes with every atom

-- S conjugated by a fan-in commutes with S and Z on wire 0.
SZ∥Y : (q b : F) (w : Vec F n) → (₁₊ n) ⊢ SZ q b ∥ (R w ⁻¹ • S h • R w)
SZ∥Y {zero} q b [] = via (Width.trans Width.left-unit Width.right-unit) (SZ∥S q b)
SZ∥Y {suc m} q b w with nz? w
... | inj₁ e = via Y≈S (SZ∥S q b)
  where
  open Width (₂₊ m)
  Rε : (₂₊ m) ⊢ R w ≈ ε
  Rε = Eq.subst (λ v → (₂₊ m) ⊢ R v ≈ ε) (Eq.sym e) R-zero
  Y≈S : (₂₊ m) ⊢ R w ⁻¹ • S h • R w ≈ S h
  Y≈S = trans (cong (Inv.⁻¹-cong (₂₊ m) Rε) (back _ Rε)) (trans left-unit right-unit)
... | inj₂ (ℓ' , e) = via Y≈ (∥-• SZ∥ρ⁻¹ (∥-• (SZ∥P q b) (SZ-up q b (r ℓ'))))
  where
  open Width (₂₊ m)
  ρ : Circuit (₂₊ m)
  ρ = r ℓ' ↑
  SZ∥ρ⁻¹ : (₂₊ m) ⊢ SZ q b ∥ ρ ⁻¹
  SZ∥ρ⁻¹ = via (refl' (⁻¹-↑ (r ℓ'))) (SZ-up q b (r ℓ' ⁻¹))
  RT : (₂₊ m) ⊢ R w ≈ ρ ⁻¹ • CX • ρ
  RT = trans (refl' (Eq.cong R (Eq.sym e)))
         (sym (trans (back _ (CX-r ℓ')) (trans (sym assoc) (trans (front _ (Inv.inverseˡ (₂₊ m))) left-unit))))
  ρSρ⁻¹ : (₂₊ m) ⊢ ρ • S h • ρ ⁻¹ ≈ S h
  ρSρ⁻¹ = trans (sym assoc) (trans (front _ (sym (Sᶠ-up 1F (r ℓ'))))
            (trans assoc (trans (back _ (Inv.inverseʳ (₂₊ m))) right-unit)))
  CX⁻¹≈ : (₂₊ m) ⊢ CX ⁻¹ ≈ CX ^ᶠ (- 1F)
  CX⁻¹≈ = sym (Inv.inverseʳ-unique (₂₊ m) (CX-invʳ 1F))
  Y≈ : (₂₊ m) ⊢ R w ⁻¹ • S h • R w ≈ ρ ⁻¹ • P • ρ
  Y≈ = begin
    R w ⁻¹ • S h • R w
      ≈⟨ cong (Inv.⁻¹-cong (₂₊ m) RT) (back _ RT) ⟩
    ((ρ ⁻¹ • CX ⁻¹) • ρ ⁻¹ ⁻¹) • S h • ρ ⁻¹ • CX • ρ
      ≈⟨ front _ (back _ (Inv.⁻¹-involutive (₂₊ m))) ⟩
    ((ρ ⁻¹ • CX ⁻¹) • ρ) • S h • ρ ⁻¹ • CX • ρ
      ≈⟨ by-passoc (((□ • □) • □) • □ • □ • □ • □) (□ • □ • (□ • □ • □) • □ • □) Eq.refl ⟩
    ρ ⁻¹ • CX ⁻¹ • (ρ • S h • ρ ⁻¹) • CX • ρ
      ≈⟨ back _ (cong CX⁻¹≈ (front _ ρSρ⁻¹)) ⟩
    ρ ⁻¹ • CX ^ᶠ (- 1F) • S h • CX • ρ
      ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
    ρ ⁻¹ • P • ρ ∎

S∥A : (ℓ : NZ (₁₊ n)) → (₁₊ n) ⊢ S h ∥ A ℓ
S∥A (small ℓ) = via (A-small ℓ) (Sᶠ-up 1F (A ℓ))
S∥A {n} (big a w) = begin
  S h • (Mi • R w ⁻¹) • S h • R w • M⟨ a ⟩
    ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) ((□ • □) • (□ • □ • □) • □) Eq.refl ⟩
  (S h • Mi) • Y • M⟨ a ⟩
    ≈⟨ front _ (S-M⁻¹ a) ⟩
  (Mi • W) • Y • M⟨ a ⟩
    ≈⟨ trans assoc (back _ (trans (sym assoc) (front _ (SZ∥Y (sq⁻ a) (β⁻ a) w)))) ⟩
  Mi • (Y • W) • M⟨ a ⟩
    ≈⟨ back _ (trans assoc (back _ (sym (M-S a)))) ⟩
  Mi • Y • M⟨ a ⟩ • S h
    ≈⟨ by-passoc (□ • (□ • □ • □) • □ • □) (((□ • □) • □ • □ • □) • □) Eq.refl ⟩
  ((Mi • R w ⁻¹) • S h • R w • M⟨ a ⟩) • S h ∎
  where
  open Width (₁₊ n)
  Mi W Y : Circuit (₁₊ n)
  Mi = M⟨ a ⟩ ⁻¹
  W  = SZ (sq⁻ a) (β⁻ a)
  Y  = R w ⁻¹ • S h • R w

-- So atoms commute.
A∥A : (ℓ ℓ' : NZ (₁₊ n)) → (₁₊ n) ⊢ A ℓ ∥ A ℓ'
A∥A ℓ ℓ' = conj-into ℓ (A ℓ') (via (rr⁻¹ ℓ ℓ') (S∥A (ℓ' ⋆* linv (rL ℓ))))

------------------------------------------------------------------------
-- Atoms and columns of Z's

Zc-conj : (ℓ : NZ (₁₊ n)) (c : Vec F (₁₊ n)) → (₁₊ n) ⊢ r ℓ • Zc c • r ℓ ⁻¹ ≈ Zc (c ⋆ᴿ* linv (rL ℓ))
Zc-conj {n} ℓ c = begin
  r ℓ • Zc c • r ℓ ⁻¹                  ≈⟨ back _ (back _ (sym (⌊linv-rL⌋ ℓ))) ⟩
  r ℓ • Zc c • ⌊ L ⌋                   ≈⟨ back _ (Z-push* L c) ⟩
  r ℓ • ⌊ L ⌋ • Zc (c ⋆ᴿ* L)           ≈⟨ trans (sym assoc) (trans (front _ (trans (back _ (⌊linv-rL⌋ ℓ)) (Inv.inverseʳ (₁₊ n)))) left-unit) ⟩
  Zc (c ⋆ᴿ* L)                         ∎
  where
  open Width (₁₊ n)
  L = linv (rL ℓ)

-- A column conjugated by a representative.
Zc-rconj : (ℓ : NZ (₁₊ n)) (c : Vec F (₁₊ n)) → (₁₊ n) ⊢ r ℓ ⁻¹ • Zc c • r ℓ ≈ Zc (c ⋆ᴿ* rL ℓ)
Zc-rconj {n} ℓ c = begin
  r ℓ ⁻¹ • Zc c • r ℓ                  ≈⟨ back _ Zr ⟩
  r ℓ ⁻¹ • r ℓ • Zc (c ⋆ᴿ* rL ℓ)       ≈⟨ trans (sym assoc) (trans (front _ (Inv.inverseˡ (₁₊ n))) left-unit) ⟩
  Zc (c ⋆ᴿ* rL ℓ)                      ∎
  where
  open Width (₁₊ n)
  Zr : (₁₊ n) ⊢ Zc c • r ℓ ≈ r ℓ • Zc (c ⋆ᴿ* rL ℓ)
  Zr = Eq.subst (λ q → (₁₊ n) ⊢ Zc c • q ≈ q • Zc (c ⋆ᴿ* rL ℓ)) (⌊rL⌋ ℓ) (Z-push* (rL ℓ) c)

S∥Zc : (c : Vec F (₁₊ n)) → (₁₊ n) ⊢ S h ∥ Zc c
S∥Zc (c ∷ cs) = ∥-• (Sᶠ∥Zᶠ 1F c) (Sᶠ-up 1F (Zc cs))

Zc∥A : (c : Vec F (₁₊ n)) (ℓ : NZ (₁₊ n)) → (₁₊ n) ⊢ Zc c ∥ A ℓ
Zc∥A c ℓ = ∥-sym (conj-into ℓ (Zc c) (via (Zc-conj ℓ c) (S∥Zc _)))

------------------------------------------------------------------------
-- Atoms past translations

module _ {n : ℕ} where

  open Width (₁₊ n)

  private
    module OZ = Pow.Order (₁₊ n) {Z h₁} Z-order
    module OW = Pow.Order (₁₊ n) {ω h₁} ω-order

    m̂ : ℕ → F
    m̂ m = m ×ᶠ 1F

    X-split : (m : ℕ) → (₁₊ n) ⊢ X ^ suc m ≈ X ^ m • X
    X-split m = trans (refl' (Eq.cong (X ^_) (ℕP.+-comm 1 m))) (Pow.pow-+ (₁₊ n) X m 1)

    zero* : (k : F) → k * 0F ≡ 0F
    zero* = FR.zeroʳ

    binom2-0 : binom2 0F ≡ 0F
    binom2-0 = Eq.trans (Eq.cong (_* half) (FR.zeroˡ (0F - 1F))) (FR.zeroˡ half)

    z-step : (k c : F) → k + k * c ≡ k * (1F + c)
    z-step = solve 2 (λ k c → k :+ k :* c := k :* (con (ℤ.+ 1) :+ c)) Eq.refl

    t-step : (k c : F) → (k * c) * 1F + k * binom2 c ≡ k * binom2 (1F + c)
    t-step k c = Eq.trans (solve 3 (λ k c b → (k :* c) :* con (ℤ.+ 1) :+ k :* b := k :* (b :+ c)) Eq.refl k c (binom2 c))
                   (Eq.cong (k *_) (Eq.trans (Eq.sym (Odd.binom2-shift odd c)) (Eq.cong binom2 (FR.+-comm c 1F))))

  -- Rule (25) iterated.
  S-X^ : (k : F) (m : ℕ) →
         (₁₊ n) ⊢ S h ^ᶠ k • X ^ m ≈ X ^ m • S h ^ᶠ k • Z h₁ ^ᶠ (k * m̂ m) • ω h₁ ^ᶠ (k * binom2 (m̂ m))
  S-X^ k zero = sym (trans left-unit (back _ (trans (cong (OZ.^ᶠ-≡ (zero* k)) (OW.^ᶠ-≡ (Eq.trans (Eq.cong (k *_) binom2-0) (zero* k))))
                                                (trans left-unit refl))))
  S-X^ k (suc m) = begin
    S h ^ᶠ k • X ^ suc m
      ≈⟨ back _ (X-split m) ⟩
    S h ^ᶠ k • X ^ m • X
      ≈⟨ trans (sym assoc) (front _ (S-X^ k m)) ⟩
    (X ^ m • S h ^ᶠ k • Z h₁ ^ᶠ z • ω h₁ ^ᶠ t) • X
      ≈⟨ by-passoc ((□ • □ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
    X ^ m • S h ^ᶠ k • Z h₁ ^ᶠ z • ω h₁ ^ᶠ t • X
      ≈⟨ back _ (back _ (back _ (ωᶠ-comm t X))) ⟩
    X ^ m • S h ^ᶠ k • Z h₁ ^ᶠ z • X • ω h₁ ^ᶠ t
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (Zᶠ-Xᶠ z 1F)) assoc))) ⟩
    X ^ m • S h ^ᶠ k • X • (Z h₁ ^ᶠ z • ω h₁ ^ᶠ (z * 1F)) • ω h₁ ^ᶠ t
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (Sᶠ-X k)) assoc)) ⟩
    X ^ m • X • (Z h₁ ^ᶠ k • S h ^ᶠ k) • (Z h₁ ^ᶠ z • ω h₁ ^ᶠ (z * 1F)) • ω h₁ ^ᶠ t
      ≈⟨ back _ (back _ (front _ (sym (Sᶠ∥Zᶠ k k)))) ⟩
    X ^ m • X • (S h ^ᶠ k • Z h₁ ^ᶠ k) • (Z h₁ ^ᶠ z • ω h₁ ^ᶠ (z * 1F)) • ω h₁ ^ᶠ t
      ≈⟨ by-passoc (□ • □ • (□ • □) • (□ • □) • □) ((□ • □) • □ • (□ • □) • □ • □) Eq.refl ⟩
    (X ^ m • X) • S h ^ᶠ k • (Z h₁ ^ᶠ k • Z h₁ ^ᶠ z) • ω h₁ ^ᶠ (z * 1F) • ω h₁ ^ᶠ t
      ≈⟨ cong (sym (X-split m)) (back _ (cong (trans (OZ.^ᶠ-+ k z) (OZ.^ᶠ-≡ (z-step k (m̂ m))))
                                           (trans (OW.^ᶠ-+ (z * 1F) t) (OW.^ᶠ-≡ (t-step k (m̂ m)))))) ⟩
    X ^ suc m • S h ^ᶠ k • Z h₁ ^ᶠ (k * m̂ (suc m)) • ω h₁ ^ᶠ (k * binom2 (m̂ (suc m))) ∎
    where
    z t : F
    z = k * m̂ m
    t = k * binom2 (m̂ m)

  S-Xᶠ : (k a : F) → (₁₊ n) ⊢ S h ^ᶠ k • X ^ᶠ a ≈ X ^ᶠ a • S h ^ᶠ k • Z h₁ ^ᶠ (k * a) • ω h₁ ^ᶠ (k * binom2 a)
  S-Xᶠ k a = Eq.subst (λ c → (₁₊ n) ⊢ S h ^ᶠ k • X ^ᶠ a ≈ X ^ᶠ a • S h ^ᶠ k • Z h₁ ^ᶠ (k * c) • ω h₁ ^ᶠ (k * binom2 c))
                      (Eq.trans (×ᶠ-toℕ a 1F) (FR.*-identityʳ a)) (S-X^ k (toℕ a))

  -- S^k past a translation.
  S-Xc : (k : F) (v : Vec F (₁₊ n)) →
         (₁₊ n) ⊢ S h ^ᶠ k • Xc v ≈ Xc v • S h ^ᶠ k • (Z h₁ ^ᶠ (k * head v) • ω h₁ ^ᶠ (k * binom2 (head v)))
  S-Xc k (a ∷ vs) = begin
    S h ^ᶠ k • X ^ᶠ a • Xc vs ↑
      ≈⟨ trans (sym assoc) (trans (front _ (S-Xᶠ k a)) assoc) ⟩
    X ^ᶠ a • (S h ^ᶠ k • D) • Xc vs ↑
      ≈⟨ back _ (•-∥ (Sᶠ-up k (Xc vs)) (•-∥ (Zᶠ-up (k * a) (Xc vs)) (ωᶠ-comm _ _))) ⟩
    X ^ᶠ a • Xc vs ↑ • S h ^ᶠ k • D
      ≈⟨ sym assoc ⟩
    (X ^ᶠ a • Xc vs ↑) • S h ^ᶠ k • D ∎
    where
    D = Z h₁ ^ᶠ (k * a) • ω h₁ ^ᶠ (k * binom2 a)

  -- An iterate of an atom past a translation.
  A-Xc : (ℓ : NZ (₁₊ n)) (k : F) (b : Vec F (₁₊ n)) →
         (₁₊ n) ⊢ A ℓ ^ᶠ k • Xc b ≈
                  Xc b • A ℓ ^ᶠ k • Zc ((k * head (b ⋆ˣ* rL ℓ) ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • ω h₁ ^ᶠ (k * binom2 (head (b ⋆ˣ* rL ℓ)))
  A-Xc ℓ k b = begin
    A ℓ ^ᶠ k • Xc b
      ≈⟨ front _ (A-^ ℓ (toℕ k)) ⟩
    (ρ ⁻¹ • S h ^ᶠ k • ρ) • Xc b
      ≈⟨ conj-X ℓ b (S-Xc k (b ⋆ˣ* rL ℓ)) ⟩
    Xc b • (ρ ⁻¹ • S h ^ᶠ k • ρ) • ρ ⁻¹ • (Z h₁ ^ᶠ c • ω h₁ ^ᶠ t) • ρ
      ≈⟨ back _ (cong (sym (A-^ ℓ (toℕ k))) D≈) ⟩
    Xc b • A ℓ ^ᶠ k • Zc ((c ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • ω h₁ ^ᶠ t ∎
    where
    ρ : Circuit (₁₊ n)
    ρ = r ℓ
    v₀ c t : F
    v₀ = head (b ⋆ˣ* rL ℓ)
    c  = k * v₀
    t  = k * binom2 v₀
    Z≈ : (₁₊ n) ⊢ Z h₁ ^ᶠ c ≈ Zc (c ∷ 0ᵛ)
    Z≈ = sym (trans (back _ (lift Zc-zero)) right-unit)
    D≈ : (₁₊ n) ⊢ ρ ⁻¹ • (Z h₁ ^ᶠ c • ω h₁ ^ᶠ t) • ρ ≈ Zc ((c ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • ω h₁ ^ᶠ t
    D≈ = begin
      ρ ⁻¹ • (Z h₁ ^ᶠ c • ω h₁ ^ᶠ t) • ρ        ≈⟨ back _ (trans assoc (back _ (ωᶠ-comm t ρ))) ⟩
      ρ ⁻¹ • Z h₁ ^ᶠ c • ρ • ω h₁ ^ᶠ t          ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
      (ρ ⁻¹ • Z h₁ ^ᶠ c • ρ) • ω h₁ ^ᶠ t        ≈⟨ front _ (trans (back _ (front _ Z≈)) (Zc-rconj ℓ (c ∷ 0ᵛ))) ⟩
      Zc ((c ∷ 0ᵛ) ⋆ᴿ* rL ℓ) • ω h₁ ^ᶠ t        ∎

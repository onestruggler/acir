------------------------------------------------------------------------
-- Presentations of groups
--
-- Cubic phases: T, and its gadget with CX
--
-- From level 3 on there is T, of order p (rule (31)), commuting with S
-- and Z (rules (33), (36)), and commuting with CX when on its control
-- (rule (39)), hence also on the control of CXʳ.  It moves past a
-- multiplier into S, Z and T (rule (32)), and past X into T and S (rule
-- (34)); iterating, an iterate T^k past X^m leaves S^(km), Z^(k (m
-- choose 2)) and ω^(k (m choose 3)) (T-X^, T-Xᶠ).  So T is a gate of
-- Phase.Gadget:
--
--     PT = CX⁻¹ • T • CX = CXʳ⁻¹ • T ↑ • CXʳ           (PT≈PT′)
--
-- and every word S^q Z^b T^t on wire 0 commutes with P and PT (STZ∥P,
-- STZ∥PT): it passes CXʳ, and anything one wire up.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Phase.Cube.T
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) (h : 3 ≤ lv) (gt3 : 2 ≤ p-2) where

import Data.Integer.Base as ℤ
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using ( F ; F* ; p ; 0F ; 1F ; 2F ; _+_ ; _-_ ; _*_ ; -_ ; -1* ; binom2 ; binom3 ; half ; sixth ; _×ᶠ_ ; ×ᶠ-toℕ
        ; big⇒odd ; module FR ; module Odd ; module Big ; solve ; _:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con )
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Lib p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Linear.Wires p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Phase.Gadget p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Phase.Quad.CZ p-2 p-prime lv (quad₃ h) (big⇒odd gt3)

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
-- T on one wire

module _ {n : ℕ} where

  open Width (₁₊ n)

  -- Rule (31).
  T-order : (₁₊ n) ⊢ T h ^ p ≈ ε
  T-order = ax (ax31 h)

  -- Rules (33) and (36).
  T∥S : (₁₊ n) ⊢ T h ∥ S h₂
  T∥S = ax (ax33 h)

  T∥Z : (₁₊ n) ⊢ T h ∥ Z h₁
  T∥Z = ax (ax36 h)

  -- On wire 0, T commutes with everything one wire up.
  Tᶠ-up : (t : F) (w : Circuit n) → (₁₊ n) ⊢ (T h ^ᶠ t) ∥ (w ↑)
  Tᶠ-up t w = ∥-^ᶠ t (sym (comm-gate₁-w↑ (T-gate h) w))

  -- Rule (32): a multiplier scales T.
  T-M : (x : F*) → (₁₊ n) ⊢ T h • M⟨ x ⟩ ≈
        M⟨ x ⟩ • S h₂ ^ᶠ (2F * proj₁ x * binom2 (proj₁ x)) • Z h₁ ^ᶠ binom3 (proj₁ x) • T h ^ᶠ (proj₁ x * proj₁ x * proj₁ x)
  T-M x = sym (ax (ax32 h x))

  -- Rule (34): X shifts T.
  Tᶠ-X : (k : F) → (₁₊ n) ⊢ T h ^ᶠ k • X ≈ X • T h ^ᶠ k • S h₂ ^ᶠ k
  Tᶠ-X k = begin
    T h ^ᶠ k • X                     ≈⟨ sym (slideᶠ k (sym (ax (ax34 h)))) ⟩
    X • (T h • S h₂) ^ᶠ k            ≈⟨ back _ (Pow.pow-• (₁₊ n) (toℕ k) T∥S) ⟩
    X • T h ^ᶠ k • S h₂ ^ᶠ k         ∎

  private
    module OS = Pow.Order (₁₊ n) {S h₂} S-order
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

    binom3-0 : binom3 0F ≡ 0F
    binom3-0 = Eq.trans (Eq.cong (λ t → (t * (0F - 2F)) * sixth) (FR.zeroˡ (0F - 1F)))
                 (Eq.trans (Eq.cong (_* sixth) (FR.zeroˡ (0F - 2F))) (FR.zeroˡ sixth))

    b2-step : (k c : F) → k * c + k * binom2 c ≡ k * binom2 (1F + c)
    b2-step k c = Eq.trans (solve 3 (λ k c b → k :* c :+ k :* b := k :* (b :+ c)) Eq.refl k c (binom2 c))
                    (Eq.cong (k *_) (Eq.trans (Eq.sym (Odd.binom2-shift odd c)) (Eq.cong binom2 (FR.+-comm c 1F))))

    b3-step : (k c : F) → (k * binom2 c) * 1F + k * binom3 c ≡ k * binom3 (1F + c)
    b3-step k c = Eq.trans (solve 3 (λ k b2 b3 → (k :* b2) :* con (ℤ.+ 1) :+ k :* b3 := k :* (b3 :+ b2)) Eq.refl k (binom2 c) (binom3 c))
                    (Eq.cong (k *_) (Eq.trans (Eq.sym (Big.binom3-shift gt3 c)) (Eq.cong binom3 (FR.+-comm c 1F))))

    s-step : (k c : F) → k + k * c ≡ k * (1F + c)
    s-step = solve 2 (λ k c → k :+ k :* c := k :* (con (ℤ.+ 1) :+ c)) Eq.refl

  -- Rule (34) iterated.
  T-X^ : (k : F) (m : ℕ) → (₁₊ n) ⊢ T h ^ᶠ k • X ^ m ≈
         X ^ m • T h ^ᶠ k • S h₂ ^ᶠ (k * m̂ m) • Z h₁ ^ᶠ (k * binom2 (m̂ m)) • ω h₁ ^ᶠ (k * binom3 (m̂ m))
  T-X^ k zero = sym (trans left-unit (back _ (trans (cong (OS.^ᶠ-≡ (zero* k))
                  (cong (OZ.^ᶠ-≡ (Eq.trans (Eq.cong (k *_) binom2-0) (zero* k)))
                        (OW.^ᶠ-≡ (Eq.trans (Eq.cong (k *_) binom3-0) (zero* k)))))
                  (trans left-unit (trans left-unit refl)))))
  T-X^ k (suc m) = begin
    T h ^ᶠ k • X ^ suc m
      ≈⟨ back _ (X-split m) ⟩
    T h ^ᶠ k • X ^ m • X
      ≈⟨ trans (sym assoc) (front _ (T-X^ k m)) ⟩
    (X ^ m • T h ^ᶠ k • S h₂ ^ᶠ s • Z h₁ ^ᶠ b • ω h₁ ^ᶠ t) • X
      ≈⟨ by-passoc ((□ • □ • □ • □ • □) • □) (□ • □ • □ • □ • □ • □) Eq.refl ⟩
    X ^ m • T h ^ᶠ k • S h₂ ^ᶠ s • Z h₁ ^ᶠ b • ω h₁ ^ᶠ t • X
      ≈⟨ back _ (back _ (back _ (back _ (ωᶠ-comm t X)))) ⟩
    X ^ m • T h ^ᶠ k • S h₂ ^ᶠ s • Z h₁ ^ᶠ b • X • ω h₁ ^ᶠ t
      ≈⟨ back _ (back _ (back _ (trans (sym assoc) (trans (front _ (Zᶠ-Xᶠ b 1F)) assoc)))) ⟩
    X ^ m • T h ^ᶠ k • S h₂ ^ᶠ s • X • (Z h₁ ^ᶠ b • ω h₁ ^ᶠ (b * 1F)) • ω h₁ ^ᶠ t
      ≈⟨ back _ (back _ (trans (sym assoc) (trans (front _ (Sᶠ-X s)) assoc))) ⟩
    X ^ m • T h ^ᶠ k • X • (Z h₁ ^ᶠ s • S h₂ ^ᶠ s) • (Z h₁ ^ᶠ b • ω h₁ ^ᶠ (b * 1F)) • ω h₁ ^ᶠ t
      ≈⟨ back _ (trans (sym assoc) (trans (front _ (Tᶠ-X k)) assoc)) ⟩
    X ^ m • X • (T h ^ᶠ k • S h₂ ^ᶠ k) • (Z h₁ ^ᶠ s • S h₂ ^ᶠ s) • (Z h₁ ^ᶠ b • ω h₁ ^ᶠ (b * 1F)) • ω h₁ ^ᶠ t
      ≈⟨ by-passoc (□ • □ • (□ • □) • (□ • □) • (□ • □) • □) ((□ • □) • □ • □ • (□ • □) • □ • □ • □) Eq.refl ⟩
    (X ^ m • X) • T h ^ᶠ k • S h₂ ^ᶠ k • (Z h₁ ^ᶠ s • S h₂ ^ᶠ s) • Z h₁ ^ᶠ b • ω h₁ ^ᶠ (b * 1F) • ω h₁ ^ᶠ t
      ≈⟨ back _ (back _ (back _ (front _ (sym (Sᶠ∥Zᶠ s s))))) ⟩
    (X ^ m • X) • T h ^ᶠ k • S h₂ ^ᶠ k • (S h₂ ^ᶠ s • Z h₁ ^ᶠ s) • Z h₁ ^ᶠ b • ω h₁ ^ᶠ (b * 1F) • ω h₁ ^ᶠ t
      ≈⟨ back _ (back _ (by-passoc (□ • (□ • □) • □ • □ • □) ((□ • □) • (□ • □) • (□ • □)) Eq.refl)) ⟩
    (X ^ m • X) • T h ^ᶠ k • (S h₂ ^ᶠ k • S h₂ ^ᶠ s) • (Z h₁ ^ᶠ s • Z h₁ ^ᶠ b) • (ω h₁ ^ᶠ (b * 1F) • ω h₁ ^ᶠ t)
      ≈⟨ cong (sym (X-split m)) (back _ (cong (trans (OS.^ᶠ-+ k s) (OS.^ᶠ-≡ (s-step k (m̂ m))))
                                      (cong (trans (OZ.^ᶠ-+ s b) (OZ.^ᶠ-≡ (b2-step k (m̂ m))))
                                            (trans (OW.^ᶠ-+ (b * 1F) t) (OW.^ᶠ-≡ (b3-step k (m̂ m))))))) ⟩
    X ^ suc m • T h ^ᶠ k • S h₂ ^ᶠ (k * m̂ (suc m)) • Z h₁ ^ᶠ (k * binom2 (m̂ (suc m))) • ω h₁ ^ᶠ (k * binom3 (m̂ (suc m))) ∎
    where
    s b t : F
    s = k * m̂ m
    b = k * binom2 (m̂ m)
    t = k * binom3 (m̂ m)

  T-Xᶠ : (k a : F) → (₁₊ n) ⊢ T h ^ᶠ k • X ^ᶠ a ≈
         X ^ᶠ a • T h ^ᶠ k • S h₂ ^ᶠ (k * a) • Z h₁ ^ᶠ (k * binom2 a) • ω h₁ ^ᶠ (k * binom3 a)
  T-Xᶠ k a = Eq.subst (λ c → (₁₊ n) ⊢ T h ^ᶠ k • X ^ᶠ a ≈
                               X ^ᶠ a • T h ^ᶠ k • S h₂ ^ᶠ (k * c) • Z h₁ ^ᶠ (k * binom2 c) • ω h₁ ^ᶠ (k * binom3 c))
                      (Eq.trans (×ᶠ-toℕ a 1F) (FR.*-identityʳ a)) (T-X^ k (toℕ a))

------------------------------------------------------------------------
-- Words of S, Z and T on wire 0

module _ {n : ℕ} where

  open Width (₁₊ n)

  STZ : F → F → F → Circuit (₁₊ n)
  STZ q b t = S h₂ ^ᶠ q • Z h₁ ^ᶠ b • T h ^ᶠ t

  STZ-up : (q b t : F) (w : Circuit n) → (₁₊ n) ⊢ STZ q b t ∥ (w ↑)
  STZ-up q b t w = •-∥ (Sᶠ-up q w) (•-∥ (Zᶠ-up b w) (Tᶠ-up t w))

  -- The words commute with S and T.
  STZ∥S : (q b t : F) → (₁₊ n) ⊢ STZ q b t ∥ S h₂
  STZ∥S q b t = •-∥ (∥-^ᶠ q refl) (•-∥ (∥-^ᶠ b (∥-sym S∥Z)) (∥-^ᶠ t T∥S))

  STZ∥T : (q b t : F) → (₁₊ n) ⊢ STZ q b t ∥ T h
  STZ∥T q b t = •-∥ (∥-^ᶠ q (∥-sym T∥S)) (•-∥ (∥-^ᶠ b (∥-sym T∥Z)) (∥-^ᶠ t refl))

  -- S past a multiplier is such a word.
  S-STZ : (q b : F) → (₁₊ n) ⊢ SZ q b ≈ STZ q b 0F
  S-STZ q b = back _ (sym right-unit)

------------------------------------------------------------------------
-- T and the two-wire gates

module _ {n : ℕ} where

  open Width (₂₊ n)

  private
    ss : (₂₊ n) ⊢ SWAP • SWAP ≈ ε
    ss = ax swap-order

  -- Rule (39): T on the control of CX.
  T↑-CX : (₂₊ n) ⊢ CX • T h ↑ ≈ T h ↑ • CX
  T↑-CX = ax (ax39 h)

  sT : (₂₊ n) ⊢ SWAP • T h ≈ T h ↑ • SWAP
  sT = unslide ss (sym (ax (swap-T h)))

  sT↑ : (₂₊ n) ⊢ SWAP • T h ↑ ≈ T h • SWAP
  sT↑ = sym (ax (swap-T h))

  T∥CXʳ : (₂₊ n) ⊢ T h • CXʳ ≈ CXʳ • T h
  T∥CXʳ = across (slide sT↑ sCX) (slide sCX sT↑) (sym T↑-CX)

  T∥T↑ : (₂₊ n) ⊢ T h ∥ T h ↑
  T∥T↑ = sym (comm-gate₁-w↑ (T-gate h) (T h))

  -- The gadget of T.
  PT : Circuit (₂₊ n)
  PT = CX ^ᶠ (- 1F) • T h • CX

  PT′ : Circuit (₂₊ n)
  PT′ = CXʳ ^ᶠ (- 1F) • T h ↑ • CXʳ

  PT≈PT′ : (₂₊ n) ⊢ PT ≈ PT′
  PT≈PT′ = begin
    CX ^ᶠ (- 1F) • T h • CX           ≈⟨ back _ (gadget T∥CXʳ (sym (comm-gate₁-w↑ (T-gate h) M⟨ -1* ⟩)) (ax (swap-T h))) ⟩
    CX ^ᶠ (- 1F) • CX • PT′           ≈⟨ cancel-in (CX-invˡ 1F) _ ⟩
    PT′                               ∎

  PT^ : (k : ℕ) → (₂₊ n) ⊢ PT ^ k ≈ CX ^ᶠ (- 1F) • T h ^ k • CX
  PT^ = conj-pow (CX-invˡ 1F) (CX-invʳ 1F)

  -- A gate passing CXʳ passes CXʳ⁻¹ w ↑ CXʳ.
  ∥-gad : {G : Circuit (₂₊ n)} (w : Circuit (₁₊ n)) → (₂₊ n) ⊢ G ∥ CXʳ → (₂₊ n) ⊢ G ∥ (w ↑) →
          (₂₊ n) ⊢ G ∥ (CXʳ ^ᶠ (- 1F) • w ↑ • CXʳ)
  ∥-gad w gc gw = ∥-• (∥-sym (∥-^ᶠ (- 1F) (∥-sym gc))) (∥-• gw gc)

  STZ∥CXʳ : (q b t : F) → (₂₊ n) ⊢ STZ q b t ∥ CXʳ
  STZ∥CXʳ q b t = •-∥ (∥-^ᶠ q S∥CXʳ) (•-∥ (∥-^ᶠ b Z∥CXʳ) (∥-^ᶠ t T∥CXʳ))

  -- The words pass both gadgets.
  STZ∥P : (q b t : F) → (₂₊ n) ⊢ STZ q b t ∥ P
  STZ∥P q b t = trans (back _ P≈P′) (trans (∥-gad (S h₂) (STZ∥CXʳ q b t) (STZ-up q b t (S h₂))) (front _ (sym P≈P′)))

  STZ∥PT : (q b t : F) → (₂₊ n) ⊢ STZ q b t ∥ PT
  STZ∥PT q b t = trans (back _ PT≈PT′) (trans (∥-gad (T h) (STZ∥CXʳ q b t) (STZ-up q b t (T h))) (front _ (sym PT≈PT′)))

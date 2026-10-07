------------------------------------------------------------------------
-- Presentations of groups
--
-- Identities of linear circuits on two and three wires
--
-- Notation, in operator order (the right letter acts first):
--
--     CX       x₀ += x₁          CX₂₀     x₀ += x₂
--     CX ↑     x₁ += x₂          M⟨ x ⟩   x₀ := x x₀
--
-- * Iterates of CX add their labels (CX-+), and the multipliers move
--   past CX by scaling the label: on the target (M-CXᶠ, rule (5)) and
--   on the control (CXᶠ-M↑, rule (4)).
-- * The commutator relation (8), b a c = a b for a = CX, b = CX ↑,
--   c = CX₂₀, together with its conjugates by multipliers, gives the
--   two commutations of the Steinberg relations: CX₂₀ commutes with
--   CX (same target, XX-comm) and with CX ↑ (same control, XX2-comm)
--   (the paper's Lemmas 22 and 23).  For p odd, conjugating (8) by M₂
--   gives b a² c² = a² b, from which the commutations follow; for
--   p = 2 they follow from c² = id instead.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Linear.Lib
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc ; s≤s ; z≤n)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

import Data.Nat.Properties as ℕP

open import Notations using (₁₊ ; ₃₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; F* ; p ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; _⁻¹* ; _⊛_ ; 1* ; ×ᶠ-toℕ ; _×ᶠ_
        ; two≢0 ; module FR ; ⁻¹ᶠ-inverseʳ ; ⁻¹ᶠ-inverseˡ)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Iterates of CX

module _ {n : ℕ} where

  open Width (₂₊ n)
  private module O = Pow.Order (₂₊ n) {CX} CX-order

  CX-+ : (k l : F) → (₂₊ n) ⊢ CX ^ᶠ k • CX ^ᶠ l ≈ CX ^ᶠ (k + l)
  CX-+ = O.^ᶠ-+

  CX-invˡ : (k : F) → (₂₊ n) ⊢ CX ^ᶠ (- k) • CX ^ᶠ k ≈ ε
  CX-invˡ = O.^ᶠ-inverseˡ

  CX-invʳ : (k : F) → (₂₊ n) ⊢ CX ^ᶠ k • CX ^ᶠ (- k) ≈ ε
  CX-invʳ = O.^ᶠ-inverseʳ

  CX-≡ : {k l : F} → k ≡ l → (₂₊ n) ⊢ CX ^ᶠ k ≈ CX ^ᶠ l
  CX-≡ = O.^ᶠ-≡

------------------------------------------------------------------------
-- Multipliers past CX

module _ {n : ℕ} where

  open Width (₂₊ n)

  -- On the target (rule (5)).
  M-CX : (x : F*) → (₂₊ n) ⊢ M⟨ x ⟩ • CX ≈ CX ^ᶠ proj₁ x • M⟨ x ⟩
  M-CX x = begin
    M⟨ x ⟩ • CX                                   ≈⟨ sym left-unit ⟩
    ε • M⟨ x ⟩ • CX                               ≈⟨ front _ (sym (CX-invʳ (proj₁ x))) ⟩
    (CX ^ᶠ proj₁ x • CX ^ᶠ (- proj₁ x)) • M⟨ x ⟩ • CX ≈⟨ assoc ⟩
    CX ^ᶠ proj₁ x • CX ^ᶠ (- proj₁ x) • M⟨ x ⟩ • CX ≈⟨ back _ (ax (ax5 x)) ⟩
    CX ^ᶠ proj₁ x • M⟨ x ⟩                        ∎

  M-CX^ : (x : F*) (m : ℕ) → (₂₊ n) ⊢ M⟨ x ⟩ • CX ^ m ≈ CX ^ᶠ (m ×ᶠ proj₁ x) • M⟨ x ⟩
  M-CX^ x zero    = trans right-unit (sym left-unit)
  M-CX^ x (suc m) = begin
    M⟨ x ⟩ • CX ^ suc m                           ≈⟨ back _ (Pow.pow-suc (₂₊ n) CX m) ⟩
    M⟨ x ⟩ • CX • CX ^ m                          ≈⟨ sym assoc ⟩
    (M⟨ x ⟩ • CX) • CX ^ m                        ≈⟨ front _ (M-CX x) ⟩
    (CX ^ᶠ proj₁ x • M⟨ x ⟩) • CX ^ m             ≈⟨ assoc ⟩
    CX ^ᶠ proj₁ x • M⟨ x ⟩ • CX ^ m               ≈⟨ back _ (M-CX^ x m) ⟩
    CX ^ᶠ proj₁ x • CX ^ᶠ (m ×ᶠ proj₁ x) • M⟨ x ⟩ ≈⟨ sym assoc ⟩
    (CX ^ᶠ proj₁ x • CX ^ᶠ (m ×ᶠ proj₁ x)) • M⟨ x ⟩ ≈⟨ front _ (CX-+ (proj₁ x) (m ×ᶠ proj₁ x)) ⟩
    CX ^ᶠ (proj₁ x + m ×ᶠ proj₁ x) • M⟨ x ⟩       ∎

  M-CXᶠ : (x : F*) (k : F) → (₂₊ n) ⊢ M⟨ x ⟩ • CX ^ᶠ k ≈ CX ^ᶠ (k * proj₁ x) • M⟨ x ⟩
  M-CXᶠ x k = trans (M-CX^ x (toℕ k)) (front _ (CX-≡ (×ᶠ-toℕ k (proj₁ x))))

  -- On the control (rule (4)).
  CX^-M↑ : (x : F*) (m : ℕ) → (₂₊ n) ⊢ CX ^ m • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ • CX ^ᶠ (m ×ᶠ proj₁ x)
  CX^-M↑ x zero    = trans left-unit (sym right-unit)
  CX^-M↑ x (suc m) = begin
    CX ^ suc m • M⟨ x ⟩ ↑                         ≈⟨ front _ (Pow.pow-suc (₂₊ n) CX m) ⟩
    (CX • CX ^ m) • M⟨ x ⟩ ↑                      ≈⟨ assoc ⟩
    CX • CX ^ m • M⟨ x ⟩ ↑                        ≈⟨ back _ (CX^-M↑ x m) ⟩
    CX • M⟨ x ⟩ ↑ • CX ^ᶠ (m ×ᶠ proj₁ x)          ≈⟨ sym assoc ⟩
    (CX • M⟨ x ⟩ ↑) • CX ^ᶠ (m ×ᶠ proj₁ x)        ≈⟨ front _ (ax (ax4 x)) ⟩
    (M⟨ x ⟩ ↑ • CX ^ᶠ proj₁ x) • CX ^ᶠ (m ×ᶠ proj₁ x) ≈⟨ assoc ⟩
    M⟨ x ⟩ ↑ • CX ^ᶠ proj₁ x • CX ^ᶠ (m ×ᶠ proj₁ x) ≈⟨ back _ (CX-+ (proj₁ x) (m ×ᶠ proj₁ x)) ⟩
    M⟨ x ⟩ ↑ • CX ^ᶠ (proj₁ x + m ×ᶠ proj₁ x)     ∎

  CXᶠ-M↑ : (x : F*) (k : F) → (₂₊ n) ⊢ CX ^ᶠ k • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ • CX ^ᶠ (k * proj₁ x)
  CXᶠ-M↑ x k = trans (CX^-M↑ x (toℕ k)) (back _ (CX-≡ (×ᶠ-toℕ k (proj₁ x))))

------------------------------------------------------------------------
-- Conjugating an equation

module _ {m : ℕ} where

  open Width m

  -- If g h ≈ ε, conjugation by g preserves equations, and an equation
  -- u g ≈ g v, read the other way.
  conj-≈ : {g h u v : Circuit m} → g • h ≈ ε → h • g ≈ ε → u • g ≈ g • v → h • u • g ≈ v
  conj-≈ {g} {h} {u} {v} gh hg e = begin
    h • u • g          ≈⟨ back h e ⟩
    h • g • v          ≈⟨ cancel-in hg v ⟩
    v                  ∎

------------------------------------------------------------------------
-- The Steinberg commutations, as group algebra
--
-- For any words a, b, c with the commutator relation b a c = a b:
-- c commutes with a if also b a² c² = a² b (from conjugating by M₂ on
-- the target), with b if also b² a c² = a b² (by M₂ on the common
-- control), and with both if a, b, c are involutions (p = 2).

module Steinberg {m : ℕ} {a b c : Circuit m} (F1 : m ⊢ b • a • c ≈ a • b) where

  open Width m
  open Inv m using (inverseˡ ; inverseʳ ; •-cancelˡ ; •-cancelʳ)

  private
    ba : m ⊢ b • a ≈ a • b • c ⁻¹
    ba = begin
      b • a                       ≈⟨ sym right-unit ⟩
      (b • a) • ε                 ≈⟨ back _ (sym inverseʳ) ⟩
      (b • a) • c • c ⁻¹          ≈⟨ by-passoc ((□ • □) • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
      (b • a • c) • c ⁻¹          ≈⟨ front _ F1 ⟩
      (a • b) • c ⁻¹              ≈⟨ assoc ⟩
      a • b • c ⁻¹                ∎

  comm-F2 : m ⊢ b • (a • a) • (c • c) ≈ (a • a) • b → m ⊢ a • c ≈ c • a
  comm-F2 F2 = sym (begin
      c • a                       ≈⟨ back c a≈ ⟩
      c • c ⁻¹ • a • c            ≈⟨ sym assoc ⟩
      (c • c ⁻¹) • a • c          ≈⟨ front _ inverseʳ ⟩
      ε • a • c                   ≈⟨ left-unit ⟩
      a • c                       ∎)
    where
    step : m ⊢ a • b ≈ b • c ⁻¹ • a • c • c
    step = •-cancelˡ (begin
      a • a • b                   ≈⟨ sym assoc ⟩
      (a • a) • b                 ≈⟨ sym F2 ⟩
      b • (a • a) • (c • c)       ≈⟨ by-passoc (□ • (□ • □) • (□ • □)) ((□ • □) • □ • □ • □) Eq.refl ⟩
      (b • a) • a • c • c         ≈⟨ front _ ba ⟩
      (a • b • c ⁻¹) • a • c • c  ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • □ • □ • □ • □) Eq.refl ⟩
      a • b • c ⁻¹ • a • c • c    ∎)
    ac : m ⊢ a • c ≈ c ⁻¹ • a • c • c
    ac = •-cancelˡ (trans F1 step)
    a≈ : m ⊢ a ≈ c ⁻¹ • a • c
    a≈ = •-cancelʳ (trans ac (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl))

  comm-F3 : m ⊢ (b • b) • a • (c • c) ≈ a • (b • b) → m ⊢ b • c ≈ c • b
  comm-F3 F3 = •-cancelˡ (begin
      a • b • c                   ≈⟨ sym assoc ⟩
      (a • b) • c                 ≈⟨ front _ (sym F1) ⟩
      (b • a • c) • c             ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
      b • a • c • c               ≈⟨ •-cancelˡ step ⟩
      a • c • b                   ∎)
    where
    step : m ⊢ b • b • a • c • c ≈ b • a • c • b
    step = begin
      b • b • a • c • c           ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (b • b) • a • (c • c)       ≈⟨ F3 ⟩
      a • (b • b)                 ≈⟨ sym assoc ⟩
      (a • b) • b                 ≈⟨ front _ (sym F1) ⟩
      (b • a • c) • b             ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
      b • a • c • b               ∎

  module Order2 (aa : m ⊢ a • a ≈ ε) (bb : m ⊢ b • b ≈ ε) (cc : m ⊢ c • c ≈ ε) where

    private
      -- c is a commutator: c = a b a b.
      c≈ : m ⊢ c ≈ a • b • a • b
      c≈ = sym (begin
        a • b • a • b             ≈⟨ back a (back b (sym F1)) ⟩
        a • b • b • a • c         ≈⟨ back a (cancel-in bb (a • c)) ⟩
        a • a • c                 ≈⟨ cancel-in aa c ⟩
        c                         ∎)

      -- (b a)⁴ = id, from c c = id.
      ba⁴ : m ⊢ b • a • b • a • b • a • b • a ≈ ε
      ba⁴ = begin
        b • a • b • a • b • a • b • a
          ≈⟨ sym (cancel-at bb _) ⟩
        (b • a • b • a • b • a • b • a) • b • b
          ≈⟨ by-passoc ((□ • □ • □ • □ • □ • □ • □ • □) • □ • □)
                       (□ • ((□ • □ • □ • □) • (□ • □ • □ • □)) • □) Eq.refl ⟩
        b • ((a • b • a • b) • (a • b • a • b)) • b
          ≈⟨ back b (front b (sym (cong c≈ c≈))) ⟩
        b • (c • c) • b
          ≈⟨ back b (trans (front b cc) left-unit) ⟩
        b • b
          ≈⟨ bb ⟩
        ε ∎

      bab² : m ⊢ (b • a • b) • (b • a • b) ≈ ε
      bab² = begin
        (b • a • b) • (b • a • b)  ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
        b • a • (b • b) • a • b    ≈⟨ back b (back a (trans (front _ bb) left-unit)) ⟩
        b • a • a • b              ≈⟨ back b (cancel-in aa b) ⟩
        b • b                      ≈⟨ bb ⟩
        ε                          ∎

      aba² : m ⊢ (a • b • a) • (a • b • a) ≈ ε
      aba² = begin
        (a • b • a) • (a • b • a)  ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
        a • b • (a • a) • b • a    ≈⟨ back a (back b (trans (front _ aa) left-unit)) ⟩
        a • b • b • a              ≈⟨ back a (cancel-in bb a) ⟩
        a • a                      ≈⟨ aa ⟩
        ε                          ∎

    comm-a : m ⊢ a • c ≈ c • a
    comm-a = begin
      a • c                        ≈⟨ back a c≈ ⟩
      a • a • b • a • b            ≈⟨ cancel-in aa _ ⟩
      b • a • b                    ≈⟨ •-cancelˡ (trans (by-passoc ((□ • □ • □) • (□ • □ • □ • □ • □))
                                                         (□ • □ • □ • □ • □ • □ • □ • □) Eq.refl)
                                                  (trans ba⁴ (sym bab²))) ⟨
      a • b • a • b • a            ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □ • □) • □) Eq.refl ⟩
      (a • b • a • b) • a          ≈⟨ front a (sym c≈) ⟩
      c • a                        ∎

    comm-b : m ⊢ b • c ≈ c • b
    comm-b = begin
      b • c                        ≈⟨ back b c≈ ⟩
      b • a • b • a • b            ≈⟨ •-cancelʳ (trans (by-passoc ((□ • □ • □ • □ • □) • (□ • □ • □))
                                                         (□ • □ • □ • □ • □ • □ • □ • □) Eq.refl)
                                                  (trans ba⁴ (sym aba²))) ⟩
      a • b • a                    ≈⟨ sym (back a (back b (cancel-at bb a))) ⟩
      a • b • a • b • b            ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □ • □) • □) Eq.refl ⟩
      (a • b • a • b) • b          ≈⟨ front b (sym c≈) ⟩
      c • b                        ∎

------------------------------------------------------------------------
-- Conjugation by an involution

module _ {m : ℕ} where

  open Width m

  -- Iterates of a conjugate.
  conj-^ : {s w : Circuit m} → s • s ≈ ε → (k : ℕ) → (s • w • s) ^ k ≈ s • w ^ k • s
  conj-^ {s} ss zero = sym (trans (back s left-unit) ss)
  conj-^ ss (suc zero) = refl
  conj-^ {s} {w} ss (suc (suc k)) = begin
    (s • w • s) • (s • w • s) ^ suc k     ≈⟨ back _ (conj-^ ss (suc k)) ⟩
    (s • w • s) • s • w ^ suc k • s       ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    s • w • (s • s) • w ^ suc k • s       ≈⟨ back s (back w (trans (front _ ss) left-unit)) ⟩
    s • w • w ^ suc k • s                 ≈⟨ back s (sym assoc) ⟩
    s • (w • w ^ suc k) • s               ∎

------------------------------------------------------------------------
-- CX on wires 2 and 0, and the multipliers

module _ {n : ℕ} where

  open Width (₃₊ n)

  SWAP↑² : (₃₊ n) ⊢ SWAP ↑ • SWAP ↑ ≈ ε
  SWAP↑² = lift (ax swap-order)

  CX₂₀ᶠ : (k : F) → (₃₊ n) ⊢ CX₂₀ ^ᶠ k ≈ SWAP ↑ • CX ^ᶠ k • SWAP ↑
  CX₂₀ᶠ k = conj-^ SWAP↑² (toℕ k)

  CX₂₀-order : (₃₊ n) ⊢ CX₂₀ ^ p ≈ ε
  CX₂₀-order = begin
    CX₂₀ ^ p                     ≈⟨ conj-^ SWAP↑² p ⟩
    SWAP ↑ • CX ^ p • SWAP ↑     ≈⟨ back _ (trans (front _ CX-order) left-unit) ⟩
    SWAP ↑ • SWAP ↑              ≈⟨ SWAP↑² ⟩
    ε                            ∎

  -- M on wire 0 commutes with SWAP ↑ and CX ↑; on wire 2, with CX.
  M-SWAP↑ : (x : F*) → (₃₊ n) ⊢ M⟨ x ⟩ • SWAP ↑ ≈ SWAP ↑ • M⟨ x ⟩
  M-SWAP↑ x = sym (comm-gate₁-w↑ (M-gate (proj₁ x) (proj₂ x)) SWAP)

  M-CX↑ : (x : F*) → (₃₊ n) ⊢ M⟨ x ⟩ • CX ↑ ≈ CX ↑ • M⟨ x ⟩
  M-CX↑ x = sym (comm-gate₁-w↑ (M-gate (proj₁ x) (proj₂ x)) CX)

  M↑↑-CX : (x : F*) → (₃₊ n) ⊢ CX • M⟨ x ⟩ ↑ ↑ ≈ M⟨ x ⟩ ↑ ↑ • CX
  M↑↑-CX x = sym (comm-gate₂-w↑↑ CX-gate M⟨ x ⟩)

  -- M on wire 1 past SWAP ↑ (rule swap-M one wire up), both ways.
  SWAP↑-M↑↑ : (x : F*) → (₃₊ n) ⊢ SWAP ↑ • M⟨ x ⟩ ↑ ↑ ≈ M⟨ x ⟩ ↑ • SWAP ↑
  SWAP↑-M↑↑ x = sym (lift (ax (swap-M (proj₁ x) (proj₂ x))))

  SWAP↑-M↑ : (x : F*) → (₃₊ n) ⊢ SWAP ↑ • M⟨ x ⟩ ↑ ≈ M⟨ x ⟩ ↑ ↑ • SWAP ↑
  SWAP↑-M↑ x = sym (I.conj→' (I.conj← (SWAP↑-M↑↑ x)))
    where module I = Involution SWAP↑²

  -- Multipliers past CX₂₀: on its target (wire 0) and on its control
  -- (wire 2).
  M-CX₂₀ : (x : F*) → (₃₊ n) ⊢ M⟨ x ⟩ • CX₂₀ ≈ CX₂₀ ^ᶠ proj₁ x • M⟨ x ⟩
  M-CX₂₀ x = begin
    M⟨ x ⟩ • SWAP ↑ • CX • SWAP ↑                ≈⟨ slide (M-SWAP↑ x) (slide (M-CX x) (M-SWAP↑ x)) ⟩
    (SWAP ↑ • CX ^ᶠ proj₁ x • SWAP ↑) • M⟨ x ⟩   ≈⟨ front _ (sym (CX₂₀ᶠ (proj₁ x))) ⟩
    CX₂₀ ^ᶠ proj₁ x • M⟨ x ⟩                     ∎

  CX₂₀ᶠ-M↑↑ : (x : F*) (k : F) → (₃₊ n) ⊢ CX₂₀ ^ᶠ k • M⟨ x ⟩ ↑ ↑ ≈ M⟨ x ⟩ ↑ ↑ • CX₂₀ ^ᶠ (k * proj₁ x)
  CX₂₀ᶠ-M↑↑ x k = begin
    CX₂₀ ^ᶠ k • M⟨ x ⟩ ↑ ↑                               ≈⟨ front _ (CX₂₀ᶠ k) ⟩
    (SWAP ↑ • CX ^ᶠ k • SWAP ↑) • M⟨ x ⟩ ↑ ↑             ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
    SWAP ↑ • CX ^ᶠ k • SWAP ↑ • M⟨ x ⟩ ↑ ↑               ≈⟨ back _ (back _ (SWAP↑-M↑↑ x)) ⟩
    SWAP ↑ • CX ^ᶠ k • M⟨ x ⟩ ↑ • SWAP ↑                 ≈⟨ back _ (trans (sym assoc) (front _ (CXᶠ-M↑ x k))) ⟩
    SWAP ↑ • (M⟨ x ⟩ ↑ • CX ^ᶠ (k * proj₁ x)) • SWAP ↑   ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (SWAP ↑ • M⟨ x ⟩ ↑) • CX ^ᶠ (k * proj₁ x) • SWAP ↑   ≈⟨ front _ (SWAP↑-M↑ x) ⟩
    (M⟨ x ⟩ ↑ ↑ • SWAP ↑) • CX ^ᶠ (k * proj₁ x) • SWAP ↑ ≈⟨ assoc ⟩
    M⟨ x ⟩ ↑ ↑ • SWAP ↑ • CX ^ᶠ (k * proj₁ x) • SWAP ↑   ≈⟨ back _ (sym (CX₂₀ᶠ (k * proj₁ x))) ⟩
    M⟨ x ⟩ ↑ ↑ • CX₂₀ ^ᶠ (k * proj₁ x)                   ∎

------------------------------------------------------------------------
-- Moving an equation across a word

module _ {m : ℕ} where

  open Width m
  open Inv m using (•-cancelˡ ; •-cancelʳ)

  -- If g moves across both sides of an equation, the equation moves
  -- with it: rightwards (across) and leftwards (across').
  across : {g l r l' r' : Circuit m} → g • l ≈ l' • g → g • r ≈ r' • g → l ≈ r → l' ≈ r'
  across el er e = •-cancelʳ (trans (sym el) (trans (back _ e) er))

  across' : {g l r l' r' : Circuit m} → l • g ≈ g • l' → r • g ≈ g • r' → l ≈ r → l' ≈ r'
  across' el er e = •-cancelˡ (trans (sym el) (trans (front _ e) er))

  -- A word g slid leftwards across a product.
  slideʳ : {g a a' b b' : Circuit m} → a • g ≈ g • a' → b • g ≈ g • b' → (a • b) • g ≈ g • (a' • b')
  slideʳ ea eb = sym (slide (sym ea) (sym eb))

------------------------------------------------------------------------
-- The Steinberg relations

module _ {n : ℕ} where

  open Width (₃₊ n)

  -- Rule (8) conjugated by M_x on wire 0, then by M_y on wire 2.
  steinberg₁ : (x : F*) → (₃₊ n) ⊢ CX ↑ • CX ^ᶠ proj₁ x • CX₂₀ ^ᶠ proj₁ x ≈ CX ^ᶠ proj₁ x • CX ↑
  steinberg₁ x =
    across (slide (M-CX↑ x) (slide (M-CX x) (M-CX₂₀ x))) (slide (M-CX x) (M-CX↑ x)) (ax ax8)

  steinberg : (x y : F*) →
    (₃₊ n) ⊢ (CX ^ᶠ proj₁ y) ↑ • CX ^ᶠ proj₁ x • CX₂₀ ^ᶠ (proj₁ x * proj₁ y)
           ≈ CX ^ᶠ proj₁ x • (CX ^ᶠ proj₁ y) ↑
  steinberg x y = across' (slideʳ up (slideʳ mid' (CX₂₀ᶠ-M↑↑ y (proj₁ x)))) (slideʳ mid' up) (steinberg₁ x)
    where
    up : (₃₊ n) ⊢ CX ↑ • M⟨ y ⟩ ↑ ↑ ≈ M⟨ y ⟩ ↑ ↑ • (CX ^ᶠ proj₁ y) ↑
    up = lift (ax (ax4 y))
    mid' : (₃₊ n) ⊢ CX ^ᶠ proj₁ x • M⟨ y ⟩ ↑ ↑ ≈ M⟨ y ⟩ ↑ ↑ • CX ^ᶠ proj₁ x
    mid' = Pow.pow-comm (₃₊ n) (toℕ (proj₁ x)) (M↑↑-CX y)

  private
    module S = Steinberg {₃₊ n} {CX} {CX ↑} {CX₂₀} (ax ax8)
    module OA = Pow.Order (₃₊ n) {CX} CX-order
    module OA' = Pow.Order (₂₊ n) {CX} CX-order
    module OC = Pow.Order (₃₊ n) {CX₂₀} CX₂₀-order

    two : 1 ≤ p-2 → F*
    two odd = 2F , two≢0 odd

    F2 : 1 ≤ p-2 → (₃₊ n) ⊢ CX ↑ • (CX • CX) • (CX₂₀ • CX₂₀) ≈ (CX • CX) • CX ↑
    F2 odd = begin
      CX ↑ • (CX • CX) • (CX₂₀ • CX₂₀)   ≈⟨ back _ (sym (cong OA.^ᶠ-2 OC.^ᶠ-2)) ⟩
      CX ↑ • CX ^ᶠ 2F • CX₂₀ ^ᶠ 2F         ≈⟨ steinberg₁ (two odd) ⟩
      CX ^ᶠ 2F • CX ↑                      ≈⟨ front _ OA.^ᶠ-2 ⟩
      (CX • CX) • CX ↑                     ∎

    F3 : 1 ≤ p-2 → (₃₊ n) ⊢ (CX ↑ • CX ↑) • CX • (CX₂₀ • CX₂₀) ≈ CX • (CX ↑ • CX ↑)
    F3 odd = begin
      (CX ↑ • CX ↑) • CX • (CX₂₀ • CX₂₀)
        ≈⟨ cong (sym (lift OA'.^ᶠ-2)) (back _ (trans (sym OC.^ᶠ-2) (OC.^ᶠ-≡ (Eq.sym (FR.*-identityˡ 2F))))) ⟩
      (CX ^ᶠ 2F) ↑ • CX • CX₂₀ ^ᶠ (1F * 2F)
        ≈⟨ steinberg 1* (two odd) ⟩
      CX • (CX ^ᶠ 2F) ↑
        ≈⟨ back _ (lift OA'.^ᶠ-2) ⟩
      CX • (CX ↑ • CX ↑)                   ∎

    -- For p = 2 the three are involutions.
    sq : {m : ℕ} {w : Circuit m} → p-2 ≡ 0 → m ⊢ w ^ p ≈ ε → m ⊢ w • w ≈ ε
    sq {m} {w} e wp = W.trans (W.refl' (Eq.cong (λ k → w ^ suc (suc k)) (Eq.sym e))) wp
      where module W = Width m

    module S2 (e : p-2 ≡ 0) =
      S.Order2 (sq e CX-order) (lift (sq e CX-order)) (sq e CX₂₀-order)

    even : ¬ 1 ≤ p-2 → p-2 ≡ 0
    even ¬odd = ℕP.n<1⇒n≡0 (ℕP.≰⇒> ¬odd)

  -- CX₂₀ commutes with CX (same target, the paper's XX-comm) and with
  -- CX ↑ (same control, XX2-comm).
  XX-comm : (₃₊ n) ⊢ CX • CX₂₀ ≈ CX₂₀ • CX
  XX-comm with 1 ℕP.≤? p-2
  ... | yes odd = S.comm-F2 (F2 odd)
  ... | no ¬odd = S2.comm-a (even ¬odd)

  XX2-comm : (₃₊ n) ⊢ CX ↑ • CX₂₀ ≈ CX₂₀ • CX ↑
  XX2-comm with 1 ℕP.≤? p-2
  ... | yes odd = S.comm-F3 (F3 odd)
  ... | no ¬odd = S2.comm-b (even ¬odd)

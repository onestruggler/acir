------------------------------------------------------------------------
-- Presentations of groups
--
-- Iterates of circuits
--
-- The laws of w ^ k (Pow): iterates add, multiply, commute with what
-- w commutes with, and those of commuting words multiply.  For a word
-- of order p (Order), iterates are taken modulo p, so the iterates
-- labelled by F_p, w ^ᶠ k, add and multiply as the labels do: this is
-- the paper's label convention (Remark 15) made into equations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Powers
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base as ℕ using (zero ; suc ; NonZero)
open import Data.Nat.DivMod using (_%_ ; _/_ ; m≡m%n+[m/n]*n)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
  using (F ; p ; 0F ; 1F ; 2F ; _+_ ; _*_ ; -_ ; toℕ-+ ; toℕ-* ; module FR)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv

module Pow (n : ℕ) where

  open Width n

  pow-suc : (w : Circuit n) (k : ℕ) → w ^ suc k ≈ w • w ^ k
  pow-suc w zero    = sym right-unit
  pow-suc w (suc k) = refl

  pow-+ : (w : Circuit n) (i j : ℕ) → w ^ (i ℕ.+ j) ≈ w ^ i • w ^ j
  pow-+ w zero    j = sym left-unit
  pow-+ w (suc i) j = begin
    w ^ suc (i ℕ.+ j)        ≈⟨ pow-suc w (i ℕ.+ j) ⟩
    w • w ^ (i ℕ.+ j)        ≈⟨ back w (pow-+ w i j) ⟩
    w • w ^ i • w ^ j        ≈⟨ sym assoc ⟩
    (w • w ^ i) • w ^ j      ≈⟨ front _ (sym (pow-suc w i)) ⟩
    w ^ suc i • w ^ j        ∎

  pow-cong : ∀ {w v : Circuit n} (k : ℕ) → w ≈ v → w ^ k ≈ v ^ k
  pow-cong zero          e = refl
  pow-cong (suc zero)    e = e
  pow-cong (suc (suc k)) e = cong e (pow-cong (suc k) e)

  pow-ε : (k : ℕ) → ε ^ k ≈ ε
  pow-ε zero          = refl
  pow-ε (suc zero)    = refl
  pow-ε (suc (suc k)) = trans left-unit (pow-ε (suc k))

  -- A power of a power.
  pow-pow : (w : Circuit n) (i j : ℕ) → (w ^ i) ^ j ≈ w ^ (j ℕ.* i)
  pow-pow w i zero    = refl
  pow-pow w i (suc j) = begin
    (w ^ i) ^ suc j          ≈⟨ pow-suc (w ^ i) j ⟩
    w ^ i • (w ^ i) ^ j      ≈⟨ back _ (pow-pow w i j) ⟩
    w ^ i • w ^ (j ℕ.* i)    ≈⟨ sym (pow-+ w i (j ℕ.* i)) ⟩
    w ^ (i ℕ.+ j ℕ.* i)      ∎

  -- Iterates of one word commute.
  pow-pow-comm : (w : Circuit n) (i j : ℕ) → w ^ i • w ^ j ≈ w ^ j • w ^ i
  pow-pow-comm w i j = begin
    w ^ i • w ^ j            ≈⟨ sym (pow-+ w i j) ⟩
    w ^ (i ℕ.+ j)            ≈⟨ refl' (Eq.cong (w ^_) (ℕP.+-comm i j)) ⟩
    w ^ (j ℕ.+ i)            ≈⟨ pow-+ w j i ⟩
    w ^ j • w ^ i            ∎

  -- Powers of commuting words commute.
  pow-comm : ∀ {a b : Circuit n} (i : ℕ) → a • b ≈ b • a → a ^ i • b ≈ b • a ^ i
  pow-comm zero          e = trans left-unit (sym right-unit)
  pow-comm (suc zero)    e = e
  pow-comm {a} {b} (suc (suc i)) e = begin
    (a • a ^ suc i) • b      ≈⟨ assoc ⟩
    a • a ^ suc i • b        ≈⟨ back a (pow-comm (suc i) e) ⟩
    a • b • a ^ suc i        ≈⟨ sym assoc ⟩
    (a • b) • a ^ suc i      ≈⟨ front _ e ⟩
    (b • a) • a ^ suc i      ≈⟨ assoc ⟩
    b • a • a ^ suc i        ∎

  pow-comm₂ : ∀ {a b : Circuit n} (i j : ℕ) → a • b ≈ b • a → a ^ i • b ^ j ≈ b ^ j • a ^ i
  pow-comm₂ i j e = sym (pow-comm j (sym (pow-comm i e)))

  -- The power of a product of commuting words.
  pow-• : ∀ {a b : Circuit n} (k : ℕ) → a • b ≈ b • a → (a • b) ^ k ≈ a ^ k • b ^ k
  pow-• zero          e = sym left-unit
  pow-• (suc zero)    e = refl
  pow-• {a} {b} (suc (suc k)) e = begin
    (a • b) • (a • b) ^ suc k          ≈⟨ back _ (pow-• (suc k) e) ⟩
    (a • b) • a ^ suc k • b ^ suc k    ≈⟨ assoc ⟩
    a • b • a ^ suc k • b ^ suc k      ≈⟨ back a (trans (sym assoc) (front _ (sym (pow-comm (suc k) e)))) ⟩
    a • (a ^ suc k • b) • b ^ suc k    ≈⟨ back a assoc ⟩
    a • a ^ suc k • b • b ^ suc k      ≈⟨ sym assoc ⟩
    (a • a ^ suc k) • b • b ^ suc k    ∎

  -- A power of a power by a multiple of d.
  pow-*d : (w : Circuit n) (d q : ℕ) → w ^ (q ℕ.* d) ≈ (w ^ d) ^ q
  pow-*d w d zero    = refl
  pow-*d w d (suc q) = begin
    w ^ (d ℕ.+ q ℕ.* d)      ≈⟨ pow-+ w d (q ℕ.* d) ⟩
    w ^ d • w ^ (q ℕ.* d)    ≈⟨ back _ (pow-*d w d q) ⟩
    w ^ d • (w ^ d) ^ q      ≈⟨ sym (pow-suc (w ^ d) q) ⟩
    (w ^ d) ^ suc q          ∎

  ----------------------------------------------------------------------
  -- Words of order p

  module Order {w : Circuit n} (wp : w ^ p ≈ ε) where

    -- Powers are taken modulo p.
    pow-mod : (k : ℕ) → w ^ k ≈ w ^ (k % p)
    pow-mod k = begin
      w ^ k                                ≈⟨ refl' (Eq.cong (w ^_) (m≡m%n+[m/n]*n k p)) ⟩
      w ^ (k % p ℕ.+ (k / p) ℕ.* p)        ≈⟨ pow-+ w (k % p) ((k / p) ℕ.* p) ⟩
      w ^ (k % p) • w ^ ((k / p) ℕ.* p)    ≈⟨ back _ (pow-*d w p (k / p)) ⟩
      w ^ (k % p) • (w ^ p) ^ (k / p)      ≈⟨ back _ (trans (pow-cong (k / p) wp) (pow-ε (k / p))) ⟩
      w ^ (k % p) • ε                      ≈⟨ right-unit ⟩
      w ^ (k % p)                          ∎

    -- The labelled iterates add and multiply as their labels.
    ^ᶠ-+ : (k l : F) → w ^ᶠ k • w ^ᶠ l ≈ w ^ᶠ (k + l)
    ^ᶠ-+ k l = begin
      w ^ toℕ k • w ^ toℕ l                ≈⟨ sym (pow-+ w (toℕ k) (toℕ l)) ⟩
      w ^ (toℕ k ℕ.+ toℕ l)                ≈⟨ pow-mod (toℕ k ℕ.+ toℕ l) ⟩
      w ^ ((toℕ k ℕ.+ toℕ l) % p)          ≈⟨ refl' (Eq.cong (w ^_) (Eq.sym (toℕ-+ k l))) ⟩
      w ^ toℕ (k + l)                      ∎

    ^ᶠ-* : (k l : F) → (w ^ᶠ k) ^ᶠ l ≈ w ^ᶠ (k * l)
    ^ᶠ-* k l = begin
      (w ^ toℕ k) ^ toℕ l                  ≈⟨ pow-pow w (toℕ k) (toℕ l) ⟩
      w ^ (toℕ l ℕ.* toℕ k)                ≈⟨ refl' (Eq.cong (w ^_) (ℕP.*-comm (toℕ l) (toℕ k))) ⟩
      w ^ (toℕ k ℕ.* toℕ l)                ≈⟨ pow-mod (toℕ k ℕ.* toℕ l) ⟩
      w ^ ((toℕ k ℕ.* toℕ l) % p)          ≈⟨ refl' (Eq.cong (w ^_) (Eq.sym (toℕ-* k l))) ⟩
      w ^ toℕ (k * l)                      ∎

    -- Labels that are equal give equal iterates.
    ^ᶠ-≡ : {k l : F} → k ≡ l → w ^ᶠ k ≈ w ^ᶠ l
    ^ᶠ-≡ e = refl' (Eq.cong (w ^ᶠ_) e)

    -- The iterate labelled 2 is the square.
    ^ᶠ-2 : w ^ᶠ 2F ≈ w • w
    ^ᶠ-2 = sym (^ᶠ-+ 1F 1F)

    -- The iterate by -k undoes the iterate by k.
    ^ᶠ-inverseˡ : (k : F) → w ^ᶠ (- k) • w ^ᶠ k ≈ ε
    ^ᶠ-inverseˡ k = trans (^ᶠ-+ (- k) k) (^ᶠ-≡ (FR.-‿inverseˡ k))

    ^ᶠ-inverseʳ : (k : F) → w ^ᶠ k • w ^ᶠ (- k) ≈ ε
    ^ᶠ-inverseʳ k = trans (^ᶠ-+ k (- k)) (^ᶠ-≡ (FR.-‿inverseʳ k))

    -- In particular w ^ᶠ (- 1) is the inverse of w.
    inverseˡ : w ^ᶠ (- 1F) • w ≈ ε
    inverseˡ = ^ᶠ-inverseˡ 1F

    inverseʳ : w • w ^ᶠ (- 1F) ≈ ε
    inverseʳ = ^ᶠ-inverseʳ 1F

-- Powers one wire up.
↑-pow : ∀ {n} (w : Circuit n) (k : ℕ) → (w ^ k) ↑ ≡ (w ↑) ^ k
↑-pow w zero          = Eq.refl
↑-pow w (suc zero)    = Eq.refl
↑-pow w (suc (suc k)) = Eq.cong (w ↑ •_) (↑-pow w (suc k))

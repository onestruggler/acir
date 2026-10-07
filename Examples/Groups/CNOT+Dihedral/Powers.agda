------------------------------------------------------------------------
-- Presentations of groups
--
-- Powers of circuits
--
-- The laws of w ^ k used by the diagonal calculus: powers add and
-- multiply, a word of order 8 has its powers modulo 8, powers of
-- commuting words commute, and a power of a conjugate is the conjugate
-- of the power.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Powers where

open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _%_ ; _/_ ; NonZero)
open import Data.Nat.DivMod using (m≡m%n+[m/n]*n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Evaluation using (_⁻¹ ; module Inv)

module Pow (n : ℕ) where

  open Width n

  pow-suc : (w : Circuit n) (k : ℕ) → w ^ suc k ≈ w • w ^ k
  pow-suc w zero    = sym right-unit
  pow-suc w (suc k) = refl

  pow-+ : (w : Circuit n) (i j : ℕ) → w ^ (i + j) ≈ w ^ i • w ^ j
  pow-+ w zero    j = sym left-unit
  pow-+ w (suc i) j = begin
    w ^ suc (i + j)          ≈⟨ pow-suc w (i + j) ⟩
    w • w ^ (i + j)          ≈⟨ back w (pow-+ w i j) ⟩
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
  pow-*8 : (w : Circuit n) (q : ℕ) → w ^ (q * 8) ≈ (w ^ 8) ^ q
  pow-*8 w zero    = refl
  pow-*8 w (suc q) = begin
    w ^ (8 + q * 8)          ≈⟨ pow-+ w 8 (q * 8) ⟩
    w ^ 8 • w ^ (q * 8)      ≈⟨ back _ (pow-*8 w q) ⟩
    w ^ 8 • (w ^ 8) ^ q      ≈⟨ sym (pow-suc (w ^ 8) q) ⟩
    (w ^ 8) ^ suc q          ∎

  -- A word of order 8 has its powers modulo 8.
  pow-mod : (w : Circuit n) → w ^ 8 ≈ ε → (k : ℕ) → w ^ k ≈ w ^ (k % 8)
  pow-mod w e k = begin
    w ^ k                                ≈⟨ refl' (Eq.cong (w ^_) (m≡m%n+[m/n]*n k 8)) ⟩
    w ^ (k % 8 + (k / 8) * 8)            ≈⟨ pow-+ w (k % 8) ((k / 8) * 8) ⟩
    w ^ (k % 8) • w ^ ((k / 8) * 8)      ≈⟨ back _ (pow-*8 w (k / 8)) ⟩
    w ^ (k % 8) • (w ^ 8) ^ (k / 8)      ≈⟨ back _ (trans (pow-cong (k / 8) e) (pow-ε (k / 8))) ⟩
    w ^ (k % 8) • ε                      ≈⟨ right-unit ⟩
    w ^ (k % 8)                          ∎

  -- And in general: a word of order d has its powers modulo d.
  pow-*d : (w : Circuit n) (d q : ℕ) → w ^ (q * d) ≈ (w ^ d) ^ q
  pow-*d w d zero    = refl
  pow-*d w d (suc q) = begin
    w ^ (d + q * d)          ≈⟨ pow-+ w d (q * d) ⟩
    w ^ d • w ^ (q * d)      ≈⟨ back _ (pow-*d w d q) ⟩
    w ^ d • (w ^ d) ^ q      ≈⟨ sym (pow-suc (w ^ d) q) ⟩
    (w ^ d) ^ suc q          ∎

  pow-mod-by : (w : Circuit n) (d : ℕ) .{{_ : NonZero d}} → w ^ d ≈ ε →
               (k : ℕ) → w ^ k ≈ w ^ (k % d)
  pow-mod-by w d e k = begin
    w ^ k                                ≈⟨ refl' (Eq.cong (w ^_) (m≡m%n+[m/n]*n k d)) ⟩
    w ^ (k % d + (k / d) * d)            ≈⟨ pow-+ w (k % d) ((k / d) * d) ⟩
    w ^ (k % d) • w ^ ((k / d) * d)      ≈⟨ back _ (pow-*d w d (k / d)) ⟩
    w ^ (k % d) • (w ^ d) ^ (k / d)      ≈⟨ back _ (trans (pow-cong (k / d) e) (pow-ε (k / d))) ⟩
    w ^ (k % d) • ε                      ≈⟨ right-unit ⟩
    w ^ (k % d)                          ∎

  -- A power of a power.
  pow-pow : (w : Circuit n) (i j : ℕ) → (w ^ i) ^ j ≈ w ^ (j * i)
  pow-pow w i zero    = refl
  pow-pow w i (suc j) = begin
    (w ^ i) ^ suc j          ≈⟨ pow-suc (w ^ i) j ⟩
    w ^ i • (w ^ i) ^ j      ≈⟨ back _ (pow-pow w i j) ⟩
    w ^ i • w ^ (j * i)      ≈⟨ sym (pow-+ w i (j * i)) ⟩
    w ^ (i + j * i)          ∎

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

  -- The power of a conjugate.
  pow-conj : (ρ X : Circuit n) (k : ℕ) → (ρ ⁻¹ • X • ρ) ^ k ≈ ρ ⁻¹ • X ^ k • ρ
  pow-conj ρ X zero = sym (trans (back _ left-unit) (Inv.inverseˡ n))
  pow-conj ρ X (suc zero) = refl
  pow-conj ρ X (suc (suc k)) = begin
    (ρ ⁻¹ • X • ρ) • (ρ ⁻¹ • X • ρ) ^ suc k
      ≈⟨ back _ (pow-conj ρ X (suc k)) ⟩
    (ρ ⁻¹ • X • ρ) • ρ ⁻¹ • X ^ suc k • ρ
      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    ρ ⁻¹ • X • (ρ • ρ ⁻¹) • X ^ suc k • ρ
      ≈⟨ back _ (back _ (trans (front _ (Inv.inverseʳ n)) left-unit)) ⟩
    ρ ⁻¹ • X • X ^ suc k • ρ
      ≈⟨ back _ (sym assoc) ⟩
    ρ ⁻¹ • (X • X ^ suc k) • ρ ∎

-- Powers one wire up.
↑-pow : ∀ {n} (w : Circuit n) (k : ℕ) → (w ^ k) ↑ ≡ (w ↑) ^ k
↑-pow w zero          = Eq.refl
↑-pow w (suc zero)    = Eq.refl
↑-pow w (suc (suc k)) = Eq.cong (w ↑ •_) (↑-pow w (suc k))

------------------------------------------------------------------------
-- Presentations of groups
--
-- The errata of ERRATA.md, checked on the matrices: each printed
-- equation that is false is refuted by one entry of its two sides,
-- and each correction that the rest of the development does not
-- already check is checked by computing both sides.
--
-- The corrections to (33), (97) and (100) are the relations r33, r97
-- and r100 of Syntactics, and Soundness checks them; the corrected
-- alias (-1)_[0] is StdMatrices.mm0, and X_[6,7] = CCX₀₁ is
-- StdMatrices.mT6.  That r_K does not follow from R₁ is
-- Independence.R₁-incomplete.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Errata where

open import Data.Fin using (Fin ; #_)
open import Data.Vec.Base using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; cong)

open import Quantum.Synthesis.Matrix using (Matrix)

open import Word.Base using (Word ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D ; _+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actV ; set₁ ; set₂)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Syntactics
open import Examples.Groups.CCX+HH-3qubit-opus.Encoding
open import Examples.Groups.CCX+HH-3qubit-opus.Semantics using (⟦_⟧)

------------------------------------------------------------------------
-- Readings at a fixed level, and the entry in row r and column c

⟦_⟧₀ : Word (Gate 0) → Matrix 8 8 D
⟦ w ⟧₀ = ⟦ w ⟧

⟦_⟧₁ : Word (Gate 1) → Matrix 8 8 D
⟦ w ⟧₁ = ⟦ w ⟧

entry : Fin 8 → Fin 8 → Matrix 8 8 D → D
entry r c A = lookup (lookup (Matrix.unMatrix A) c) r

-- Two matrices that differ at one entry differ.
apart : ∀ {A B} r c → entry r c A ≢ entry r c B → A ≢ B
apart r c ne e = ne (cong (entry r c) e)

------------------------------------------------------------------------
-- The computations

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  -- (33), Figure 4: CCX₀₁ ≈ σ₁₂ CCX₀₂ σ₀₂ is false (entry (1, 1): 1
  -- against 0).
  e33 : entry (# 1) (# 1) ⟦ CCX01 ⟧₀ ≢ entry (# 1) (# 1) ⟦ SW12 • CCX02 • SW02 ⟧₀
  e33 ()

  -- Section 5.5: CCX₁₂ = X_[6,7] is false (entry (3, 3): 0 against 1);
  -- CCX₁₂ is X_[3,7].
  e67 : entry (# 3) (# 3) ⟦ CCX12 ⟧₀ ≢ entry (# 3) (# 3) S1.⟦ X[ # 6 , # 7 ] ⟧ᵐ
  e67 ()

  ccx12 : ⟦ CCX12 ⟧₀ ≡ S1.⟦ X[ # 3 , # 7 ] ⟧ᵐ
  ccx12 = refl

  -- Section 5.5, (r_CX): CX₀₁ ≈ X_[2,6] X_[3,7] is false (entry (2, 2):
  -- 1 against 0); X_[2,6] X_[3,7] is CX₁₀, and CX₀₁ is X_[4,6] X_[5,7].
  eCX : entry (# 2) (# 2) ⟦ CX01 ⟧₀ ≢ entry (# 2) (# 2) S1.⟦ X[ # 2 , # 6 ] • X[ # 3 , # 7 ] ⟧ᵐ
  eCX ()

  cx10 : ⟦ CX10 ⟧₀ ≡ S1.⟦ X[ # 2 , # 6 ] • X[ # 3 , # 7 ] ⟧ᵐ
  cx10 = refl

  rCX : ⟦ CX01 ⟧₀ ≡ S1.⟦ X[ # 4 , # 6 ] • X[ # 5 , # 7 ] ⟧ᵐ
  rCX = refl

  -- Section 5.6: (-1)_[0] = X₀ X₁ CCZ X₁ X₀ is false (entry (0, 0): -1
  -- against 1); the right-hand side is (-1)_[1].
  em0 : entry (# 0) (# 0) S1.⟦ M[ # 0 ] ⟧ᵐ ≢ entry (# 0) (# 0) ⟦ X0 • X1 • CCZw • X1 • X0 ⟧₁
  em0 ()

  m1 : ⟦ X0 • X1 • CCZw • X1 • X0 ⟧₁ ≡ S1.⟦ M[ # 1 ] ⟧ᵐ
  m1 = refl

  -- (97), Figure 7 (and (78), (125), which are (97) on the two-level
  -- generators): X_[0,1] K_[0,1,2,3] ≈ K_[0,1,2,3] X_[0,1] (-1)_[1]
  -- (-1)_[3] is false (entry (1, 1): 1/2 against -1/2).
  e97 : entry (# 1) (# 1) ⟦ T 0 • NKw ⟧₁ ≢ entry (# 1) (# 1) ⟦ NKw • T 0 • m 1 • m 3 ⟧₁
  e97 ()

  -- (100), Figure 7 (and (81), (128)): K_[0,1,2,3] and K_[1,3,4,5] do
  -- not commute (entry (0, 3): 0 against 1/2).
  e100 : entry (# 0) (# 3) ⟦ NKw • Kq 1 3 4 5 ⟧₁ ≢ entry (# 0) (# 3) ⟦ Kq 1 3 4 5 • NKw ⟧₁
  e100 ()

  -- Section 5.7: CCZ = K₁₂ CZ₁₂ X₀ K_[0,1,2,3] X₀ CZ₁₂ K_[0,1,2,3] X_[5,6]
  -- is false (entry (4, 4): 1 against 1/2); with K₁₂ for the second
  -- K_[0,1,2,3] it holds.
  eCCZ : entry (# 4) (# 4) ⟦ CCZw ⟧₁ ≢
         entry (# 4) (# 4) ⟦ K12 • CZ12 • X0 • NKw • X0 • CZ12 • NKw • T 5 ⟧₁
  eCCZ ()

  ccz : ⟦ CCZw ⟧₁ ≡ ⟦ K12 • CZ12 • X0 • NKw • X0 • CZ12 • K12 • T 5 ⟧₁
  ccz = refl

  -- The other decomposition of Section 5.7 holds as printed.
  nk : ⟦ NKw ⟧₁ ≡ ⟦ (K12 • CCZw) • (K12 • CCZw) • (K12 • CCZw) • T 5 ⟧₁
  nk = refl

------------------------------------------------------------------------
-- The printed equations are false

r033-false : ⟦ CCX01 ⟧₀ ≢ ⟦ SW12 • CCX02 • SW02 ⟧₀
r033-false = apart (# 1) (# 1) e33

x67-false : ⟦ CCX12 ⟧₀ ≢ S1.⟦ X[ # 6 , # 7 ] ⟧ᵐ
x67-false = apart (# 3) (# 3) e67

rCX-false : ⟦ CX01 ⟧₀ ≢ S1.⟦ X[ # 2 , # 6 ] • X[ # 3 , # 7 ] ⟧ᵐ
rCX-false = apart (# 2) (# 2) eCX

m0-false : S1.⟦ M[ # 0 ] ⟧ᵐ ≢ ⟦ X0 • X1 • CCZw • X1 • X0 ⟧₁
m0-false = apart (# 0) (# 0) em0

r097-false : ⟦ T 0 • NKw ⟧₁ ≢ ⟦ NKw • T 0 • m 1 • m 3 ⟧₁
r097-false = apart (# 1) (# 1) e97

r100-false : ⟦ NKw • Kq 1 3 4 5 ⟧₁ ≢ ⟦ Kq 1 3 4 5 • NKw ⟧₁
r100-false = apart (# 0) (# 3) e100

ccz-false : ⟦ CCZw ⟧₁ ≢ ⟦ K12 • CZ12 • X0 • NKw • X0 • CZ12 • NKw • T 5 ⟧₁
ccz-false = apart (# 4) (# 4) eCCZ

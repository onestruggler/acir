------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of Amy, Ross and Wesley (arXiv:2407.11152v3):
--
--   R₀ (Figure 4), 46 relations on the Toffoli-K gates 𝒟;
--   R₈₄ (Figure 7), 19 relations on Σ₁ = 𝒟 ∪ {K_[0,1,2,3], CCZ};
--   Figure 8, 7 relations for H₂;
--
-- and the presentations R₁ = R₀ ∪ R₈₄ (Theorem 5.2) and R₂ = R₁ ∪
-- Figure 8 (Theorem 6.3).  Each figure is a relation at every level
-- at which its gates exist, so a derivation from R₀ is one at every
-- level.
--
-- Corrections (each checked on the matrices, Soundness):
--
--   (33)  printed CCX₀₁ = σ₁₂ CCX₀₂ σ₀₂; it is σ₁₂ CCX₀₂ σ₁₂.
--   (97)  printed X_[0,1] on the right; it is X_[1,3], as in
--         Li-Ross-Selinger's (4a).
--   (100) printed as a commutation of K_[0,1,2,3] and K_[1,3,4,5]; it is
--         Li-Ross-Selinger's (5a), K_[0,1,2,3] K_[1,3,4,5] =
--         K_[2,3,4,5] K_[0,1,2,4].
--   The alias (-1)_[0] = X₀ X₁ CCZ X₁ X₀ of Section 5.6 needs X₂ as
--   well: (-1)_[0] = X₀ X₁ X₂ CCZ X₂ X₁ X₀.  (And X_[6,7] is CCX₀₁,
--   not CCX₁₂ as Section 5.5 says; the alias X_[6,7] = CCX₀₁ of
--   Section 5.6 is right.)
--
-- One relation is missing.  Figure 7 relates K_[0,1,2,3] and CCZ to the
-- permutations only, and Figure 4 never mentions them, so nothing in
-- R₁ relates K₁₂ to K_[0,1,2,3]: the relation r_K of Section 5.5,
--
--   K₁₂ = K_[4,5,6,7] X₀ K_[4,5,6,7] X₀ = X₀ K_[0,1,2,3] X₀ K_[0,1,2,3],
--
-- is used to introduce K₁₂ and never eliminated.  It is not derivable
-- from R₁ (Independence), so R₁ is not complete for O(8, 𝔻); R₁⁺ and
-- R₂⁺ add it.
--
-- The aliases of Figure 7 are words over Σ₁: X_[a,a+1] are the circuits
-- of Section 5.6, X_[a,b] = X_[a,a+1] X_[a+1,b] X_[a,a+1] for b > a + 1,
-- (-1)_[c] = X_[0,c] (-1)_[0] X_[0,c] and K_[a,b,c,d] = X_[0,a] X_[1,b]
-- X_[2,c] X_[3,d] K_[0,1,2,3] X_[3,d] X_[2,c] X_[1,b] X_[0,a] (Section
-- 5.3), with X_[a,a] = ε.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Syntactics where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _∸_)

open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.CCX+HH-3qubit-opus.Gates public

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Figure 4: R₀

infix 4 _===₀_

data _===₀_ {k : ℕ} : WRel (Gate k) where
  r1  : CZ01 ===₀ K12 • CX01 • K12
  r2  : X1 ===₀ CX01 • X0 • CX01 • X0
  r3  : Z0 ===₀ CZ01 • CX01 • CZ01 • CX01
  r4  : Z1 ===₀ K12 • X1 • K12
  r5  : CX20 ===₀ X1 • CCX12 • X1 • CCX12
  r6  : CX21 ===₀ CX20 • CX01 • CX20 • CX01
  r7  : CX12 ===₀ K12 • CX21 • K12
  r8  : SW12 ===₀ CX12 • CX21 • CX12
  r9  : CX02 ===₀ SW12 • CX01 • SW12
  r10 : SW02 ===₀ CX02 • CX20 • CX02
  r11 : K01 ===₀ SW02 • K12 • SW02
  r12 : CX10 ===₀ K01 • CX01 • K01
  r13 : SW01 ===₀ CX01 • CX10 • CX01
  r14 : CCX02 ===₀ SW01 • CCX12 • SW01
  r15 : X2 ===₀ SW02 • X0 • SW02
  r16 : Z2 ===₀ SW02 • Z0 • SW02
  r17 : CCX01 ===₀ K12 • CCX02 • K12
  r18 : CZ02 ===₀ SW12 • CZ01 • SW12
  r19 : CZ12 ===₀ SW01 • CZ02 • SW01
  r20 : SW12 ===₀ CZ12 • K12 • CZ12 • K12 • CZ12 • K12
  r21 : X0 • X0 ===₀ ε
  r22 : CX01 • CX01 ===₀ ε
  r23 : K12 • K12 ===₀ ε
  r24 : CCX12 • CCX12 ===₀ ε
  r25 : K01 • K01 ===₀ ε
  r26 : CX12 • X0 ===₀ X0 • CX12
  r27 : X0 • K12 ===₀ K12 • X0
  r28 : X1 ===₀ SW01 • X0 • SW01
  r29 : CX20 ===₀ SW02 • CX02 • SW02
  r30 : CX12 ===₀ SW01 • CX02 • SW01
  r31 : CX21 ===₀ SW01 • CX20 • SW01
  r32 : CCX01 ===₀ SW02 • CCX12 • SW02
  r33 : CCX01 ===₀ SW12 • CCX02 • SW12
  r34 : Z1 ===₀ SW01 • Z0 • SW01
  r35 : K01 ===₀ SW01 • K01 • SW01
  r36 : CCX12 • CX10 ===₀ CX10 • CCX12
  r37 : X0 • CCX12 ===₀ CCX12 • X0
  r38 : X0 • CX10 ===₀ CX10 • X0
  r39 : K01 • K12 ===₀ K12 • K01
  r40 : CZ01 • CZ12 ===₀ CZ12 • CZ01
  r41 : K01 • Z0 ===₀ X0 • K01
  r42 : X0 • CCX01 ===₀ CCX01 • CX12 • X0
  r43 : CX01 • CZ12 ===₀ CZ12 • CZ02 • CX01
  r44 : CX12 • CCX12 ===₀ CCX12 • CX10 • CX12
  r45 : CCX12 • CX01 ===₀ CX01 • CCX02 • CCX12 • CCX02
  r46 : CCX01 • CCX02 ===₀ CCX02 • CCX01 • CCX02 • CCX01

------------------------------------------------------------------------
-- The aliases of Figure 7

-- X_[a,a+1], the circuits of Section 5.6.
T : ℕ → Word (Gate k)
T 0 = X0 • X1 • CCX01 • X1 • X0
T 1 = X0 • CCX01 • CCX02 • CCX01 • X0
T 2 = X0 • CCX01 • X0
T 3 = X0 • X2 • CCX01 • X0 • CCX12 • CCX02 • CCX12 • X0 • CCX01 • X2 • X0
T 4 = X1 • CCX01 • X1
T 5 = CCX01 • CCX02 • CCX01
T (suc (suc (suc (suc (suc (suc _)))))) = CCX01

-- X_[a, a+1+d].
Tʳ : ℕ → ℕ → Word (Gate k)
Tʳ a zero    = T a
Tʳ a (suc d) = T a • Tʳ (suc a) d • T a

-- X_[a,b], with X_[a,a] = ε.
Xab : ℕ → ℕ → Word (Gate k)
Xab a b = go (b ∸ a)
  where
  go : ℕ → Word (Gate _)
  go zero    = ε
  go (suc d) = Tʳ a d

module _ {k : ℕ} where

  -- (-1)_[0] and (-1)_[c].
  m0 : Word (Gate (suc k))
  m0 = X0 • X1 • X2 • CCZw • X2 • X1 • X0

  m : ℕ → Word (Gate (suc k))
  m c = Xab 0 c • m0 • Xab 0 c

  -- K_[a,b,c,d].
  Kq : ℕ → ℕ → ℕ → ℕ → Word (Gate (suc k))
  Kq a b c d = Xab 0 a • Xab 1 b • Xab 2 c • Xab 3 d • NKw • Xab 3 d • Xab 2 c • Xab 1 b • Xab 0 a

  -- The substring written Ω in Figure 7.
  Ω : Word (Gate (suc k))
  Ω = Kq 4 5 6 7 • NKw • T 3 • NKw • Kq 4 5 6 7

------------------------------------------------------------------------
-- Figure 7: R₈₄

infix 4 _===₇_

data _===₇_ {k : ℕ} : WRel (Gate (suc k)) where
  r83  : m0 • m0 ===₇ ε
  r84  : NKw • NKw ===₇ ε
  r85  : T 1 • m0 ===₇ m0 • T 1
  r86  : T 2 • m0 ===₇ m0 • T 2
  r87  : T 3 • m0 ===₇ m0 • T 3
  r88  : T 4 • m0 ===₇ m0 • T 4
  r89  : T 5 • m0 ===₇ m0 • T 5
  r90  : T 6 • m0 ===₇ m0 • T 6
  r91  : T 4 • NKw ===₇ NKw • T 4
  r92  : T 5 • NKw ===₇ NKw • T 5
  r93  : T 6 • NKw ===₇ NKw • T 6
  r94  : m 4 • NKw ===₇ NKw • m 4
  r95  : m0 • m 4 ===₇ m 4 • m0
  r96  : NKw • Kq 4 5 6 7 ===₇ Kq 4 5 6 7 • NKw
  r97  : T 0 • NKw ===₇ NKw • Xab 1 3 • m 1 • m 3
  r98  : T 1 • NKw ===₇ m0 • NKw • m0 • NKw • m0
  r99  : T 2 • NKw ===₇ NKw • Xab 1 3
  r100 : NKw • Kq 1 3 4 5 ===₇ Kq 2 3 4 5 • Kq 0 1 2 4
  r101 : m0 • m 4 • Xab 0 4 • Ω • Xab 0 4 • m 4 • m0 ===₇ Ω

------------------------------------------------------------------------
-- Figure 8

infix 4 _===₈_

data _===₈_ {k : ℕ} : WRel (Gate (suc (suc k))) where
  r102 : H2 • X0 ===₈ X0 • H2
  r103 : H2 • CX01 ===₈ CX01 • H2
  r104 : H2 • CCX12 ===₈ K01 • K12 • CCZw • K12 • K01 • H2
  r105 : H2 • CCZw ===₈ CCX01 • H2
  r106 : H2 • K12 ===₈ K12 • H2
  r107 : H2 • NKw ===₈ NKw • H2
  r108 : H2 • H2 ===₈ ε

------------------------------------------------------------------------
-- The relation r_K of Section 5.5, missing from R₁

infix 4 _===ᴷ_

data _===ᴷ_ {k : ℕ} : WRel (Gate (suc k)) where
  rK : K12 ===ᴷ X0 • NKw • X0 • NKw

------------------------------------------------------------------------
-- The presentations

-- R₁ = R₀ ∪ R₈₄ (Theorem 5.2), and R₁⁺ = R₁ ∪ {r_K}.
infix 4 _===₁_ _===₁⁺_

data _===₁_ : WRel G₁ where
  fig4 : ∀ {w v} → w ===₀ v → w ===₁ v
  fig7 : ∀ {w v} → w ===₇ v → w ===₁ v

data _===₁⁺_ : WRel G₁ where
  fig4 : ∀ {w v} → w ===₀ v → w ===₁⁺ v
  fig7 : ∀ {w v} → w ===₇ v → w ===₁⁺ v
  rK   : ∀ {w v} → w ===ᴷ v → w ===₁⁺ v

-- R₂ = R₁ ∪ Figure 8 (Theorem 6.3), and R₂⁺ = R₂ ∪ {r_K}.
infix 4 _===₂_ _===₂⁺_

data _===₂_ : WRel G₂ where
  fig4 : ∀ {w v} → w ===₀ v → w ===₂ v
  fig7 : ∀ {w v} → w ===₇ v → w ===₂ v
  fig8 : ∀ {w v} → w ===₈ v → w ===₂ v

data _===₂⁺_ : WRel G₂ where
  fig4 : ∀ {w v} → w ===₀ v → w ===₂⁺ v
  fig7 : ∀ {w v} → w ===₇ v → w ===₂⁺ v
  fig8 : ∀ {w v} → w ===₈ v → w ===₂⁺ v
  rK   : ∀ {w v} → w ===ᴷ v → w ===₂⁺ v

------------------------------------------------------------------------
-- Presentations of groups
--
-- The gates of Amy, Ross and Wesley, "A Sound and Complete Equational
-- Theory for 3-Qubit Toffoli-Hadamard Circuits" (QPL 2024,
-- arXiv:2407.11152), by the level at which they enter:
--
--   level 0, the Toffoli-K gates 𝒟 of Section 4.1:
--     X_j, Z_j, CX_{j,k}, CZ_{j,k}, CCX_{j,k}, K_{0,1}, K_{1,2} and
--     the swaps σ_{j,k} (written SW here);
--   level 1, Σ₁ = 𝒟 ∪ {K_[0,1,2,3], CCZ} of Section 5.6 (NK is the
--     paper's K_[0,1,2,3], the K₁₂ gate controlled negatively by
--     qubit 0);
--   level 2, Σ₂ = Σ₁ ∪ {H₂} of Section 6.
--
-- A gate of level k is a letter of `Gate k′` for every k′ ≥ k, so the
-- letters keep their names across the three alphabets.  Qubit 0 is
-- the most significant: basis state |x₀x₁x₂⟩ is index 4x₀ + 2x₁ + x₂.
-- CX_{j,k} has control j and target k, CCX_{j,k} has controls j and k,
-- and words are in operator order (the rightmost letter acts first).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Gates where

open import Data.Nat.Base using (ℕ ; zero ; suc)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Letters

data Gate : ℕ → Set where
  X₀ X₁ X₂ Z₀ Z₁ Z₂                 : Gate k
  CX₀₁ CX₀₂ CX₁₀ CX₁₂ CX₂₀ CX₂₁     : Gate k
  CZ₀₁ CZ₀₂ CZ₁₂                    : Gate k
  CCX₀₁ CCX₀₂ CCX₁₂                 : Gate k
  K₀₁ K₁₂                           : Gate k
  SW₀₁ SW₀₂ SW₁₂                    : Gate k
  NK CCZ                            : Gate (suc k)
  H₂                                : Gate (suc (suc k))

-- Toffoli-K circuits, circuits over Σ₁ and over Σ₂.
Gᴰ G₁ G₂ : Set
Gᴰ = Gate 0
G₁ = Gate 1
G₂ = Gate 2

-- A letter of one level is a letter of the next.
up : Gate k → Gate (suc k)
up X₀ = X₀
up X₁ = X₁
up X₂ = X₂
up Z₀ = Z₀
up Z₁ = Z₁
up Z₂ = Z₂
up CX₀₁ = CX₀₁
up CX₀₂ = CX₀₂
up CX₁₀ = CX₁₀
up CX₁₂ = CX₁₂
up CX₂₀ = CX₂₀
up CX₂₁ = CX₂₁
up CZ₀₁ = CZ₀₁
up CZ₀₂ = CZ₀₂
up CZ₁₂ = CZ₁₂
up CCX₀₁ = CCX₀₁
up CCX₀₂ = CCX₀₂
up CCX₁₂ = CCX₁₂
up K₀₁ = K₀₁
up K₁₂ = K₁₂
up SW₀₁ = SW₀₁
up SW₀₂ = SW₀₂
up SW₁₂ = SW₁₂
up NK = NK
up CCZ = CCZ
up H₂ = H₂

↑ʷ : Word (Gate k) → Word (Gate (suc k))
↑ʷ = wmap up

------------------------------------------------------------------------
-- One-letter words

X0 X1 X2 Z0 Z1 Z2 CX01 CX02 CX10 CX12 CX20 CX21 CZ01 CZ02 CZ12
  CCX01 CCX02 CCX12 K01 K12 SW01 SW02 SW12 : Word (Gate k)
X0 = [ X₀ ]ʷ
X1 = [ X₁ ]ʷ
X2 = [ X₂ ]ʷ
Z0 = [ Z₀ ]ʷ
Z1 = [ Z₁ ]ʷ
Z2 = [ Z₂ ]ʷ
CX01 = [ CX₀₁ ]ʷ
CX02 = [ CX₀₂ ]ʷ
CX10 = [ CX₁₀ ]ʷ
CX12 = [ CX₁₂ ]ʷ
CX20 = [ CX₂₀ ]ʷ
CX21 = [ CX₂₁ ]ʷ
CZ01 = [ CZ₀₁ ]ʷ
CZ02 = [ CZ₀₂ ]ʷ
CZ12 = [ CZ₁₂ ]ʷ
CCX01 = [ CCX₀₁ ]ʷ
CCX02 = [ CCX₀₂ ]ʷ
CCX12 = [ CCX₁₂ ]ʷ
K01 = [ K₀₁ ]ʷ
K12 = [ K₁₂ ]ʷ
SW01 = [ SW₀₁ ]ʷ
SW02 = [ SW₀₂ ]ʷ
SW12 = [ SW₁₂ ]ʷ

NKw CCZw : Word (Gate (suc k))
NKw = [ NK ]ʷ
CCZw = [ CCZ ]ʷ

H2 : Word (Gate (suc (suc k)))
H2 = [ H₂ ]ʷ

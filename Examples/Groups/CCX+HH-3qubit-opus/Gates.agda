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

open import Data.Nat.Base using (ℕ ; zero ; suc ; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; trans ; cong)

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
-- Codes

-- An injective code, for comparing letters by computation.
code : Gate k → ℕ
code X₀    = 0
code X₁    = 1
code X₂    = 2
code Z₀    = 3
code Z₁    = 4
code Z₂    = 5
code CX₀₁  = 6
code CX₀₂  = 7
code CX₁₀  = 8
code CX₁₂  = 9
code CX₂₀  = 10
code CX₂₁  = 11
code CZ₀₁  = 12
code CZ₀₂  = 13
code CZ₁₂  = 14
code CCX₀₁ = 15
code CCX₀₂ = 16
code CCX₁₂ = 17
code K₀₁   = 18
code K₁₂   = 19
code SW₀₁  = 20
code SW₀₂  = 21
code SW₁₂  = 22
code NK    = 23
code CCZ   = 24
code H₂    = 25

decode : (k : ℕ) → ℕ → Gate k
decode′ : (k : ℕ) → ℕ → Gate k

decode _ 0 = X₀
decode _ 1 = X₁
decode _ 2 = X₂
decode _ 3 = Z₀
decode _ 4 = Z₁
decode _ 5 = Z₂
decode _ 6 = CX₀₁
decode _ 7 = CX₀₂
decode _ 8 = CX₁₀
decode _ 9 = CX₁₂
decode _ 10 = CX₂₀
decode _ 11 = CX₂₁
decode _ 12 = CZ₀₁
decode _ 13 = CZ₀₂
decode _ 14 = CZ₁₂
decode _ 15 = CCX₀₁
decode _ 16 = CCX₀₂
decode _ 17 = CCX₁₂
decode _ 18 = K₀₁
decode _ 19 = K₁₂
decode k n = decode′ k (n ∸ 20)

decode′ _ 0 = SW₀₁
decode′ _ 1 = SW₀₂
decode′ _ 2 = SW₁₂
decode′ (suc _) 3 = NK
decode′ (suc _) 4 = CCZ
decode′ (suc (suc _)) 5 = H₂
decode′ _ _ = X₀

decode-code : (g : Gate k) → decode k (code g) ≡ g
decode-code X₀ = refl
decode-code X₁ = refl
decode-code X₂ = refl
decode-code Z₀ = refl
decode-code Z₁ = refl
decode-code Z₂ = refl
decode-code CX₀₁ = refl
decode-code CX₀₂ = refl
decode-code CX₁₀ = refl
decode-code CX₁₂ = refl
decode-code CX₂₀ = refl
decode-code CX₂₁ = refl
decode-code CZ₀₁ = refl
decode-code CZ₀₂ = refl
decode-code CZ₁₂ = refl
decode-code CCX₀₁ = refl
decode-code CCX₀₂ = refl
decode-code CCX₁₂ = refl
decode-code K₀₁ = refl
decode-code K₁₂ = refl
decode-code SW₀₁ = refl
decode-code SW₀₂ = refl
decode-code SW₁₂ = refl
decode-code NK = refl
decode-code CCZ = refl
decode-code H₂ = refl

code-inj : {x y : Gate k} → code x ≡ code y → x ≡ y
code-inj {k} {x} {y} e = trans (sym (decode-code x)) (trans (cong (decode k) e) (decode-code y))

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

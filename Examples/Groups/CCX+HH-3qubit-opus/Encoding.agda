------------------------------------------------------------------------
-- Presentations of groups
--
-- Every gate written as a word over the one-, two- and four-level
-- generators of Li, Ross and Selinger (CCX+HH-TwoLevel), at n = 8:
--
--   a permutation gate is the product of the transpositions X_[a,b] of
--   the basis states it exchanges, a diagonal gate the product of the
--   (-1)_[a] it negates, K₁₂ = K_[0,1,2,3] K_[4,5,6,7] and K₀₁ =
--   K_[0,2,4,6] K_[1,3,5,7] (H ⊗ H on the pairs of qubits, the other one
--   fixed), K_[0,1,2,3] itself, CCZ = (-1)_[7], and H₂ the global
--   generator I ⊗ H of §5 of Li-Ross-Selinger.
--
-- These words are the semantics: a circuit denotes the matrix of its
-- encoding (Semantics), and that each gate's matrix is the expected one
-- is checked entry by entry (GateMatrices).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Encoding where

open import Data.Bool.Base using (T)
open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin ; toℕ ; _<_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics as L
  using (Gen ; M-gen ; X-gen ; K-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics
  using (Genᴸ ; ⌊_⌋ʷ ; IH)

open import Examples.Groups.CCX+HH-3qubit-opus.Gates

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- Two-level letters at literal indices

-- The order side conditions, by evaluation.
lt : (a b : Fin 8) → {T (toℕ a <ᵇ toℕ b)} → a < b
lt a b {p} = <ᵇ⇒< (toℕ a) (toℕ b) p

M[_] : Fin 8 → Word (Gen 8)
M[ a ] = [ M-gen a ]ʷ

X[_,_] : (a b : Fin 8) → {T (toℕ a <ᵇ toℕ b)} → Word (Gen 8)
X[ a , b ] {p} = [ X-gen a b (lt a b {p}) ]ʷ

K[_,_,_,_] : (a b c d : Fin 8) → {T (toℕ a <ᵇ toℕ b)} → {T (toℕ b <ᵇ toℕ c)} → {T (toℕ c <ᵇ toℕ d)} →
             Word (Gen 8)
K[ a , b , c , d ] {p} {q} {r} = [ K-gen a b c d (lt a b {p}) (lt b c {q}) (lt c d {r}) ]ʷ

------------------------------------------------------------------------
-- The encoding

-- The letters of Σ₁; H₂, which has no matrix over 𝔻, is sent to ε here
-- and handled by encᴸ.
enc : Gate k → Word (Gen 8)
enc X₀    = X[ # 0 , # 4 ] • X[ # 1 , # 5 ] • X[ # 2 , # 6 ] • X[ # 3 , # 7 ]
enc X₁    = X[ # 0 , # 2 ] • X[ # 1 , # 3 ] • X[ # 4 , # 6 ] • X[ # 5 , # 7 ]
enc X₂    = X[ # 0 , # 1 ] • X[ # 2 , # 3 ] • X[ # 4 , # 5 ] • X[ # 6 , # 7 ]
enc Z₀    = M[ # 4 ] • M[ # 5 ] • M[ # 6 ] • M[ # 7 ]
enc Z₁    = M[ # 2 ] • M[ # 3 ] • M[ # 6 ] • M[ # 7 ]
enc Z₂    = M[ # 1 ] • M[ # 3 ] • M[ # 5 ] • M[ # 7 ]
enc CX₀₁  = X[ # 4 , # 6 ] • X[ # 5 , # 7 ]
enc CX₀₂  = X[ # 4 , # 5 ] • X[ # 6 , # 7 ]
enc CX₁₀  = X[ # 2 , # 6 ] • X[ # 3 , # 7 ]
enc CX₁₂  = X[ # 2 , # 3 ] • X[ # 6 , # 7 ]
enc CX₂₀  = X[ # 1 , # 5 ] • X[ # 3 , # 7 ]
enc CX₂₁  = X[ # 1 , # 3 ] • X[ # 5 , # 7 ]
enc CZ₀₁  = M[ # 6 ] • M[ # 7 ]
enc CZ₀₂  = M[ # 5 ] • M[ # 7 ]
enc CZ₁₂  = M[ # 3 ] • M[ # 7 ]
enc CCX₀₁ = X[ # 6 , # 7 ]
enc CCX₀₂ = X[ # 5 , # 7 ]
enc CCX₁₂ = X[ # 3 , # 7 ]
enc K₀₁   = K[ # 0 , # 2 , # 4 , # 6 ] • K[ # 1 , # 3 , # 5 , # 7 ]
enc K₁₂   = K[ # 0 , # 1 , # 2 , # 3 ] • K[ # 4 , # 5 , # 6 , # 7 ]
enc SW₀₁  = X[ # 2 , # 4 ] • X[ # 3 , # 5 ]
enc SW₀₂  = X[ # 1 , # 4 ] • X[ # 3 , # 6 ]
enc SW₁₂  = X[ # 1 , # 2 ] • X[ # 5 , # 6 ]
enc NK    = K[ # 0 , # 1 , # 2 , # 3 ]
enc CCZ   = M[ # 7 ]
enc H₂    = ε

-- The letters of Σ₂.
encᴸ : Gate k → Word (Genᴸ 8)
encᴸ H₂ = [ IH ]ʷ
encᴸ g@X₀ = ⌊ enc g ⌋ʷ
encᴸ g@X₁ = ⌊ enc g ⌋ʷ
encᴸ g@X₂ = ⌊ enc g ⌋ʷ
encᴸ g@Z₀ = ⌊ enc g ⌋ʷ
encᴸ g@Z₁ = ⌊ enc g ⌋ʷ
encᴸ g@Z₂ = ⌊ enc g ⌋ʷ
encᴸ g@CX₀₁ = ⌊ enc g ⌋ʷ
encᴸ g@CX₀₂ = ⌊ enc g ⌋ʷ
encᴸ g@CX₁₀ = ⌊ enc g ⌋ʷ
encᴸ g@CX₁₂ = ⌊ enc g ⌋ʷ
encᴸ g@CX₂₀ = ⌊ enc g ⌋ʷ
encᴸ g@CX₂₁ = ⌊ enc g ⌋ʷ
encᴸ g@CZ₀₁ = ⌊ enc g ⌋ʷ
encᴸ g@CZ₀₂ = ⌊ enc g ⌋ʷ
encᴸ g@CZ₁₂ = ⌊ enc g ⌋ʷ
encᴸ g@CCX₀₁ = ⌊ enc g ⌋ʷ
encᴸ g@CCX₀₂ = ⌊ enc g ⌋ʷ
encᴸ g@CCX₁₂ = ⌊ enc g ⌋ʷ
encᴸ g@K₀₁ = ⌊ enc g ⌋ʷ
encᴸ g@K₁₂ = ⌊ enc g ⌋ʷ
encᴸ g@SW₀₁ = ⌊ enc g ⌋ʷ
encᴸ g@SW₀₂ = ⌊ enc g ⌋ʷ
encᴸ g@SW₁₂ = ⌊ enc g ⌋ʷ
encᴸ g@NK = ⌊ enc g ⌋ʷ
encᴸ g@CCZ = ⌊ enc g ⌋ʷ

-- On words.
encʷ : Word (Gate k) → Word (Gen 8)
encʷ = enc ʷ

encᴸʷ : Word (Gate k) → Word (Genᴸ 8)
encᴸʷ = encᴸ ʷ

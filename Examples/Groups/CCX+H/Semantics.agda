------------------------------------------------------------------------
-- Presentations of groups
--
-- Direct matrices for X, CX, CCX and H, independently of the encoder.
--
-- X/CX/CCX act by their Boolean permutations.  H has entry
-- (-1)^(r_p c_p)/sqrt(2) when all other bits agree, and zero otherwise.
-- Wire 0 is the least significant bit; products are in operator order.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Semantics where

open import Data.Bool.Base using (_∧_ ; if_then_else_)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Nat.Base using (ℕ ; suc ; _+_ ; _∸_ ; _≡ᵇ_)
  renaming (_^_ to _^ℕ_)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Examples.Groups.CCX+H.Syntactics
open import Examples.Groups.CCX+HH.Encoding using (bit)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring using (D ; √½)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (RingD ; 0ᴰ ; 1ᴰ ; -ᴰ_)

private
  variable
    n : ℕ

flip clear : ℕ → ℕ → ℕ
flip a p = if bit a p then a ∸ 2 ^ℕ p else a + 2 ^ℕ p
clear a p = if bit a p then a ∸ 2 ^ℕ p else a

-- These permutations are involutions, so the inverse row action has
-- the same formula as the action on computational basis vectors.
permutation : View → ℕ → ℕ
permutation (at-X p) a = flip a p
permutation (at-CX p) a =
  if bit a (suc p) then flip a p else a
permutation (at-CCX p) a =
  if bit a (suc p) ∧ bit a (suc (suc p)) then flip a p else a
permutation (at-H p) a = a

classical : View → Fin (2 ^ℕ n) → Fin (2 ^ℕ n) → D
classical g r c =
  if permutation g (toℕ r) ≡ᵇ toℕ c then 1ᴰ else 0ᴰ

hadamard : ℕ → Fin (2 ^ℕ n) → Fin (2 ^ℕ n) → D
hadamard p r c =
  if clear (toℕ r) p ≡ᵇ clear (toℕ c) p
  then (if bit (toℕ r) p ∧ bit (toℕ c) p then -ᴰ √½ else √½)
  else 0ᴰ

coefficient : View → Fin (2 ^ℕ n) → Fin (2 ^ℕ n) → D
coefficient {n} (at-H p) = hadamard {n} p
coefficient {n} (at-X p) = classical {n} (at-X p)
coefficient {n} (at-CX p) = classical {n} (at-CX p)
coefficient {n} (at-CCX p) = classical {n} (at-CCX p)

gate-matrix : Gen n → Matrix (2 ^ℕ n) (2 ^ℕ n) D
gate-matrix {n} g = S.mk (coefficient {n} (view g))

interpret : Circuit n → Matrix (2 ^ℕ n) (2 ^ℕ n) D
interpret [ g ]ʷ = gate-matrix g
interpret ε = S.𝕀
interpret (w • v) = interpret w ·*· interpret v

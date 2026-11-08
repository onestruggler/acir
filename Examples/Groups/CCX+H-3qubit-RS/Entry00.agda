------------------------------------------------------------------------
-- Presentations of groups
--
-- The exponent of 1/2 in the entry at (0, 0) of a matrix over 𝔻, in a
-- module of its own: Quantum.Synthesis.Ring, which names the field,
-- also brings an instance Ring Dyadic into scope, which makes Ring D
-- ambiguous wherever it is imported.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Entry00 where

open import Data.Nat.Base using (ℕ)
open import Data.Vec.Base using (head)

import Quantum.Synthesis.Ring as QR
open import Quantum.Synthesis.Matrix using (Matrix)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (D)

exp00 : Matrix 8 8 D → ℕ
exp00 A = QR.Dyadic.exponent (head (head (Matrix.unMatrix A)))

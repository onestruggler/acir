------------------------------------------------------------------------
-- Presentations of groups
--
-- The matrix semantics.  A circuit over Σ₁ (in particular a Toffoli-K
-- circuit) denotes an orthogonal 8 × 8 matrix over 𝔻 = ℤ[1/2], an
-- element of the group O(8, 𝔻) of CCX+HH-TwoLevel; a circuit over Σ₂
-- denotes an orthogonal scaled dyadic matrix over ℤ[1/√2], an element
-- of the group L₈ = TofH(3) of CCX+HH-TwoLevel.Scaled.  In both cases
-- the matrix is that of the circuit's encoding (Encoding), so ⟦_⟧ is a
-- monoid homomorphism by those developments, and GateMatrices checks
-- that each gate denotes its usual matrix.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit-opus.Semantics where

open import Algebra.Bundles using (Group)
open import Data.Nat.Base using (ℕ)
open import Level using (0ℓ)
open import Data.Product.Base using (_,_ ; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Word.Base using (Word ; _•_)
import Examples.Groups.CCX+HH-TwoLevel.Ring as R1
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SL
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as RL
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Presentation as LP
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)

open import Examples.Groups.CCX+HH-3qubit-opus.Gates
open import Examples.Groups.CCX+HH-3qubit-opus.Encoding

private
  variable
    k : ℕ

------------------------------------------------------------------------
-- In O(8, 𝔻)

-- The group, and the matrices over 𝔻.
O8 : Group 0ℓ 0ℓ
O8 = S1.O 8

𝔻 : Set
𝔻 = R1.D

⟦_⟧ : Word (Gate k) → Matrix 8 8 𝔻
⟦ w ⟧ = S1.⟦ encʷ w ⟧ᵐ

⟦_⟧ᵒ : Word (Gate k) → S1.OMat 8
⟦ w ⟧ᵒ = ⟦ w ⟧ , S1.Unitary-⟦⟧ᵐ (encʷ w)

⟦•⟧ : (u w : Word (Gate k)) → ⟦ u • w ⟧ ≡ ⟦ u ⟧ ·*· ⟦ w ⟧
⟦•⟧ u w = S1.⟦•⟧ᵐ (encʷ u) (encʷ w)

------------------------------------------------------------------------
-- In TofH(3) = L₈

-- The group L₈ (n = 2 (3 + 1)), and the matrices over ℤ[1/√2].
TofH3 : Group 0ℓ 0ℓ
TofH3 = LP.L 3

ℤ[1/√2] : Set
ℤ[1/√2] = RL.D

open SL.Dim 4 using (⟦_⟧ᴸ ; ⟦•⟧ᴸ ; Unitary-⟦⟧ᴸ)

⟦_⟧ᴴ : Word (Gate k) → Matrix 8 8 ℤ[1/√2]
⟦ w ⟧ᴴ = ⟦ encᴸʷ w ⟧ᴸ

⟦•⟧ᴴ : (u w : Word (Gate k)) → ⟦ u • w ⟧ᴴ ≡ ⟦ u ⟧ᴴ ·*· ⟦ w ⟧ᴴ
⟦•⟧ᴴ u w = ⟦•⟧ᴸ (encᴸʷ u) (encᴸʷ w)

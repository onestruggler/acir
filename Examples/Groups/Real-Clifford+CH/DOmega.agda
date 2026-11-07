------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's real Clifford+CH circuits, read in U_{2ⁿ}(𝔻[ω])
--
-- Figure 4 is a sub-presentation of O_{2ⁿ}(ℤ[1/√2]) at every width
-- (Presentation.subpresentationᴼ, Theorem 8.9), and O_{2ⁿ}(ℤ[1/√2])
-- is a subgroup of U_{2ⁿ}(𝔻[ω]) (Real-Clifford+CH-TwoLevel.DOmega), so
-- Figure 4 is a sub-presentation of U_{2ⁿ}(𝔻[ω]): two circuits are
-- equal by Figure 4 and the swap rules exactly when their matrices over
-- 𝔻[ω] are equal (sound, complete).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH.DOmega where

open import Data.Nat.Base using (ℕ ; _^_)

open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Real-Clifford+CH.Syntactics using (_VRel,_===_)
import Examples.Groups.Real-Clifford+CH.Presentation as P
import Examples.Groups.Real-Clifford+CH-TwoLevel.DOmega as RΩ
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)

presentation : ∀ n → (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
presentation n = RΩ.Embed.along (2 ^ n) (P.subpresentationᴼ n)

module _ {n : ℕ} where

  open PE.Sub (presentation n) public using (⟦_⟧ ; sound ; complete)

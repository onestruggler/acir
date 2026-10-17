------------------------------------------------------------------------
-- Presentations of groups
--
-- X on the top wire as a placed letter
--
-- Lambda.Placed shows that S on the top wire of k + 1 wires is S on the
-- bottom wire placed by any network that sends the top wire to wire 0
-- (`Sᵗ-placed`).  The same holds for X, by the same argument (`HX-up`:
-- a placement survives ↑, Lambda.Placed.up-step), which is what carries
-- the X of a white controlled letter along the networks that move its
-- S-box (Stable.Mix789).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.XPlace where

open import Data.Fin using (Fin ; toℕ ; inject₁ ; fromℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.PermCalc using (perm ; revS ; perm-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (bring₁)
open import Examples.Groups.Clifford+CS.NetTop using (topS)
open import Examples.Groups.Clifford+CS.Lambda using (Xᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Placed using (cycS ; up-step ; perm-up)

private
  variable
    n : ℕ

  back-to : ∀ {w} (ν : Word (S.Gen w)) {a i} → perm ν ⟨$⟩ʳ a ≡ i → perm (revS ν) ⟨$⟩ʳ i ≡ a
  back-to ν {a} e = Eq.subst (λ x → perm (revS ν) ⟨$⟩ʳ x ≡ a) e (perm-inv ν a)

  agree1 : ∀ {r} (ν τ : Word (S.Gen (₁₊ r))) {a} → perm ν ⟨$⟩ʳ a ≡ 0F → perm τ ⟨$⟩ʳ a ≡ 0F →
           ∀ (j : Fin (₁₊ r)) → toℕ j < 1 → perm τ ⟨$⟩ʳ (perm (revS ν) ⟨$⟩ʳ j) ≡ j
  agree1 ν τ eν eτ 0F     _        = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν eν)) eτ
  agree1 ν τ eν eτ (sF j) (s≤s ())

  pl-ε : ∀ {w} (g : Circuit w) → w ⊢ pl ε g ≈ g
  pl-ε g = PB.trans PB.left-unit PB.right-unit

-- The letter L is X on wire t placed by any network sending t to 0.
HX : ∀ r → Fin (₁₊ r) → Circuit (₁₊ r) → Set
HX r t L = ∀ (τ : Word (S.Gen (₁₊ r))) → perm τ ⟨$⟩ʳ t ≡ 0F → (₁₊ r) ⊢ L ≈ pl τ (X {0} ↓ᵏ r)

HX-base : HX 0 0F X
HX-base τ τt = PB.trans (PB.sym (pl-ε X)) (place-eq {k = 1} X ε τ (agree1 ε τ Eq.refl τt))

HX-up : ∀ r (t : Fin (₁₊ r)) (L : Circuit (₁₊ r)) → HX r t L → HX (suc r) (sF t) (L ↑)
HX-up r t L h τ τt =
  PB.trans (up-step L (X {0} ↓ᵏ r) τ′ (h τ′ (proj₂ B)))
           (place-eq {k = 1} X ν τ (agree1 ν τ νt τt))
  where
  B  = bring₁ t
  τ′ = proj₁ B
  ν  = cycS (₁₊ r) • topS τ′
  νt : perm ν ⟨$⟩ʳ sF t ≡ 0F
  νt = Eq.trans (perm-up τ′ t) (Eq.cong inject₁ (proj₂ B))

-- X on the top wire.
Xᵗ-placed : ∀ k → HX k (fromℕ k) (Xᵗ k)
Xᵗ-placed zero    = HX-base
Xᵗ-placed (suc k) = HX-up k (fromℕ k) (Xᵗ k) (Xᵗ-placed k)

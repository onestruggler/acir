------------------------------------------------------------------------
-- Presentations of groups
--
-- A swap network with one more wire on top
--
-- `topS u` is the network u at the next width, the new wire on top
-- untouched: its circuit is u's with an idle top wire (`net-top`), its
-- reverse is the widened reverse (`revS-top`), and it sends a wire below
-- the top where u does (`perm-top`, the top wire fixed: `perm-top-last`).
-- So a gate placed by u, with an idle wire on top, is the gate placed by
-- topS u (`pl-top`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.NetTop where

open import Data.Fin using (Fin ; inject₁ ; fromℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₁₊ ; ₂₊)

import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; perm ; revS)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl)
open import Examples.Groups.Clifford+CS.Lambda.Split using (top-↑)
open import Examples.Groups.Clifford+CS.Networks using (perm-↑0 ; perm-↑s)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The widened network

_↧S : S.Gen n → S.Gen (₁₊ n)
S.gate₀ h ↧S = S.gate₀ h
S.gate₁ h ↧S = S.gate₁ h
S.gate₂ h ↧S = S.gate₂ h
(g S.↥)   ↧S = (g ↧S) S.↥

topS : Word (S.Gen n) → Word (S.Gen (₁₊ n))
topS = wmap _↧S

net-top : ∀ (u : Word (S.Gen n)) → net (topS u) ≡ top (net u)
net-top [ g ]ʷ  = gen g
  where
  gen : ∀ {n} (g : S.Gen n) → net [ g ↧S ]ʷ ≡ top (net [ g ]ʷ)
  gen (S.gate₀ ())
  gen (S.gate₁ ())
  gen (S.gate₂ S.σ-gate) = Eq.refl
  gen (g S.↥) = Eq.trans (Eq.cong _↑ (gen g)) (Eq.sym (top-↑ (net [ g ]ʷ)))
net-top ε       = Eq.refl
net-top (u • v) = Eq.cong₂ _•_ (net-top u) (net-top v)

revS-top : ∀ (u : Word (S.Gen n)) → revS (topS u) ≡ topS (revS u)
revS-top [ g ]ʷ  = Eq.refl
revS-top ε       = Eq.refl
revS-top (u • v) = Eq.cong₂ _•_ (revS-top v) (revS-top u)

perm-top : ∀ (u : Word (S.Gen n)) (k : Fin n) → perm (topS u) ⟨$⟩ʳ inject₁ k ≡ inject₁ (perm u ⟨$⟩ʳ k)
perm-top [ g ]ʷ  k = gen g k
  where
  gen : ∀ {n} (g : S.Gen n) (k : Fin n) → perm [ g ↧S ]ʷ ⟨$⟩ʳ inject₁ k ≡ inject₁ (perm [ g ]ʷ ⟨$⟩ʳ k)
  gen (S.gate₀ ())
  gen (S.gate₁ ())
  gen (S.gate₂ S.σ-gate) 0F          = Eq.refl
  gen (S.gate₂ S.σ-gate) (sF 0F)     = Eq.refl
  gen (S.gate₂ S.σ-gate) (sF (sF k)) = Eq.refl
  gen (g S.↥) 0F     = Eq.trans (perm-↑0 [ g ↧S ]ʷ) (Eq.cong inject₁ (Eq.sym (perm-↑0 [ g ]ʷ)))
  gen (g S.↥) (sF k) =
    Eq.trans (perm-↑s [ g ↧S ]ʷ (inject₁ k))
      (Eq.trans (Eq.cong sF (gen g k)) (Eq.cong inject₁ (Eq.sym (perm-↑s [ g ]ʷ k))))
perm-top ε       k = Eq.refl
perm-top (u • v) k = Eq.trans (Eq.cong (perm (topS v) ⟨$⟩ʳ_) (perm-top u k)) (perm-top v (perm u ⟨$⟩ʳ k))

-- A placement with an idle wire on top.
pl-top : ∀ (u : Word (S.Gen n)) (g : Circuit n) → top (pl u g) ≡ pl (topS u) (top g)
pl-top u g = Eq.sym (Eq.cong₂ (λ a b → a • top g • b) (net-top u)
                      (Eq.trans (Eq.cong net (revS-top u)) (net-top (revS u))))

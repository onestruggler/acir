------------------------------------------------------------------------
-- Presentations of groups
--
-- Frames: networks with idle wires on top
--
-- The λ-calculus at every width reduces an equation between letters on
-- a few wires of a wide circuit to one between closed letters on few
-- wires: a network τ brings the wires to the bottom, and each letter is
-- τ applied to a closed letter widened by idle wires (LocalPlace.pl).
-- Here the tools for the second half: a network on k wires widened by r
-- idle wires on top (`wid`) is the same network (`net-wid`, `revS-wid`,
-- `perm-wid`), so a placement widened is the widened placement
-- (`pl-wid`), and a placement inside a placement is one placement
-- (`pl-in`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Wide.Frame where

open import Data.Fin using (Fin ; _↑ˡ_) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

import Circuit.Base
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.PermCalc using (net ; net-↑ ; perm ; revS ; revS-↑)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-pl)
open import Examples.Groups.Clifford+CS.Networks using (perm-↑0 ; perm-↑s)
open import Examples.Groups.Clifford+CS.Weakening using (↑-↓ᵏ)

private
  module SC = Circuit.Base S.Gate

  variable
    k : ℕ

------------------------------------------------------------------------
-- A network with r idle wires on top

wid : (r : ℕ) → Word (S.Gen k) → Word (S.Gen (k +ℕ r))
wid r = wmap (SC._↧ᵏ r)

net-wid : ∀ r (ν : Word (S.Gen k)) → net (wid r ν) ≡ net ν ↓ᵏ r
net-wid r [ g ]ʷ  = gen g
  where
  gen : ∀ {k} (g : S.Gen k) → net [ g SC.↧ᵏ r ]ʷ ≡ net [ g ]ʷ ↓ᵏ r
  gen (S.gate₀ ())
  gen (S.gate₁ ())
  gen (S.gate₂ S.σ-gate) = Eq.refl
  gen (g S.↥) = Eq.trans (Eq.cong _↑ (gen g)) (Eq.sym (↑-↓ᵏ (net [ g ]ʷ) r))
net-wid r ε       = Eq.refl
net-wid r (u • v) = Eq.cong₂ _•_ (net-wid r u) (net-wid r v)

revS-wid : ∀ r (ν : Word (S.Gen k)) → revS (wid r ν) ≡ wid r (revS ν)
revS-wid r [ g ]ʷ  = Eq.refl
revS-wid r ε       = Eq.refl
revS-wid r (u • v) = Eq.cong₂ _•_ (revS-wid r v) (revS-wid r u)

perm-wid : ∀ r (ν : Word (S.Gen k)) (x : Fin k) →
           perm (wid r ν) ⟨$⟩ʳ (x ↑ˡ r) ≡ (perm ν ⟨$⟩ʳ x) ↑ˡ r
perm-wid r [ g ]ʷ  x = gen g x
  where
  gen : ∀ {k} (g : S.Gen k) (x : Fin k) →
        perm [ g SC.↧ᵏ r ]ʷ ⟨$⟩ʳ (x ↑ˡ r) ≡ (perm [ g ]ʷ ⟨$⟩ʳ x) ↑ˡ r
  gen (S.gate₀ ())
  gen (S.gate₁ ())
  gen (S.gate₂ S.σ-gate) 0F          = Eq.refl
  gen (S.gate₂ S.σ-gate) (sF 0F)     = Eq.refl
  gen (S.gate₂ S.σ-gate) (sF (sF x)) = Eq.refl
  gen (g S.↥) 0F     = Eq.trans (perm-↑0 [ g SC.↧ᵏ r ]ʷ) (Eq.cong (_↑ˡ r) (Eq.sym (perm-↑0 [ g ]ʷ)))
  gen (g S.↥) (sF x) =
    Eq.trans (perm-↑s [ g SC.↧ᵏ r ]ʷ (x ↑ˡ r))
      (Eq.trans (Eq.cong sF (gen g x)) (Eq.cong (_↑ˡ r) (Eq.sym (perm-↑s [ g ]ʷ x))))
perm-wid r ε       x = Eq.refl
perm-wid r (u • v) x =
  Eq.trans (Eq.cong (perm (wid r v) ⟨$⟩ʳ_) (perm-wid r u x)) (perm-wid r v (perm u ⟨$⟩ʳ x))

-- A placement with idle wires on top.
pl-wid : ∀ r (ν : Word (S.Gen k)) (c : Circuit k) → (pl ν c) ↓ᵏ r ≡ pl (wid r ν) (c ↓ᵏ r)
pl-wid r ν c = Eq.sym (Eq.cong₂ (λ a b → a • (c ↓ᵏ r) • b) (net-wid r ν)
                        (Eq.trans (Eq.cong net (revS-wid r ν)) (net-wid r (revS ν))))

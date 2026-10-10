------------------------------------------------------------------------
-- Presentations of groups
--
-- On four indices, in any set of relations Γ that derives the local
-- ones: Clément's (20) gives the diagram of his Subcase 3.4.1, read as
-- the relation Route = H_[0,1] (as for Diagram30).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (WRel)
import Presentation.Base as PB
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.LocalRelations using (_===ˡ_)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Diagram20
  (Γ : WRel (Gen 4)) (loc : ∀ {u v} → u ===ˡ v → PB._≈_ Γ u v) where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (H-gen ; X-gen ; Z-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Engine Γ loc
open PB Γ using (_≈_)

------------------------------------------------------------------------
-- Letters

f0 f1 f2 f3 : Fin 4
f0 = zero
f1 = (suc zero)
f2 = (suc (suc zero))
f3 = (suc (suc (suc zero)))

lt01 : f0 < f1
lt01 = s≤s z≤n
lt02 : f0 < f2
lt02 = s≤s z≤n
lt03 : f0 < f3
lt03 = s≤s z≤n
lt12 : f1 < f2
lt12 = s≤s (s≤s z≤n)
lt13 : f1 < f3
lt13 = s≤s (s≤s z≤n)
lt23 : f2 < f3
lt23 = s≤s (s≤s (s≤s z≤n))

h01 : Gen 4
h01 = H-gen f0 f1 lt01
h02 : Gen 4
h02 = H-gen f0 f2 lt02
h13 : Gen 4
h13 = H-gen f1 f3 lt13
z0 : Gen 4
z0 = Z-gen f0
z1 : Gen 4
z1 = Z-gen f1

------------------------------------------------------------------------
-- The relation and the diagram as letter lists (operator order)

L20 : List (Gen 4)
L20 = (h01 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
R20 : List (Gen 4)
R20 = (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
Route : List (Gen 4)
Route = (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h13 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ z1 ∷ z0 ∷ h01 ∷ h13 ∷ h02 ∷ [])
C0w : List (Gen 4)
C0w = (h01 ∷ [])

------------------------------------------------------------------------
-- The diagram commutes

module From (r20eh : ⟪ L20 ⟫ ≈ ⟪ R20 ⟫) where

  private
    r20e : Eqn
    r20e = eqn L20 R20 r20eh

    δd20 : Eqn
    δd20 = derive (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h13 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ z1 ∷ z0 ∷ h01 ∷ h13 ∷ h02 ∷ []) (h01 ∷ [])
      ( perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h13 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h01 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 10 (ʟd1 f0 f1 lt01)
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h13 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 r20e
      ∷ rw 2 (sym⁼ (ʟd1 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h01 ∷ h13 ∷ h13 ∷ h02 ∷ h02 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 5 (ʟa3 f1 f3 lt13)
      ∷ rw 5 (ʟa3 f0 f2 lt02)
      ∷ rw 4 (ʟa3 f0 f1 lt01)
      ∷ perm (h02 ∷ h13 ∷ z0 ∷ z0 ∷ z1 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 2 (ʟa1 f0)
      ∷ perm (h02 ∷ h02 ∷ h13 ∷ z1 ∷ z1 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 0 (ʟa3 f0 f2 lt02)
      ∷ rw 1 (ʟa1 f1)
      ∷ rw 0 (ʟa3 f1 f3 lt13)
      ∷ perm (h01 ∷ [])
      ∷ perm (h01 ∷ [])
      ∷ []
      ) refl

  d20 : ⟪ Route ⟫ ≈ ⟪ C0w ⟫
  d20 = prf δd20

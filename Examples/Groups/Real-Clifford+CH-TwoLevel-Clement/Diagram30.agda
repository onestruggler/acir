------------------------------------------------------------------------
-- Presentations of groups
--
-- On six indices, in any set of relations Γ that derives the local
-- ones: Clément's (21) gives his diagram (30) (Lemma 3.17), read as the
-- relation Route = H_[0,1] where Route goes down its left side, along
-- the bottom H_[0,1] and up its right side.  Its sides are the word P of
-- (21), C₀ P = P C₀, up to commuting letters and (d1).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (WRel)
import Presentation.Base as PB
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.LocalRelations using (_===ˡ_)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Diagram30 where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (H-gen ; X-gen ; Z-gen)
import Presentation.Tactics.Words as TW

------------------------------------------------------------------------
-- Letters

f0 f1 f2 f3 f4 f5 : Fin 6
f0 = zero
f1 = (suc zero)
f2 = (suc (suc zero))
f3 = (suc (suc (suc zero)))
f4 = (suc (suc (suc (suc zero))))
f5 = (suc (suc (suc (suc (suc zero)))))

lt01 : f0 < f1
lt01 = s≤s z≤n
lt02 : f0 < f2
lt02 = s≤s z≤n
lt03 : f0 < f3
lt03 = s≤s z≤n
lt04 : f0 < f4
lt04 = s≤s z≤n
lt05 : f0 < f5
lt05 = s≤s z≤n
lt12 : f1 < f2
lt12 = s≤s (s≤s z≤n)
lt13 : f1 < f3
lt13 = s≤s (s≤s z≤n)
lt14 : f1 < f4
lt14 = s≤s (s≤s z≤n)
lt15 : f1 < f5
lt15 = s≤s (s≤s z≤n)
lt23 : f2 < f3
lt23 = s≤s (s≤s (s≤s z≤n))
lt24 : f2 < f4
lt24 = s≤s (s≤s (s≤s z≤n))
lt25 : f2 < f5
lt25 = s≤s (s≤s (s≤s z≤n))
lt34 : f3 < f4
lt34 = s≤s (s≤s (s≤s (s≤s z≤n)))
lt35 : f3 < f5
lt35 = s≤s (s≤s (s≤s (s≤s z≤n)))
lt45 : f4 < f5
lt45 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

h01 : Gen 6
h01 = H-gen f0 f1 lt01
h02 : Gen 6
h02 = H-gen f0 f2 lt02
h04 : Gen 6
h04 = H-gen f0 f4 lt04
h13 : Gen 6
h13 = H-gen f1 f3 lt13
h15 : Gen 6
h15 = H-gen f1 f5 lt15
z0 : Gen 6
z0 = Z-gen f0
z1 : Gen 6
z1 = Z-gen f1

------------------------------------------------------------------------
-- The relation and the diagram as letter lists (operator order)

L21 : List (Gen 6)
L21 = (h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
R21 : List (Gen 6)
R21 = (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
Route : List (Gen 6)
Route = (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z1 ∷ z0 ∷ h01 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ [])
C0w : List (Gen 6)
C0w = (h01 ∷ [])

------------------------------------------------------------------------
-- The diagram commutes

module From (Γ : WRel (Gen 6)) (loc : ∀ {u v} → u ===ˡ v → PB._≈_ Γ u v)
  (r21eh : PB._≈_ Γ (TW.Associative.word-of-list L21) (TW.Associative.word-of-list R21)) where

  open import Examples.Groups.Real-Clifford+CH-TwoLevel.Engine Γ loc
  open PB Γ using (_≈_)

  private
    r21e : Eqn
    r21e = eqn L21 R21 r21eh

    δd30 : Eqn
    δd30 = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z1 ∷ z0 ∷ h01 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ []) (h01 ∷ [])
      ( perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h01 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 16 (ʟd1 f0 f1 lt01)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 11 r21e
      ∷ rw 4 (sym⁼ (ʟd1 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h01 ∷ h15 ∷ h04 ∷ h13 ∷ h13 ∷ h02 ∷ h02 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 9 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h01 ∷ h15 ∷ h15 ∷ h04 ∷ h02 ∷ h02 ∷ h04 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 7 (ʟa3 f1 f5 lt15)
      ∷ rw 8 (ʟa3 f0 f2 lt02)
      ∷ rw 7 (ʟa3 f0 f4 lt04)
      ∷ rw 6 (ʟa3 f0 f1 lt01)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z0 ∷ z1 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 4 (ʟa1 f0)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h04 ∷ h15 ∷ z1 ∷ z1 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 2 (ʟa3 f0 f4 lt04)
      ∷ perm (h02 ∷ h02 ∷ h13 ∷ h15 ∷ z1 ∷ z1 ∷ h15 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 0 (ʟa3 f0 f2 lt02)
      ∷ rw 2 (ʟa1 f1)
      ∷ rw 1 (ʟa3 f1 f5 lt15)
      ∷ rw 0 (ʟa3 f1 f3 lt13)
      ∷ perm (h01 ∷ [])
      ∷ perm (h01 ∷ [])
      ∷ []
      ) refl

  d30 : ⟪ Route ⟫ ≈ ⟪ C0w ⟫
  d30 = prf δd30

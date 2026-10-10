------------------------------------------------------------------------
-- Presentations of groups
--
-- On six indices 0 < … < 5, in any set of relations Γ that derives the
-- local ones: (d4) gives Clément's (21), and (21) gives (d4).
--
-- Read the indices as three blocks (0,1), (2,3), (4,5) of a pair, and
-- the doubled letters H_[2i,2j] H_[2i+1,2j+1] as the blocks' Hadamard.
-- On the w₋ part of each pair (the -1 eigenvector of H) C₀ = H_[0,1]
-- is a reflection M; on the w₊ part, N = (-1)_[0] (-1)_[1] H_[0,1] is.
-- (d4) is a Coxeter relation M_u M_w M_u = M_{M_u w} for unit vectors
-- u, w of the blocks at angle 60°, and (21) says that M_{e₀} commutes
-- with N_y, y = (e₀ + e₁ + √2 e₂)/2; conjugation by the block word
-- B = H_[0,1] X_[1,2] (doubled) turns one into the other, and the
-- block identities it needs are local (q: B H_[1,2] X_[0,2] is Ŝ times
-- -I, Ŝ the reflection in y).  The steps follow these milestones.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (WRel)
import Presentation.Base as PB
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.LocalRelations using (_===ˡ_)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.Six
  (Γ : WRel (Gen 6)) (loc : ∀ {u v} → u ===ˡ v → PB._≈_ Γ u v) where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (H-gen ; X-gen ; Z-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Engine Γ loc
open PB Γ using (_≈_)

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
h05 : Gen 6
h05 = H-gen f0 f5 lt05
h13 : Gen 6
h13 = H-gen f1 f3 lt13
h15 : Gen 6
h15 = H-gen f1 f5 lt15
h24 : Gen 6
h24 = H-gen f2 f4 lt24
h35 : Gen 6
h35 = H-gen f3 f5 lt35
h45 : Gen 6
h45 = H-gen f4 f5 lt45
x02 : Gen 6
x02 = X-gen f0 f2 lt02
x04 : Gen 6
x04 = X-gen f0 f4 lt04
x13 : Gen 6
x13 = X-gen f1 f3 lt13
x15 : Gen 6
x15 = X-gen f1 f5 lt15
x24 : Gen 6
x24 = X-gen f2 f4 lt24
x35 : Gen 6
x35 = X-gen f3 f5 lt35
z0 : Gen 6
z0 = Z-gen f0
z1 : Gen 6
z1 = Z-gen f1
z2 : Gen 6
z2 = Z-gen f2
z3 : Gen 6
z3 = Z-gen f3
z4 : Gen 6
z4 = Z-gen f4
z5 : Gen 6
z5 = Z-gen f5

------------------------------------------------------------------------
-- The relations as letter lists

L21 : List (Gen 6)
L21 = (h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
R21 : List (Gen 6)
R21 = (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
Ld4 : List (Gen 6)
Ld4 = (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
Rd4 : List (Gen 6)
Rd4 = (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ x24 ∷ x35 ∷ [])

------------------------------------------------------------------------
-- (d4) gives (21)

module FromD4 (d4eh : ⟪ Ld4 ⟫ ≈ ⟪ Rd4 ⟫) where

  private
    d4e : Eqn
    d4e = eqn Ld4 Rd4 d4eh

    δhzbh-04 : Eqn
    δhzbh-04 = derive (h04 ∷ z4 ∷ h04 ∷ []) (x04 ∷ [])
      ( perm (h04 ∷ z4 ∷ h04 ∷ [])
      ∷ rw 1 (ʟd2 f0 f4 lt04)
      ∷ perm (h04 ∷ h04 ∷ x04 ∷ [])
      ∷ rw 0 (ʟa3 f0 f4 lt04)
      ∷ perm (x04 ∷ [])
      ∷ perm (x04 ∷ [])
      ∷ []
      ) refl

    δhzah-04 : Eqn
    δhzah-04 = derive (h04 ∷ z0 ∷ h04 ∷ []) (x04 ∷ z0 ∷ z4 ∷ [])
      ( perm (h04 ∷ z0 ∷ h04 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa1 f4))
      ∷ perm (h04 ∷ z4 ∷ z0 ∷ z4 ∷ h04 ∷ [])
      ∷ rw 2 (ʟd1 f0 f4 lt04)
      ∷ perm (h04 ∷ z4 ∷ h04 ∷ z0 ∷ z4 ∷ [])
      ∷ rw 0 δhzbh-04
      ∷ perm (x04 ∷ z0 ∷ z4 ∷ [])
      ∷ perm (x04 ∷ z0 ∷ z4 ∷ [])
      ∷ []
      ) refl

    δhzbh-15 : Eqn
    δhzbh-15 = derive (h15 ∷ z5 ∷ h15 ∷ []) (x15 ∷ [])
      ( perm (h15 ∷ z5 ∷ h15 ∷ [])
      ∷ rw 1 (ʟd2 f1 f5 lt15)
      ∷ perm (h15 ∷ h15 ∷ x15 ∷ [])
      ∷ rw 0 (ʟa3 f1 f5 lt15)
      ∷ perm (x15 ∷ [])
      ∷ perm (x15 ∷ [])
      ∷ []
      ) refl

    δhzah-15 : Eqn
    δhzah-15 = derive (h15 ∷ z1 ∷ h15 ∷ []) (x15 ∷ z1 ∷ z5 ∷ [])
      ( perm (h15 ∷ z1 ∷ h15 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa1 f5))
      ∷ perm (h15 ∷ z5 ∷ z1 ∷ z5 ∷ h15 ∷ [])
      ∷ rw 2 (ʟd1 f1 f5 lt15)
      ∷ perm (h15 ∷ z5 ∷ h15 ∷ z1 ∷ z5 ∷ [])
      ∷ rw 0 δhzbh-15
      ∷ perm (x15 ∷ z1 ∷ z5 ∷ [])
      ∷ perm (x15 ∷ z1 ∷ z5 ∷ [])
      ∷ []
      ) refl

    δsigA1 : Eqn
    δsigA1 = derive (x24 ∷ x35 ∷ h02 ∷ h13 ∷ []) (h04 ∷ h15 ∷ x24 ∷ x35 ∷ [])
      ( perm (x24 ∷ h02 ∷ x35 ∷ h13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟc5 f1 f3 f5 lt13 lt35))
      ∷ perm (h15 ∷ x24 ∷ h02 ∷ x35 ∷ [])
      ∷ rw 1 (sym⁼ (ʟc5 f0 f2 f4 lt02 lt24))
      ∷ perm (h04 ∷ h15 ∷ x24 ∷ x35 ∷ [])
      ∷ perm (h04 ∷ h15 ∷ x24 ∷ x35 ∷ [])
      ∷ []
      ) refl

    δh45 : Eqn
    δh45 = derive (x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ []) (h45 ∷ [])
      ( perm (x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 1 (sym⁼ (ʟc5 f0 f1 f5 lt01 lt15))
      ∷ perm (x04 ∷ h05 ∷ x15 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 0 (sym⁼ (ʟc4 f0 f4 f5 lt04 lt45))
      ∷ perm (h45 ∷ x15 ∷ x15 ∷ x04 ∷ x04 ∷ [])
      ∷ rw 1 (ʟa2 f1 f5 lt15)
      ∷ perm (h45 ∷ x04 ∷ x04 ∷ [])
      ∷ rw 1 (ʟa2 f0 f4 lt04)
      ∷ perm (h45 ∷ [])
      ∷ perm (h45 ∷ [])
      ∷ []
      ) refl

    δpz2 : Eqn
    δpz2 = derive (h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ []) (x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ [])
      ( perm (h04 ∷ z0 ∷ h04 ∷ h15 ∷ z1 ∷ h15 ∷ [])
      ∷ perm (h04 ∷ z0 ∷ h04 ∷ h15 ∷ z1 ∷ h15 ∷ [])
      ∷ rw 3 δhzah-15
      ∷ perm (x15 ∷ z1 ∷ h04 ∷ z0 ∷ h04 ∷ z5 ∷ [])
      ∷ rw 2 δhzah-04
      ∷ perm (x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ [])
      ∷ []
      ) refl

    δxr1 : Eqn
    δxr1 = derive (x04 ∷ x15 ∷ x24 ∷ x35 ∷ x04 ∷ x15 ∷ []) (x02 ∷ x13 ∷ [])
      ( perm (x04 ∷ x24 ∷ x04 ∷ x15 ∷ x35 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ x24 ∷ x04 ∷ x15 ∷ x35 ∷ x15 ∷ [])
      ∷ rw 0 (ʟc3 f0 f2 f4 lt02 lt24)
      ∷ perm (x24 ∷ x02 ∷ x04 ∷ x15 ∷ x35 ∷ x15 ∷ [])
      ∷ rw 3 (ʟc3 f1 f3 f5 lt13 lt35)
      ∷ perm (x24 ∷ x02 ∷ x04 ∷ x35 ∷ x13 ∷ x15 ∷ [])
      ∷ rw 3 (ʟc2 f1 f3 f5 lt13 lt35)
      ∷ perm (x24 ∷ x02 ∷ x04 ∷ x13 ∷ x15 ∷ x15 ∷ [])
      ∷ rw 0 (ʟc2 f0 f2 f4 lt02 lt24)
      ∷ perm (x02 ∷ x04 ∷ x04 ∷ x13 ∷ x15 ∷ x15 ∷ [])
      ∷ rw 4 (ʟa2 f1 f5 lt15)
      ∷ perm (x02 ∷ x04 ∷ x04 ∷ x13 ∷ [])
      ∷ rw 1 (ʟa2 f0 f4 lt04)
      ∷ perm (x02 ∷ x13 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ [])
      ∷ []
      ) refl

    δxr2 : Eqn
    δxr2 = derive (x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ []) (x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ( perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ h35 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ h35 ∷ x15 ∷ [])
      ∷ rw 5 (sym⁼ (ʟa2 f1 f3 lt13))
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ h35 ∷ x13 ∷ x13 ∷ x15 ∷ [])
      ∷ rw 6 (sym⁼ (ʟc2 f1 f3 f5 lt13 lt35))
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ h35 ∷ x13 ∷ x35 ∷ x13 ∷ [])
      ∷ rw 4 (ʟc4 f1 f3 f5 lt13 lt35)
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x13 ∷ h15 ∷ x35 ∷ x13 ∷ [])
      ∷ rw 5 (ʟc5 f1 f3 f5 lt13 lt35)
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x13 ∷ x35 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa2 f1 f3 lt13))
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x13 ∷ x35 ∷ x13 ∷ x13 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 5 (ʟc2 f1 f3 f5 lt13 lt35)
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x13 ∷ x13 ∷ x15 ∷ x13 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 4 (ʟa2 f1 f3 lt13)
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x15 ∷ x13 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟa2 f0 f2 lt02))
      ∷ perm (x15 ∷ x15 ∷ x04 ∷ x13 ∷ h24 ∷ x02 ∷ h13 ∷ x02 ∷ x04 ∷ x13 ∷ [])
      ∷ rw 4 (ʟc4 f0 f2 f4 lt02 lt24)
      ∷ perm (x15 ∷ x15 ∷ x04 ∷ x02 ∷ x13 ∷ h04 ∷ h13 ∷ x02 ∷ x04 ∷ x13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟc2 f0 f2 f4 lt02 lt24))
      ∷ perm (x15 ∷ x15 ∷ x04 ∷ x02 ∷ x13 ∷ h04 ∷ x24 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 5 (ʟc5 f0 f2 f4 lt02 lt24)
      ∷ perm (x15 ∷ x15 ∷ x04 ∷ x02 ∷ x24 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 0 (ʟa2 f1 f5 lt15)
      ∷ perm (x04 ∷ x02 ∷ x24 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa2 f0 f2 lt02))
      ∷ perm (x04 ∷ x02 ∷ x24 ∷ x02 ∷ x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 2 (ʟc2 f0 f2 f4 lt02 lt24)
      ∷ perm (x04 ∷ x02 ∷ x02 ∷ x04 ∷ x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 1 (ʟa2 f0 f2 lt02)
      ∷ perm (x04 ∷ x04 ∷ x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 0 (ʟa2 f0 f4 lt04)
      ∷ perm (x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ []
      ) refl

    δtd2 : Eqn
    δtd2 = derive (h02 ∷ h13 ∷ x02 ∷ x13 ∷ []) (z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ x02 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟd2 f1 f3 lt13))
      ∷ perm (z3 ∷ h02 ∷ x02 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ (ʟd2 f0 f2 lt02))
      ∷ perm (z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δq1 : Eqn
    δq1 = derive (x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ []) (x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ( perm (x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa2 f1 f5 lt15))
      ∷ perm (x15 ∷ x15 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa2 f0 f4 lt04))
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa2 f1 f5 lt15))
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ x15 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa2 f0 f4 lt04))
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ x04 ∷ x15 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ x04 ∷ x15 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 2 δxr1
      ∷ perm (x04 ∷ x15 ∷ x02 ∷ x13 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ x02 ∷ x13 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 4 δxr2
      ∷ perm (x04 ∷ x15 ∷ x02 ∷ x13 ∷ x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ x02 ∷ x02 ∷ x13 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 4 (ʟa2 f1 f3 lt13)
      ∷ perm (x04 ∷ x02 ∷ x02 ∷ x15 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 1 (ʟa2 f0 f2 lt02)
      ∷ perm (x04 ∷ x15 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 2 δtd2
      ∷ perm (x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δq : Eqn
    δq = derive (h02 ∷ h13 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ( perm (h02 ∷ h13 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 2 δq1
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa1 f4))
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ z4 ∷ z4 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa1 f5))
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z4 ∷ z5 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa1 f1))
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z1 ∷ z4 ∷ z5 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa1 f0))
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (sym⁼ δpz2)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ z0 ∷ z2 ∷ z4 ∷ z5 ∷ h02 ∷ z1 ∷ z3 ∷ h13 ∷ [])
      ∷ rw 13 (ʟd1 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h13 ∷ z1 ∷ z0 ∷ z2 ∷ h02 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ rw 10 (ʟd1 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ []
      ) refl

    δmy : Eqn
    δmy = derive (h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 δsigA1
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ x35 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ x35 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa2 f2 f4 lt24))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ x24 ∷ x24 ∷ h15 ∷ h01 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 δsigA1
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ x24 ∷ x24 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ x35 ∷ x24 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 10 (ʟa2 f2 f4 lt24)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ h01 ∷ x24 ∷ h04 ∷ h15 ∷ x35 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (ʟa2 f3 f5 lt35)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ h01 ∷ x24 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa2 f3 f5 lt35))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ x35 ∷ h01 ∷ x24 ∷ x35 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ x24 ∷ x35 ∷ x24 ∷ x35 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ x24 ∷ x24 ∷ x35 ∷ x35 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (ʟa2 f3 f5 lt35)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ x24 ∷ x24 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (ʟa2 f2 f4 lt24)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δzallC0 : Eqn
    δzallC0 = derive (z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ []) (h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ( perm (z2 ∷ z3 ∷ z4 ∷ z5 ∷ z0 ∷ z1 ∷ h01 ∷ [])
      ∷ rw 4 (ʟd1 f0 f1 lt01)
      ∷ perm (h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ perm (h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ []
      ) refl

    δsymn : Eqn
    δsymn = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ (ʟa3 f1 f5 lt15))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h15 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h15 ∷ h13 ∷ h13 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (sym⁼ (ʟa3 f0 f4 lt04))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h13 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δsynm : Eqn
    δsynm = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ (ʟd1 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa3 f1 f5 lt15))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h15 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h15 ∷ h13 ∷ h13 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 10 (sym⁼ (ʟa3 f0 f4 lt04))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h13 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 10 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δd4p : Eqn
    δd4p = derive (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ []) (h24 ∷ h35 ∷ x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ [])
      ( perm (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 19 (sym⁼ (ʟa2 f3 f5 lt35))
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x35 ∷ x35 ∷ [])
      ∷ rw 20 (sym⁼ (ʟa2 f2 f4 lt24))
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ x24 ∷ x35 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 0 d4e
      ∷ perm (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ x24 ∷ x35 ∷ x24 ∷ x35 ∷ [])
      ∷ perm (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ x24 ∷ x24 ∷ x35 ∷ x35 ∷ [])
      ∷ rw 7 (ʟa2 f3 f5 lt35)
      ∷ perm (h24 ∷ h35 ∷ h45 ∷ h24 ∷ x24 ∷ x24 ∷ h35 ∷ [])
      ∷ rw 4 (ʟa2 f2 f4 lt24)
      ∷ perm (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ [])
      ∷ perm (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ [])
      ∷ rw 2 (sym⁼ δh45)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ [])
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ [])
      ∷ []
      ) refl

    δr21pp : Eqn
    δr21pp = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ( rw 0 (sym⁼ δmy)
      ∷ rw 14 (sym⁼ δmy)
      ∷ rw 4 δd4p
      ∷ rw 0 δq
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x24 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 17 (rev⁼ δq)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h13 ∷ h02 ∷ h15 ∷ h04 ∷ z1 ∷ z0 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 10 δzallC0
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h13 ∷ h02 ∷ h15 ∷ h04 ∷ z1 ∷ z0 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 11 (ʟa1 f0)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ z1 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h13 ∷ h02 ∷ h15 ∷ h04 ∷ z1 ∷ z0 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 11 (ʟa1 f1)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ z2 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z3 ∷ z4 ∷ z5 ∷ h13 ∷ h02 ∷ h15 ∷ h04 ∷ z1 ∷ z0 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 11 (ʟa1 f2)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ z3 ∷ z3 ∷ z4 ∷ z5 ∷ z4 ∷ z5 ∷ h13 ∷ h02 ∷ h15 ∷ h04 ∷ z1 ∷ z0 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 11 (ʟa1 f3)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ z4 ∷ z4 ∷ z5 ∷ z5 ∷ h13 ∷ h02 ∷ h15 ∷ h04 ∷ z1 ∷ z0 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ [])
      ∷ rw 11 (ʟa1 f4)
      ∷ rw 11 (ʟa1 f5)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δmymy : Eqn
    δmymy = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) ([])
      ( perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h02 ∷ h13 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h04 ∷ h15 ∷ h13 ∷ h13 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (ʟa3 f0 f4 lt04)
      ∷ rw 6 (ʟa3 f1 f3 lt13)
      ∷ rw 5 (ʟa3 f1 f5 lt15)
      ∷ rw 4 (ʟa3 f0 f1 lt01)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h04 ∷ h15 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (ʟa3 f0 f4 lt04)
      ∷ perm (h02 ∷ h02 ∷ h13 ∷ h15 ∷ h15 ∷ h13 ∷ [])
      ∷ rw 0 (ʟa3 f0 f2 lt02)
      ∷ rw 1 (ʟa3 f1 f5 lt15)
      ∷ rw 0 (ʟa3 f1 f3 lt13)
      ∷ perm ([])
      ∷ perm ([])
      ∷ []
      ) refl

    δnyny : Eqn
    δnyny = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) ([])
      ( perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h02 ∷ h13 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h04 ∷ h15 ∷ h13 ∷ h13 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (ʟa3 f0 f4 lt04)
      ∷ rw 8 (ʟa3 f1 f3 lt13)
      ∷ rw 7 (ʟa3 f1 f5 lt15)
      ∷ rw 5 (ʟd1 f0 f1 lt01)
      ∷ rw 4 (ʟa3 f0 f1 lt01)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z0 ∷ z1 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (ʟa1 f0)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h04 ∷ h15 ∷ z1 ∷ z1 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (ʟa3 f0 f4 lt04)
      ∷ perm (h02 ∷ h02 ∷ h13 ∷ h15 ∷ z1 ∷ z1 ∷ h15 ∷ h13 ∷ [])
      ∷ rw 0 (ʟa3 f0 f2 lt02)
      ∷ rw 2 (ʟa1 f1)
      ∷ rw 1 (ʟa3 f1 f5 lt15)
      ∷ rw 0 (ʟa3 f1 f3 lt13)
      ∷ perm ([])
      ∷ perm ([])
      ∷ []
      ) refl

    δncn : Eqn
    δncn = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) (h01 ∷ [])
      ( rw 0 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ rw 1 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ rw 2 (sym⁼ (ʟa3 f0 f4 lt04))
      ∷ rw 3 (sym⁼ (ʟa3 f1 f5 lt15))
      ∷ rw 4 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ rw 5 (sym⁼ (ʟa3 f0 f4 lt04))
      ∷ rw 6 (sym⁼ (ʟa3 f1 f5 lt15))
      ∷ rw 7 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ rw 8 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ rw 41 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ rw 42 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ rw 43 (sym⁼ (ʟa3 f0 f4 lt04))
      ∷ rw 44 (sym⁼ (ʟa3 f1 f5 lt15))
      ∷ rw 45 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ rw 46 (sym⁼ (ʟa3 f0 f4 lt04))
      ∷ rw 47 (sym⁼ (ʟa3 f1 f5 lt15))
      ∷ rw 48 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ rw 49 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (sym⁼ δsymn)
      ∷ rw 20 (sym⁼ δsynm)
      ∷ rw 9 (sym⁼ δr21pp)
      ∷ rw 0 δmymy
      ∷ rw 1 δmymy
      ∷ perm (h01 ∷ [])
      ∷ perm (h01 ∷ [])
      ∷ []
      ) refl

    δr21 : Eqn
    δr21 = derive (h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ( rw 0 (sym⁼ δnyny)
      ∷ rw 11 δncn
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ []
      ) refl

  r21 : ⟪ L21 ⟫ ≈ ⟪ R21 ⟫
  r21 = prf δr21

------------------------------------------------------------------------
-- (21) gives (d4)

module FromR21 (r21eh : ⟪ L21 ⟫ ≈ ⟪ R21 ⟫) where

  private
    r21e : Eqn
    r21e = eqn L21 R21 r21eh

    δhzbh-04 : Eqn
    δhzbh-04 = derive (h04 ∷ z4 ∷ h04 ∷ []) (x04 ∷ [])
      ( perm (h04 ∷ z4 ∷ h04 ∷ [])
      ∷ rw 1 (ʟd2 f0 f4 lt04)
      ∷ perm (h04 ∷ h04 ∷ x04 ∷ [])
      ∷ rw 0 (ʟa3 f0 f4 lt04)
      ∷ perm (x04 ∷ [])
      ∷ perm (x04 ∷ [])
      ∷ []
      ) refl

    δhzah-04 : Eqn
    δhzah-04 = derive (h04 ∷ z0 ∷ h04 ∷ []) (x04 ∷ z0 ∷ z4 ∷ [])
      ( perm (h04 ∷ z0 ∷ h04 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa1 f4))
      ∷ perm (h04 ∷ z4 ∷ z0 ∷ z4 ∷ h04 ∷ [])
      ∷ rw 2 (ʟd1 f0 f4 lt04)
      ∷ perm (h04 ∷ z4 ∷ h04 ∷ z0 ∷ z4 ∷ [])
      ∷ rw 0 δhzbh-04
      ∷ perm (x04 ∷ z0 ∷ z4 ∷ [])
      ∷ perm (x04 ∷ z0 ∷ z4 ∷ [])
      ∷ []
      ) refl

    δhzbh-15 : Eqn
    δhzbh-15 = derive (h15 ∷ z5 ∷ h15 ∷ []) (x15 ∷ [])
      ( perm (h15 ∷ z5 ∷ h15 ∷ [])
      ∷ rw 1 (ʟd2 f1 f5 lt15)
      ∷ perm (h15 ∷ h15 ∷ x15 ∷ [])
      ∷ rw 0 (ʟa3 f1 f5 lt15)
      ∷ perm (x15 ∷ [])
      ∷ perm (x15 ∷ [])
      ∷ []
      ) refl

    δhzah-15 : Eqn
    δhzah-15 = derive (h15 ∷ z1 ∷ h15 ∷ []) (x15 ∷ z1 ∷ z5 ∷ [])
      ( perm (h15 ∷ z1 ∷ h15 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa1 f5))
      ∷ perm (h15 ∷ z5 ∷ z1 ∷ z5 ∷ h15 ∷ [])
      ∷ rw 2 (ʟd1 f1 f5 lt15)
      ∷ perm (h15 ∷ z5 ∷ h15 ∷ z1 ∷ z5 ∷ [])
      ∷ rw 0 δhzbh-15
      ∷ perm (x15 ∷ z1 ∷ z5 ∷ [])
      ∷ perm (x15 ∷ z1 ∷ z5 ∷ [])
      ∷ []
      ) refl

    δsigA1 : Eqn
    δsigA1 = derive (x24 ∷ x35 ∷ h02 ∷ h13 ∷ []) (h04 ∷ h15 ∷ x24 ∷ x35 ∷ [])
      ( perm (x24 ∷ h02 ∷ x35 ∷ h13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟc5 f1 f3 f5 lt13 lt35))
      ∷ perm (h15 ∷ x24 ∷ h02 ∷ x35 ∷ [])
      ∷ rw 1 (sym⁼ (ʟc5 f0 f2 f4 lt02 lt24))
      ∷ perm (h04 ∷ h15 ∷ x24 ∷ x35 ∷ [])
      ∷ perm (h04 ∷ h15 ∷ x24 ∷ x35 ∷ [])
      ∷ []
      ) refl

    δh45 : Eqn
    δh45 = derive (x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ []) (h45 ∷ [])
      ( perm (x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 1 (sym⁼ (ʟc5 f0 f1 f5 lt01 lt15))
      ∷ perm (x04 ∷ h05 ∷ x15 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 0 (sym⁼ (ʟc4 f0 f4 f5 lt04 lt45))
      ∷ perm (h45 ∷ x15 ∷ x15 ∷ x04 ∷ x04 ∷ [])
      ∷ rw 1 (ʟa2 f1 f5 lt15)
      ∷ perm (h45 ∷ x04 ∷ x04 ∷ [])
      ∷ rw 1 (ʟa2 f0 f4 lt04)
      ∷ perm (h45 ∷ [])
      ∷ perm (h45 ∷ [])
      ∷ []
      ) refl

    δpz2 : Eqn
    δpz2 = derive (h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ []) (x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ [])
      ( perm (h04 ∷ z0 ∷ h04 ∷ h15 ∷ z1 ∷ h15 ∷ [])
      ∷ perm (h04 ∷ z0 ∷ h04 ∷ h15 ∷ z1 ∷ h15 ∷ [])
      ∷ rw 3 δhzah-15
      ∷ perm (x15 ∷ z1 ∷ h04 ∷ z0 ∷ h04 ∷ z5 ∷ [])
      ∷ rw 2 δhzah-04
      ∷ perm (x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ [])
      ∷ []
      ) refl

    δxr1 : Eqn
    δxr1 = derive (x04 ∷ x15 ∷ x24 ∷ x35 ∷ x04 ∷ x15 ∷ []) (x02 ∷ x13 ∷ [])
      ( perm (x04 ∷ x24 ∷ x04 ∷ x15 ∷ x35 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ x24 ∷ x04 ∷ x15 ∷ x35 ∷ x15 ∷ [])
      ∷ rw 0 (ʟc3 f0 f2 f4 lt02 lt24)
      ∷ perm (x24 ∷ x02 ∷ x04 ∷ x15 ∷ x35 ∷ x15 ∷ [])
      ∷ rw 3 (ʟc3 f1 f3 f5 lt13 lt35)
      ∷ perm (x24 ∷ x02 ∷ x04 ∷ x35 ∷ x13 ∷ x15 ∷ [])
      ∷ rw 3 (ʟc2 f1 f3 f5 lt13 lt35)
      ∷ perm (x24 ∷ x02 ∷ x04 ∷ x13 ∷ x15 ∷ x15 ∷ [])
      ∷ rw 0 (ʟc2 f0 f2 f4 lt02 lt24)
      ∷ perm (x02 ∷ x04 ∷ x04 ∷ x13 ∷ x15 ∷ x15 ∷ [])
      ∷ rw 4 (ʟa2 f1 f5 lt15)
      ∷ perm (x02 ∷ x04 ∷ x04 ∷ x13 ∷ [])
      ∷ rw 1 (ʟa2 f0 f4 lt04)
      ∷ perm (x02 ∷ x13 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ [])
      ∷ []
      ) refl

    δxr2 : Eqn
    δxr2 = derive (x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ []) (x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ( perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ h35 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ h35 ∷ x15 ∷ [])
      ∷ rw 5 (sym⁼ (ʟa2 f1 f3 lt13))
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ h35 ∷ x13 ∷ x13 ∷ x15 ∷ [])
      ∷ rw 6 (sym⁼ (ʟc2 f1 f3 f5 lt13 lt35))
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ h35 ∷ x13 ∷ x35 ∷ x13 ∷ [])
      ∷ rw 4 (ʟc4 f1 f3 f5 lt13 lt35)
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x13 ∷ h15 ∷ x35 ∷ x13 ∷ [])
      ∷ rw 5 (ʟc5 f1 f3 f5 lt13 lt35)
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x13 ∷ x35 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa2 f1 f3 lt13))
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x13 ∷ x35 ∷ x13 ∷ x13 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 5 (ʟc2 f1 f3 f5 lt13 lt35)
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x13 ∷ x13 ∷ x15 ∷ x13 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 4 (ʟa2 f1 f3 lt13)
      ∷ perm (x04 ∷ h24 ∷ x04 ∷ x15 ∷ x15 ∷ x13 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟa2 f0 f2 lt02))
      ∷ perm (x15 ∷ x15 ∷ x04 ∷ x13 ∷ h24 ∷ x02 ∷ h13 ∷ x02 ∷ x04 ∷ x13 ∷ [])
      ∷ rw 4 (ʟc4 f0 f2 f4 lt02 lt24)
      ∷ perm (x15 ∷ x15 ∷ x04 ∷ x02 ∷ x13 ∷ h04 ∷ h13 ∷ x02 ∷ x04 ∷ x13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟc2 f0 f2 f4 lt02 lt24))
      ∷ perm (x15 ∷ x15 ∷ x04 ∷ x02 ∷ x13 ∷ h04 ∷ x24 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 5 (ʟc5 f0 f2 f4 lt02 lt24)
      ∷ perm (x15 ∷ x15 ∷ x04 ∷ x02 ∷ x24 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 0 (ʟa2 f1 f5 lt15)
      ∷ perm (x04 ∷ x02 ∷ x24 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa2 f0 f2 lt02))
      ∷ perm (x04 ∷ x02 ∷ x24 ∷ x02 ∷ x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 2 (ʟc2 f0 f2 f4 lt02 lt24)
      ∷ perm (x04 ∷ x02 ∷ x02 ∷ x04 ∷ x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 1 (ʟa2 f0 f2 lt02)
      ∷ perm (x04 ∷ x04 ∷ x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 0 (ʟa2 f0 f4 lt04)
      ∷ perm (x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ []
      ) refl

    δtd2 : Eqn
    δtd2 = derive (h02 ∷ h13 ∷ x02 ∷ x13 ∷ []) (z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ x02 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟd2 f1 f3 lt13))
      ∷ perm (z3 ∷ h02 ∷ x02 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ (ʟd2 f0 f2 lt02))
      ∷ perm (z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δq1 : Eqn
    δq1 = derive (x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ []) (x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ( perm (x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa2 f1 f5 lt15))
      ∷ perm (x15 ∷ x15 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa2 f0 f4 lt04))
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa2 f1 f5 lt15))
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ x15 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa2 f0 f4 lt04))
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ x04 ∷ x15 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ x04 ∷ x15 ∷ x24 ∷ x35 ∷ x04 ∷ x15 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 2 δxr1
      ∷ perm (x04 ∷ x15 ∷ x02 ∷ x13 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ x02 ∷ x13 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 4 δxr2
      ∷ perm (x04 ∷ x15 ∷ x02 ∷ x13 ∷ x02 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ x02 ∷ x02 ∷ x13 ∷ x13 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 4 (ʟa2 f1 f3 lt13)
      ∷ perm (x04 ∷ x02 ∷ x02 ∷ x15 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 1 (ʟa2 f0 f2 lt02)
      ∷ perm (x04 ∷ x15 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ h02 ∷ h13 ∷ x02 ∷ x13 ∷ [])
      ∷ rw 2 δtd2
      ∷ perm (x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δq : Eqn
    δq = derive (h02 ∷ h13 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ( perm (h02 ∷ h13 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ [])
      ∷ rw 2 δq1
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa1 f4))
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ z4 ∷ z4 ∷ x15 ∷ z2 ∷ z3 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa1 f5))
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z4 ∷ z5 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa1 f1))
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z1 ∷ z4 ∷ z5 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa1 f0))
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (sym⁼ δpz2)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ z0 ∷ z2 ∷ z4 ∷ z5 ∷ h02 ∷ z1 ∷ z3 ∷ h13 ∷ [])
      ∷ rw 13 (ʟd1 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h13 ∷ z1 ∷ z0 ∷ z2 ∷ h02 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ rw 10 (ʟd1 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ []
      ) refl

    δmy : Eqn
    δmy = derive (h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 δsigA1
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ x35 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ x35 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa2 f2 f4 lt24))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ x24 ∷ x24 ∷ h15 ∷ h01 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 δsigA1
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ x24 ∷ x24 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ x35 ∷ x24 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 10 (ʟa2 f2 f4 lt24)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ h01 ∷ x24 ∷ h04 ∷ h15 ∷ x35 ∷ x35 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (ʟa2 f3 f5 lt35)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ h01 ∷ x24 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa2 f3 f5 lt35))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ x24 ∷ x35 ∷ h01 ∷ x24 ∷ x35 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ x24 ∷ x35 ∷ x24 ∷ x35 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ x24 ∷ x24 ∷ x35 ∷ x35 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (ʟa2 f3 f5 lt35)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ x24 ∷ x24 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (ʟa2 f2 f4 lt24)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δzallC0 : Eqn
    δzallC0 = derive (z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ []) (h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ( perm (z2 ∷ z3 ∷ z4 ∷ z5 ∷ z0 ∷ z1 ∷ h01 ∷ [])
      ∷ rw 4 (ʟd1 f0 f1 lt01)
      ∷ perm (h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ perm (h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ [])
      ∷ []
      ) refl

    δsymn : Eqn
    δsymn = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ (ʟa3 f1 f5 lt15))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h15 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h15 ∷ h13 ∷ h13 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (sym⁼ (ʟa3 f0 f4 lt04))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h13 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δsynm : Eqn
    δsynm = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ (ʟd1 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa3 f1 f5 lt15))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h15 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h15 ∷ h13 ∷ h13 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 10 (sym⁼ (ʟa3 f0 f4 lt04))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h13 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 10 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δnyny : Eqn
    δnyny = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) ([])
      ( perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h02 ∷ h13 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h04 ∷ h15 ∷ h13 ∷ h13 ∷ h15 ∷ h01 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (ʟa3 f0 f4 lt04)
      ∷ rw 8 (ʟa3 f1 f3 lt13)
      ∷ rw 7 (ʟa3 f1 f5 lt15)
      ∷ rw 5 (ʟd1 f0 f1 lt01)
      ∷ rw 4 (ʟa3 f0 f1 lt01)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z0 ∷ z1 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (ʟa1 f0)
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h04 ∷ h15 ∷ z1 ∷ z1 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (ʟa3 f0 f4 lt04)
      ∷ perm (h02 ∷ h02 ∷ h13 ∷ h15 ∷ z1 ∷ z1 ∷ h15 ∷ h13 ∷ [])
      ∷ rw 0 (ʟa3 f0 f2 lt02)
      ∷ rw 2 (ʟa1 f1)
      ∷ rw 1 (ʟa3 f1 f5 lt15)
      ∷ rw 0 (ʟa3 f1 f3 lt13)
      ∷ perm ([])
      ∷ perm ([])
      ∷ []
      ) refl

    δr21pp : Eqn
    δr21pp = derive (h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ( rw 0 δsymn
      ∷ rw 21 δsynm
      ∷ rw 9 (sym⁼ r21e)
      ∷ rw 10 δnyny
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ h01 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δd4p : Eqn
    δd4p = derive (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ []) (h24 ∷ h35 ∷ x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ [])
      ( rw 0 (sym⁼ (ʟa2 f2 f4 lt24))
      ∷ rw 1 (sym⁼ (ʟa2 f3 f5 lt35))
      ∷ rw 2 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ rw 3 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (x24 ∷ x35 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 27 (sym⁼ (ʟa2 f2 f4 lt24))
      ∷ rw 28 (sym⁼ (ʟa2 f3 f5 lt35))
      ∷ rw 29 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ rw 30 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (x24 ∷ x35 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 4 δmy
      ∷ rw 14 δmy
      ∷ rw 4 (sym⁼ δr21pp)
      ∷ rw 14 (sym⁼ (ʟa1 f0))
      ∷ rw 15 (sym⁼ (ʟa1 f1))
      ∷ rw 16 (sym⁼ (ʟa1 f2))
      ∷ rw 17 (sym⁼ (ʟa1 f3))
      ∷ rw 18 (sym⁼ (ʟa1 f4))
      ∷ rw 19 (sym⁼ (ʟa1 f5))
      ∷ perm (x24 ∷ x35 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ h02 ∷ h13 ∷ h04 ∷ h15 ∷ z0 ∷ z1 ∷ h04 ∷ h15 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 4 (sym⁼ δq)
      ∷ rw 19 (sym⁼ (ʟa1 f0))
      ∷ rw 20 (sym⁼ (ʟa1 f1))
      ∷ rw 21 (sym⁼ (ʟa1 f2))
      ∷ rw 22 (sym⁼ (ʟa1 f3))
      ∷ rw 23 (sym⁼ (ʟa1 f4))
      ∷ rw 24 (sym⁼ (ʟa1 f5))
      ∷ perm (x24 ∷ x35 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ z5 ∷ z4 ∷ z3 ∷ z2 ∷ z1 ∷ z0 ∷ h13 ∷ h02 ∷ h15 ∷ h04 ∷ z1 ∷ z0 ∷ h15 ∷ h04 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 25 (sym⁼ (rev⁼ δq))
      ∷ perm (x24 ∷ x35 ∷ h02 ∷ h02 ∷ h13 ∷ h13 ∷ x24 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x24 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 2 (ʟa3 f0 f2 lt02)
      ∷ perm (x24 ∷ x24 ∷ x35 ∷ h13 ∷ h13 ∷ x35 ∷ h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x24 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 0 (ʟa2 f2 f4 lt24)
      ∷ rw 1 (ʟa3 f1 f3 lt13)
      ∷ rw 0 (ʟa2 f3 f5 lt35)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z2 ∷ z2 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ z0 ∷ z1 ∷ z3 ∷ z4 ∷ z5 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x24 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 6 (ʟa1 f2)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z3 ∷ z3 ∷ z4 ∷ z5 ∷ h01 ∷ z0 ∷ z1 ∷ z4 ∷ z5 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x24 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 6 (ʟa1 f3)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z4 ∷ z4 ∷ z5 ∷ h01 ∷ z0 ∷ z1 ∷ z5 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x24 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 6 (ʟa1 f4)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ z5 ∷ z5 ∷ h01 ∷ z0 ∷ z1 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x24 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 6 (ʟa1 f5)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ h01 ∷ z0 ∷ z1 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x24 ∷ h13 ∷ h13 ∷ h02 ∷ h02 ∷ x24 ∷ x35 ∷ [])
      ∷ rw 15 (ʟa3 f1 f3 lt13)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ z0 ∷ z1 ∷ h01 ∷ z0 ∷ z1 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ x35 ∷ x35 ∷ x24 ∷ h02 ∷ h02 ∷ x24 ∷ [])
      ∷ rw 13 (ʟa2 f3 f5 lt35)
      ∷ rw 14 (ʟa3 f0 f2 lt02)
      ∷ rw 13 (ʟa2 f2 f4 lt24)
      ∷ rw 4 (ʟd1 f0 f1 lt01)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ h01 ∷ z0 ∷ z0 ∷ z1 ∷ z1 ∷ x15 ∷ x04 ∷ h35 ∷ h24 ∷ [])
      ∷ rw 5 (ʟa1 f0)
      ∷ rw 5 (ʟa1 f1)
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ [])
      ∷ perm (h24 ∷ h35 ∷ x04 ∷ x15 ∷ h01 ∷ x04 ∷ x15 ∷ h24 ∷ h35 ∷ [])
      ∷ []
      ) refl

    δd4 : Eqn
    δd4 = derive (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ x24 ∷ x35 ∷ []) (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ x24 ∷ x35 ∷ [])
      ( rw 0 δd4p
      ∷ rw 2 δh45
      ∷ perm (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ x24 ∷ x35 ∷ [])
      ∷ perm (h24 ∷ h35 ∷ h45 ∷ h24 ∷ h35 ∷ x24 ∷ x35 ∷ [])
      ∷ []
      ) refl

  d4 : ⟪ Ld4 ⟫ ≈ ⟪ Rd4 ⟫
  d4 = prf δd4

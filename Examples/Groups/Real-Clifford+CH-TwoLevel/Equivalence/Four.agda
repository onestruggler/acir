------------------------------------------------------------------------
-- Presentations of groups
--
-- On four indices 0 < 1 < 2 < 3, in any set of relations Γ that
-- derives the local ones: (d3) and (f1) (= Clément's (19)) give
-- Clément's (20), and (20) and (f1) give (d3).  With C₀ = H_[0,1],
-- C₁ = H_[2,3], A = H_[0,2] H_[1,3] and D = A C₁ A, both go through
-- C₀ D = D C₁; (f1) makes C₀ C₁ commute with A, and A Z₀ Z₁ A is a
-- signed permutation that exchanges C₀ and C₁.  The steps are found by
-- a search between these milestones (Engine).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (WRel)
import Presentation.Base as PB
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.LocalRelations using (_===ˡ_)

module Examples.Groups.Real-Clifford+CH-TwoLevel.Equivalence.Four
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
h03 : Gen 4
h03 = H-gen f0 f3 lt03
h13 : Gen 4
h13 = H-gen f1 f3 lt13
h23 : Gen 4
h23 = H-gen f2 f3 lt23
x02 : Gen 4
x02 = X-gen f0 f2 lt02
x13 : Gen 4
x13 = X-gen f1 f3 lt13
z0 : Gen 4
z0 = Z-gen f0
z1 : Gen 4
z1 = Z-gen f1
z2 : Gen 4
z2 = Z-gen f2
z3 : Gen 4
z3 = Z-gen f3

------------------------------------------------------------------------
-- The relations as letter lists

L20 : List (Gen 4)
L20 = (h01 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
R20 : List (Gen 4)
R20 = (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
Ld3 : List (Gen 4)
Ld3 = (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
Rd3 : List (Gen 4)
Rd3 = (h01 ∷ h23 ∷ [])
Lf1 : List (Gen 4)
Lf1 = (h01 ∷ h23 ∷ h02 ∷ h13 ∷ [])
Rf1 : List (Gen 4)
Rf1 = (h02 ∷ h13 ∷ h01 ∷ h23 ∷ [])

------------------------------------------------------------------------
-- (d3) and (f1) give (20)

module FromD3 (d3eh : ⟪ Ld3 ⟫ ≈ ⟪ Rd3 ⟫) (f1eh : ⟪ Lf1 ⟫ ≈ ⟪ Rf1 ⟫) where

  private
    d3e : Eqn
    d3e = eqn Ld3 Rd3 d3eh
    f1e : Eqn
    f1e = eqn Lf1 Rf1 f1eh

    δhzbh-02 : Eqn
    δhzbh-02 = derive (h02 ∷ z2 ∷ h02 ∷ []) (x02 ∷ [])
      ( perm (h02 ∷ z2 ∷ h02 ∷ [])
      ∷ rw 1 (ʟd2 f0 f2 lt02)
      ∷ perm (h02 ∷ h02 ∷ x02 ∷ [])
      ∷ rw 0 (ʟa3 f0 f2 lt02)
      ∷ perm (x02 ∷ [])
      ∷ perm (x02 ∷ [])
      ∷ []
      ) refl

    δhzah-02 : Eqn
    δhzah-02 = derive (h02 ∷ z0 ∷ h02 ∷ []) (x02 ∷ z0 ∷ z2 ∷ [])
      ( perm (h02 ∷ z0 ∷ h02 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa1 f2))
      ∷ perm (h02 ∷ z2 ∷ z0 ∷ z2 ∷ h02 ∷ [])
      ∷ rw 2 (ʟd1 f0 f2 lt02)
      ∷ perm (h02 ∷ z2 ∷ h02 ∷ z0 ∷ z2 ∷ [])
      ∷ rw 0 δhzbh-02
      ∷ perm (x02 ∷ z0 ∷ z2 ∷ [])
      ∷ perm (x02 ∷ z0 ∷ z2 ∷ [])
      ∷ []
      ) refl

    δhzbh-13 : Eqn
    δhzbh-13 = derive (h13 ∷ z3 ∷ h13 ∷ []) (x13 ∷ [])
      ( perm (h13 ∷ z3 ∷ h13 ∷ [])
      ∷ rw 1 (ʟd2 f1 f3 lt13)
      ∷ perm (h13 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 0 (ʟa3 f1 f3 lt13)
      ∷ perm (x13 ∷ [])
      ∷ perm (x13 ∷ [])
      ∷ []
      ) refl

    δhzah-13 : Eqn
    δhzah-13 = derive (h13 ∷ z1 ∷ h13 ∷ []) (x13 ∷ z1 ∷ z3 ∷ [])
      ( perm (h13 ∷ z1 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa1 f3))
      ∷ perm (h13 ∷ z3 ∷ z1 ∷ z3 ∷ h13 ∷ [])
      ∷ rw 2 (ʟd1 f1 f3 lt13)
      ∷ perm (h13 ∷ z3 ∷ h13 ∷ z1 ∷ z3 ∷ [])
      ∷ rw 0 δhzbh-13
      ∷ perm (x13 ∷ z1 ∷ z3 ∷ [])
      ∷ perm (x13 ∷ z1 ∷ z3 ∷ [])
      ∷ []
      ) refl

    δpz : Eqn
    δpz = derive (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ []) (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ( perm (h02 ∷ z0 ∷ h02 ∷ h13 ∷ z1 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ z0 ∷ h02 ∷ h13 ∷ z1 ∷ h13 ∷ [])
      ∷ rw 3 δhzah-13
      ∷ perm (x13 ∷ z1 ∷ h02 ∷ z0 ∷ h02 ∷ z3 ∷ [])
      ∷ rw 2 δhzah-02
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ []
      ) refl

    δc0p : Eqn
    δc0p = derive (h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ( perm (h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 1 δpz
      ∷ perm (h01 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ perm (h01 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa2 f0 f2 lt02))
      ∷ perm (x02 ∷ x02 ∷ h01 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa2 f1 f3 lt13))
      ∷ perm (x13 ∷ x02 ∷ x02 ∷ x13 ∷ h01 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 3 (sym⁼ (ʟc5 f0 f1 f3 lt01 lt13))
      ∷ perm (x02 ∷ x13 ∷ x02 ∷ h03 ∷ x13 ∷ x13 ∷ x02 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 2 (sym⁼ (ʟc4 f0 f2 f3 lt02 lt23))
      ∷ perm (x02 ∷ x13 ∷ h23 ∷ x13 ∷ x13 ∷ x02 ∷ x02 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 3 (ʟa2 f1 f3 lt13)
      ∷ perm (x02 ∷ x13 ∷ h23 ∷ x02 ∷ x02 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 3 (ʟa2 f0 f2 lt02)
      ∷ perm (x02 ∷ x13 ∷ h23 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ h23 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 4 (sym⁼ (ʟd1 f2 f3 lt23))
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ h23 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ h23 ∷ [])
      ∷ rw 0 (sym⁼ δpz)
      ∷ perm (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ []
      ) refl

    δk1p : Eqn
    δk1p = derive (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ( perm (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 (rot⁼ 0 6 d3e)
      ∷ perm (h01 ∷ h23 ∷ h13 ∷ h02 ∷ h23 ∷ h13 ∷ h02 ∷ h23 ∷ [])
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h02 ∷ h23 ∷ [])
      ∷ rw 0 f1e
      ∷ perm (h13 ∷ h02 ∷ h23 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ rw 3 f1e
      ∷ perm (h13 ∷ h02 ∷ h23 ∷ h13 ∷ h02 ∷ h23 ∷ h01 ∷ h23 ∷ [])
      ∷ perm (h13 ∷ h02 ∷ h23 ∷ h13 ∷ h02 ∷ h01 ∷ h23 ∷ h23 ∷ [])
      ∷ rw 6 (ʟa3 f2 f3 lt23)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ []
      ) refl

    δk1 : Eqn
    δk1 = derive (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ( perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h02 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟa3 f2 f3 lt23))
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ δk1p)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 10 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (ʟa3 f2 f3 lt23)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ h02 ∷ h02 ∷ [])
      ∷ rw 6 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h02 ∷ [])
      ∷ rw 6 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ []
      ) refl

    δr20 : Eqn
    δr20 = derive (h01 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ( perm (h01 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h01 ∷ h13 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa3 f2 f3 lt23))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h01 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h01 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ f1e)
      ∷ perm (h01 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 (ʟa3 f0 f1 lt01)
      ∷ perm (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 δk1p
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 δc0p
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ rw 2 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h01 ∷ h23 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ rw 6 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h01 ∷ h23 ∷ h13 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ rw 5 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h01 ∷ h23 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h23 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ rw 4 (sym⁼ (ʟd1 f0 f1 lt01))
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ rw 5 f1e
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h23 ∷ h23 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h23 ∷ h23 ∷ [])
      ∷ rw 8 (ʟa3 f2 f3 lt23)
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ []
      ) refl

  r20 : ⟪ L20 ⟫ ≈ ⟪ R20 ⟫
  r20 = prf δr20

------------------------------------------------------------------------
-- (20) and (f1) give (d3)

module FromR20 (r20eh : ⟪ L20 ⟫ ≈ ⟪ R20 ⟫) (f1eh : ⟪ Lf1 ⟫ ≈ ⟪ Rf1 ⟫) where

  private
    r20e : Eqn
    r20e = eqn L20 R20 r20eh
    f1e : Eqn
    f1e = eqn Lf1 Rf1 f1eh

    δhzbh-02 : Eqn
    δhzbh-02 = derive (h02 ∷ z2 ∷ h02 ∷ []) (x02 ∷ [])
      ( perm (h02 ∷ z2 ∷ h02 ∷ [])
      ∷ rw 1 (ʟd2 f0 f2 lt02)
      ∷ perm (h02 ∷ h02 ∷ x02 ∷ [])
      ∷ rw 0 (ʟa3 f0 f2 lt02)
      ∷ perm (x02 ∷ [])
      ∷ perm (x02 ∷ [])
      ∷ []
      ) refl

    δhzah-02 : Eqn
    δhzah-02 = derive (h02 ∷ z0 ∷ h02 ∷ []) (x02 ∷ z0 ∷ z2 ∷ [])
      ( perm (h02 ∷ z0 ∷ h02 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa1 f2))
      ∷ perm (h02 ∷ z2 ∷ z0 ∷ z2 ∷ h02 ∷ [])
      ∷ rw 2 (ʟd1 f0 f2 lt02)
      ∷ perm (h02 ∷ z2 ∷ h02 ∷ z0 ∷ z2 ∷ [])
      ∷ rw 0 δhzbh-02
      ∷ perm (x02 ∷ z0 ∷ z2 ∷ [])
      ∷ perm (x02 ∷ z0 ∷ z2 ∷ [])
      ∷ []
      ) refl

    δhzbh-13 : Eqn
    δhzbh-13 = derive (h13 ∷ z3 ∷ h13 ∷ []) (x13 ∷ [])
      ( perm (h13 ∷ z3 ∷ h13 ∷ [])
      ∷ rw 1 (ʟd2 f1 f3 lt13)
      ∷ perm (h13 ∷ h13 ∷ x13 ∷ [])
      ∷ rw 0 (ʟa3 f1 f3 lt13)
      ∷ perm (x13 ∷ [])
      ∷ perm (x13 ∷ [])
      ∷ []
      ) refl

    δhzah-13 : Eqn
    δhzah-13 = derive (h13 ∷ z1 ∷ h13 ∷ []) (x13 ∷ z1 ∷ z3 ∷ [])
      ( perm (h13 ∷ z1 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa1 f3))
      ∷ perm (h13 ∷ z3 ∷ z1 ∷ z3 ∷ h13 ∷ [])
      ∷ rw 2 (ʟd1 f1 f3 lt13)
      ∷ perm (h13 ∷ z3 ∷ h13 ∷ z1 ∷ z3 ∷ [])
      ∷ rw 0 δhzbh-13
      ∷ perm (x13 ∷ z1 ∷ z3 ∷ [])
      ∷ perm (x13 ∷ z1 ∷ z3 ∷ [])
      ∷ []
      ) refl

    δpz : Eqn
    δpz = derive (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ []) (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ( perm (h02 ∷ z0 ∷ h02 ∷ h13 ∷ z1 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ z0 ∷ h02 ∷ h13 ∷ z1 ∷ h13 ∷ [])
      ∷ rw 3 δhzah-13
      ∷ perm (x13 ∷ z1 ∷ h02 ∷ z0 ∷ h02 ∷ z3 ∷ [])
      ∷ rw 2 δhzah-02
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ []
      ) refl

    δc0p : Eqn
    δc0p = derive (h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ( perm (h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 1 δpz
      ∷ perm (h01 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ perm (h01 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa2 f0 f2 lt02))
      ∷ perm (x02 ∷ x02 ∷ h01 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa2 f1 f3 lt13))
      ∷ perm (x13 ∷ x02 ∷ x02 ∷ x13 ∷ h01 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 3 (sym⁼ (ʟc5 f0 f1 f3 lt01 lt13))
      ∷ perm (x02 ∷ x13 ∷ x02 ∷ h03 ∷ x13 ∷ x13 ∷ x02 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 2 (sym⁼ (ʟc4 f0 f2 f3 lt02 lt23))
      ∷ perm (x02 ∷ x13 ∷ h23 ∷ x13 ∷ x13 ∷ x02 ∷ x02 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 3 (ʟa2 f1 f3 lt13)
      ∷ perm (x02 ∷ x13 ∷ h23 ∷ x02 ∷ x02 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 3 (ʟa2 f0 f2 lt02)
      ∷ perm (x02 ∷ x13 ∷ h23 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ h23 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 4 (sym⁼ (ʟd1 f2 f3 lt23))
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ h23 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ h23 ∷ [])
      ∷ rw 0 (sym⁼ δpz)
      ∷ perm (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ []
      ) refl

    δpc0 : Eqn
    δpc0 = derive (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ []) (h23 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 0 δpz
      ∷ perm (x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ h01 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ z2 ∷ z3 ∷ z0 ∷ z1 ∷ h01 ∷ [])
      ∷ rw 4 (ʟd1 f0 f1 lt01)
      ∷ perm (x02 ∷ x13 ∷ h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ perm (x02 ∷ x13 ∷ h01 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 1 (sym⁼ (ʟc5 f0 f1 f3 lt01 lt13))
      ∷ perm (x02 ∷ h03 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 0 (sym⁼ (ʟc4 f0 f2 f3 lt02 lt23))
      ∷ perm (h23 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ perm (h23 ∷ x02 ∷ x13 ∷ z0 ∷ z1 ∷ z2 ∷ z3 ∷ [])
      ∷ rw 1 (sym⁼ δpz)
      ∷ perm (h23 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h23 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δy : Eqn
    δy = derive (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ []) (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ( perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h13 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟa3 f2 f3 lt23))
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 (sym⁼ f1e)
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ []
      ) refl

    δy20 : Eqn
    δy20 = derive (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ []) (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ( perm (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ perm (h01 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ δy)
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 r20e
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 0 δy
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ []
      ) refl

    δk1 : Eqn
    δk1 = derive (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ( perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 6 (sym⁼ (ʟa1 f1))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ z1 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 7 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ z1 ∷ h13 ∷ h13 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (sym⁼ (ʟa1 f0))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ z0 ∷ z1 ∷ h13 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ (ʟa3 f2 f3 lt23))
      ∷ perm (h01 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h23 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ δy)
      ∷ perm (h23 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (sym⁼ (ʟa3 f0 f1 lt01))
      ∷ perm (h23 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 1 (sym⁼ r20e)
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 δy
      ∷ perm (h01 ∷ h23 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h01 ∷ h23 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (sym⁼ δy)
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h01 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h02 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 f1e
      ∷ perm (h02 ∷ h13 ∷ h01 ∷ h01 ∷ h23 ∷ h02 ∷ h02 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (ʟa3 f0 f1 lt01)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h02 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 δpc0
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h02 ∷ h13 ∷ h13 ∷ z0 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 12 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ z0 ∷ h02 ∷ h02 ∷ z0 ∷ z1 ∷ z1 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 12 (ʟa1 f1)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ z0 ∷ h02 ∷ h02 ∷ z0 ∷ h02 ∷ h13 ∷ h13 ∷ [])
      ∷ rw 12 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ z0 ∷ h02 ∷ h02 ∷ z0 ∷ h02 ∷ [])
      ∷ rw 8 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ z0 ∷ z0 ∷ h02 ∷ [])
      ∷ rw 7 (ʟa1 f0)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h02 ∷ [])
      ∷ rw 6 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ [])
      ∷ []
      ) refl

    δk1p : Eqn
    δk1p = derive (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ []) (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ( perm (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h02 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 2 (sym⁼ (ʟa3 f2 f3 lt23))
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 3 (sym⁼ (ʟa3 f1 f3 lt13))
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 4 (sym⁼ (ʟa3 f0 f2 lt02))
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 5 (sym⁼ δk1)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 10 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 9 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 8 (ʟa3 f2 f3 lt23)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h13 ∷ h13 ∷ h02 ∷ h02 ∷ [])
      ∷ rw 6 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h02 ∷ [])
      ∷ rw 6 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ []
      ) refl

    δd3 : Eqn
    δd3 = derive (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ []) (h01 ∷ h23 ∷ [])
      ( perm (h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 0 δk1p
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ [])
      ∷ rw 6 δk1p
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h01 ∷ [])
      ∷ rw 5 δk1
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h01 ∷ [])
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h13 ∷ h02 ∷ h02 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h01 ∷ [])
      ∷ rw 4 (ʟa3 f0 f2 lt02)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h13 ∷ h13 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h01 ∷ [])
      ∷ rw 3 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h13 ∷ h23 ∷ h23 ∷ h02 ∷ h13 ∷ h23 ∷ h01 ∷ [])
      ∷ rw 2 (ʟa3 f2 f3 lt23)
      ∷ perm (h13 ∷ h13 ∷ h02 ∷ h02 ∷ h01 ∷ h23 ∷ [])
      ∷ rw 0 (ʟa3 f1 f3 lt13)
      ∷ perm (h02 ∷ h02 ∷ h01 ∷ h23 ∷ [])
      ∷ rw 0 (ʟa3 f0 f2 lt02)
      ∷ perm (h01 ∷ h23 ∷ [])
      ∷ perm (h01 ∷ h23 ∷ [])
      ∷ []
      ) refl

  d3 : ⟪ Ld3 ⟫ ≈ ⟪ Rd3 ⟫
  d3 = prf δd3

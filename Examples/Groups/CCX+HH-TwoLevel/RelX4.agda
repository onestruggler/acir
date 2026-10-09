------------------------------------------------------------------------
-- Presentations of groups
--
-- Squares for the edge X_[x,x+1] when x and x+1 are both among the
-- indices a < b < c < d of the normal syllable N = K_[a,b,c,d]
-- (-1)_[a]^t (Lemma A.20, Subcase 1.2.3): V N = N X with V a word of
-- X's and (-1)'s.  Written 0 < 1 < 2 < 3, derived from Table 1 and
-- Rel4 (Engine).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.RelX4 where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Engine
import Examples.Groups.CCX+HH-TwoLevel.Rel4 as R4

------------------------------------------------------------------------
-- Letters and axioms

private
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
  k0123 : Gen 4
  k0123 = K-gen f0 f1 f2 f3 lt01 lt12 lt23
  m0 : Gen 4
  m0 = M-gen f0
  m1 : Gen 4
  m1 = M-gen f1
  m2 : Gen 4
  m2 = M-gen f2
  m3 : Gen 4
  m3 = M-gen f3
  x01 : Gen 4
  x01 = X-gen f0 f1 lt01
  x02 : Gen 4
  x02 = X-gen f0 f2 lt02
  x12 : Gen 4
  x12 = X-gen f1 f2 lt12
  x13 : Gen 4
  x13 = X-gen f1 f3 lt13
  x23 : Gen 4
  x23 = X-gen f2 f3 lt23

  ax-1a-x01-x01 : Eqn 4
  ax-1a-x01-x01 = ax⁼ (x01 ∷ x01 ∷ []) ([]) (r1a lt01)
  ax-1b-m0-m0 : Eqn 4
  ax-1b-m0-m0 = ax⁼ (m0 ∷ m0 ∷ []) ([]) (r1b)
  ax-3c-x01-m1 : Eqn 4
  ax-3c-x01-m1 = ax⁼ (x01 ∷ m1 ∷ []) (m0 ∷ x01 ∷ []) (r3c lt01)
  ax-4a-x01-k0123 : Eqn 4
  ax-4a-x01-k0123 = ax⁼ (x01 ∷ k0123 ∷ []) (k0123 ∷ x13 ∷ m1 ∷ m3 ∷ []) (r4a lt01 lt12 lt23 lt13)
  ax-4c-x23-k0123 : Eqn 4
  ax-4c-x23-k0123 = ax⁼ (x23 ∷ k0123 ∷ []) (k0123 ∷ x13 ∷ []) (r4c lt01 lt12 lt23 lt13)

------------------------------------------------------------------------
-- The relations

-- X_[a,b], t = 0: (-1)_[d] (-1)_[b] X_[b,d] K = K X_[a,b].
sq-01-f : Eqn 4
sq-01-f = derive (m3 ∷ m1 ∷ x13 ∷ k0123 ∷ []) (k0123 ∷ x01 ∷ [])
  ( perm (m3 ∷ m1 ∷ x13 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ (rev⁼ ax-4a-x01-k0123))
  ∷ perm (k0123 ∷ x01 ∷ [])
  ∷ perm (k0123 ∷ x01 ∷ [])
  ∷ [] ) refl

-- X_[a,b], t = 1: (-1)_[a] (-1)_[c] X_[a,c] K (-1)_[a] = K (-1)_[a] X_[a,b].
sq-01-t : Eqn 4
sq-01-t = derive (m0 ∷ m2 ∷ x02 ∷ k0123 ∷ m0 ∷ []) (k0123 ∷ m0 ∷ x01 ∷ [])
  ( perm (m0 ∷ m2 ∷ x02 ∷ k0123 ∷ m0 ∷ [])
  ∷ rw 4 (sym⁼ ax-1a-x01-x01)
  ∷ perm (m0 ∷ m2 ∷ x02 ∷ k0123 ∷ x01 ∷ x01 ∷ m0 ∷ [])
  ∷ rw 3 (rev⁼ ax-4a-x01-k0123)
  ∷ perm (m3 ∷ m2 ∷ m1 ∷ m0 ∷ x13 ∷ x02 ∷ k0123 ∷ x01 ∷ m0 ∷ [])
  ∷ rw 0 (sym⁼ (rev⁼ R4.r9a))
  ∷ perm (k0123 ∷ m0 ∷ m1 ∷ x01 ∷ m0 ∷ [])
  ∷ rw 2 (rev⁼ ax-3c-x01-m1)
  ∷ perm (k0123 ∷ m0 ∷ x01 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 3 ax-1b-m0-m0
  ∷ perm (k0123 ∷ m0 ∷ x01 ∷ [])
  ∷ perm (k0123 ∷ m0 ∷ x01 ∷ [])
  ∷ [] ) refl

-- X_[b,c]: X_[b,c] K = K X_[b,c].
sq-12 : Eqn 4
sq-12 = derive (x12 ∷ k0123 ∷ []) (k0123 ∷ x12 ∷ [])
  ( perm (x12 ∷ k0123 ∷ [])
  ∷ rw 0 R4.r8c
  ∷ perm (k0123 ∷ x12 ∷ [])
  ∷ perm (k0123 ∷ x12 ∷ [])
  ∷ [] ) refl

-- X_[c,d]: X_[b,d] K = K X_[c,d].
sq-23 : Eqn 4
sq-23 = derive (x13 ∷ k0123 ∷ []) (k0123 ∷ x23 ∷ [])
  ( perm (x13 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ (rev⁼ ax-4c-x23-k0123))
  ∷ perm (k0123 ∷ x23 ∷ [])
  ∷ perm (k0123 ∷ x23 ∷ [])
  ∷ [] ) refl

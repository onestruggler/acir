------------------------------------------------------------------------
-- Presentations of groups
--
-- Relations among the generators on four indices a < b < c < d,
-- written 0 < 1 < 2 < 3, derived from Table 1 (Engine, the steps found
-- by a search that follows the paper's derivations):
--
-- * Proposition A.11, (8a)–(8d): X_[x,y] K = K S for a signed
--   permutation S, for the transpositions not in (4a), (4c);
-- * Proposition A.12, (9a)–(9g): (-1)_[x] (-1)_[y] K = K S, and the
--   same for all four signs;
-- * K (-1)_[a] K (-1)_[a] K = (-1)_[a] X_[b,c], from (4b).
--
-- They hold at any increasing choice of four indices (Engine.emb⁼).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Rel4 where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Engine

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
  x03 : Gen 4
  x03 = X-gen f0 f3 lt03
  x12 : Gen 4
  x12 = X-gen f1 f2 lt12
  x13 : Gen 4
  x13 = X-gen f1 f3 lt13
  x23 : Gen 4
  x23 = X-gen f2 f3 lt23

  ax-1a-x02-x02 : Eqn 4
  ax-1a-x02-x02 = ax⁼ (x02 ∷ x02 ∷ []) ([]) (r1a lt02)
  ax-1a-x12-x12 : Eqn 4
  ax-1a-x12-x12 = ax⁼ (x12 ∷ x12 ∷ []) ([]) (r1a lt12)
  ax-1a-x13-x13 : Eqn 4
  ax-1a-x13-x13 = ax⁼ (x13 ∷ x13 ∷ []) ([]) (r1a lt13)
  ax-1a-x23-x23 : Eqn 4
  ax-1a-x23-x23 = ax⁼ (x23 ∷ x23 ∷ []) ([]) (r1a lt23)
  ax-1b-m0-m0 : Eqn 4
  ax-1b-m0-m0 = ax⁼ (m0 ∷ m0 ∷ []) ([]) (r1b)
  ax-1b-m1-m1 : Eqn 4
  ax-1b-m1-m1 = ax⁼ (m1 ∷ m1 ∷ []) ([]) (r1b)
  ax-1b-m2-m2 : Eqn 4
  ax-1b-m2-m2 = ax⁼ (m2 ∷ m2 ∷ []) ([]) (r1b)
  ax-1b-m3-m3 : Eqn 4
  ax-1b-m3-m3 = ax⁼ (m3 ∷ m3 ∷ []) ([]) (r1b)
  ax-1c-k0123-k0123 : Eqn 4
  ax-1c-k0123-k0123 = ax⁼ (k0123 ∷ k0123 ∷ []) ([]) (r1c lt01 lt12 lt23)
  ax-3a-x12-x13 : Eqn 4
  ax-3a-x12-x13 = ax⁼ (x12 ∷ x13 ∷ []) (x23 ∷ x12 ∷ []) (r3a lt12 lt23 lt13)
  ax-3b-x12-x01 : Eqn 4
  ax-3b-x12-x01 = ax⁼ (x12 ∷ x01 ∷ []) (x02 ∷ x12 ∷ []) (r3b lt01 lt12 lt02)
  ax-3b-x23-x02 : Eqn 4
  ax-3b-x23-x02 = ax⁼ (x23 ∷ x02 ∷ []) (x03 ∷ x23 ∷ []) (r3b lt02 lt23 lt03)
  ax-3b-x23-x12 : Eqn 4
  ax-3b-x23-x12 = ax⁼ (x23 ∷ x12 ∷ []) (x13 ∷ x23 ∷ []) (r3b lt12 lt23 lt13)
  ax-3c-x02-m2 : Eqn 4
  ax-3c-x02-m2 = ax⁼ (x02 ∷ m2 ∷ []) (m0 ∷ x02 ∷ []) (r3c lt02)
  ax-3c-x12-m2 : Eqn 4
  ax-3c-x12-m2 = ax⁼ (x12 ∷ m2 ∷ []) (m1 ∷ x12 ∷ []) (r3c lt12)
  ax-3c-x13-m3 : Eqn 4
  ax-3c-x13-m3 = ax⁼ (x13 ∷ m3 ∷ []) (m1 ∷ x13 ∷ []) (r3c lt13)
  ax-4a-x01-k0123 : Eqn 4
  ax-4a-x01-k0123 = ax⁼ (x01 ∷ k0123 ∷ []) (k0123 ∷ x13 ∷ m1 ∷ m3 ∷ []) (r4a lt01 lt12 lt23 lt13)
  ax-4b-x12-k0123 : Eqn 4
  ax-4b-x12-k0123 = ax⁼ (x12 ∷ k0123 ∷ []) (m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ []) (r4b lt01 lt12 lt23)
  ax-4c-x23-k0123 : Eqn 4
  ax-4c-x23-k0123 = ax⁼ (x23 ∷ k0123 ∷ []) (k0123 ∷ x13 ∷ []) (r4c lt01 lt12 lt23 lt13)

------------------------------------------------------------------------
-- Derived relations

r8c : Eqn 4
r8c = derive (x12 ∷ k0123 ∷ []) (k0123 ∷ x12 ∷ [])
  ( perm (x12 ∷ k0123 ∷ [])
  ∷ rw 0 ax-4b-x12-k0123
  ∷ perm (m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k0123-k0123)
  ∷ perm (m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ k0123 ∷ k0123 ∷ m0 ∷ [])
  ∷ rw 4 (sym⁼ ax-1a-x12-x12)
  ∷ perm (m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ x12 ∷ x12 ∷ k0123 ∷ k0123 ∷ m0 ∷ [])
  ∷ rw 5 (sym⁼ ax-1c-k0123-k0123)
  ∷ perm (m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ x12 ∷ k0123 ∷ k0123 ∷ x12 ∷ k0123 ∷ k0123 ∷ m0 ∷ [])
  ∷ rw 8 ax-1c-k0123-k0123
  ∷ perm (m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ x12 ∷ k0123 ∷ k0123 ∷ m0 ∷ x12 ∷ [])
  ∷ rw 4 ax-4b-x12-k0123
  ∷ perm (m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ x12 ∷ [])
  ∷ rw 6 (sym⁼ ax-4b-x12-k0123)
  ∷ perm (m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ x12 ∷ k0123 ∷ x12 ∷ [])
  ∷ rw 0 (sym⁼ ax-4b-x12-k0123)
  ∷ perm (x12 ∷ k0123 ∷ k0123 ∷ x12 ∷ k0123 ∷ x12 ∷ [])
  ∷ rw 1 ax-1c-k0123-k0123
  ∷ perm (x12 ∷ x12 ∷ k0123 ∷ x12 ∷ [])
  ∷ rw 0 ax-1a-x12-x12
  ∷ perm (k0123 ∷ x12 ∷ [])
  ∷ perm (k0123 ∷ x12 ∷ [])
  ∷ [] ) refl

r8d : Eqn 4
r8d = derive (x13 ∷ k0123 ∷ []) (k0123 ∷ x23 ∷ [])
  ( perm (x13 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ ax-1c-k0123-k0123)
  ∷ perm (k0123 ∷ k0123 ∷ x13 ∷ k0123 ∷ [])
  ∷ rw 1 (sym⁼ ax-4c-x23-k0123)
  ∷ perm (k0123 ∷ x23 ∷ k0123 ∷ k0123 ∷ [])
  ∷ rw 2 ax-1c-k0123-k0123
  ∷ perm (k0123 ∷ x23 ∷ [])
  ∷ perm (k0123 ∷ x23 ∷ [])
  ∷ [] ) refl

r8a : Eqn 4
r8a = derive (x02 ∷ k0123 ∷ []) (k0123 ∷ x23 ∷ m2 ∷ m3 ∷ [])
  ( perm (x02 ∷ k0123 ∷ [])
  ∷ rw 1 (sym⁼ ax-1a-x12-x12)
  ∷ perm (x02 ∷ x12 ∷ x12 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ ax-3b-x12-x01)
  ∷ perm (x12 ∷ x01 ∷ x12 ∷ k0123 ∷ [])
  ∷ perm (x12 ∷ x01 ∷ x12 ∷ k0123 ∷ [])
  ∷ rw 2 r8c
  ∷ perm (x12 ∷ x01 ∷ k0123 ∷ x12 ∷ [])
  ∷ perm (x12 ∷ x01 ∷ k0123 ∷ x12 ∷ [])
  ∷ rw 1 ax-4a-x01-k0123
  ∷ perm (x12 ∷ k0123 ∷ x13 ∷ m1 ∷ m3 ∷ x12 ∷ [])
  ∷ perm (x12 ∷ k0123 ∷ x13 ∷ m1 ∷ m3 ∷ x12 ∷ [])
  ∷ rw 0 r8c
  ∷ perm (k0123 ∷ x12 ∷ x13 ∷ m1 ∷ m3 ∷ x12 ∷ [])
  ∷ perm (k0123 ∷ x12 ∷ x13 ∷ m1 ∷ m3 ∷ x12 ∷ [])
  ∷ rw 1 ax-3a-x12-x13
  ∷ perm (k0123 ∷ x23 ∷ x12 ∷ m3 ∷ m1 ∷ x12 ∷ [])
  ∷ rw 4 (sym⁼ ax-3c-x12-m2)
  ∷ perm (k0123 ∷ x23 ∷ x12 ∷ x12 ∷ m2 ∷ m3 ∷ [])
  ∷ rw 2 ax-1a-x12-x12
  ∷ perm (k0123 ∷ x23 ∷ m2 ∷ m3 ∷ [])
  ∷ perm (k0123 ∷ x23 ∷ m2 ∷ m3 ∷ [])
  ∷ [] ) refl

r8b : Eqn 4
r8b = derive (x03 ∷ k0123 ∷ []) (k0123 ∷ x13 ∷ x23 ∷ x13 ∷ m1 ∷ m2 ∷ [])
  ( perm (x03 ∷ k0123 ∷ [])
  ∷ rw 1 (sym⁼ ax-1a-x23-x23)
  ∷ perm (x03 ∷ x23 ∷ x23 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ ax-3b-x23-x02)
  ∷ perm (x23 ∷ x02 ∷ x23 ∷ k0123 ∷ [])
  ∷ perm (x23 ∷ x02 ∷ x23 ∷ k0123 ∷ [])
  ∷ rw 2 ax-4c-x23-k0123
  ∷ perm (x23 ∷ x02 ∷ k0123 ∷ x13 ∷ [])
  ∷ perm (x23 ∷ x02 ∷ k0123 ∷ x13 ∷ [])
  ∷ rw 1 r8a
  ∷ perm (x23 ∷ k0123 ∷ x23 ∷ m2 ∷ m3 ∷ x13 ∷ [])
  ∷ perm (x23 ∷ k0123 ∷ x23 ∷ m2 ∷ m3 ∷ x13 ∷ [])
  ∷ rw 0 ax-4c-x23-k0123
  ∷ perm (k0123 ∷ x13 ∷ x23 ∷ m2 ∷ m3 ∷ x13 ∷ [])
  ∷ perm (k0123 ∷ x13 ∷ x23 ∷ m2 ∷ m3 ∷ x13 ∷ [])
  ∷ rw 3 (sym⁼ ax-1a-x13-x13)
  ∷ perm (k0123 ∷ x13 ∷ x23 ∷ x13 ∷ m2 ∷ x13 ∷ m3 ∷ x13 ∷ [])
  ∷ rw 5 ax-3c-x13-m3
  ∷ perm (k0123 ∷ x13 ∷ x23 ∷ x13 ∷ m1 ∷ x13 ∷ x13 ∷ m2 ∷ [])
  ∷ rw 5 ax-1a-x13-x13
  ∷ perm (k0123 ∷ x13 ∷ x23 ∷ x13 ∷ m1 ∷ m2 ∷ [])
  ∷ perm (k0123 ∷ x13 ∷ x23 ∷ x13 ∷ m1 ∷ m2 ∷ [])
  ∷ [] ) refl

r9e : Eqn 4
r9e = derive (m1 ∷ m3 ∷ k0123 ∷ []) (k0123 ∷ x01 ∷ x23 ∷ [])
  ( perm (m1 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1a-x23-x23)
  ∷ perm (m1 ∷ m3 ∷ k0123 ∷ x23 ∷ x23 ∷ [])
  ∷ perm (m1 ∷ m3 ∷ k0123 ∷ x23 ∷ x23 ∷ [])
  ∷ rw 2 (sym⁼ r8d)
  ∷ perm (m1 ∷ m3 ∷ x13 ∷ k0123 ∷ x23 ∷ [])
  ∷ perm (m1 ∷ m3 ∷ x13 ∷ k0123 ∷ x23 ∷ [])
  ∷ rw 0 (sym⁼ ax-1a-x13-x13)
  ∷ perm (x13 ∷ x13 ∷ m1 ∷ m3 ∷ x13 ∷ k0123 ∷ x23 ∷ [])
  ∷ rw 0 (sym⁼ ax-1c-k0123-k0123)
  ∷ perm (k0123 ∷ k0123 ∷ x13 ∷ x13 ∷ m3 ∷ m1 ∷ x13 ∷ k0123 ∷ x23 ∷ [])
  ∷ rw 3 ax-3c-x13-m3
  ∷ perm (k0123 ∷ k0123 ∷ x13 ∷ m1 ∷ x13 ∷ m1 ∷ x13 ∷ k0123 ∷ x23 ∷ [])
  ∷ rw 5 (sym⁼ ax-3c-x13-m3)
  ∷ perm (k0123 ∷ k0123 ∷ x13 ∷ m1 ∷ x13 ∷ x13 ∷ m3 ∷ k0123 ∷ x23 ∷ [])
  ∷ rw 4 ax-1a-x13-x13
  ∷ perm (k0123 ∷ k0123 ∷ x13 ∷ m1 ∷ m3 ∷ k0123 ∷ x23 ∷ [])
  ∷ rw 1 (sym⁼ ax-4a-x01-k0123)
  ∷ perm (k0123 ∷ x01 ∷ k0123 ∷ k0123 ∷ x23 ∷ [])
  ∷ rw 2 ax-1c-k0123-k0123
  ∷ perm (k0123 ∷ x01 ∷ x23 ∷ [])
  ∷ perm (k0123 ∷ x01 ∷ x23 ∷ [])
  ∷ [] ) refl

r9f : Eqn 4
r9f = derive (m2 ∷ m3 ∷ k0123 ∷ []) (k0123 ∷ x02 ∷ x13 ∷ [])
  ( perm (m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ ax-1a-x12-x12)
  ∷ perm (x12 ∷ x12 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 1 ax-3c-x12-m2
  ∷ perm (x12 ∷ m1 ∷ x12 ∷ m3 ∷ k0123 ∷ [])
  ∷ perm (x12 ∷ m1 ∷ m3 ∷ x12 ∷ k0123 ∷ [])
  ∷ rw 3 r8c
  ∷ perm (x12 ∷ m1 ∷ m3 ∷ k0123 ∷ x12 ∷ [])
  ∷ perm (x12 ∷ m1 ∷ m3 ∷ k0123 ∷ x12 ∷ [])
  ∷ rw 1 r9e
  ∷ perm (x12 ∷ k0123 ∷ x01 ∷ x23 ∷ x12 ∷ [])
  ∷ perm (x12 ∷ k0123 ∷ x01 ∷ x23 ∷ x12 ∷ [])
  ∷ rw 0 r8c
  ∷ perm (k0123 ∷ x12 ∷ x01 ∷ x23 ∷ x12 ∷ [])
  ∷ perm (k0123 ∷ x12 ∷ x01 ∷ x23 ∷ x12 ∷ [])
  ∷ rw 3 (sym⁼ ax-3a-x12-x13)
  ∷ perm (k0123 ∷ x12 ∷ x01 ∷ x12 ∷ x13 ∷ [])
  ∷ rw 1 ax-3b-x12-x01
  ∷ perm (k0123 ∷ x02 ∷ x12 ∷ x12 ∷ x13 ∷ [])
  ∷ rw 2 ax-1a-x12-x12
  ∷ perm (k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ perm (k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ [] ) refl

r9d : Eqn 4
r9d = derive (m1 ∷ m2 ∷ k0123 ∷ []) (k0123 ∷ x03 ∷ x12 ∷ [])
  ( perm (m1 ∷ m2 ∷ k0123 ∷ [])
  ∷ rw 1 (sym⁼ ax-1a-x13-x13)
  ∷ perm (m2 ∷ m1 ∷ x13 ∷ x13 ∷ k0123 ∷ [])
  ∷ rw 1 (sym⁼ ax-3c-x13-m3)
  ∷ perm (m2 ∷ x13 ∷ m3 ∷ x13 ∷ k0123 ∷ [])
  ∷ perm (m2 ∷ x13 ∷ m3 ∷ x13 ∷ k0123 ∷ [])
  ∷ rw 3 r8d
  ∷ perm (m2 ∷ x13 ∷ m3 ∷ k0123 ∷ x23 ∷ [])
  ∷ perm (x13 ∷ m2 ∷ m3 ∷ k0123 ∷ x23 ∷ [])
  ∷ perm (x13 ∷ m2 ∷ m3 ∷ k0123 ∷ x23 ∷ [])
  ∷ rw 1 r9f
  ∷ perm (x13 ∷ k0123 ∷ x02 ∷ x13 ∷ x23 ∷ [])
  ∷ perm (x13 ∷ k0123 ∷ x02 ∷ x13 ∷ x23 ∷ [])
  ∷ rw 0 r8d
  ∷ perm (k0123 ∷ x23 ∷ x02 ∷ x13 ∷ x23 ∷ [])
  ∷ perm (k0123 ∷ x23 ∷ x02 ∷ x13 ∷ x23 ∷ [])
  ∷ rw 1 ax-3b-x23-x02
  ∷ perm (k0123 ∷ x03 ∷ x23 ∷ x13 ∷ x23 ∷ [])
  ∷ rw 3 (sym⁼ ax-3b-x23-x12)
  ∷ perm (k0123 ∷ x03 ∷ x23 ∷ x23 ∷ x12 ∷ [])
  ∷ rw 2 ax-1a-x23-x23
  ∷ perm (k0123 ∷ x03 ∷ x12 ∷ [])
  ∷ perm (k0123 ∷ x03 ∷ x12 ∷ [])
  ∷ [] ) refl

r9g : Eqn 4
r9g = derive (m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ []) (k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ( perm (m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 2 r9f
  ∷ perm (m0 ∷ m1 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ perm (m0 ∷ m1 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 2 (sym⁼ ax-1a-x13-x13)
  ∷ perm (m0 ∷ m1 ∷ x13 ∷ x13 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 1 (sym⁼ ax-3c-x13-m3)
  ∷ perm (x13 ∷ m0 ∷ m3 ∷ x13 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 3 (sym⁼ ax-1a-x02-x02)
  ∷ perm (x13 ∷ m0 ∷ x02 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 1 (sym⁼ ax-3c-x02-m2)
  ∷ perm (x02 ∷ x13 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ perm (x02 ∷ x13 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 4 (sym⁼ ax-1c-k0123-k0123)
  ∷ perm (x02 ∷ x13 ∷ m2 ∷ m3 ∷ k0123 ∷ k0123 ∷ x02 ∷ x13 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 5 (sym⁼ r9f)
  ∷ perm (x02 ∷ x13 ∷ m2 ∷ m3 ∷ k0123 ∷ m2 ∷ m3 ∷ k0123 ∷ k0123 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 7 ax-1c-k0123-k0123
  ∷ perm (x02 ∷ x13 ∷ m2 ∷ m3 ∷ k0123 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ [])
  ∷ perm (x02 ∷ x13 ∷ m2 ∷ m3 ∷ k0123 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 2 r9f
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ x02 ∷ x13 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ [])
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ x13 ∷ x02 ∷ m2 ∷ m3 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 4 ax-3c-x02-m2
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ m0 ∷ x02 ∷ x13 ∷ m3 ∷ x02 ∷ x13 ∷ [])
  ∷ rw 5 ax-3c-x13-m3
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ m0 ∷ x02 ∷ x02 ∷ m1 ∷ x13 ∷ x13 ∷ [])
  ∷ rw 7 ax-1a-x13-x13
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ m0 ∷ x02 ∷ x02 ∷ m1 ∷ [])
  ∷ rw 4 ax-1a-x02-x02
  ∷ perm (x02 ∷ x13 ∷ k0123 ∷ m0 ∷ m1 ∷ [])
  ∷ perm (x13 ∷ x02 ∷ k0123 ∷ m0 ∷ m1 ∷ [])
  ∷ rw 1 r8a
  ∷ perm (x13 ∷ k0123 ∷ x23 ∷ m2 ∷ m3 ∷ m0 ∷ m1 ∷ [])
  ∷ rw 1 (sym⁼ r8d)
  ∷ perm (x13 ∷ x13 ∷ k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ rw 0 ax-1a-x13-x13
  ∷ perm (k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ perm (k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ [] ) refl

r9b : Eqn 4
r9b = derive (m0 ∷ m2 ∷ k0123 ∷ []) (k0123 ∷ x01 ∷ x23 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ( perm (m0 ∷ m2 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ ax-1b-m3-m3)
  ∷ perm (m3 ∷ m0 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1b-m1-m1)
  ∷ perm (m1 ∷ m3 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ perm (m1 ∷ m3 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 2 r9g
  ∷ perm (m1 ∷ m3 ∷ k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ perm (m1 ∷ m3 ∷ k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ rw 0 r9e
  ∷ perm (k0123 ∷ x01 ∷ x23 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ perm (k0123 ∷ x01 ∷ x23 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ [] ) refl

r9a : Eqn 4
r9a = derive (m0 ∷ m1 ∷ k0123 ∷ []) (k0123 ∷ x02 ∷ x13 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ( perm (m0 ∷ m1 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ ax-1b-m3-m3)
  ∷ perm (m3 ∷ m0 ∷ m1 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1b-m2-m2)
  ∷ perm (m2 ∷ m3 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ perm (m2 ∷ m3 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 2 r9g
  ∷ perm (m2 ∷ m3 ∷ k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ perm (m2 ∷ m3 ∷ k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ rw 0 r9f
  ∷ perm (k0123 ∷ x02 ∷ x13 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ perm (k0123 ∷ x02 ∷ x13 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ [] ) refl

r9c : Eqn 4
r9c = derive (m0 ∷ m3 ∷ k0123 ∷ []) (k0123 ∷ x03 ∷ x12 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ( perm (m0 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ ax-1b-m2-m2)
  ∷ perm (m2 ∷ m0 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1b-m1-m1)
  ∷ perm (m1 ∷ m2 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ perm (m1 ∷ m2 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ k0123 ∷ [])
  ∷ rw 2 r9g
  ∷ perm (m1 ∷ m2 ∷ k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ perm (m1 ∷ m2 ∷ k0123 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ rw 0 r9d
  ∷ perm (k0123 ∷ x03 ∷ x12 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ perm (k0123 ∷ x03 ∷ x12 ∷ m0 ∷ m1 ∷ m2 ∷ m3 ∷ [])
  ∷ [] ) refl

kmkmk : Eqn 4
kmkmk = derive (k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ []) (m0 ∷ x12 ∷ [])
  ( perm (k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ [])
  ∷ rw 0 (sym⁼ ax-1b-m0-m0)
  ∷ perm (m0 ∷ m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ m0 ∷ k0123 ∷ [])
  ∷ rw 1 (sym⁼ ax-4b-x12-k0123)
  ∷ perm (m0 ∷ x12 ∷ k0123 ∷ k0123 ∷ [])
  ∷ perm (m0 ∷ x12 ∷ k0123 ∷ k0123 ∷ [])
  ∷ rw 2 ax-1c-k0123-k0123
  ∷ perm (m0 ∷ x12 ∷ [])
  ∷ perm (m0 ∷ x12 ∷ [])
  ∷ [] ) refl

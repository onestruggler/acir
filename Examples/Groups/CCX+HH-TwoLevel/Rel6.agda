------------------------------------------------------------------------
-- Presentations of groups
--
-- Relations on six indices 0 < 1 < 2 < 3 < c < d, for the edge
-- K_[0,1,2,3] out of a state whose first four odd entries are a < b
-- among 0, 1, 2, 3 and c < d beyond (Lemma A.20; the paper's
-- Proposition A.15).  Written 0 < … < 5, derived from Table 1 (Engine;
-- the steps found by a search between waypoints):
--
-- * the core, from (5a) and (3g):
--     K_[1,3,c,d] K_[0,1,2,3] K_[2,3,c,d] = X_[3,c] K_[0,1,2,3] X_[3,c];
-- * twelve skeletons K_[x,y,c,d] K_[0,1,2,3] (-1)_[c]^e K_[u,v,c,d] =
--   V K_[0,1,2,3] W, from the core by renaming 0, 1, 2, 3 (ren-…,
--   skel-…);
-- * for each of the 24 configurations (the odd pair a, b; the parity Σ
--   of Lemma A.20; the sign t of the normal syllable N = K_[a,b,c,d]
--   (-1)_[a]^t), the relation N′ K_[0,1,2,3] = V₁ K_[0,1,2,3] V₂ N with
--   N′ the normal syllable after K_[0,1,2,3] and V₁, V₂ words of X's
--   and (-1)'s (cfg-…, with the lists cfg-…-V₁ etc.).  The signs come
--   out of the middle in pairs, using (-1)_[c], which commutes with
--   K_[0,1,2,3] (g-…).
--
-- They hold at any increasing choice of six indices (Engine.emb⁼).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Rel6 where

open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Data.Vec.Base using () renaming ([] to []ᵛ ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Engine
open import Examples.Groups.CCX+HH-TwoLevel.Embedding using (Emb ; emb ; [_]ᵢ ; _∷ᵢ_)
import Examples.Groups.CCX+HH-TwoLevel.Rel4 as R4

------------------------------------------------------------------------
-- Letters, embeddings and axioms

private
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
  k0123 : Gen 6
  k0123 = K-gen f0 f1 f2 f3 lt01 lt12 lt23
  k0124 : Gen 6
  k0124 = K-gen f0 f1 f2 f4 lt01 lt12 lt24
  k0145 : Gen 6
  k0145 = K-gen f0 f1 f4 f5 lt01 lt14 lt45
  k0245 : Gen 6
  k0245 = K-gen f0 f2 f4 f5 lt02 lt24 lt45
  k0345 : Gen 6
  k0345 = K-gen f0 f3 f4 f5 lt03 lt34 lt45
  k1245 : Gen 6
  k1245 = K-gen f1 f2 f4 f5 lt12 lt24 lt45
  k1345 : Gen 6
  k1345 = K-gen f1 f3 f4 f5 lt13 lt34 lt45
  k2345 : Gen 6
  k2345 = K-gen f2 f3 f4 f5 lt23 lt34 lt45
  m0 : Gen 6
  m0 = M-gen f0
  m1 : Gen 6
  m1 = M-gen f1
  m2 : Gen 6
  m2 = M-gen f2
  m3 : Gen 6
  m3 = M-gen f3
  m4 : Gen 6
  m4 = M-gen f4
  m5 : Gen 6
  m5 = M-gen f5
  x01 : Gen 6
  x01 = X-gen f0 f1 lt01
  x02 : Gen 6
  x02 = X-gen f0 f2 lt02
  x03 : Gen 6
  x03 = X-gen f0 f3 lt03
  x12 : Gen 6
  x12 = X-gen f1 f2 lt12
  x13 : Gen 6
  x13 = X-gen f1 f3 lt13
  x15 : Gen 6
  x15 = X-gen f1 f5 lt15
  x23 : Gen 6
  x23 = X-gen f2 f3 lt23
  x25 : Gen 6
  x25 = X-gen f2 f5 lt25
  x34 : Gen 6
  x34 = X-gen f3 f4 lt34
  x45 : Gen 6
  x45 = X-gen f4 f5 lt45
  e0123 : Emb 4 6
  e0123 = emb (f0 ∷ᵛ f1 ∷ᵛ f2 ∷ᵛ f3 ∷ᵛ []ᵛ) (lt01 ∷ᵢ lt12 ∷ᵢ lt23 ∷ᵢ [ f3 ]ᵢ)
  e0145 : Emb 4 6
  e0145 = emb (f0 ∷ᵛ f1 ∷ᵛ f4 ∷ᵛ f5 ∷ᵛ []ᵛ) (lt01 ∷ᵢ lt14 ∷ᵢ lt45 ∷ᵢ [ f5 ]ᵢ)
  e0245 : Emb 4 6
  e0245 = emb (f0 ∷ᵛ f2 ∷ᵛ f4 ∷ᵛ f5 ∷ᵛ []ᵛ) (lt02 ∷ᵢ lt24 ∷ᵢ lt45 ∷ᵢ [ f5 ]ᵢ)
  e0345 : Emb 4 6
  e0345 = emb (f0 ∷ᵛ f3 ∷ᵛ f4 ∷ᵛ f5 ∷ᵛ []ᵛ) (lt03 ∷ᵢ lt34 ∷ᵢ lt45 ∷ᵢ [ f5 ]ᵢ)
  e1245 : Emb 4 6
  e1245 = emb (f1 ∷ᵛ f2 ∷ᵛ f4 ∷ᵛ f5 ∷ᵛ []ᵛ) (lt12 ∷ᵢ lt24 ∷ᵢ lt45 ∷ᵢ [ f5 ]ᵢ)
  e1345 : Emb 4 6
  e1345 = emb (f1 ∷ᵛ f3 ∷ᵛ f4 ∷ᵛ f5 ∷ᵛ []ᵛ) (lt13 ∷ᵢ lt34 ∷ᵢ lt45 ∷ᵢ [ f5 ]ᵢ)
  e2345 : Emb 4 6
  e2345 = emb (f2 ∷ᵛ f3 ∷ᵛ f4 ∷ᵛ f5 ∷ᵛ []ᵛ) (lt23 ∷ᵢ lt34 ∷ᵢ lt45 ∷ᵢ [ f5 ]ᵢ)

  ax-1a-x01-x01 : Eqn 6
  ax-1a-x01-x01 = ax⁼ (x01 ∷ x01 ∷ []) ([]) (r1a lt01)
  ax-1a-x02-x02 : Eqn 6
  ax-1a-x02-x02 = ax⁼ (x02 ∷ x02 ∷ []) ([]) (r1a lt02)
  ax-1a-x03-x03 : Eqn 6
  ax-1a-x03-x03 = ax⁼ (x03 ∷ x03 ∷ []) ([]) (r1a lt03)
  ax-1a-x12-x12 : Eqn 6
  ax-1a-x12-x12 = ax⁼ (x12 ∷ x12 ∷ []) ([]) (r1a lt12)
  ax-1a-x13-x13 : Eqn 6
  ax-1a-x13-x13 = ax⁼ (x13 ∷ x13 ∷ []) ([]) (r1a lt13)
  ax-1a-x23-x23 : Eqn 6
  ax-1a-x23-x23 = ax⁼ (x23 ∷ x23 ∷ []) ([]) (r1a lt23)
  ax-1a-x34-x34 : Eqn 6
  ax-1a-x34-x34 = ax⁼ (x34 ∷ x34 ∷ []) ([]) (r1a lt34)
  ax-1a-x45-x45 : Eqn 6
  ax-1a-x45-x45 = ax⁼ (x45 ∷ x45 ∷ []) ([]) (r1a lt45)
  ax-1b-m0-m0 : Eqn 6
  ax-1b-m0-m0 = ax⁼ (m0 ∷ m0 ∷ []) ([]) (r1b)
  ax-1b-m1-m1 : Eqn 6
  ax-1b-m1-m1 = ax⁼ (m1 ∷ m1 ∷ []) ([]) (r1b)
  ax-1b-m2-m2 : Eqn 6
  ax-1b-m2-m2 = ax⁼ (m2 ∷ m2 ∷ []) ([]) (r1b)
  ax-1b-m4-m4 : Eqn 6
  ax-1b-m4-m4 = ax⁼ (m4 ∷ m4 ∷ []) ([]) (r1b)
  ax-1b-m5-m5 : Eqn 6
  ax-1b-m5-m5 = ax⁼ (m5 ∷ m5 ∷ []) ([]) (r1b)
  ax-1c-k0145-k0145 : Eqn 6
  ax-1c-k0145-k0145 = ax⁼ (k0145 ∷ k0145 ∷ []) ([]) (r1c lt01 lt14 lt45)
  ax-1c-k0245-k0245 : Eqn 6
  ax-1c-k0245-k0245 = ax⁼ (k0245 ∷ k0245 ∷ []) ([]) (r1c lt02 lt24 lt45)
  ax-1c-k0345-k0345 : Eqn 6
  ax-1c-k0345-k0345 = ax⁼ (k0345 ∷ k0345 ∷ []) ([]) (r1c lt03 lt34 lt45)
  ax-1c-k1245-k1245 : Eqn 6
  ax-1c-k1245-k1245 = ax⁼ (k1245 ∷ k1245 ∷ []) ([]) (r1c lt12 lt24 lt45)
  ax-1c-k1345-k1345 : Eqn 6
  ax-1c-k1345-k1345 = ax⁼ (k1345 ∷ k1345 ∷ []) ([]) (r1c lt13 lt34 lt45)
  ax-1c-k2345-k2345 : Eqn 6
  ax-1c-k2345-k2345 = ax⁼ (k2345 ∷ k2345 ∷ []) ([]) (r1c lt23 lt34 lt45)
  ax-3a-x01-x02 : Eqn 6
  ax-3a-x01-x02 = ax⁼ (x01 ∷ x02 ∷ []) (x12 ∷ x01 ∷ []) (r3a lt01 lt12 lt02)
  ax-3a-x01-x03 : Eqn 6
  ax-3a-x01-x03 = ax⁼ (x01 ∷ x03 ∷ []) (x13 ∷ x01 ∷ []) (r3a lt01 lt13 lt03)
  ax-3a-x02-x03 : Eqn 6
  ax-3a-x02-x03 = ax⁼ (x02 ∷ x03 ∷ []) (x23 ∷ x02 ∷ []) (r3a lt02 lt23 lt03)
  ax-3a-x12-x13 : Eqn 6
  ax-3a-x12-x13 = ax⁼ (x12 ∷ x13 ∷ []) (x23 ∷ x12 ∷ []) (r3a lt12 lt23 lt13)
  ax-3a-x12-x15 : Eqn 6
  ax-3a-x12-x15 = ax⁼ (x12 ∷ x15 ∷ []) (x25 ∷ x12 ∷ []) (r3a lt12 lt25 lt15)
  ax-3b-x12-x01 : Eqn 6
  ax-3b-x12-x01 = ax⁼ (x12 ∷ x01 ∷ []) (x02 ∷ x12 ∷ []) (r3b lt01 lt12 lt02)
  ax-3d-x01-k0345 : Eqn 6
  ax-3d-x01-k0345 = ax⁼ (x01 ∷ k0345 ∷ []) (k1345 ∷ x01 ∷ []) (r3d lt01 lt13 lt34 lt45 lt03)
  ax-3d-x02-k0345 : Eqn 6
  ax-3d-x02-k0345 = ax⁼ (x02 ∷ k0345 ∷ []) (k2345 ∷ x02 ∷ []) (r3d lt02 lt23 lt34 lt45 lt03)
  ax-3d-x12-k1345 : Eqn 6
  ax-3d-x12-k1345 = ax⁼ (x12 ∷ k1345 ∷ []) (k2345 ∷ x12 ∷ []) (r3d lt12 lt23 lt34 lt45 lt13)
  ax-3e-x13-k0145 : Eqn 6
  ax-3e-x13-k0145 = ax⁼ (x13 ∷ k0145 ∷ []) (k0345 ∷ x13 ∷ []) (r3e lt01 lt13 lt34 lt45 lt14 lt03)
  ax-3e-x23-k0245 : Eqn 6
  ax-3e-x23-k0245 = ax⁼ (x23 ∷ k0245 ∷ []) (k0345 ∷ x23 ∷ []) (r3e lt02 lt23 lt34 lt45 lt24 lt03)
  ax-3e-x23-k1245 : Eqn 6
  ax-3e-x23-k1245 = ax⁼ (x23 ∷ k1245 ∷ []) (k1345 ∷ x23 ∷ []) (r3e lt12 lt23 lt34 lt45 lt24 lt13)
  ax-3g-x34-k0123 : Eqn 6
  ax-3g-x34-k0123 = ax⁼ (x34 ∷ k0123 ∷ []) (k0124 ∷ x34 ∷ []) (r3g lt01 lt12 lt23 lt34 lt24)
  ax-4a-x01-k0123 : Eqn 6
  ax-4a-x01-k0123 = ax⁼ (x01 ∷ k0123 ∷ []) (k0123 ∷ x13 ∷ m1 ∷ m3 ∷ []) (r4a lt01 lt12 lt23 lt13)
  ax-4a-x12-k1245 : Eqn 6
  ax-4a-x12-k1245 = ax⁼ (x12 ∷ k1245 ∷ []) (k1245 ∷ x25 ∷ m2 ∷ m5 ∷ []) (r4a lt12 lt24 lt45 lt25)
  ax-4c-x23-k0123 : Eqn 6
  ax-4c-x23-k0123 = ax⁼ (x23 ∷ k0123 ∷ []) (k0123 ∷ x13 ∷ []) (r4c lt01 lt12 lt23 lt13)
  ax-5a-k0123-k1345 : Eqn 6
  ax-5a-k0123-k1345 = ax⁼ (k0123 ∷ k1345 ∷ []) (k2345 ∷ k0124 ∷ []) (r5a lt01 lt12 lt23 lt34 lt45 lt13 lt24)

------------------------------------------------------------------------
-- The core, the renamings, the skeletons and the configurations

private

  core : Eqn 6
  core = derive (k1345 ∷ k0123 ∷ k2345 ∷ []) (x34 ∷ k0123 ∷ x34 ∷ [])
    ( perm (k1345 ∷ k0123 ∷ k2345 ∷ [])
    ∷ rw 0 (rev⁼ ax-5a-k0123-k1345)
    ∷ perm (k0124 ∷ k2345 ∷ k2345 ∷ [])
    ∷ perm (k0124 ∷ k2345 ∷ k2345 ∷ [])
    ∷ rw 1 ax-1c-k2345-k2345
    ∷ perm (k0124 ∷ [])
    ∷ perm (k0124 ∷ [])
    ∷ rw 1 (sym⁼ ax-1a-x34-x34)
    ∷ perm (k0124 ∷ x34 ∷ x34 ∷ [])
    ∷ rw 0 (sym⁼ ax-3g-x34-k0123)
    ∷ perm (x34 ∷ k0123 ∷ x34 ∷ [])
    ∷ perm (x34 ∷ k0123 ∷ x34 ∷ [])
    ∷ [] ) refl

  ren-02-01-0-a : Eqn 6
  ren-02-01-0-a = derive (k0245 ∷ []) (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ [])
    ( perm (k0245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x23-x23)
    ∷ perm (x23 ∷ x23 ∷ k0245 ∷ [])
    ∷ rw 1 ax-3e-x23-k0245
    ∷ perm (x23 ∷ k0345 ∷ x23 ∷ [])
    ∷ rw 1 (sym⁼ ax-1a-x01-x01)
    ∷ perm (x01 ∷ x23 ∷ x01 ∷ k0345 ∷ x23 ∷ [])
    ∷ rw 2 ax-3d-x01-k0345
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ [])
    ∷ [] ) refl

  ren-02-01-0-b : Eqn 6
  ren-02-01-0-b = derive (k0145 ∷ []) (x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ( perm (k0145 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x13-x13)
    ∷ perm (x13 ∷ x13 ∷ k0145 ∷ [])
    ∷ rw 1 ax-3e-x13-k0145
    ∷ perm (x13 ∷ k0345 ∷ x13 ∷ [])
    ∷ rw 1 (sym⁼ ax-1a-x02-x02)
    ∷ perm (x02 ∷ x13 ∷ x02 ∷ k0345 ∷ x13 ∷ [])
    ∷ rw 2 ax-3d-x02-k0345
    ∷ perm (x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ [] ) refl

  skel-02-01-0 : Eqn 6
  skel-02-01-0 = derive (k0245 ∷ k0123 ∷ k0145 ∷ []) (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ( perm (k0245 ∷ k0123 ∷ k0145 ∷ [])
    ∷ rw 2 ren-02-01-0-b
    ∷ perm (k0245 ∷ k0123 ∷ x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 0 ren-02-01-0-a
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ k0123 ∷ x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ k0123 ∷ x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 3 (sym⁼ ax-1b-m5-m5)
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ m5 ∷ m5 ∷ x01 ∷ x23 ∷ k0123 ∷ x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 6 ax-4c-x23-k0123
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ m5 ∷ m5 ∷ x01 ∷ k0123 ∷ x02 ∷ x13 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 8 ax-1a-x13-x13
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ m5 ∷ x01 ∷ k0123 ∷ x02 ∷ m5 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 5 (rev⁼ (emb⁼ e0123 R4.r8a))
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ x23 ∷ x01 ∷ k0123 ∷ m5 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 6 (sym⁼ (rev⁼ (emb⁼ e0123 R4.r9e)))
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ k0123 ∷ m1 ∷ m3 ∷ m5 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ k0123 ∷ m1 ∷ m3 ∷ m5 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 8 (emb⁼ e2345 R4.r9e)
    ∷ perm (x01 ∷ x23 ∷ m2 ∷ k1345 ∷ m5 ∷ m3 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 3 (rev⁼ (emb⁼ e1345 R4.r9e))
    ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 5 core
    ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ∷ [] ) refl

  ren-01-02-0-a : Eqn 6
  ren-01-02-0-a = derive (k0145 ∷ []) (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ x01 ∷ [])
    ( perm (k0145 ∷ [])
    ∷ rw 1 (sym⁼ ax-1a-x01-x01)
    ∷ perm (k0145 ∷ x01 ∷ x01 ∷ [])
    ∷ rw 2 (sym⁼ ax-1a-x03-x03)
    ∷ perm (k0145 ∷ x01 ∷ x03 ∷ x03 ∷ x01 ∷ [])
    ∷ rw 1 ax-3a-x01-x03
    ∷ perm (k0145 ∷ x13 ∷ x01 ∷ x03 ∷ x01 ∷ [])
    ∷ rw 0 (rev⁼ ax-3e-x13-k0145)
    ∷ perm (x13 ∷ k0345 ∷ x01 ∷ x03 ∷ x01 ∷ [])
    ∷ rw 1 (rev⁼ ax-3d-x01-k0345)
    ∷ perm (x13 ∷ x01 ∷ k1345 ∷ x03 ∷ x01 ∷ [])
    ∷ rw 0 (sym⁼ ax-3a-x01-x03)
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ x01 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ x01 ∷ [])
    ∷ [] ) refl

  ren-01-02-0-b : Eqn 6
  ren-01-02-0-b = derive (k0245 ∷ []) (x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ( perm (k0245 ∷ [])
    ∷ rw 1 (sym⁼ ax-1a-x02-x02)
    ∷ perm (k0245 ∷ x02 ∷ x02 ∷ [])
    ∷ rw 2 (sym⁼ ax-1a-x03-x03)
    ∷ perm (k0245 ∷ x02 ∷ x03 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 1 ax-3a-x02-x03
    ∷ perm (k0245 ∷ x23 ∷ x02 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 0 (rev⁼ ax-3e-x23-k0245)
    ∷ perm (x23 ∷ k0345 ∷ x02 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 1 (rev⁼ ax-3d-x02-k0345)
    ∷ perm (x23 ∷ x02 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 0 (sym⁼ ax-3a-x02-x03)
    ∷ perm (x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ [] ) refl

  skel-01-02-0 : Eqn 6
  skel-01-02-0 = derive (k0145 ∷ k0123 ∷ k0245 ∷ []) (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ( perm (k0145 ∷ k0123 ∷ k0245 ∷ [])
    ∷ rw 2 ren-01-02-0-b
    ∷ perm (k0145 ∷ k0123 ∷ x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 0 ren-01-02-0-a
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ x01 ∷ k0123 ∷ x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ x01 ∷ k0123 ∷ x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 3 (sym⁼ ax-1b-m5-m5)
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ m5 ∷ m5 ∷ x03 ∷ x01 ∷ k0123 ∷ x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 5 (rev⁼ ax-3a-x01-x03)
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ m5 ∷ m5 ∷ x01 ∷ x13 ∷ k0123 ∷ x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 6 (sym⁼ (rev⁼ ax-4c-x23-k0123))
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ m5 ∷ m5 ∷ x01 ∷ k0123 ∷ x23 ∷ x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 7 (sym⁼ ax-3a-x02-x03)
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ m5 ∷ x01 ∷ k0123 ∷ x02 ∷ x03 ∷ x03 ∷ m5 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 5 (rev⁼ (emb⁼ e0123 R4.r8a))
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ x23 ∷ x01 ∷ k0123 ∷ x03 ∷ x03 ∷ m5 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 6 (sym⁼ (rev⁼ (emb⁼ e0123 R4.r9e)))
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ k0123 ∷ m1 ∷ m3 ∷ x03 ∷ x03 ∷ m5 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 9 ax-1a-x03-x03
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ k0123 ∷ m1 ∷ m3 ∷ m5 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ k0123 ∷ m1 ∷ m3 ∷ m5 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 8 (emb⁼ e2345 R4.r9e)
    ∷ perm (x01 ∷ x03 ∷ m2 ∷ k1345 ∷ m5 ∷ m3 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 3 (rev⁼ (emb⁼ e1345 R4.r9e))
    ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 5 core
    ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ∷ [] ) refl

  ren-03-03-0-a : Eqn 6
  ren-03-03-0-a = derive (k0345 ∷ []) (x01 ∷ k1345 ∷ x01 ∷ [])
    ( perm (k0345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x01-x01)
    ∷ perm (x01 ∷ x01 ∷ k0345 ∷ [])
    ∷ rw 1 ax-3d-x01-k0345
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ [])
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ [])
    ∷ [] ) refl

  ren-03-03-0-b : Eqn 6
  ren-03-03-0-b = derive (k0345 ∷ []) (x02 ∷ k2345 ∷ x02 ∷ [])
    ( perm (k0345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x02-x02)
    ∷ perm (x02 ∷ x02 ∷ k0345 ∷ [])
    ∷ rw 1 ax-3d-x02-k0345
    ∷ perm (x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ perm (x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ [] ) refl

  skel-03-03-0 : Eqn 6
  skel-03-03-0 = derive (k0345 ∷ k0123 ∷ k0345 ∷ []) (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ( perm (k0345 ∷ k0123 ∷ k0345 ∷ [])
    ∷ rw 2 ren-03-03-0-b
    ∷ perm (k0345 ∷ k0123 ∷ x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 0 ren-03-03-0-a
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ k0123 ∷ x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ k0123 ∷ x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 2 (sym⁼ ax-1b-m5-m5)
    ∷ perm (x01 ∷ k1345 ∷ m5 ∷ m5 ∷ x01 ∷ k0123 ∷ x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 4 ax-4a-x01-k0123
    ∷ perm (x01 ∷ k1345 ∷ m5 ∷ k0123 ∷ x02 ∷ x13 ∷ m1 ∷ m3 ∷ m5 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 3 (sym⁼ (emb⁼ e0123 R4.r9f))
    ∷ perm (x01 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ k0123 ∷ m1 ∷ m3 ∷ m5 ∷ k2345 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ k1345 ∷ m2 ∷ m3 ∷ m5 ∷ k0123 ∷ m1 ∷ m3 ∷ m5 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 7 (emb⁼ e2345 R4.r9e)
    ∷ perm (x01 ∷ m2 ∷ k1345 ∷ m5 ∷ m3 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ∷ rw 2 (rev⁼ (emb⁼ e1345 R4.r9e))
    ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ∷ rw 4 core
    ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ∷ [] ) refl

  ren-12-12-0-a : Eqn 6
  ren-12-12-0-a = derive (k1245 ∷ []) (x23 ∷ k1345 ∷ x23 ∷ [])
    ( perm (k1245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x23-x23)
    ∷ perm (x23 ∷ x23 ∷ k1245 ∷ [])
    ∷ rw 1 ax-3e-x23-k1245
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ [])
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ [])
    ∷ [] ) refl

  ren-12-12-0-b : Eqn 6
  ren-12-12-0-b = derive (k1245 ∷ []) (x13 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ( perm (k1245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x12-x12)
    ∷ perm (x12 ∷ x12 ∷ k1245 ∷ [])
    ∷ rw 1 ax-4a-x12-k1245
    ∷ perm (x12 ∷ k1245 ∷ x25 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 1 ren-12-12-0-a
    ∷ perm (x12 ∷ x23 ∷ k1345 ∷ x23 ∷ x25 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 0 (sym⁼ (rev⁼ ax-3a-x12-x13))
    ∷ perm (x13 ∷ x12 ∷ k1345 ∷ x23 ∷ x25 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 1 ax-3d-x12-k1345
    ∷ perm (x13 ∷ k2345 ∷ x12 ∷ x23 ∷ x25 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ ax-3a-x12-x13))
    ∷ perm (x13 ∷ k2345 ∷ x13 ∷ x12 ∷ x25 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 3 (sym⁼ (rev⁼ ax-3a-x12-x15))
    ∷ perm (x13 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ perm (x13 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ [] ) refl

  skel-12-12-0 : Eqn 6
  skel-12-12-0 = derive (k1245 ∷ k0123 ∷ k1245 ∷ []) (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ( perm (k1245 ∷ k0123 ∷ k1245 ∷ [])
    ∷ rw 2 ren-12-12-0-b
    ∷ perm (k1245 ∷ k0123 ∷ x13 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 0 ren-12-12-0-a
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ k0123 ∷ x13 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ k0123 ∷ x13 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 2 ax-4c-x23-k0123
    ∷ perm (x23 ∷ k1345 ∷ k0123 ∷ x13 ∷ x13 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 3 ax-1a-x13-x13
    ∷ perm (x23 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ perm (x23 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ perm (x23 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ rw 1 core
    ∷ perm (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ perm (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ [] ) refl

  ren-23-13-0-a : Eqn 6
  ren-23-13-0-a = derive (k2345 ∷ []) (x12 ∷ k1345 ∷ x12 ∷ [])
    ( perm (k2345 ∷ [])
    ∷ rw 1 (sym⁼ ax-1a-x12-x12)
    ∷ perm (k2345 ∷ x12 ∷ x12 ∷ [])
    ∷ rw 0 (sym⁼ ax-3d-x12-k1345)
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ [])
    ∷ [] ) refl

  ren-23-13-0-b : Eqn 6
  ren-23-13-0-b = derive (k1345 ∷ []) (x12 ∷ k2345 ∷ x12 ∷ [])
    ( perm (k1345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x12-x12)
    ∷ perm (x12 ∷ x12 ∷ k1345 ∷ [])
    ∷ rw 1 ax-3d-x12-k1345
    ∷ perm (x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ [] ) refl

  skel-23-13-0 : Eqn 6
  skel-23-13-0 = derive (k2345 ∷ k0123 ∷ k1345 ∷ []) (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ [])
    ( perm (k2345 ∷ k0123 ∷ k1345 ∷ [])
    ∷ rw 2 ren-23-13-0-b
    ∷ perm (k2345 ∷ k0123 ∷ x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 0 ren-23-13-0-a
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ k0123 ∷ x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ k0123 ∷ x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 3 (sym⁼ (emb⁼ e0123 R4.r8c))
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ x12 ∷ k0123 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 2 ax-1a-x12-x12
    ∷ perm (x12 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 1 core
    ∷ perm (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ [])
    ∷ [] ) refl

  ren-13-23-0-a : Eqn 6
  ren-13-23-0-a = derive (k1345 ∷ []) (k1345 ∷ [])
    ( perm (k1345 ∷ [])
    ∷ perm (k1345 ∷ [])
    ∷ [] ) refl

  ren-13-23-0-b : Eqn 6
  ren-13-23-0-b = derive (k2345 ∷ []) (k2345 ∷ [])
    ( perm (k2345 ∷ [])
    ∷ perm (k2345 ∷ [])
    ∷ [] ) refl

  skel-13-23-0 : Eqn 6
  skel-13-23-0 = derive (k1345 ∷ k0123 ∷ k2345 ∷ []) (x34 ∷ k0123 ∷ x34 ∷ [])
    ( perm (k1345 ∷ k0123 ∷ k2345 ∷ [])
    ∷ perm (k1345 ∷ k0123 ∷ k2345 ∷ [])
    ∷ perm (k1345 ∷ k0123 ∷ k2345 ∷ [])
    ∷ perm (k1345 ∷ k0123 ∷ k2345 ∷ [])
    ∷ rw 0 core
    ∷ perm (x34 ∷ k0123 ∷ x34 ∷ [])
    ∷ perm (x34 ∷ k0123 ∷ x34 ∷ [])
    ∷ [] ) refl

  ren-13-01-1-a : Eqn 6
  ren-13-01-1-a = derive (k1345 ∷ []) (k1345 ∷ [])
    ( perm (k1345 ∷ [])
    ∷ perm (k1345 ∷ [])
    ∷ [] ) refl

  ren-13-01-1-b : Eqn 6
  ren-13-01-1-b = derive (k0145 ∷ []) (x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ( perm (k0145 ∷ [])
    ∷ rw 0 ren-02-01-0-b
    ∷ perm (x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ [] ) refl

  skel-13-01-1 : Eqn 6
  skel-13-01-1 = derive (k1345 ∷ k0123 ∷ m4 ∷ k0145 ∷ []) (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ [])
    ( perm (k1345 ∷ k0123 ∷ m4 ∷ k0145 ∷ [])
    ∷ rw 3 ren-02-01-0-b
    ∷ perm (k1345 ∷ k0123 ∷ m4 ∷ x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (k1345 ∷ m4 ∷ k0123 ∷ x02 ∷ x13 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e0123 R4.r9f))
    ∷ perm (k1345 ∷ m2 ∷ m3 ∷ m4 ∷ k0123 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (m2 ∷ k1345 ∷ m4 ∷ m3 ∷ k0123 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 1 (rev⁼ (emb⁼ e1345 R4.r9d))
    ∷ perm (x15 ∷ x34 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x15 ∷ x34 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x02 ∷ x13 ∷ [])
    ∷ rw 3 core
    ∷ perm (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ [])
    ∷ [] ) refl

  ren-23-02-1-a : Eqn 6
  ren-23-02-1-a = derive (k2345 ∷ []) (x12 ∷ k1345 ∷ x12 ∷ [])
    ( perm (k2345 ∷ [])
    ∷ rw 0 ren-23-13-0-a
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ [])
    ∷ [] ) refl

  ren-23-02-1-b : Eqn 6
  ren-23-02-1-b = derive (k0245 ∷ []) (x02 ∷ x03 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ( perm (k0245 ∷ [])
    ∷ rw 0 ren-01-02-0-b
    ∷ perm (x02 ∷ x03 ∷ k2345 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 3 (sym⁼ ax-1a-x01-x01)
    ∷ perm (x02 ∷ x03 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x02 ∷ x03 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ [] ) refl

  skel-23-02-1 : Eqn 6
  skel-23-02-1 = derive (k2345 ∷ k0123 ∷ m4 ∷ k0245 ∷ []) (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ( perm (k2345 ∷ k0123 ∷ m4 ∷ k0245 ∷ [])
    ∷ rw 3 ren-23-02-1-b
    ∷ perm (k2345 ∷ k0123 ∷ m4 ∷ x02 ∷ x03 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 0 ren-23-13-0-a
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ k0123 ∷ m4 ∷ x02 ∷ x03 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x12 ∷ k1345 ∷ x12 ∷ k0123 ∷ m4 ∷ x02 ∷ x03 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 2 (emb⁼ e0123 R4.r8c)
    ∷ perm (x12 ∷ k1345 ∷ k0123 ∷ m4 ∷ x12 ∷ x02 ∷ x03 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 4 (sym⁼ (rev⁼ ax-3b-x12-x01))
    ∷ perm (x12 ∷ k1345 ∷ k0123 ∷ m4 ∷ x01 ∷ x03 ∷ x12 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 4 ax-3a-x01-x03
    ∷ perm (x12 ∷ k1345 ∷ m4 ∷ k0123 ∷ x13 ∷ x01 ∷ x12 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 5 (sym⁼ (rev⁼ ax-3a-x01-x02))
    ∷ perm (x12 ∷ k1345 ∷ m4 ∷ k0123 ∷ x02 ∷ x13 ∷ x01 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 3 (sym⁼ (emb⁼ e0123 R4.r9f))
    ∷ perm (x12 ∷ k1345 ∷ m2 ∷ m3 ∷ m4 ∷ k0123 ∷ x01 ∷ x01 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 6 ax-1a-x01-x01
    ∷ perm (x12 ∷ k1345 ∷ m2 ∷ m3 ∷ m4 ∷ k0123 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x12 ∷ m2 ∷ k1345 ∷ m4 ∷ m3 ∷ k0123 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 2 (rev⁼ (emb⁼ e1345 R4.r9d))
    ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ rw 4 core
    ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ [] ) refl

  ren-12-03-1-a : Eqn 6
  ren-12-03-1-a = derive (k1245 ∷ []) (x23 ∷ k1345 ∷ x23 ∷ [])
    ( perm (k1245 ∷ [])
    ∷ rw 0 ren-12-12-0-a
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ [])
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ [])
    ∷ [] ) refl

  ren-12-03-1-b : Eqn 6
  ren-12-03-1-b = derive (k0345 ∷ []) (x02 ∷ k2345 ∷ x02 ∷ [])
    ( perm (k0345 ∷ [])
    ∷ rw 0 ren-03-03-0-b
    ∷ perm (x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ perm (x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ [] ) refl

  skel-12-03-1 : Eqn 6
  skel-12-03-1 = derive (k1245 ∷ k0123 ∷ m4 ∷ k0345 ∷ []) (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ [])
    ( perm (k1245 ∷ k0123 ∷ m4 ∷ k0345 ∷ [])
    ∷ rw 0 ren-12-12-0-a
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ k0123 ∷ m4 ∷ k0345 ∷ [])
    ∷ rw 5 ren-03-03-0-b
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ k0123 ∷ m4 ∷ x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ k0123 ∷ m4 ∷ x02 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 2 ax-4c-x23-k0123
    ∷ perm (x23 ∷ k1345 ∷ m4 ∷ k0123 ∷ x02 ∷ x13 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 3 (sym⁼ (emb⁼ e0123 R4.r9f))
    ∷ perm (x23 ∷ k1345 ∷ m2 ∷ m3 ∷ m4 ∷ k0123 ∷ k2345 ∷ x02 ∷ [])
    ∷ perm (x23 ∷ m2 ∷ k1345 ∷ m4 ∷ m3 ∷ k0123 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 2 (rev⁼ (emb⁼ e1345 R4.r9d))
    ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x02 ∷ [])
    ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x02 ∷ [])
    ∷ rw 4 core
    ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ [])
    ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ [])
    ∷ [] ) refl

  ren-03-12-1-a : Eqn 6
  ren-03-12-1-a = derive (k0345 ∷ []) (x01 ∷ k1345 ∷ x01 ∷ [])
    ( perm (k0345 ∷ [])
    ∷ rw 0 ren-03-03-0-a
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ [])
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ [])
    ∷ [] ) refl

  ren-03-12-1-b : Eqn 6
  ren-03-12-1-b = derive (k1245 ∷ []) (x12 ∷ x13 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ( perm (k1245 ∷ [])
    ∷ rw 0 ren-12-12-0-a
    ∷ perm (x23 ∷ k1345 ∷ x23 ∷ [])
    ∷ rw 1 ren-23-13-0-b
    ∷ perm (x23 ∷ x12 ∷ k2345 ∷ x12 ∷ x23 ∷ [])
    ∷ rw 3 (sym⁼ (rev⁼ ax-3a-x12-x13))
    ∷ perm (x23 ∷ x12 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ rw 0 (sym⁼ ax-3a-x12-x13)
    ∷ perm (x12 ∷ x13 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ x13 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ [] ) refl

  skel-03-12-1 : Eqn 6
  skel-03-12-1 = derive (k0345 ∷ k0123 ∷ m4 ∷ k1245 ∷ []) (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
    ( perm (k0345 ∷ k0123 ∷ m4 ∷ k1245 ∷ [])
    ∷ rw 3 ren-03-12-1-b
    ∷ perm (k0345 ∷ k0123 ∷ m4 ∷ x12 ∷ x13 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ rw 0 ren-03-03-0-a
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ k0123 ∷ m4 ∷ x12 ∷ x13 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ m4 ∷ k0123 ∷ x12 ∷ x13 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ rw 4 (sym⁼ (emb⁼ e0123 R4.r8c))
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ m4 ∷ x12 ∷ k0123 ∷ x13 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ rw 5 (sym⁼ ax-4c-x23-k0123)
    ∷ perm (x01 ∷ k1345 ∷ x01 ∷ x12 ∷ x23 ∷ k0123 ∷ m4 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ ax-3a-x01-x02))
    ∷ perm (x01 ∷ k1345 ∷ x02 ∷ x23 ∷ x01 ∷ k0123 ∷ m4 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ rw 3 (sym⁼ (rev⁼ (emb⁼ e0123 R4.r9e)))
    ∷ perm (x01 ∷ k1345 ∷ x02 ∷ k0123 ∷ m1 ∷ m3 ∷ m4 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ k1345 ∷ x02 ∷ k0123 ∷ m1 ∷ m3 ∷ m4 ∷ k2345 ∷ x13 ∷ x12 ∷ [])
    ∷ rw 5 (emb⁼ e2345 R4.r9d)
    ∷ perm (x01 ∷ x02 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ x02 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
    ∷ rw 2 core
    ∷ perm (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
    ∷ [] ) refl

  ren-01-13-1-a : Eqn 6
  ren-01-13-1-a = derive (k0145 ∷ []) (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ x02 ∷ x03 ∷ x01 ∷ [])
    ( perm (k0145 ∷ [])
    ∷ rw 0 ren-01-02-0-a
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ x01 ∷ [])
    ∷ rw 3 (sym⁼ ax-1a-x02-x02)
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ x02 ∷ x03 ∷ x01 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ x02 ∷ x03 ∷ x01 ∷ [])
    ∷ [] ) refl

  ren-01-13-1-b : Eqn 6
  ren-01-13-1-b = derive (k1345 ∷ []) (x12 ∷ k2345 ∷ x12 ∷ [])
    ( perm (k1345 ∷ [])
    ∷ rw 0 ren-23-13-0-b
    ∷ perm (x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ [] ) refl

  skel-01-13-1 : Eqn 6
  skel-01-13-1 = derive (k0145 ∷ k0123 ∷ m4 ∷ k1345 ∷ []) (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
    ( perm (k0145 ∷ k0123 ∷ m4 ∷ k1345 ∷ [])
    ∷ rw 0 ren-01-13-1-a
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ x02 ∷ x03 ∷ x01 ∷ k0123 ∷ m4 ∷ k1345 ∷ [])
    ∷ rw 9 ren-23-13-0-b
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ x02 ∷ x03 ∷ x01 ∷ k0123 ∷ m4 ∷ x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x02 ∷ x02 ∷ x03 ∷ x01 ∷ k0123 ∷ m4 ∷ x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 3 ax-1a-x02-x02
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ x01 ∷ m4 ∷ k0123 ∷ x12 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 6 (sym⁼ (emb⁼ e0123 R4.r8c))
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ m4 ∷ x01 ∷ x12 ∷ k0123 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 5 (sym⁼ (rev⁼ ax-3a-x01-x02))
    ∷ perm (x01 ∷ x03 ∷ k1345 ∷ x03 ∷ x02 ∷ x01 ∷ k0123 ∷ m4 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 3 (rev⁼ ax-3a-x02-x03)
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ x23 ∷ x01 ∷ k0123 ∷ m4 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 4 (sym⁼ (rev⁼ (emb⁼ e0123 R4.r9e)))
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ k0123 ∷ m1 ∷ m3 ∷ m4 ∷ k2345 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ k0123 ∷ m1 ∷ m3 ∷ m4 ∷ k2345 ∷ x12 ∷ [])
    ∷ rw 6 (emb⁼ e2345 R4.r9d)
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
    ∷ rw 3 core
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
    ∷ [] ) refl

  ren-02-23-1-a : Eqn 6
  ren-02-23-1-a = derive (k0245 ∷ []) (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ [])
    ( perm (k0245 ∷ [])
    ∷ rw 0 ren-02-01-0-a
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ [])
    ∷ [] ) refl

  ren-02-23-1-b : Eqn 6
  ren-02-23-1-b = derive (k2345 ∷ []) (k2345 ∷ [])
    ( perm (k2345 ∷ [])
    ∷ perm (k2345 ∷ [])
    ∷ [] ) refl

  skel-02-23-1 : Eqn 6
  skel-02-23-1 = derive (k0245 ∷ k0123 ∷ m4 ∷ k2345 ∷ []) (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ [])
    ( perm (k0245 ∷ k0123 ∷ m4 ∷ k2345 ∷ [])
    ∷ rw 0 ren-02-01-0-a
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ x01 ∷ x23 ∷ k0123 ∷ m4 ∷ k2345 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ x23 ∷ x01 ∷ k0123 ∷ m4 ∷ k2345 ∷ [])
    ∷ rw 3 (sym⁼ (rev⁼ (emb⁼ e0123 R4.r9e)))
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ k0123 ∷ m1 ∷ m3 ∷ m4 ∷ k2345 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ k0123 ∷ m1 ∷ m3 ∷ m4 ∷ k2345 ∷ [])
    ∷ rw 5 (emb⁼ e2345 R4.r9d)
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x25 ∷ x34 ∷ m1 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x25 ∷ x34 ∷ m1 ∷ [])
    ∷ rw 2 core
    ∷ perm (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ [])
    ∷ [] ) refl

  g-01-f-f : Eqn 6
  g-01-f-f = derive (k0245 ∷ k0123 ∷ k0145 ∷ []) (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ( perm (k0245 ∷ k0123 ∷ k0145 ∷ [])
    ∷ rw 0 skel-02-01-0
    ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
    ∷ [] ) refl

  g-01-f-t : Eqn 6
  g-01-f-t = derive (k0245 ∷ m0 ∷ k0123 ∷ m0 ∷ k0145 ∷ []) (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ( perm (k0245 ∷ m0 ∷ k0123 ∷ m0 ∷ k0145 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x02-x02)
    ∷ perm (x02 ∷ x02 ∷ k0245 ∷ m0 ∷ k0123 ∷ m0 ∷ k0145 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x02 ∷ x02 ∷ k0245 ∷ m0 ∷ k0123 ∷ m0 ∷ k0145 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x02 ∷ x45 ∷ x45 ∷ x02 ∷ k0245 ∷ m0 ∷ m4 ∷ m4 ∷ k0123 ∷ m0 ∷ k0145 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e0245 R4.r9e)))
    ∷ perm (x02 ∷ x45 ∷ k0245 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ m0 ∷ k0145 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e0245 R4.r9g))
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m4 ∷ k0123 ∷ m0 ∷ k0145 ∷ [])
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ k0123 ∷ m0 ∷ m4 ∷ k0145 ∷ [])
    ∷ rw 8 (emb⁼ e0145 R4.r9b)
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ k0123 ∷ k0145 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ k0123 ∷ k0145 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 6 skel-02-01-0
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-01-t-f : Eqn 6
  g-01-t-f = derive (k1345 ∷ m1 ∷ k0123 ∷ k0145 ∷ []) (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ [])
    ( perm (k1345 ∷ m1 ∷ k0123 ∷ k0145 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x13-x13)
    ∷ perm (x13 ∷ x13 ∷ k1345 ∷ m1 ∷ k0123 ∷ k0145 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x13 ∷ x13 ∷ k1345 ∷ m1 ∷ k0123 ∷ k0145 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x13 ∷ x45 ∷ x45 ∷ x13 ∷ k1345 ∷ m1 ∷ m4 ∷ m4 ∷ k0123 ∷ k0145 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e1345 R4.r9e)))
    ∷ perm (x13 ∷ x45 ∷ k1345 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ k0145 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e1345 R4.r9g))
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m4 ∷ k0123 ∷ k0145 ∷ [])
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ k0123 ∷ m4 ∷ k0145 ∷ [])
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ k0123 ∷ m4 ∷ k0145 ∷ [])
    ∷ rw 6 skel-13-01-1
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ [])
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ [])
    ∷ [] ) refl

  g-01-t-t : Eqn 6
  g-01-t-t = derive (k1345 ∷ k0123 ∷ m0 ∷ k0145 ∷ []) (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ( perm (k1345 ∷ k0123 ∷ m0 ∷ k0145 ∷ [])
    ∷ rw 1 (sym⁼ ax-1b-m4-m4)
    ∷ perm (k1345 ∷ k0123 ∷ m4 ∷ m0 ∷ m4 ∷ k0145 ∷ [])
    ∷ rw 3 (emb⁼ e0145 R4.r9b)
    ∷ perm (k1345 ∷ k0123 ∷ m4 ∷ k0145 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (k1345 ∷ k0123 ∷ m4 ∷ k0145 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 0 skel-13-01-1
    ∷ perm (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-02-f-f : Eqn 6
  g-02-f-f = derive (k0145 ∷ k0123 ∷ k0245 ∷ []) (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ( perm (k0145 ∷ k0123 ∷ k0245 ∷ [])
    ∷ rw 0 skel-01-02-0
    ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
    ∷ [] ) refl

  g-02-f-t : Eqn 6
  g-02-f-t = derive (k0145 ∷ m0 ∷ k0123 ∷ m0 ∷ k0245 ∷ []) (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ( perm (k0145 ∷ m0 ∷ k0123 ∷ m0 ∷ k0245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x01-x01)
    ∷ perm (x01 ∷ x01 ∷ k0145 ∷ m0 ∷ k0123 ∷ m0 ∷ k0245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x01 ∷ x01 ∷ k0145 ∷ m0 ∷ k0123 ∷ m0 ∷ k0245 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x01 ∷ x45 ∷ x45 ∷ x01 ∷ k0145 ∷ m0 ∷ m4 ∷ m4 ∷ k0123 ∷ m0 ∷ k0245 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e0145 R4.r9e)))
    ∷ perm (x01 ∷ x45 ∷ k0145 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ m0 ∷ k0245 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e0145 R4.r9g))
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m4 ∷ k0123 ∷ m0 ∷ k0245 ∷ [])
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ k0123 ∷ m0 ∷ m4 ∷ k0245 ∷ [])
    ∷ rw 8 (emb⁼ e0245 R4.r9b)
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ k0123 ∷ k0245 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ k0123 ∷ k0245 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 6 skel-01-02-0
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-02-t-f : Eqn 6
  g-02-t-f = derive (k2345 ∷ m2 ∷ k0123 ∷ k0245 ∷ []) (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ( perm (k2345 ∷ m2 ∷ k0123 ∷ k0245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x23-x23)
    ∷ perm (x23 ∷ x23 ∷ k2345 ∷ m2 ∷ k0123 ∷ k0245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x23 ∷ x23 ∷ k2345 ∷ m2 ∷ k0123 ∷ k0245 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x23 ∷ x45 ∷ x45 ∷ x23 ∷ k2345 ∷ m2 ∷ m4 ∷ m4 ∷ k0123 ∷ k0245 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e2345 R4.r9e)))
    ∷ perm (x23 ∷ x45 ∷ k2345 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ k0245 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e2345 R4.r9g))
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m4 ∷ k0123 ∷ k0245 ∷ [])
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ k0123 ∷ m4 ∷ k0245 ∷ [])
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ k0123 ∷ m4 ∷ k0245 ∷ [])
    ∷ rw 6 skel-23-02-1
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ [])
    ∷ [] ) refl

  g-02-t-t : Eqn 6
  g-02-t-t = derive (k2345 ∷ k0123 ∷ m0 ∷ k0245 ∷ []) (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ( perm (k2345 ∷ k0123 ∷ m0 ∷ k0245 ∷ [])
    ∷ rw 1 (sym⁼ ax-1b-m4-m4)
    ∷ perm (k2345 ∷ k0123 ∷ m4 ∷ m0 ∷ m4 ∷ k0245 ∷ [])
    ∷ rw 3 (emb⁼ e0245 R4.r9b)
    ∷ perm (k2345 ∷ k0123 ∷ m4 ∷ k0245 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (k2345 ∷ k0123 ∷ m4 ∷ k0245 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 0 skel-23-02-1
    ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-03-f-f : Eqn 6
  g-03-f-f = derive (k0345 ∷ k0123 ∷ k0345 ∷ []) (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ( perm (k0345 ∷ k0123 ∷ k0345 ∷ [])
    ∷ rw 0 skel-03-03-0
    ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
    ∷ [] ) refl

  g-03-f-t : Eqn 6
  g-03-f-t = derive (k0345 ∷ m0 ∷ k0123 ∷ m0 ∷ k0345 ∷ []) (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ( perm (k0345 ∷ m0 ∷ k0123 ∷ m0 ∷ k0345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x03-x03)
    ∷ perm (x03 ∷ x03 ∷ k0345 ∷ m0 ∷ k0123 ∷ m0 ∷ k0345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x03 ∷ x03 ∷ k0345 ∷ m0 ∷ k0123 ∷ m0 ∷ k0345 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x03 ∷ x45 ∷ x45 ∷ x03 ∷ k0345 ∷ m0 ∷ m4 ∷ m4 ∷ k0123 ∷ m0 ∷ k0345 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e0345 R4.r9e)))
    ∷ perm (x03 ∷ x45 ∷ k0345 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ m0 ∷ k0345 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e0345 R4.r9g))
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m4 ∷ k0123 ∷ m0 ∷ k0345 ∷ [])
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ k0123 ∷ m0 ∷ m4 ∷ k0345 ∷ [])
    ∷ rw 8 (emb⁼ e0345 R4.r9b)
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ k0123 ∷ k0345 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ k0123 ∷ k0345 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 6 skel-03-03-0
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-03-t-f : Eqn 6
  g-03-t-f = derive (k1245 ∷ m1 ∷ k0123 ∷ k0345 ∷ []) (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ [])
    ( perm (k1245 ∷ m1 ∷ k0123 ∷ k0345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x12-x12)
    ∷ perm (x12 ∷ x12 ∷ k1245 ∷ m1 ∷ k0123 ∷ k0345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x12 ∷ x12 ∷ k1245 ∷ m1 ∷ k0123 ∷ k0345 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x12 ∷ x45 ∷ x45 ∷ x12 ∷ k1245 ∷ m1 ∷ m4 ∷ m4 ∷ k0123 ∷ k0345 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e1245 R4.r9e)))
    ∷ perm (x12 ∷ x45 ∷ k1245 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ k0345 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e1245 R4.r9g))
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m4 ∷ k0123 ∷ k0345 ∷ [])
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ k0123 ∷ m4 ∷ k0345 ∷ [])
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ k0123 ∷ m4 ∷ k0345 ∷ [])
    ∷ rw 6 skel-12-03-1
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ [])
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ [])
    ∷ [] ) refl

  g-03-t-t : Eqn 6
  g-03-t-t = derive (k1245 ∷ k0123 ∷ m0 ∷ k0345 ∷ []) (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ( perm (k1245 ∷ k0123 ∷ m0 ∷ k0345 ∷ [])
    ∷ rw 1 (sym⁼ ax-1b-m4-m4)
    ∷ perm (k1245 ∷ k0123 ∷ m4 ∷ m0 ∷ m4 ∷ k0345 ∷ [])
    ∷ rw 3 (emb⁼ e0345 R4.r9b)
    ∷ perm (k1245 ∷ k0123 ∷ m4 ∷ k0345 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (k1245 ∷ k0123 ∷ m4 ∷ k0345 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 0 skel-12-03-1
    ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-12-f-f : Eqn 6
  g-12-f-f = derive (k0345 ∷ m0 ∷ k0123 ∷ k1245 ∷ []) (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
    ( perm (k0345 ∷ m0 ∷ k0123 ∷ k1245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x03-x03)
    ∷ perm (x03 ∷ x03 ∷ k0345 ∷ m0 ∷ k0123 ∷ k1245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x03 ∷ x03 ∷ k0345 ∷ m0 ∷ k0123 ∷ k1245 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x03 ∷ x45 ∷ x45 ∷ x03 ∷ k0345 ∷ m0 ∷ m4 ∷ m4 ∷ k0123 ∷ k1245 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e0345 R4.r9e)))
    ∷ perm (x03 ∷ x45 ∷ k0345 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ k1245 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e0345 R4.r9g))
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m4 ∷ k0123 ∷ k1245 ∷ [])
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ k0123 ∷ m4 ∷ k1245 ∷ [])
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ k0123 ∷ m4 ∷ k1245 ∷ [])
    ∷ rw 6 skel-03-12-1
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
    ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
    ∷ [] ) refl

  g-12-f-t : Eqn 6
  g-12-f-t = derive (k0345 ∷ k0123 ∷ m1 ∷ k1245 ∷ []) (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ( perm (k0345 ∷ k0123 ∷ m1 ∷ k1245 ∷ [])
    ∷ rw 1 (sym⁼ ax-1b-m4-m4)
    ∷ perm (k0345 ∷ k0123 ∷ m4 ∷ m1 ∷ m4 ∷ k1245 ∷ [])
    ∷ rw 3 (emb⁼ e1245 R4.r9b)
    ∷ perm (k0345 ∷ k0123 ∷ m4 ∷ k1245 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (k0345 ∷ k0123 ∷ m4 ∷ k1245 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 0 skel-03-12-1
    ∷ perm (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-12-t-f : Eqn 6
  g-12-t-f = derive (k1245 ∷ k0123 ∷ k1245 ∷ []) (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ( perm (k1245 ∷ k0123 ∷ k1245 ∷ [])
    ∷ rw 0 skel-12-12-0
    ∷ perm (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ perm (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-12-t-t : Eqn 6
  g-12-t-t = derive (k1245 ∷ m1 ∷ k0123 ∷ m1 ∷ k1245 ∷ []) (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ( perm (k1245 ∷ m1 ∷ k0123 ∷ m1 ∷ k1245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x12-x12)
    ∷ perm (x12 ∷ x12 ∷ k1245 ∷ m1 ∷ k0123 ∷ m1 ∷ k1245 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x12 ∷ x12 ∷ k1245 ∷ m1 ∷ k0123 ∷ m1 ∷ k1245 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x12 ∷ x45 ∷ x45 ∷ x12 ∷ k1245 ∷ m1 ∷ m4 ∷ m4 ∷ k0123 ∷ m1 ∷ k1245 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e1245 R4.r9e)))
    ∷ perm (x12 ∷ x45 ∷ k1245 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ m1 ∷ k1245 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e1245 R4.r9g))
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m4 ∷ k0123 ∷ m1 ∷ k1245 ∷ [])
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ k0123 ∷ m1 ∷ m4 ∷ k1245 ∷ [])
    ∷ rw 8 (emb⁼ e1245 R4.r9b)
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ k0123 ∷ k1245 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ k0123 ∷ k1245 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 6 skel-12-12-0
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-13-f-f : Eqn 6
  g-13-f-f = derive (k0145 ∷ m0 ∷ k0123 ∷ k1345 ∷ []) (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
    ( perm (k0145 ∷ m0 ∷ k0123 ∷ k1345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x01-x01)
    ∷ perm (x01 ∷ x01 ∷ k0145 ∷ m0 ∷ k0123 ∷ k1345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x01 ∷ x01 ∷ k0145 ∷ m0 ∷ k0123 ∷ k1345 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x01 ∷ x45 ∷ x45 ∷ x01 ∷ k0145 ∷ m0 ∷ m4 ∷ m4 ∷ k0123 ∷ k1345 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e0145 R4.r9e)))
    ∷ perm (x01 ∷ x45 ∷ k0145 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ k1345 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e0145 R4.r9g))
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m4 ∷ k0123 ∷ k1345 ∷ [])
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ k0123 ∷ m4 ∷ k1345 ∷ [])
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ k0123 ∷ m4 ∷ k1345 ∷ [])
    ∷ rw 6 skel-01-13-1
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
    ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
    ∷ [] ) refl

  g-13-f-t : Eqn 6
  g-13-f-t = derive (k0145 ∷ k0123 ∷ m1 ∷ k1345 ∷ []) (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ( perm (k0145 ∷ k0123 ∷ m1 ∷ k1345 ∷ [])
    ∷ rw 1 (sym⁼ ax-1b-m4-m4)
    ∷ perm (k0145 ∷ k0123 ∷ m4 ∷ m1 ∷ m4 ∷ k1345 ∷ [])
    ∷ rw 3 (emb⁼ e1345 R4.r9b)
    ∷ perm (k0145 ∷ k0123 ∷ m4 ∷ k1345 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (k0145 ∷ k0123 ∷ m4 ∷ k1345 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 0 skel-01-13-1
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-13-t-f : Eqn 6
  g-13-t-f = derive (k2345 ∷ k0123 ∷ k1345 ∷ []) (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ [])
    ( perm (k2345 ∷ k0123 ∷ k1345 ∷ [])
    ∷ rw 0 skel-23-13-0
    ∷ perm (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ [])
    ∷ perm (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ [])
    ∷ [] ) refl

  g-13-t-t : Eqn 6
  g-13-t-t = derive (k2345 ∷ m2 ∷ k0123 ∷ m1 ∷ k1345 ∷ []) (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ( perm (k2345 ∷ m2 ∷ k0123 ∷ m1 ∷ k1345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x23-x23)
    ∷ perm (x23 ∷ x23 ∷ k2345 ∷ m2 ∷ k0123 ∷ m1 ∷ k1345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x23 ∷ x23 ∷ k2345 ∷ m2 ∷ k0123 ∷ m1 ∷ k1345 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x23 ∷ x45 ∷ x45 ∷ x23 ∷ k2345 ∷ m2 ∷ m4 ∷ m4 ∷ k0123 ∷ m1 ∷ k1345 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e2345 R4.r9e)))
    ∷ perm (x23 ∷ x45 ∷ k2345 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ m1 ∷ k1345 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e2345 R4.r9g))
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m4 ∷ k0123 ∷ m1 ∷ k1345 ∷ [])
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ k0123 ∷ m1 ∷ m4 ∷ k1345 ∷ [])
    ∷ rw 8 (emb⁼ e1345 R4.r9b)
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ k0123 ∷ k1345 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ k0123 ∷ k1345 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 6 skel-23-13-0
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-23-f-f : Eqn 6
  g-23-f-f = derive (k0245 ∷ m0 ∷ k0123 ∷ k2345 ∷ []) (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ [])
    ( perm (k0245 ∷ m0 ∷ k0123 ∷ k2345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x02-x02)
    ∷ perm (x02 ∷ x02 ∷ k0245 ∷ m0 ∷ k0123 ∷ k2345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x02 ∷ x02 ∷ k0245 ∷ m0 ∷ k0123 ∷ k2345 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x02 ∷ x45 ∷ x45 ∷ x02 ∷ k0245 ∷ m0 ∷ m4 ∷ m4 ∷ k0123 ∷ k2345 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e0245 R4.r9e)))
    ∷ perm (x02 ∷ x45 ∷ k0245 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ k2345 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e0245 R4.r9g))
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m4 ∷ k0123 ∷ k2345 ∷ [])
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ k0123 ∷ m4 ∷ k2345 ∷ [])
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ k0123 ∷ m4 ∷ k2345 ∷ [])
    ∷ rw 6 skel-02-23-1
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ [])
    ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ [])
    ∷ [] ) refl

  g-23-f-t : Eqn 6
  g-23-f-t = derive (k0245 ∷ k0123 ∷ m2 ∷ k2345 ∷ []) (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ( perm (k0245 ∷ k0123 ∷ m2 ∷ k2345 ∷ [])
    ∷ rw 1 (sym⁼ ax-1b-m4-m4)
    ∷ perm (k0245 ∷ k0123 ∷ m4 ∷ m2 ∷ m4 ∷ k2345 ∷ [])
    ∷ rw 3 (emb⁼ e2345 R4.r9b)
    ∷ perm (k0245 ∷ k0123 ∷ m4 ∷ k2345 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (k0245 ∷ k0123 ∷ m4 ∷ k2345 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 0 skel-02-23-1
    ∷ perm (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

  g-23-t-f : Eqn 6
  g-23-t-f = derive (k1345 ∷ k0123 ∷ k2345 ∷ []) (x34 ∷ k0123 ∷ x34 ∷ [])
    ( perm (k1345 ∷ k0123 ∷ k2345 ∷ [])
    ∷ rw 0 core
    ∷ perm (x34 ∷ k0123 ∷ x34 ∷ [])
    ∷ perm (x34 ∷ k0123 ∷ x34 ∷ [])
    ∷ [] ) refl

  g-23-t-t : Eqn 6
  g-23-t-t = derive (k1345 ∷ m1 ∷ k0123 ∷ m2 ∷ k2345 ∷ []) (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ( perm (k1345 ∷ m1 ∷ k0123 ∷ m2 ∷ k2345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x13-x13)
    ∷ perm (x13 ∷ x13 ∷ k1345 ∷ m1 ∷ k0123 ∷ m2 ∷ k2345 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x45-x45)
    ∷ perm (x45 ∷ x45 ∷ x13 ∷ x13 ∷ k1345 ∷ m1 ∷ k0123 ∷ m2 ∷ k2345 ∷ [])
    ∷ rw 5 (sym⁼ ax-1b-m4-m4)
    ∷ perm (x13 ∷ x45 ∷ x45 ∷ x13 ∷ k1345 ∷ m1 ∷ m4 ∷ m4 ∷ k0123 ∷ m2 ∷ k2345 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ (emb⁼ e1345 R4.r9e)))
    ∷ perm (x13 ∷ x45 ∷ k1345 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ m4 ∷ k0123 ∷ m2 ∷ k2345 ∷ [])
    ∷ rw 2 (sym⁼ (emb⁼ e1345 R4.r9g))
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m4 ∷ k0123 ∷ m2 ∷ k2345 ∷ [])
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ k0123 ∷ m2 ∷ m4 ∷ k2345 ∷ [])
    ∷ rw 8 (emb⁼ e2345 R4.r9b)
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ k0123 ∷ k2345 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ rw 6 core
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
    ∷ [] ) refl

------------------------------------------------------------------------
-- The relations N′ K_[0,1,2,3] = V₁ K_[0,1,2,3] V₂ N

-- {a, b} = {0, 1}, Σ = false, t = false: after K_[0,1,2,3] the odd pair is {0, 2}, t = false.
cfg-01-f-f-N′ : List (Gen 6)
cfg-01-f-f-N′ = (k0245 ∷ [])
cfg-01-f-f-V₁ : List (Gen 6)
cfg-01-f-f-V₁ = (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ [])
cfg-01-f-f-V₂ : List (Gen 6)
cfg-01-f-f-V₂ = (x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ [])
cfg-01-f-f-N : List (Gen 6)
cfg-01-f-f-N = (k0145 ∷ [])

cfg-01-f-f : Eqn 6
cfg-01-f-f = derive (k0245 ∷ k0123 ∷ []) (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ k0145 ∷ [])
  ( perm (k0245 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1c-k0145-k0145)
  ∷ perm (k0245 ∷ k0123 ∷ k0145 ∷ k0145 ∷ [])
  ∷ perm (k0245 ∷ k0123 ∷ k0145 ∷ k0145 ∷ [])
  ∷ rw 0 skel-02-01-0
  ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ k0145 ∷ [])
  ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ k0145 ∷ [])
  ∷ perm (x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ k0145 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 1}, Σ = false, t = true: after K_[0,1,2,3] the odd pair is {0, 2}, t = true.
cfg-01-f-t-N′ : List (Gen 6)
cfg-01-f-t-N′ = (k0245 ∷ m0 ∷ [])
cfg-01-f-t-V₁ : List (Gen 6)
cfg-01-f-t-V₁ = (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ [])
cfg-01-f-t-V₂ : List (Gen 6)
cfg-01-f-t-V₂ = (x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
cfg-01-f-t-N : List (Gen 6)
cfg-01-f-t-N = (k0145 ∷ m0 ∷ [])

cfg-01-f-t : Eqn 6
cfg-01-f-t = derive (k0245 ∷ m0 ∷ k0123 ∷ []) (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m0 ∷ [])
  ( perm (k0245 ∷ m0 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k0245 ∷ m0 ∷ k0123 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 4 (sym⁼ ax-1c-k0145-k0145)
  ∷ perm (k0245 ∷ m0 ∷ k0123 ∷ m0 ∷ k0145 ∷ k0145 ∷ m0 ∷ [])
  ∷ perm (k0245 ∷ m0 ∷ k0123 ∷ m0 ∷ k0145 ∷ k0145 ∷ m0 ∷ [])
  ∷ rw 0 g-01-f-t
  ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m0 ∷ [])
  ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m0 ∷ [])
  ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m0 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 1}, Σ = true, t = false: after K_[0,1,2,3] the odd pair is {1, 3}, t = true.
cfg-01-t-f-N′ : List (Gen 6)
cfg-01-t-f-N′ = (k1345 ∷ m1 ∷ [])
cfg-01-t-f-V₁ : List (Gen 6)
cfg-01-t-f-V₁ = (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ [])
cfg-01-t-f-V₂ : List (Gen 6)
cfg-01-t-f-V₂ = (x34 ∷ x02 ∷ x13 ∷ [])
cfg-01-t-f-N : List (Gen 6)
cfg-01-t-f-N = (k0145 ∷ [])

cfg-01-t-f : Eqn 6
cfg-01-t-f = derive (k1345 ∷ m1 ∷ k0123 ∷ []) (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ k0145 ∷ [])
  ( perm (k1345 ∷ m1 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k0145-k0145)
  ∷ perm (k1345 ∷ m1 ∷ k0123 ∷ k0145 ∷ k0145 ∷ [])
  ∷ perm (k1345 ∷ m1 ∷ k0123 ∷ k0145 ∷ k0145 ∷ [])
  ∷ rw 0 g-01-t-f
  ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ k0145 ∷ [])
  ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ k0145 ∷ [])
  ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ k0145 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 1}, Σ = true, t = true: after K_[0,1,2,3] the odd pair is {1, 3}, t = false.
cfg-01-t-t-N′ : List (Gen 6)
cfg-01-t-t-N′ = (k1345 ∷ [])
cfg-01-t-t-V₁ : List (Gen 6)
cfg-01-t-t-V₁ = (x15 ∷ x34 ∷ m2 ∷ x34 ∷ [])
cfg-01-t-t-V₂ : List (Gen 6)
cfg-01-t-t-V₂ = (x34 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ [])
cfg-01-t-t-N : List (Gen 6)
cfg-01-t-t-N = (k0145 ∷ m0 ∷ [])

cfg-01-t-t : Eqn 6
cfg-01-t-t = derive (k1345 ∷ k0123 ∷ []) (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m0 ∷ [])
  ( perm (k1345 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k1345 ∷ k0123 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k0145-k0145)
  ∷ perm (k1345 ∷ k0123 ∷ m0 ∷ k0145 ∷ k0145 ∷ m0 ∷ [])
  ∷ perm (k1345 ∷ k0123 ∷ m0 ∷ k0145 ∷ k0145 ∷ m0 ∷ [])
  ∷ rw 0 g-01-t-t
  ∷ perm (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m0 ∷ [])
  ∷ perm (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m0 ∷ [])
  ∷ perm (x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x13 ∷ x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ k0145 ∷ m0 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 2}, Σ = false, t = false: after K_[0,1,2,3] the odd pair is {0, 1}, t = false.
cfg-02-f-f-N′ : List (Gen 6)
cfg-02-f-f-N′ = (k0145 ∷ [])
cfg-02-f-f-V₁ : List (Gen 6)
cfg-02-f-f-V₁ = (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ [])
cfg-02-f-f-V₂ : List (Gen 6)
cfg-02-f-f-V₂ = (x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ [])
cfg-02-f-f-N : List (Gen 6)
cfg-02-f-f-N = (k0245 ∷ [])

cfg-02-f-f : Eqn 6
cfg-02-f-f = derive (k0145 ∷ k0123 ∷ []) (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ k0245 ∷ [])
  ( perm (k0145 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1c-k0245-k0245)
  ∷ perm (k0145 ∷ k0123 ∷ k0245 ∷ k0245 ∷ [])
  ∷ perm (k0145 ∷ k0123 ∷ k0245 ∷ k0245 ∷ [])
  ∷ rw 0 skel-01-02-0
  ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ k0245 ∷ [])
  ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ k0245 ∷ [])
  ∷ perm (x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ k0245 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 2}, Σ = false, t = true: after K_[0,1,2,3] the odd pair is {0, 1}, t = true.
cfg-02-f-t-N′ : List (Gen 6)
cfg-02-f-t-N′ = (k0145 ∷ m0 ∷ [])
cfg-02-f-t-V₁ : List (Gen 6)
cfg-02-f-t-V₁ = (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ [])
cfg-02-f-t-V₂ : List (Gen 6)
cfg-02-f-t-V₂ = (x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
cfg-02-f-t-N : List (Gen 6)
cfg-02-f-t-N = (k0245 ∷ m0 ∷ [])

cfg-02-f-t : Eqn 6
cfg-02-f-t = derive (k0145 ∷ m0 ∷ k0123 ∷ []) (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m0 ∷ [])
  ( perm (k0145 ∷ m0 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k0145 ∷ m0 ∷ k0123 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 4 (sym⁼ ax-1c-k0245-k0245)
  ∷ perm (k0145 ∷ m0 ∷ k0123 ∷ m0 ∷ k0245 ∷ k0245 ∷ m0 ∷ [])
  ∷ perm (k0145 ∷ m0 ∷ k0123 ∷ m0 ∷ k0245 ∷ k0245 ∷ m0 ∷ [])
  ∷ rw 0 g-02-f-t
  ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m0 ∷ [])
  ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m0 ∷ [])
  ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m0 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 2}, Σ = true, t = false: after K_[0,1,2,3] the odd pair is {2, 3}, t = true.
cfg-02-t-f-N′ : List (Gen 6)
cfg-02-t-f-N′ = (k2345 ∷ m2 ∷ [])
cfg-02-t-f-V₁ : List (Gen 6)
cfg-02-t-f-V₁ = (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ [])
cfg-02-t-f-V₂ : List (Gen 6)
cfg-02-t-f-V₂ = (x34 ∷ x01 ∷ x03 ∷ x02 ∷ [])
cfg-02-t-f-N : List (Gen 6)
cfg-02-t-f-N = (k0245 ∷ [])

cfg-02-t-f : Eqn 6
cfg-02-t-f = derive (k2345 ∷ m2 ∷ k0123 ∷ []) (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ k0245 ∷ [])
  ( perm (k2345 ∷ m2 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k0245-k0245)
  ∷ perm (k2345 ∷ m2 ∷ k0123 ∷ k0245 ∷ k0245 ∷ [])
  ∷ perm (k2345 ∷ m2 ∷ k0123 ∷ k0245 ∷ k0245 ∷ [])
  ∷ rw 0 g-02-t-f
  ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ k0245 ∷ [])
  ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ k0245 ∷ [])
  ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ k0245 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 2}, Σ = true, t = true: after K_[0,1,2,3] the odd pair is {2, 3}, t = false.
cfg-02-t-t-N′ : List (Gen 6)
cfg-02-t-t-N′ = (k2345 ∷ [])
cfg-02-t-t-V₁ : List (Gen 6)
cfg-02-t-t-V₁ = (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ [])
cfg-02-t-t-V₂ : List (Gen 6)
cfg-02-t-t-V₂ = (x34 ∷ x01 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ [])
cfg-02-t-t-N : List (Gen 6)
cfg-02-t-t-N = (k0245 ∷ m0 ∷ [])

cfg-02-t-t : Eqn 6
cfg-02-t-t = derive (k2345 ∷ k0123 ∷ []) (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m0 ∷ [])
  ( perm (k2345 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k2345 ∷ k0123 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k0245-k0245)
  ∷ perm (k2345 ∷ k0123 ∷ m0 ∷ k0245 ∷ k0245 ∷ m0 ∷ [])
  ∷ perm (k2345 ∷ k0123 ∷ m0 ∷ k0245 ∷ k0245 ∷ m0 ∷ [])
  ∷ rw 0 g-02-t-t
  ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m0 ∷ [])
  ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m0 ∷ [])
  ∷ perm (x12 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x01 ∷ x03 ∷ x02 ∷ x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ k0245 ∷ m0 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 3}, Σ = false, t = false: after K_[0,1,2,3] the odd pair is {0, 3}, t = false.
cfg-03-f-f-N′ : List (Gen 6)
cfg-03-f-f-N′ = (k0345 ∷ [])
cfg-03-f-f-V₁ : List (Gen 6)
cfg-03-f-f-V₁ = (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ [])
cfg-03-f-f-V₂ : List (Gen 6)
cfg-03-f-f-V₂ = (x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ [])
cfg-03-f-f-N : List (Gen 6)
cfg-03-f-f-N = (k0345 ∷ [])

cfg-03-f-f : Eqn 6
cfg-03-f-f = derive (k0345 ∷ k0123 ∷ []) (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ k0345 ∷ [])
  ( perm (k0345 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1c-k0345-k0345)
  ∷ perm (k0345 ∷ k0123 ∷ k0345 ∷ k0345 ∷ [])
  ∷ perm (k0345 ∷ k0123 ∷ k0345 ∷ k0345 ∷ [])
  ∷ rw 0 skel-03-03-0
  ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ k0345 ∷ [])
  ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ k0345 ∷ [])
  ∷ perm (x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ k0345 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 3}, Σ = false, t = true: after K_[0,1,2,3] the odd pair is {0, 3}, t = true.
cfg-03-f-t-N′ : List (Gen 6)
cfg-03-f-t-N′ = (k0345 ∷ m0 ∷ [])
cfg-03-f-t-V₁ : List (Gen 6)
cfg-03-f-t-V₁ = (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ [])
cfg-03-f-t-V₂ : List (Gen 6)
cfg-03-f-t-V₂ = (x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
cfg-03-f-t-N : List (Gen 6)
cfg-03-f-t-N = (k0345 ∷ m0 ∷ [])

cfg-03-f-t : Eqn 6
cfg-03-f-t = derive (k0345 ∷ m0 ∷ k0123 ∷ []) (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m0 ∷ [])
  ( perm (k0345 ∷ m0 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k0345 ∷ m0 ∷ k0123 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 4 (sym⁼ ax-1c-k0345-k0345)
  ∷ perm (k0345 ∷ m0 ∷ k0123 ∷ m0 ∷ k0345 ∷ k0345 ∷ m0 ∷ [])
  ∷ perm (k0345 ∷ m0 ∷ k0123 ∷ m0 ∷ k0345 ∷ k0345 ∷ m0 ∷ [])
  ∷ rw 0 g-03-f-t
  ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m0 ∷ [])
  ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m0 ∷ [])
  ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x13 ∷ x45 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m1 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m0 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 3}, Σ = true, t = false: after K_[0,1,2,3] the odd pair is {1, 2}, t = true.
cfg-03-t-f-N′ : List (Gen 6)
cfg-03-t-f-N′ = (k1245 ∷ m1 ∷ [])
cfg-03-t-f-V₁ : List (Gen 6)
cfg-03-t-f-V₁ = (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ [])
cfg-03-t-f-V₂ : List (Gen 6)
cfg-03-t-f-V₂ = (x34 ∷ x02 ∷ [])
cfg-03-t-f-N : List (Gen 6)
cfg-03-t-f-N = (k0345 ∷ [])

cfg-03-t-f : Eqn 6
cfg-03-t-f = derive (k1245 ∷ m1 ∷ k0123 ∷ []) (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ k0345 ∷ [])
  ( perm (k1245 ∷ m1 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k0345-k0345)
  ∷ perm (k1245 ∷ m1 ∷ k0123 ∷ k0345 ∷ k0345 ∷ [])
  ∷ perm (k1245 ∷ m1 ∷ k0123 ∷ k0345 ∷ k0345 ∷ [])
  ∷ rw 0 g-03-t-f
  ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ k0345 ∷ [])
  ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ k0345 ∷ [])
  ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ k0345 ∷ [])
  ∷ [] ) refl

-- {a, b} = {0, 3}, Σ = true, t = true: after K_[0,1,2,3] the odd pair is {1, 2}, t = false.
cfg-03-t-t-N′ : List (Gen 6)
cfg-03-t-t-N′ = (k1245 ∷ [])
cfg-03-t-t-V₁ : List (Gen 6)
cfg-03-t-t-V₁ = (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ [])
cfg-03-t-t-V₂ : List (Gen 6)
cfg-03-t-t-V₂ = (x34 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ [])
cfg-03-t-t-N : List (Gen 6)
cfg-03-t-t-N = (k0345 ∷ m0 ∷ [])

cfg-03-t-t : Eqn 6
cfg-03-t-t = derive (k1245 ∷ k0123 ∷ []) (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m0 ∷ [])
  ( perm (k1245 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1b-m0-m0)
  ∷ perm (k1245 ∷ k0123 ∷ m0 ∷ m0 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k0345-k0345)
  ∷ perm (k1245 ∷ k0123 ∷ m0 ∷ k0345 ∷ k0345 ∷ m0 ∷ [])
  ∷ perm (k1245 ∷ k0123 ∷ m0 ∷ k0345 ∷ k0345 ∷ m0 ∷ [])
  ∷ rw 0 g-03-t-t
  ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m0 ∷ [])
  ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m0 ∷ [])
  ∷ perm (x23 ∷ x15 ∷ x34 ∷ m2 ∷ x34 ∷ k0123 ∷ x34 ∷ x02 ∷ x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ k0345 ∷ m0 ∷ [])
  ∷ [] ) refl

-- {a, b} = {1, 2}, Σ = false, t = false: after K_[0,1,2,3] the odd pair is {0, 3}, t = true.
cfg-12-f-f-N′ : List (Gen 6)
cfg-12-f-f-N′ = (k0345 ∷ m0 ∷ [])
cfg-12-f-f-V₁ : List (Gen 6)
cfg-12-f-f-V₁ = (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x02 ∷ x34 ∷ [])
cfg-12-f-f-V₂ : List (Gen 6)
cfg-12-f-f-V₂ = (x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ [])
cfg-12-f-f-N : List (Gen 6)
cfg-12-f-f-N = (k1245 ∷ [])

cfg-12-f-f : Eqn 6
cfg-12-f-f = derive (k0345 ∷ m0 ∷ k0123 ∷ []) (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ k1245 ∷ [])
  ( perm (k0345 ∷ m0 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k1245-k1245)
  ∷ perm (k0345 ∷ m0 ∷ k0123 ∷ k1245 ∷ k1245 ∷ [])
  ∷ perm (k0345 ∷ m0 ∷ k0123 ∷ k1245 ∷ k1245 ∷ [])
  ∷ rw 0 g-12-f-f
  ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ k1245 ∷ [])
  ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ k1245 ∷ [])
  ∷ perm (x03 ∷ x45 ∷ m0 ∷ m3 ∷ m4 ∷ m5 ∷ x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ k1245 ∷ [])
  ∷ [] ) refl

-- {a, b} = {1, 2}, Σ = false, t = true: after K_[0,1,2,3] the odd pair is {0, 3}, t = false.
cfg-12-f-t-N′ : List (Gen 6)
cfg-12-f-t-N′ = (k0345 ∷ [])
cfg-12-f-t-V₁ : List (Gen 6)
cfg-12-f-t-V₁ = (x01 ∷ x02 ∷ x34 ∷ [])
cfg-12-f-t-V₂ : List (Gen 6)
cfg-12-f-t-V₂ = (x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
cfg-12-f-t-N : List (Gen 6)
cfg-12-f-t-N = (k1245 ∷ m1 ∷ [])

cfg-12-f-t : Eqn 6
cfg-12-f-t = derive (k0345 ∷ k0123 ∷ []) (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m1 ∷ [])
  ( perm (k0345 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1b-m1-m1)
  ∷ perm (k0345 ∷ k0123 ∷ m1 ∷ m1 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k1245-k1245)
  ∷ perm (k0345 ∷ k0123 ∷ m1 ∷ k1245 ∷ k1245 ∷ m1 ∷ [])
  ∷ perm (k0345 ∷ k0123 ∷ m1 ∷ k1245 ∷ k1245 ∷ m1 ∷ [])
  ∷ rw 0 g-12-f-t
  ∷ perm (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m1 ∷ [])
  ∷ perm (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m1 ∷ [])
  ∷ perm (x01 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x13 ∷ x12 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m1 ∷ [])
  ∷ [] ) refl

-- {a, b} = {1, 2}, Σ = true, t = false: after K_[0,1,2,3] the odd pair is {1, 2}, t = false.
cfg-12-t-f-N′ : List (Gen 6)
cfg-12-t-f-N′ = (k1245 ∷ [])
cfg-12-t-f-V₁ : List (Gen 6)
cfg-12-t-f-V₁ = (x23 ∷ x34 ∷ [])
cfg-12-t-f-V₂ : List (Gen 6)
cfg-12-t-f-V₂ = (x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ [])
cfg-12-t-f-N : List (Gen 6)
cfg-12-t-f-N = (k1245 ∷ [])

cfg-12-t-f : Eqn 6
cfg-12-t-f = derive (k1245 ∷ k0123 ∷ []) (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ k1245 ∷ [])
  ( perm (k1245 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1c-k1245-k1245)
  ∷ perm (k1245 ∷ k0123 ∷ k1245 ∷ k1245 ∷ [])
  ∷ perm (k1245 ∷ k0123 ∷ k1245 ∷ k1245 ∷ [])
  ∷ rw 0 skel-12-12-0
  ∷ perm (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ k1245 ∷ [])
  ∷ perm (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ k1245 ∷ [])
  ∷ perm (x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ k1245 ∷ [])
  ∷ [] ) refl

-- {a, b} = {1, 2}, Σ = true, t = true: after K_[0,1,2,3] the odd pair is {1, 2}, t = true.
cfg-12-t-t-N′ : List (Gen 6)
cfg-12-t-t-N′ = (k1245 ∷ m1 ∷ [])
cfg-12-t-t-V₁ : List (Gen 6)
cfg-12-t-t-V₁ = (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x34 ∷ [])
cfg-12-t-t-V₂ : List (Gen 6)
cfg-12-t-t-V₂ = (x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ [])
cfg-12-t-t-N : List (Gen 6)
cfg-12-t-t-N = (k1245 ∷ m1 ∷ [])

cfg-12-t-t : Eqn 6
cfg-12-t-t = derive (k1245 ∷ m1 ∷ k0123 ∷ []) (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m1 ∷ [])
  ( perm (k1245 ∷ m1 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1b-m1-m1)
  ∷ perm (k1245 ∷ m1 ∷ k0123 ∷ m1 ∷ m1 ∷ [])
  ∷ rw 4 (sym⁼ ax-1c-k1245-k1245)
  ∷ perm (k1245 ∷ m1 ∷ k0123 ∷ m1 ∷ k1245 ∷ k1245 ∷ m1 ∷ [])
  ∷ perm (k1245 ∷ m1 ∷ k0123 ∷ m1 ∷ k1245 ∷ k1245 ∷ m1 ∷ [])
  ∷ rw 0 g-12-t-t
  ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m1 ∷ [])
  ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m1 ∷ [])
  ∷ perm (x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x13 ∷ x15 ∷ x12 ∷ m2 ∷ m5 ∷ x12 ∷ x45 ∷ m1 ∷ m2 ∷ m4 ∷ m5 ∷ k1245 ∷ m1 ∷ [])
  ∷ [] ) refl

-- {a, b} = {1, 3}, Σ = false, t = false: after K_[0,1,2,3] the odd pair is {0, 1}, t = true.
cfg-13-f-f-N′ : List (Gen 6)
cfg-13-f-f-N′ = (k0145 ∷ m0 ∷ [])
cfg-13-f-f-V₁ : List (Gen 6)
cfg-13-f-f-V₁ = (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x02 ∷ x34 ∷ [])
cfg-13-f-f-V₂ : List (Gen 6)
cfg-13-f-f-V₂ = (x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ [])
cfg-13-f-f-N : List (Gen 6)
cfg-13-f-f-N = (k1345 ∷ [])

cfg-13-f-f : Eqn 6
cfg-13-f-f = derive (k0145 ∷ m0 ∷ k0123 ∷ []) (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ k1345 ∷ [])
  ( perm (k0145 ∷ m0 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k1345-k1345)
  ∷ perm (k0145 ∷ m0 ∷ k0123 ∷ k1345 ∷ k1345 ∷ [])
  ∷ perm (k0145 ∷ m0 ∷ k0123 ∷ k1345 ∷ k1345 ∷ [])
  ∷ rw 0 g-13-f-f
  ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ k1345 ∷ [])
  ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ k1345 ∷ [])
  ∷ perm (x01 ∷ x45 ∷ m0 ∷ m1 ∷ m4 ∷ m5 ∷ x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ k1345 ∷ [])
  ∷ [] ) refl

-- {a, b} = {1, 3}, Σ = false, t = true: after K_[0,1,2,3] the odd pair is {0, 1}, t = false.
cfg-13-f-t-N′ : List (Gen 6)
cfg-13-f-t-N′ = (k0145 ∷ [])
cfg-13-f-t-V₁ : List (Gen 6)
cfg-13-f-t-V₁ = (x01 ∷ x03 ∷ x02 ∷ x34 ∷ [])
cfg-13-f-t-V₂ : List (Gen 6)
cfg-13-f-t-V₂ = (x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
cfg-13-f-t-N : List (Gen 6)
cfg-13-f-t-N = (k1345 ∷ m1 ∷ [])

cfg-13-f-t : Eqn 6
cfg-13-f-t = derive (k0145 ∷ k0123 ∷ []) (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m1 ∷ [])
  ( perm (k0145 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1b-m1-m1)
  ∷ perm (k0145 ∷ k0123 ∷ m1 ∷ m1 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k1345-k1345)
  ∷ perm (k0145 ∷ k0123 ∷ m1 ∷ k1345 ∷ k1345 ∷ m1 ∷ [])
  ∷ perm (k0145 ∷ k0123 ∷ m1 ∷ k1345 ∷ k1345 ∷ m1 ∷ [])
  ∷ rw 0 g-13-f-t
  ∷ perm (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m1 ∷ [])
  ∷ perm (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m1 ∷ [])
  ∷ perm (x01 ∷ x03 ∷ x02 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m1 ∷ [])
  ∷ [] ) refl

-- {a, b} = {1, 3}, Σ = true, t = false: after K_[0,1,2,3] the odd pair is {2, 3}, t = false.
cfg-13-t-f-N′ : List (Gen 6)
cfg-13-t-f-N′ = (k2345 ∷ [])
cfg-13-t-f-V₁ : List (Gen 6)
cfg-13-t-f-V₁ = (x12 ∷ x34 ∷ [])
cfg-13-t-f-V₂ : List (Gen 6)
cfg-13-t-f-V₂ = (x34 ∷ x12 ∷ [])
cfg-13-t-f-N : List (Gen 6)
cfg-13-t-f-N = (k1345 ∷ [])

cfg-13-t-f : Eqn 6
cfg-13-t-f = derive (k2345 ∷ k0123 ∷ []) (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ k1345 ∷ [])
  ( perm (k2345 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1c-k1345-k1345)
  ∷ perm (k2345 ∷ k0123 ∷ k1345 ∷ k1345 ∷ [])
  ∷ perm (k2345 ∷ k0123 ∷ k1345 ∷ k1345 ∷ [])
  ∷ rw 0 skel-23-13-0
  ∷ perm (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ k1345 ∷ [])
  ∷ perm (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ k1345 ∷ [])
  ∷ perm (x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ k1345 ∷ [])
  ∷ [] ) refl

-- {a, b} = {1, 3}, Σ = true, t = true: after K_[0,1,2,3] the odd pair is {2, 3}, t = true.
cfg-13-t-t-N′ : List (Gen 6)
cfg-13-t-t-N′ = (k2345 ∷ m2 ∷ [])
cfg-13-t-t-V₁ : List (Gen 6)
cfg-13-t-t-V₁ = (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x34 ∷ [])
cfg-13-t-t-V₂ : List (Gen 6)
cfg-13-t-t-V₂ = (x34 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ [])
cfg-13-t-t-N : List (Gen 6)
cfg-13-t-t-N = (k1345 ∷ m1 ∷ [])

cfg-13-t-t : Eqn 6
cfg-13-t-t = derive (k2345 ∷ m2 ∷ k0123 ∷ []) (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m1 ∷ [])
  ( perm (k2345 ∷ m2 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1b-m1-m1)
  ∷ perm (k2345 ∷ m2 ∷ k0123 ∷ m1 ∷ m1 ∷ [])
  ∷ rw 4 (sym⁼ ax-1c-k1345-k1345)
  ∷ perm (k2345 ∷ m2 ∷ k0123 ∷ m1 ∷ k1345 ∷ k1345 ∷ m1 ∷ [])
  ∷ perm (k2345 ∷ m2 ∷ k0123 ∷ m1 ∷ k1345 ∷ k1345 ∷ m1 ∷ [])
  ∷ rw 0 g-13-t-t
  ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m1 ∷ [])
  ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m1 ∷ [])
  ∷ perm (x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ x12 ∷ x34 ∷ k0123 ∷ x34 ∷ x12 ∷ x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ k1345 ∷ m1 ∷ [])
  ∷ [] ) refl

-- {a, b} = {2, 3}, Σ = false, t = false: after K_[0,1,2,3] the odd pair is {0, 2}, t = true.
cfg-23-f-f-N′ : List (Gen 6)
cfg-23-f-f-N′ = (k0245 ∷ m0 ∷ [])
cfg-23-f-f-V₁ : List (Gen 6)
cfg-23-f-f-V₁ = (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x34 ∷ [])
cfg-23-f-f-V₂ : List (Gen 6)
cfg-23-f-f-V₂ = (x34 ∷ x25 ∷ x34 ∷ m1 ∷ [])
cfg-23-f-f-N : List (Gen 6)
cfg-23-f-f-N = (k2345 ∷ [])

cfg-23-f-f : Eqn 6
cfg-23-f-f = derive (k0245 ∷ m0 ∷ k0123 ∷ []) (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ k2345 ∷ [])
  ( perm (k0245 ∷ m0 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k2345-k2345)
  ∷ perm (k0245 ∷ m0 ∷ k0123 ∷ k2345 ∷ k2345 ∷ [])
  ∷ perm (k0245 ∷ m0 ∷ k0123 ∷ k2345 ∷ k2345 ∷ [])
  ∷ rw 0 g-23-f-f
  ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ k2345 ∷ [])
  ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ k2345 ∷ [])
  ∷ perm (x02 ∷ x45 ∷ m0 ∷ m2 ∷ m4 ∷ m5 ∷ x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ k2345 ∷ [])
  ∷ [] ) refl

-- {a, b} = {2, 3}, Σ = false, t = true: after K_[0,1,2,3] the odd pair is {0, 2}, t = false.
cfg-23-f-t-N′ : List (Gen 6)
cfg-23-f-t-N′ = (k0245 ∷ [])
cfg-23-f-t-V₁ : List (Gen 6)
cfg-23-f-t-V₁ = (x01 ∷ x23 ∷ x34 ∷ [])
cfg-23-f-t-V₂ : List (Gen 6)
cfg-23-f-t-V₂ = (x34 ∷ x25 ∷ x34 ∷ m1 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
cfg-23-f-t-N : List (Gen 6)
cfg-23-f-t-N = (k2345 ∷ m2 ∷ [])

cfg-23-f-t : Eqn 6
cfg-23-f-t = derive (k0245 ∷ k0123 ∷ []) (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m2 ∷ [])
  ( perm (k0245 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1b-m2-m2)
  ∷ perm (k0245 ∷ k0123 ∷ m2 ∷ m2 ∷ [])
  ∷ rw 3 (sym⁼ ax-1c-k2345-k2345)
  ∷ perm (k0245 ∷ k0123 ∷ m2 ∷ k2345 ∷ k2345 ∷ m2 ∷ [])
  ∷ perm (k0245 ∷ k0123 ∷ m2 ∷ k2345 ∷ k2345 ∷ m2 ∷ [])
  ∷ rw 0 g-23-f-t
  ∷ perm (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m2 ∷ [])
  ∷ perm (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m2 ∷ [])
  ∷ perm (x01 ∷ x23 ∷ x34 ∷ k0123 ∷ x34 ∷ x25 ∷ x34 ∷ m1 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m2 ∷ [])
  ∷ [] ) refl

-- {a, b} = {2, 3}, Σ = true, t = false: after K_[0,1,2,3] the odd pair is {1, 3}, t = false.
cfg-23-t-f-N′ : List (Gen 6)
cfg-23-t-f-N′ = (k1345 ∷ [])
cfg-23-t-f-V₁ : List (Gen 6)
cfg-23-t-f-V₁ = (x34 ∷ [])
cfg-23-t-f-V₂ : List (Gen 6)
cfg-23-t-f-V₂ = (x34 ∷ [])
cfg-23-t-f-N : List (Gen 6)
cfg-23-t-f-N = (k2345 ∷ [])

cfg-23-t-f : Eqn 6
cfg-23-t-f = derive (k1345 ∷ k0123 ∷ []) (x34 ∷ k0123 ∷ x34 ∷ k2345 ∷ [])
  ( perm (k1345 ∷ k0123 ∷ [])
  ∷ rw 2 (sym⁼ ax-1c-k2345-k2345)
  ∷ perm (k1345 ∷ k0123 ∷ k2345 ∷ k2345 ∷ [])
  ∷ perm (k1345 ∷ k0123 ∷ k2345 ∷ k2345 ∷ [])
  ∷ rw 0 core
  ∷ perm (x34 ∷ k0123 ∷ x34 ∷ k2345 ∷ [])
  ∷ perm (x34 ∷ k0123 ∷ x34 ∷ k2345 ∷ [])
  ∷ perm (x34 ∷ k0123 ∷ x34 ∷ k2345 ∷ [])
  ∷ [] ) refl

-- {a, b} = {2, 3}, Σ = true, t = true: after K_[0,1,2,3] the odd pair is {1, 3}, t = true.
cfg-23-t-t-N′ : List (Gen 6)
cfg-23-t-t-N′ = (k1345 ∷ m1 ∷ [])
cfg-23-t-t-V₁ : List (Gen 6)
cfg-23-t-t-V₁ = (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x34 ∷ [])
cfg-23-t-t-V₂ : List (Gen 6)
cfg-23-t-t-V₂ = (x34 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ [])
cfg-23-t-t-N : List (Gen 6)
cfg-23-t-t-N = (k2345 ∷ m2 ∷ [])

cfg-23-t-t : Eqn 6
cfg-23-t-t = derive (k1345 ∷ m1 ∷ k0123 ∷ []) (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m2 ∷ [])
  ( perm (k1345 ∷ m1 ∷ k0123 ∷ [])
  ∷ rw 3 (sym⁼ ax-1b-m2-m2)
  ∷ perm (k1345 ∷ m1 ∷ k0123 ∷ m2 ∷ m2 ∷ [])
  ∷ rw 4 (sym⁼ ax-1c-k2345-k2345)
  ∷ perm (k1345 ∷ m1 ∷ k0123 ∷ m2 ∷ k2345 ∷ k2345 ∷ m2 ∷ [])
  ∷ perm (k1345 ∷ m1 ∷ k0123 ∷ m2 ∷ k2345 ∷ k2345 ∷ m2 ∷ [])
  ∷ rw 0 g-23-t-t
  ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m2 ∷ [])
  ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m2 ∷ [])
  ∷ perm (x13 ∷ x45 ∷ m1 ∷ m3 ∷ m4 ∷ m5 ∷ x34 ∷ k0123 ∷ x34 ∷ x23 ∷ x45 ∷ m2 ∷ m3 ∷ m4 ∷ m5 ∷ k2345 ∷ m2 ∷ [])
  ∷ [] ) refl

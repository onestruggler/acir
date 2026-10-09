------------------------------------------------------------------------
-- Presentations of groups
--
-- Relations on eight indices a < b < c < d < e < f < g < h, written
-- 0 < … < 7, for the edge X_[d,e] when e is the fifth odd entry of the
-- pivot column (Lemma A.20, Subcase 1.2.2.3).  With
--
--   Y = K_[e,f,g,h] K_[a,b,c,d] X_[d,e] K_[a,b,c,d] K_[e,f,g,h],
--
-- relation (6a) says that S = (-1)_[a] (-1)_[e] X_[a,e] commutes with
-- Y, and the paper's derived variant (its Proposition A.16) says the
-- same of (-1)_[a] (-1)_[h] X_[a,h] (a16, following the paper's
-- derivation, where its step by (6a) is step6a).  Hence X_[d,e]
-- commutes with Z = K_[e,f,g,h] K_[a,b,c,d] S K_[e,f,g,h] K_[a,b,c,d]
-- for both (xz-e, xz-h), as Z X Z⁻¹ = K′ K S Y S⁻¹ K K′ = X.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Rel8 where

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
-- Letters and axioms

private
  f0 f1 f2 f3 f4 f5 f6 f7 : Fin 8
  f0 = zero
  f1 = (suc zero)
  f2 = (suc (suc zero))
  f3 = (suc (suc (suc zero)))
  f4 = (suc (suc (suc (suc zero))))
  f5 = (suc (suc (suc (suc (suc zero)))))
  f6 = (suc (suc (suc (suc (suc (suc zero))))))
  f7 = (suc (suc (suc (suc (suc (suc (suc zero)))))))
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
  lt06 : f0 < f6
  lt06 = s≤s z≤n
  lt07 : f0 < f7
  lt07 = s≤s z≤n
  lt12 : f1 < f2
  lt12 = s≤s (s≤s z≤n)
  lt13 : f1 < f3
  lt13 = s≤s (s≤s z≤n)
  lt14 : f1 < f4
  lt14 = s≤s (s≤s z≤n)
  lt15 : f1 < f5
  lt15 = s≤s (s≤s z≤n)
  lt16 : f1 < f6
  lt16 = s≤s (s≤s z≤n)
  lt17 : f1 < f7
  lt17 = s≤s (s≤s z≤n)
  lt23 : f2 < f3
  lt23 = s≤s (s≤s (s≤s z≤n))
  lt24 : f2 < f4
  lt24 = s≤s (s≤s (s≤s z≤n))
  lt25 : f2 < f5
  lt25 = s≤s (s≤s (s≤s z≤n))
  lt26 : f2 < f6
  lt26 = s≤s (s≤s (s≤s z≤n))
  lt27 : f2 < f7
  lt27 = s≤s (s≤s (s≤s z≤n))
  lt34 : f3 < f4
  lt34 = s≤s (s≤s (s≤s (s≤s z≤n)))
  lt35 : f3 < f5
  lt35 = s≤s (s≤s (s≤s (s≤s z≤n)))
  lt36 : f3 < f6
  lt36 = s≤s (s≤s (s≤s (s≤s z≤n)))
  lt37 : f3 < f7
  lt37 = s≤s (s≤s (s≤s (s≤s z≤n)))
  lt45 : f4 < f5
  lt45 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  lt46 : f4 < f6
  lt46 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  lt47 : f4 < f7
  lt47 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
  lt56 : f5 < f6
  lt56 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
  lt57 : f5 < f7
  lt57 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))
  lt67 : f6 < f7
  lt67 = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
  k0123 : Gen 8
  k0123 = K-gen f0 f1 f2 f3 lt01 lt12 lt23
  k0124 : Gen 8
  k0124 = K-gen f0 f1 f2 f4 lt01 lt12 lt24
  k3567 : Gen 8
  k3567 = K-gen f3 f5 f6 f7 lt35 lt56 lt67
  k4567 : Gen 8
  k4567 = K-gen f4 f5 f6 f7 lt45 lt56 lt67
  m0 : Gen 8
  m0 = M-gen f0
  m3 : Gen 8
  m3 = M-gen f3
  m4 : Gen 8
  m4 = M-gen f4
  m5 : Gen 8
  m5 = M-gen f5
  m6 : Gen 8
  m6 = M-gen f6
  m7 : Gen 8
  m7 = M-gen f7
  x03 : Gen 8
  x03 = X-gen f0 f3 lt03
  x04 : Gen 8
  x04 = X-gen f0 f4 lt04
  x07 : Gen 8
  x07 = X-gen f0 f7 lt07
  x34 : Gen 8
  x34 = X-gen f3 f4 lt34
  x37 : Gen 8
  x37 = X-gen f3 f7 lt37
  x47 : Gen 8
  x47 = X-gen f4 f7 lt47
  x56 : Gen 8
  x56 = X-gen f5 f6 lt56
  x57 : Gen 8
  x57 = X-gen f5 f7 lt57
  x67 : Gen 8
  x67 = X-gen f6 f7 lt67
  e3567 : Emb 4 8
  e3567 = emb (f3 ∷ᵛ f5 ∷ᵛ f6 ∷ᵛ f7 ∷ᵛ []ᵛ) (lt35 ∷ᵢ lt56 ∷ᵢ lt67 ∷ᵢ [ f7 ]ᵢ)
  e4567 : Emb 4 8
  e4567 = emb (f4 ∷ᵛ f5 ∷ᵛ f6 ∷ᵛ f7 ∷ᵛ []ᵛ) (lt45 ∷ᵢ lt56 ∷ᵢ lt67 ∷ᵢ [ f7 ]ᵢ)

  ax-1a-x04-x04 : Eqn 8
  ax-1a-x04-x04 = ax⁼ (x04 ∷ x04 ∷ []) ([]) (r1a lt04)
  ax-1a-x34-x34 : Eqn 8
  ax-1a-x34-x34 = ax⁼ (x34 ∷ x34 ∷ []) ([]) (r1a lt34)
  ax-1a-x47-x47 : Eqn 8
  ax-1a-x47-x47 = ax⁼ (x47 ∷ x47 ∷ []) ([]) (r1a lt47)
  ax-1a-x56-x56 : Eqn 8
  ax-1a-x56-x56 = ax⁼ (x56 ∷ x56 ∷ []) ([]) (r1a lt56)
  ax-1a-x67-x67 : Eqn 8
  ax-1a-x67-x67 = ax⁼ (x67 ∷ x67 ∷ []) ([]) (r1a lt67)
  ax-1b-m0-m0 : Eqn 8
  ax-1b-m0-m0 = ax⁼ (m0 ∷ m0 ∷ []) ([]) (r1b)
  ax-1b-m4-m4 : Eqn 8
  ax-1b-m4-m4 = ax⁼ (m4 ∷ m4 ∷ []) ([]) (r1b)
  ax-1c-k0123-k0123 : Eqn 8
  ax-1c-k0123-k0123 = ax⁼ (k0123 ∷ k0123 ∷ []) ([]) (r1c lt01 lt12 lt23)
  ax-1c-k4567-k4567 : Eqn 8
  ax-1c-k4567-k4567 = ax⁼ (k4567 ∷ k4567 ∷ []) ([]) (r1c lt45 lt56 lt67)
  ax-3a-x56-x57 : Eqn 8
  ax-3a-x56-x57 = ax⁼ (x56 ∷ x57 ∷ []) (x67 ∷ x56 ∷ []) (r3a lt56 lt67 lt57)
  ax-3b-x34-x03 : Eqn 8
  ax-3b-x34-x03 = ax⁼ (x34 ∷ x03 ∷ []) (x04 ∷ x34 ∷ []) (r3b lt03 lt34 lt04)
  ax-3b-x37-x03 : Eqn 8
  ax-3b-x37-x03 = ax⁼ (x37 ∷ x03 ∷ []) (x07 ∷ x37 ∷ []) (r3b lt03 lt37 lt07)
  ax-3b-x47-x04 : Eqn 8
  ax-3b-x47-x04 = ax⁼ (x47 ∷ x04 ∷ []) (x07 ∷ x47 ∷ []) (r3b lt04 lt47 lt07)
  ax-3b-x67-x56 : Eqn 8
  ax-3b-x67-x56 = ax⁼ (x67 ∷ x56 ∷ []) (x57 ∷ x67 ∷ []) (r3b lt56 lt67 lt57)
  ax-3c-x03-m3 : Eqn 8
  ax-3c-x03-m3 = ax⁼ (x03 ∷ m3 ∷ []) (m0 ∷ x03 ∷ []) (r3c lt03)
  ax-3c-x04-m4 : Eqn 8
  ax-3c-x04-m4 = ax⁼ (x04 ∷ m4 ∷ []) (m0 ∷ x04 ∷ []) (r3c lt04)
  ax-3c-x07-m7 : Eqn 8
  ax-3c-x07-m7 = ax⁼ (x07 ∷ m7 ∷ []) (m0 ∷ x07 ∷ []) (r3c lt07)
  ax-3c-x34-m4 : Eqn 8
  ax-3c-x34-m4 = ax⁼ (x34 ∷ m4 ∷ []) (m3 ∷ x34 ∷ []) (r3c lt34)
  ax-3c-x37-m7 : Eqn 8
  ax-3c-x37-m7 = ax⁼ (x37 ∷ m7 ∷ []) (m3 ∷ x37 ∷ []) (r3c lt37)
  ax-3c-x47-m7 : Eqn 8
  ax-3c-x47-m7 = ax⁼ (x47 ∷ m7 ∷ []) (m4 ∷ x47 ∷ []) (r3c lt47)
  ax-3d-x34-k3567 : Eqn 8
  ax-3d-x34-k3567 = ax⁼ (x34 ∷ k3567 ∷ []) (k4567 ∷ x34 ∷ []) (r3d lt34 lt45 lt56 lt67 lt35)
  ax-3g-x34-k0123 : Eqn 8
  ax-3g-x34-k0123 = ax⁼ (x34 ∷ k0123 ∷ []) (k0124 ∷ x34 ∷ []) (r3g lt01 lt12 lt23 lt34 lt24)
  ax-6a-m0-m4-x04-k4567-k0123-x34-k0123-k4567-x04-m0-m4 : Eqn 8
  ax-6a-m0-m4-x04-k4567-k0123-x34-k0123-k4567-x04-m0-m4 = ax⁼ (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x04 ∷ m0 ∷ m4 ∷ []) (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ []) (r6a lt01 lt12 lt23 lt34 lt45 lt56 lt67 lt04)

------------------------------------------------------------------------
-- Intermediate relations

private

  y-def : Eqn 8
  y-def = derive (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ []) (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ [])
    ( perm (k4567 ∷ k0123 ∷ x34 ∷ k4567 ∷ k0123 ∷ [])
    ∷ rw 2 (sym⁼ (rev⁼ ax-3d-x34-k3567))
    ∷ perm (k4567 ∷ k0123 ∷ k3567 ∷ x34 ∷ k0123 ∷ [])
    ∷ rw 3 ax-3g-x34-k0123
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ [])
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ [])
    ∷ [] ) refl

  sy-e : Eqn 8
  sy-e = derive (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ []) (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ [])
    ( perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ [])
    ∷ rw 8 (sym⁼ ax-1a-x04-x04)
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x04 ∷ x04 ∷ [])
    ∷ rw 9 (sym⁼ ax-1b-m0-m0)
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x04 ∷ m0 ∷ m0 ∷ x04 ∷ [])
    ∷ rw 11 (sym⁼ ax-1b-m4-m4)
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x04 ∷ m0 ∷ m4 ∷ m0 ∷ m4 ∷ x04 ∷ [])
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x04 ∷ m0 ∷ m4 ∷ m0 ∷ m4 ∷ x04 ∷ [])
    ∷ rw 0 ax-6a-m0-m4-x04-k4567-k0123-x34-k0123-k4567-x04-m0-m4
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ [])
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ [])
    ∷ [] ) refl

  step6a : Eqn 8
  step6a = derive (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x03 ∷ m0 ∷ m3 ∷ []) (x04 ∷ m0 ∷ m4 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ( perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x03 ∷ m0 ∷ m3 ∷ [])
    ∷ rw 4 (sym⁼ ax-1a-x34-x34)
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ x34 ∷ x03 ∷ m0 ∷ m3 ∷ [])
    ∷ rw 5 ax-3b-x34-x03
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ x04 ∷ m0 ∷ x34 ∷ m3 ∷ [])
    ∷ rw 7 (sym⁼ (rev⁼ ax-3c-x34-m4))
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ x04 ∷ m0 ∷ m4 ∷ x34 ∷ [])
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ x04 ∷ m0 ∷ m4 ∷ x34 ∷ [])
    ∷ rw 0 (sym⁼ y-def)
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x04 ∷ m0 ∷ m4 ∷ x34 ∷ [])
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x04 ∷ m0 ∷ m4 ∷ x34 ∷ [])
    ∷ rw 5 (sym⁼ (rev⁼ ax-3c-x04-m4))
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m4 ∷ x04 ∷ m4 ∷ x34 ∷ [])
    ∷ rw 6 ax-3c-x04-m4
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ x34 ∷ [])
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ x34 ∷ [])
    ∷ rw 0 (sym⁼ sy-e)
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x34 ∷ [])
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ x34 ∷ [])
    ∷ rw 3 y-def
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ x34 ∷ [])
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ x34 ∷ [])
    ∷ rw 7 ax-1a-x34-x34
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ perm (m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ rw 1 (rev⁼ ax-3c-x04-m4)
    ∷ perm (m0 ∷ x04 ∷ m0 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ rw 0 (sym⁼ ax-3c-x04-m4)
    ∷ perm (x04 ∷ m0 ∷ m4 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ perm (x04 ∷ m0 ∷ m4 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ [] ) refl

  a16 : Eqn 8
  a16 = derive (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ []) (x07 ∷ m0 ∷ m7 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ( perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ rw 0 (sym⁼ ax-1a-x47-x47)
    ∷ perm (x47 ∷ x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ perm (x47 ∷ x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ rw 1 (emb⁼ e4567 R4.r8b)
    ∷ perm (x47 ∷ k4567 ∷ x57 ∷ x67 ∷ x57 ∷ m5 ∷ m6 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ x57 ∷ x67 ∷ x57 ∷ m5 ∷ m6 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ x57 ∷ x67 ∷ x57 ∷ m5 ∷ m6 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ rw 4 (sym⁼ ax-3b-x67-x56)
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ x67 ∷ x56 ∷ x57 ∷ m5 ∷ m6 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ rw 5 ax-3a-x56-x57
    ∷ perm (x47 ∷ k4567 ∷ x67 ∷ x67 ∷ k0123 ∷ k0124 ∷ x56 ∷ m5 ∷ m6 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ rw 2 ax-1a-x67-x67
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ x56 ∷ m5 ∷ m6 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ x56 ∷ m5 ∷ m6 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ rw 5 (emb⁼ e3567 R4.r9d)
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ x56 ∷ k3567 ∷ x37 ∷ x56 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ rw 4 (emb⁼ e3567 R4.r8c)
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x56 ∷ x56 ∷ x37 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ rw 5 ax-1a-x56-x56
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x37 ∷ x07 ∷ m0 ∷ m7 ∷ [])
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x37 ∷ x07 ∷ m7 ∷ m0 ∷ [])
    ∷ rw 6 ax-3c-x07-m7
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x37 ∷ m0 ∷ x07 ∷ m0 ∷ [])
    ∷ rw 7 (sym⁼ (rev⁼ ax-3c-x07-m7))
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ m0 ∷ x37 ∷ m7 ∷ x07 ∷ [])
    ∷ rw 6 ax-3c-x37-m7
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ m0 ∷ m3 ∷ x37 ∷ x07 ∷ [])
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ m0 ∷ m3 ∷ x37 ∷ x07 ∷ [])
    ∷ rw 7 (sym⁼ (rev⁼ ax-3b-x37-x03))
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ m3 ∷ m0 ∷ x03 ∷ x37 ∷ [])
    ∷ rw 6 (sym⁼ ax-3c-x03-m3)
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ m3 ∷ x03 ∷ m3 ∷ x37 ∷ [])
    ∷ rw 5 (rev⁼ ax-3c-x03-m3)
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x03 ∷ m0 ∷ m3 ∷ x37 ∷ [])
    ∷ perm (x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x03 ∷ m0 ∷ m3 ∷ x37 ∷ [])
    ∷ rw 1 step6a
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x37 ∷ [])
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x37 ∷ [])
    ∷ rw 8 (sym⁼ ax-1a-x56-x56)
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x37 ∷ x56 ∷ x56 ∷ [])
    ∷ rw 7 (sym⁼ (emb⁼ e3567 R4.r9d))
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ k4567 ∷ k0123 ∷ k0124 ∷ m5 ∷ m6 ∷ k3567 ∷ x56 ∷ [])
    ∷ rw 9 (sym⁼ (emb⁼ e3567 R4.r8c))
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ k4567 ∷ k0123 ∷ k0124 ∷ m5 ∷ m6 ∷ x56 ∷ k3567 ∷ [])
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ k4567 ∷ m5 ∷ m6 ∷ x56 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ k4567 ∷ m6 ∷ m5 ∷ x56 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ rw 4 (rev⁼ (emb⁼ e4567 R4.r9d))
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ x47 ∷ x56 ∷ k4567 ∷ x56 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ rw 5 (emb⁼ e4567 R4.r8c)
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ x47 ∷ k4567 ∷ x56 ∷ x56 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ rw 6 ax-1a-x56-x56
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ perm (x47 ∷ x04 ∷ m0 ∷ m4 ∷ x47 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ rw 3 (sym⁼ ax-3c-x47-m7)
    ∷ perm (x47 ∷ x04 ∷ x47 ∷ m0 ∷ m7 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ perm (x47 ∷ x04 ∷ x47 ∷ m0 ∷ m7 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ rw 1 (rev⁼ ax-3b-x47-x04)
    ∷ perm (x47 ∷ x47 ∷ x07 ∷ m0 ∷ m7 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ rw 0 ax-1a-x47-x47
    ∷ perm (x07 ∷ m0 ∷ m7 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ perm (x07 ∷ m0 ∷ m7 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ [])
    ∷ [] ) refl

  sy-h : Eqn 8
  sy-h = derive (m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ []) (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m7 ∷ x07 ∷ [])
    ( perm (m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ [])
    ∷ rw 3 y-def
    ∷ perm (m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ [])
    ∷ perm (m7 ∷ m0 ∷ x07 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ [])
    ∷ rw 1 (sym⁼ ax-3c-x07-m7)
    ∷ perm (m7 ∷ x07 ∷ m7 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ [])
    ∷ rw 0 (rev⁼ ax-3c-x07-m7)
    ∷ perm (x07 ∷ m0 ∷ m7 ∷ k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ [])
    ∷ rw 0 (sym⁼ a16)
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x07 ∷ m0 ∷ m7 ∷ x34 ∷ [])
    ∷ rw 4 (sym⁼ (rev⁼ ax-3c-x07-m7))
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ m7 ∷ x07 ∷ m7 ∷ x34 ∷ [])
    ∷ rw 5 ax-3c-x07-m7
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ m0 ∷ m7 ∷ x07 ∷ x34 ∷ [])
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ m0 ∷ m7 ∷ x07 ∷ [])
    ∷ perm (k4567 ∷ k0123 ∷ k0124 ∷ k3567 ∷ x34 ∷ m0 ∷ m7 ∷ x07 ∷ [])
    ∷ rw 0 (sym⁼ y-def)
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m7 ∷ x07 ∷ [])
    ∷ perm (k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m7 ∷ x07 ∷ [])
    ∷ [] ) refl

------------------------------------------------------------------------
-- The relations

-- X_[d,e] Z = Z X_[d,e] for S = (-1)_[a] (-1)_[e] X_[a,e].
xz-e : Eqn 8
xz-e = derive (k4567 ∷ k0123 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ []) (x34 ∷ k4567 ∷ k0123 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ [])
  ( perm (k4567 ∷ k0123 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ [])
  ∷ rw 8 (sym⁼ ax-1c-k4567-k4567)
  ∷ perm (k4567 ∷ k0123 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k4567 ∷ k4567 ∷ [])
  ∷ rw 10 (sym⁼ ax-1c-k0123-k0123)
  ∷ perm (k4567 ∷ k0123 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ k4567 ∷ k0123 ∷ [])
  ∷ perm (k4567 ∷ k0123 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ k4567 ∷ k0123 ∷ [])
  ∷ rw 2 sy-e
  ∷ perm (k4567 ∷ k0123 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ [])
  ∷ perm (k0123 ∷ k4567 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ [])
  ∷ rw 1 ax-1c-k4567-k4567
  ∷ perm (k0123 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ [])
  ∷ rw 0 ax-1c-k0123-k0123
  ∷ perm (x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ [])
  ∷ perm (x34 ∷ k4567 ∷ k0123 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ [])
  ∷ perm (x34 ∷ k4567 ∷ k0123 ∷ m0 ∷ m4 ∷ x04 ∷ k4567 ∷ k0123 ∷ [])
  ∷ [] ) refl

-- X_[d,e] Z = Z X_[d,e] for S = (-1)_[a] (-1)_[h] X_[a,h].
xz-h : Eqn 8
xz-h = derive (k4567 ∷ k0123 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ x34 ∷ []) (x34 ∷ k4567 ∷ k0123 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ [])
  ( perm (k4567 ∷ k0123 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ x34 ∷ [])
  ∷ rw 8 (sym⁼ ax-1c-k4567-k4567)
  ∷ perm (k4567 ∷ k0123 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ x34 ∷ k4567 ∷ k4567 ∷ [])
  ∷ rw 10 (sym⁼ ax-1c-k0123-k0123)
  ∷ perm (k4567 ∷ k0123 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ k4567 ∷ k0123 ∷ [])
  ∷ perm (k4567 ∷ k0123 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ k4567 ∷ k0123 ∷ [])
  ∷ rw 2 sy-h
  ∷ perm (k4567 ∷ k0123 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ [])
  ∷ perm (k0123 ∷ k4567 ∷ k4567 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ [])
  ∷ rw 1 ax-1c-k4567-k4567
  ∷ perm (k0123 ∷ k0123 ∷ x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ [])
  ∷ rw 0 ax-1c-k0123-k0123
  ∷ perm (x34 ∷ k0123 ∷ k4567 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ [])
  ∷ perm (x34 ∷ k4567 ∷ k0123 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ [])
  ∷ perm (x34 ∷ k4567 ∷ k0123 ∷ m0 ∷ m7 ∷ x07 ∷ k4567 ∷ k0123 ∷ [])
  ∷ [] ) refl

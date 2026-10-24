{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The statements of the lemmas the derivation modules of Five/D take
--
-- As a balanced tree (`lemmas`, `St n` the n-th), WinSig's.  In a
-- module of its own: the positivity checker of a module walks every
-- definition in it; and its subtrees in modules of their own
-- (DStmt/P0, ...), checked side by side.  Written by
-- `scratchpad/four/di.py`.
------------------------------------------------------------------------

module Examples.Groups.Clifford+CS.Five.DStmt where

open import Data.List.Base using ([] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WTree ; wleaf ; wnode ; WinT)
open import Examples.Groups.Clifford+CS.Five.Letters
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)
import Examples.Groups.Clifford+CS.Five.DStmt.P0 as P0
import Examples.Groups.Clifford+CS.Five.DStmt.P1 as P1
import Examples.Groups.Clifford+CS.Five.DStmt.P2 as P2
import Examples.Groups.Clifford+CS.Five.DStmt.P3 as P3
import Examples.Groups.Clifford+CS.Five.DStmt.P4 as P4
import Examples.Groups.Clifford+CS.Five.DStmt.P5 as P5
import Examples.Groups.Clifford+CS.Five.DStmt.P6 as P6
import Examples.Groups.Clifford+CS.Five.DStmt.P7 as P7

lemmas : WTree
lemmas = (wnode (wnode (wnode P0.t (ℓ "乒亜") (ℓ "亜乒") P1.t) (ℓ "乁交") (ℓ "交乁") (wnode P2.t (ℓ "也亠") (ℓ "亠也") P3.t)) (ℓ "丳京") (ℓ "京丳") (wnode (wnode P4.t (ℓ "乙亘") (ℓ "亘乙") P5.t) (ℓ "之亠") (ℓ "亠之") (wnode P6.t (ℓ "书五") (ℓ "五书") P7.t)))

St : ℕ → Set
St n = WinT lemmas n

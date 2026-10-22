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
import Examples.Groups.Clifford+CS.Five.DStmt.P0 as P0
import Examples.Groups.Clifford+CS.Five.DStmt.P1 as P1
import Examples.Groups.Clifford+CS.Five.DStmt.P2 as P2
import Examples.Groups.Clifford+CS.Five.DStmt.P3 as P3
import Examples.Groups.Clifford+CS.Five.DStmt.P4 as P4
import Examples.Groups.Clifford+CS.Five.DStmt.P5 as P5
import Examples.Groups.Clifford+CS.Five.DStmt.P6 as P6
import Examples.Groups.Clifford+CS.Five.DStmt.P7 as P7

lemmas : WTree
lemmas = (wnode (wnode (wnode P0.t (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) P1.t) (CX04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX04 ∷ []) (wnode P2.t (CX21 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX21 ∷ []) P3.t)) (CX02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX02 ∷ []) (wnode (wnode P4.t (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ []) P5.t) (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (wnode P6.t (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) P7.t)))

St : ℕ → Set
St n = WinT lemmas n

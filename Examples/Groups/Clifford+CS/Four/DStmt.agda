{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The statements of the lemmas the derivation modules of Four/D take
--
-- As a balanced tree (`lemmas`, `St n` the n-th), WinSig's.  In a
-- module of its own: the positivity checker of a module walks every
-- definition in it; and its subtrees in modules of their own
-- (DStmt/P0, ...), checked side by side.  Written by
-- `scratchpad/four/di.py`.
------------------------------------------------------------------------

module Examples.Groups.Clifford+CS.Four.DStmt where

open import Data.List.Base using ([] ; _∷_)
open import Data.Nat.Base using (ℕ)
open import Examples.Groups.Clifford+CS.Four.WinSig using (Tree ; leaf ; node ; Win)
open import Examples.Groups.Clifford+CS.Four.Letters
import Examples.Groups.Clifford+CS.Four.DStmt.P0 as P0
import Examples.Groups.Clifford+CS.Four.DStmt.P1 as P1
import Examples.Groups.Clifford+CS.Four.DStmt.P2 as P2
import Examples.Groups.Clifford+CS.Four.DStmt.P3 as P3
import Examples.Groups.Clifford+CS.Four.DStmt.P4 as P4
import Examples.Groups.Clifford+CS.Four.DStmt.P5 as P5
import Examples.Groups.Clifford+CS.Four.DStmt.P6 as P6
import Examples.Groups.Clifford+CS.Four.DStmt.P7 as P7

lemmas : Tree
lemmas = (node (node (node P0.t (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) P1.t) (CCZ123 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ []) (node P2.t (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) P3.t)) (CCZ023 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) (node (node P4.t (CX23 ∷ Toff012 ∷ CX23 ∷ []) (Toff012 ∷ []) P5.t) (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) (node P6.t (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) P7.t)))

St : ℕ → Set
St n = Win lemmas n

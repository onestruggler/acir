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
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)
import Examples.Groups.Clifford+CS.Four.DStmt.P0 as P0
import Examples.Groups.Clifford+CS.Four.DStmt.P1 as P1
import Examples.Groups.Clifford+CS.Four.DStmt.P2 as P2
import Examples.Groups.Clifford+CS.Four.DStmt.P3 as P3
import Examples.Groups.Clifford+CS.Four.DStmt.P4 as P4
import Examples.Groups.Clifford+CS.Four.DStmt.P5 as P5
import Examples.Groups.Clifford+CS.Four.DStmt.P6 as P6
import Examples.Groups.Clifford+CS.Four.DStmt.P7 as P7

lemmas : Tree
lemmas = (node (node (node P0.t (ℓ "丽九") (ℓ "九丽") P1.t) (ℓ "乜乐") (ℓ "乐乜") (node P2.t (ℓ "乙乚") (ℓ "乚乙") P3.t)) (ℓ "乛九") (ℓ "九乛乜") (node (node P4.t (ℓ "乌九乌") (ℓ "九") P5.t) (ℓ "乜乙") (ℓ "乙乜") (node P6.t (ℓ "丶九") (ℓ "九丶") P7.t)))

St : ℕ → Set
St n = Win lemmas n

{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The windows of Four/D as equations
--
-- The n-th statement of a tree of statements (WinSig's) with its proof,
-- as the equation the derivation engine rewrites with, its lists read
-- off the tree alone (not off the proof, which is a variable where it
-- is used): so a table entry of a derivation module need not spell
-- the lists of its window or lemma, which was half of what a module
-- cost besides loading.  Written by `scratchpad/four/di.py`.
------------------------------------------------------------------------

module Examples.Groups.Clifford+CS.Four.DEqn where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.List.Base using ([] ; _∷_)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _/_ ; _%_ ; _≡ᵇ_)

open import Examples.Groups.Clifford+CS.Four.Chain using (refl)
open import Examples.Groups.Clifford+CS.Four.WinSig using (Tree ; leaf ; node ; Win ; Ws ; windows ; wn)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn)

getE : (t : Tree) (n : ℕ) → Win t n → Eqn
getE leaf           n       _ = eqn [] [] refl
getE (node a l r b) zero    p = eqn l r p
getE (node a l r b) (suc n) p = sel (n % 2 ≡ᵇ 0) p
  where
  sel : (c : Bool) → (if c then Win a (n / 2) else Win b (n / 2)) → Eqn
  sel true  q = getE a (n / 2) q
  sel false q = getE b (n / 2) q

wE : ℕ → Ws → Eqn
wE n W = getE windows n (wn n W)

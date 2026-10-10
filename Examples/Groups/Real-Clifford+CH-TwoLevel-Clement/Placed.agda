------------------------------------------------------------------------
-- Presentations of groups
--
-- The words of letters and routes on local indices placed by
-- ι : Fin m → Fin n: H i j is Hs (ι i) (ι j), X i j is Xs (ι i) (ι j),
-- Z i is Z (ι i), and a route (applied head first) is the product of
-- its letters, the last on the left.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (Fin)

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Placed {n m : ℕ} (ι : Fin m → Fin n) where

open import Data.List.Base using (List ; [] ; _∷_)

open import Word.Base
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen) renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (Hs ; Xs)
open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Check using (Let ; Hˡ ; Xˡ ; Zˡ ; Route)

wordL : Let m → Word (Gen n)
wordL (Hˡ i j) = Hs (ι i) (ι j)
wordL (Xˡ i j) = Xs (ι i) (ι j)
wordL (Zˡ i) = Zʷ (ι i)

wordR : Route m → Word (Gen n)
wordR [] = ε
wordR (g ∷ gs) = wordR gs • wordL g

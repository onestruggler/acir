{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01199 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine

open import Data.Fin.Base using (zero ; suc)

proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
proved = checked (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s2 • s1) (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  (λ { (zero) → Eq.refl ; (suc (zero)) → Eq.refl ; (suc (suc (zero))) → Eq.refl ; (suc (suc (suc (zero)))) → Eq.refl ; (suc (suc (suc (suc (zero))))) → Eq.refl ; (suc (suc (suc (suc (suc (zero)))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (zero))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (zero)))))))) → Eq.refl ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })

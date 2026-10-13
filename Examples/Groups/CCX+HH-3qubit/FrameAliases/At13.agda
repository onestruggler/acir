{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At13 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00956 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t13 ≈ p (s1 • s2 • s1)
step0 = by-assoc-and (cong (GP.gatet12) (cong (GP.gatet23) (GP.gatet12))) Eq.refl Eq.refl

proved : t13 ≈ X13
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

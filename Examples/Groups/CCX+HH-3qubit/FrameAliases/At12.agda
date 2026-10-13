{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At12 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00002 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t12 ≈ p (s1)
step0 = by-assoc-and (GP.gatet12) Eq.refl Eq.refl

proved : t12 ≈ X12
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

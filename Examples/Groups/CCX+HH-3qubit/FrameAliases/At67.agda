{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At67 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00007 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t67 ≈ p (s6)
step0 = by-assoc-and (GP.gatet67) Eq.refl Eq.refl

proved : t67 ≈ X67
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At01 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00000 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t01 ≈ p (s0)
step0 = by-assoc-and (GP.gatet01) Eq.refl Eq.refl

proved : t01 ≈ X01
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At45 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00005 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t45 ≈ p (s4)
step0 = by-assoc-and (GP.gatet45) Eq.refl Eq.refl

proved : t45 ≈ X45
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

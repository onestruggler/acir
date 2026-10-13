{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At04 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00955 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t04 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
step0 = by-assoc-and (cong (GP.gatet01) (cong (GP.gatet12) (cong (GP.gatet23) (cong (GP.gatet34) (cong (GP.gatet23) (cong (GP.gatet12) (GP.gatet01))))))) Eq.refl Eq.refl

proved : t04 ≈ X04
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

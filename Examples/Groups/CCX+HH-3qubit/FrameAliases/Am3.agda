{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Am3 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00630 as Move
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00948 as R
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00949 as Inv
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : m3 ≈ p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2)
step0 = by-assoc-and (cong (cong (GP.gatet23) (cong (GP.gatet12) (GP.gatet01))) (cong (refl {w = m0}) (cong (GP.gatet01) (cong (GP.gatet12) (GP.gatet23))))) Eq.refl Eq.refl

step1 : p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2) ≈ p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2)
step1 = cong refl (cong refl R.proved)

step2 : p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2) ≈ M3
step2 = forget-frame (by-assoc-and Move.proved Eq.refl Eq.refl) (by-assoc-and Inv.proved Eq.refl Eq.refl)

proved : m3 ≈ M3
proved = trans step0 (trans step1 step2)

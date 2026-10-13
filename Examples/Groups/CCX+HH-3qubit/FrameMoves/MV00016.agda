{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00016 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00018 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00018 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00002 as C

step0 : p (s2) • M2 ≈ p (s0 • s1 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s0)
step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s0 • s1 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s0)
step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s0)) C.proved) Eq.refl Eq.refl

step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s0) ≈ M3 • p (s2)
step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s2) • M2 ≈ M3 • p (s2)
proved = trans step0 (trans step1 step2)

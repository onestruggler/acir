{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00007 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00008 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00000 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00000 as C

step0 : p (s0) • M1 ≈ p (ε) • p (ε) • m0 • p (s0)
step0 = by-assoc-and (under (ε) (m0 • p (s0)) E1.proved) Eq.refl Eq.refl

step1 : p (ε) • p (ε) • m0 • p (s0) ≈ p (ε) • m0 • p (ε) • p (s0)
step1 = by-assoc-and (under (p (ε)) (p (s0)) C.proved) Eq.refl Eq.refl

step2 : p (ε) • m0 • p (ε) • p (s0) ≈ M0 • p (s0)
step2 = by-assoc-and (under (p (ε) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s0) • M1 ≈ M0 • p (s0)
proved = trans step0 (trans step1 step2)

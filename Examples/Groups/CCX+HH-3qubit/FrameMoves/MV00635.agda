{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00635 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00983 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00983 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00000 as C

step0 : p (ε) • M0 ≈ p (ε) • p (ε) • m0 • p (ε)
step0 = by-assoc-and (under (ε) (m0 • p (ε)) E1.proved) Eq.refl Eq.refl

step1 : p (ε) • p (ε) • m0 • p (ε) ≈ p (ε) • m0 • p (ε) • p (ε)
step1 = by-assoc-and (under (p (ε)) (p (ε)) C.proved) Eq.refl Eq.refl

step2 : p (ε) • m0 • p (ε) • p (ε) ≈ M0 • p (ε)
step2 = by-assoc-and (under (p (ε) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (ε) • M0 ≈ M0 • p (ε)
proved = trans step0 (trans step1 step2)

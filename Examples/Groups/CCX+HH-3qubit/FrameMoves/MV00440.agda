{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00440 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00568 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00569 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00012 as C

step0 : p (s0) • K0567 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) E1.proved) Eq.refl Eq.refl

step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) C.proved) Eq.refl Eq.refl

step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ K1567 • p (s0)
step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s0) • K0567 ≈ K1567 • p (s0)
proved = trans step0 (trans step1 step2)

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00612 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00912 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00913 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00013 as C

step0 : p (s1) • K3457 ≈ p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)) C.proved) Eq.refl Eq.refl

step2 : p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0) ≈ K3457 • p (s1)
step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s1) • K3457 ≈ K3457 • p (s1)
proved = trans step0 (trans step1 step2)

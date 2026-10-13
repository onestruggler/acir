{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00450 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00588 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00589 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00013 as C

step0 : p (s3) • K1235 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1 • s0)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1 • s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1 • s0)
step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1 • s0)) C.proved) Eq.refl Eq.refl

step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ K1245 • p (s3)
step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s3) • K1235 ≈ K1245 • p (s3)
proved = trans step0 (trans step1 step2)

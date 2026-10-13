{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00287 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00262 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00263 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00012 as C

step0 : p (s2) • K0137 ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) E1.proved) Eq.refl Eq.refl

step1 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
step1 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) C.proved) Eq.refl Eq.refl

step2 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ K0127 • p (s2)
step2 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s2) • K0137 ≈ K0127 • p (s2)
proved = trans step0 (trans step1 step2)

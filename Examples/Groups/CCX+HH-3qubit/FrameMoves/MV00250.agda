{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00250 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Frames
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00213 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00004 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00012 as C

step0 : p (s3) • K0124 ≈ p (ε) • p (ε) • NK • p (s3)
step0 = by-assoc-and (under (ε) (NK • p (s3)) E1.proved) Eq.refl Eq.refl

step1 : p (ε) • p (ε) • NK • p (s3) ≈ p (ε) • NK • p (ε) • p (s3)
step1 = by-assoc-and (under (p (ε)) (p (s3)) C.proved) Eq.refl Eq.refl

step2 : p (ε) • NK • p (ε) • p (s3) ≈ K0123 • p (s3)
step2 = by-assoc-and (under (p (ε) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s3) • K0124 ≈ K0123 • p (s3)
proved = trans step0 (trans step1 step2)

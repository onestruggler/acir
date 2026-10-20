{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV03034 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0124 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00004 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00004 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00012 as C

step0 : p (ε) • K0124 ≈ p (s3) • p (ε) • NK • p (s3)
step0 = by-assoc-and (under (ε) (NK • p (s3)) E1.proved) Eq.refl Eq.refl

step1 : p (s3) • p (ε) • NK • p (s3) ≈ p (s3) • NK • p (ε) • p (s3)
step1 = by-assoc-and (under (p (s3)) (p (s3)) C.proved) Eq.refl Eq.refl

step2 : p (s3) • NK • p (ε) • p (s3) ≈ K0124 • p (ε)
step2 = by-assoc-and (under (p (s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (ε) • K0124 ≈ K0124 • p (ε)
proved = trans step0 (trans step1 step2)

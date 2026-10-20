{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00333 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0235 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; s2 ; s3 ; s4 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00354 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00355 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00013 as C

step0 : p (s4) • K0235 ≈ p (s1 • s2 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1)) E1.proved) Eq.refl Eq.refl

step1 : p (s1 • s2 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1)
step1 = by-assoc-and (under (p (s1 • s2 • s3)) (p (s3 • s4 • s3 • s2 • s1)) C.proved) Eq.refl Eq.refl

step2 : p (s1 • s2 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1) ≈ K0234 • p (s4)
step2 = by-assoc-and (under (p (s1 • s2 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s4) • K0235 ≈ K0234 • p (s4)
proved = trans step0 (trans step1 step2)

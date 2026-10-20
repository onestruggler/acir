{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00445 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K1234 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s0 ; s1 ; s2 ; s3 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00578 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00579 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00012 as C

step0 : p (s0) • K1234 ≈ p (s1 • s2 • s3) • p (ε) • NK • p (s3 • s2 • s1 • s0)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1 • s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s1 • s2 • s3) • p (ε) • NK • p (s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3) • NK • p (ε) • p (s3 • s2 • s1 • s0)
step1 = by-assoc-and (under (p (s1 • s2 • s3)) (p (s3 • s2 • s1 • s0)) C.proved) Eq.refl Eq.refl

step2 : p (s1 • s2 • s3) • NK • p (ε) • p (s3 • s2 • s1 • s0) ≈ K0234 • p (s0)
step2 = by-assoc-and (under (p (s1 • s2 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s0) • K1234 ≈ K0234 • p (s0)
proved = trans step0 (trans step1 step2)

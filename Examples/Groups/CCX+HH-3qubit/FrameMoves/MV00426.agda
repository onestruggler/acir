{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00426 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0356 ; K0456 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00540 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00541 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00016 as C

step0 : p (s3) • K0456 ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) E1.proved) Eq.refl Eq.refl

step1 : p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) C.proved) Eq.refl Eq.refl

step2 : p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0356 • p (s3)
step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s3) • K0456 ≈ K0356 • p (s3)
proved = trans step0 (trans step1 step2)

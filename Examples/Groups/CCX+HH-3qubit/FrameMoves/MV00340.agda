{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00340 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0235 ; K0236 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00368 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00369 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00014 as C

step0 : p (s5) • K0236 ≈ p (s1 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) E1.proved) Eq.refl Eq.refl

step1 : p (s1 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) C.proved) Eq.refl Eq.refl

step2 : p (s1 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ K0235 • p (s5)
step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s5) • K0236 ≈ K0235 • p (s5)
proved = trans step0 (trans step1 step2)

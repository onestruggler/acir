{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00297 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0146 ; K0246 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00282 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00283 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00012 as C

step0 : p (s1) • K0146 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) E1.proved) Eq.refl Eq.refl

step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) C.proved) Eq.refl Eq.refl

step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0246 • p (s1)
step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s1) • K0146 ≈ K0246 • p (s1)
proved = trans step0 (trans step1 step2)

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00322 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0167 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00332 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00333 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00017 as C

step0 : p (s3) • K0167 ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) E1.proved) Eq.refl Eq.refl

step1 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) C.proved) Eq.refl Eq.refl

step2 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ K0167 • p (s3)
step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s3) • K0167 ≈ K0167 • p (s3)
proved = trans step0 (trans step1 step2)

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00317 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0147 ; K0157 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00322 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00323 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00013 as C

step0 : p (s4) • K0157 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) E1.proved) Eq.refl Eq.refl

step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) C.proved) Eq.refl Eq.refl

step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0147 • p (s4)
step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s4) • K0157 ≈ K0147 • p (s4)
proved = trans step0 (trans step1 step2)

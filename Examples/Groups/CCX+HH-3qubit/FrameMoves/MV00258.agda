{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00258 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0125 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; s4 ; s6 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00156 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00156 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00015 as C

step0 : p (s6) • K0125 ≈ p (s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3)
step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3)) E1.proved) Eq.refl Eq.refl

step1 : p (s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3) ≈ p (s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3)
step1 = by-assoc-and (under (p (s3 • s4 • s3)) (p (s3 • s4 • s3)) C.proved) Eq.refl Eq.refl

step2 : p (s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3) ≈ K0125 • p (s6)
step2 = by-assoc-and (under (p (s3 • s4 • s3) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s6) • K0125 ≈ K0125 • p (s6)
proved = trans step0 (trans step1 step2)

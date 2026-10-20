{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00054 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M7 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00061 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00061 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00005 as C

step0 : p (s5) • M7 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) C.proved) Eq.refl Eq.refl

step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M7 • p (s5)
step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s5) • M7 ≈ M7 • p (s5)
proved = trans step0 (trans step1 step2)

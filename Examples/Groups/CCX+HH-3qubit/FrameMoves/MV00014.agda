{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00014 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M2 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; p ; s0 ; s1 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00015 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00016 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00001 as C

step0 : p (s0) • M2 ≈ p (s0 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s0)
step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s0 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s0) ≈ p (s0 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s0)
step1 = by-assoc-and (under (p (s0 • s1 • s0)) (p (s0 • s1 • s0)) C.proved) Eq.refl Eq.refl

step2 : p (s0 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s0) ≈ M2 • p (s0)
step2 = by-assoc-and (under (p (s0 • s1 • s0) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s0) • M2 ≈ M2 • p (s0)
proved = trans step0 (trans step1 step2)

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00009 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; p ; s0 ; s2 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00010 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00010 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00002 as C

step0 : p (s2) • M1 ≈ p (s0) • p (s2) • m0 • p (s0)
step0 = by-assoc-and (under (ε) (m0 • p (s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s0) • p (s2) • m0 • p (s0) ≈ p (s0) • m0 • p (s2) • p (s0)
step1 = by-assoc-and (under (p (s0)) (p (s0)) C.proved) Eq.refl Eq.refl

step2 : p (s0) • m0 • p (s2) • p (s0) ≈ M1 • p (s2)
step2 = by-assoc-and (under (p (s0) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s2) • M1 ≈ M1 • p (s2)
proved = trans step0 (trans step1 step2)

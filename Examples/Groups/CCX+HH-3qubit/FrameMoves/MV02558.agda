{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02558 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; p ; s0 ; s1 ; s2 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01371 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01371 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00000 as C

step0 : p (ε) • M3 ≈ p (s0 • s1 • s2 • s1 • s0) • p (ε) • m0 • p (s0 • s1 • s2 • s1 • s0)
step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s0 • s1 • s2 • s1 • s0) • p (ε) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (ε) • p (s0 • s1 • s2 • s1 • s0)
step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) C.proved) Eq.refl Eq.refl

step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (ε) • p (s0 • s1 • s2 • s1 • s0) ≈ M3 • p (ε)
step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (ε) • M3 ≈ M3 • p (ε)
proved = trans step0 (trans step1 step2)

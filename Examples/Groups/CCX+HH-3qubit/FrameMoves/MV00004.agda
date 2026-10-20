{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00004 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; p ; s4 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00005 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00005 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00004 as C

step0 : p (s4) • M0 ≈ p (ε) • p (s4) • m0 • p (ε)
step0 = by-assoc-and (under (ε) (m0 • p (ε)) E1.proved) Eq.refl Eq.refl

step1 : p (ε) • p (s4) • m0 • p (ε) ≈ p (ε) • m0 • p (s4) • p (ε)
step1 = by-assoc-and (under (p (ε)) (p (ε)) C.proved) Eq.refl Eq.refl

step2 : p (ε) • m0 • p (s4) • p (ε) ≈ M0 • p (s4)
step2 = by-assoc-and (under (p (ε) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s4) • M0 ≈ M0 • p (s4)
proved = trans step0 (trans step1 step2)

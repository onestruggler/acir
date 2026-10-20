{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02557 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; p ; s0 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00000 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00000 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00000 as C

step0 : p (ε) • M1 ≈ p (s0) • p (ε) • m0 • p (s0)
step0 = by-assoc-and (under (ε) (m0 • p (s0)) E1.proved) Eq.refl Eq.refl

step1 : p (s0) • p (ε) • m0 • p (s0) ≈ p (s0) • m0 • p (ε) • p (s0)
step1 = by-assoc-and (under (p (s0)) (p (s0)) C.proved) Eq.refl Eq.refl

step2 : p (s0) • m0 • p (ε) • p (s0) ≈ M1 • p (ε)
step2 = by-assoc-and (under (p (s0) • m0) (ε) E2.proved) Eq.refl Eq.refl

proved : p (ε) • M1 ≈ M1 • p (ε)
proved = trans step0 (trans step1 step2)

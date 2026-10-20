{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00248 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; NK ; _•_ ; _≈_ ; by-assoc-and ; p ; s6 ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00007 as E1
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00007 as E2
import Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00015 as C

step0 : p (s6) • K0123 ≈ p (ε) • p (s6) • NK • p (ε)
step0 = by-assoc-and (under (ε) (NK • p (ε)) E1.proved) Eq.refl Eq.refl

step1 : p (ε) • p (s6) • NK • p (ε) ≈ p (ε) • NK • p (s6) • p (ε)
step1 = by-assoc-and (under (p (ε)) (p (ε)) C.proved) Eq.refl Eq.refl

step2 : p (ε) • NK • p (s6) • p (ε) ≈ K0123 • p (s6)
step2 = by-assoc-and (under (p (ε) • NK) (ε) E2.proved) Eq.refl Eq.refl

proved : p (s6) • K0123 ≈ K0123 • p (s6)
proved = trans step0 (trans step1 step2)

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Am3 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M3 ; _•_ ; _≈_ ; by-assoc-and ; cong ; forget-frame ; m0 ; m3 ; p ; refl ; s0 ; s1 ; s2 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00630)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00948 ; module PE00949)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : m3 ≈ p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2)
step0 = by-assoc-and (cong (cong (GP.gatet23) (cong (GP.gatet12) (GP.gatet01))) (cong (refl {w = m0}) (cong (GP.gatet01) (cong (GP.gatet12) (GP.gatet23))))) Eq.refl Eq.refl

step1 : p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2) ≈ p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2)
step1 = cong refl (cong refl PE00948.proved)

step2 : p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2) ≈ M3
step2 = forget-frame (by-assoc-and MV00630.proved Eq.refl Eq.refl) (by-assoc-and PE00949.proved Eq.refl Eq.refl)

proved : m3 ≈ M3
proved = trans step0 (trans step1 step2)

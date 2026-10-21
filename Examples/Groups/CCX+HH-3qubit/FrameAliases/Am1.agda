{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Am1 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; _•_ ; _≈_ ; by-assoc-and ; cong ; forget-frame ; m0 ; m1 ; p ; refl ; s0 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00000 ; module PE00008)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : m1 ≈ p (s0) • m0 • p (s0)
step0 = by-assoc-and (cong (GP.gatet01) (cong (refl {w = m0}) (GP.gatet01))) Eq.refl Eq.refl

step1 : p (s0) • m0 • p (s0) ≈ p (s0) • m0 • p (s0)
step1 = cong refl (cong refl PE00000.proved)

step2 : p (s0) • m0 • p (s0) ≈ M1
step2 = forget-frame (by-assoc-and MV00000.proved Eq.refl Eq.refl) (by-assoc-and PE00008.proved Eq.refl Eq.refl)

proved : m1 ≈ M1
proved = trans step0 (trans step1 step2)

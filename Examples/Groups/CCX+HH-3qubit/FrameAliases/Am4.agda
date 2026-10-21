{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Am4 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M4 ; _•_ ; _≈_ ; by-assoc-and ; cong ; forget-frame ; m0 ; m4 ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00631)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00950 ; module PE00951)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : m4 ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • m0 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
step0 = by-assoc-and (cong (GP.gateX0) (cong (refl {w = m0}) (GP.gateX0))) Eq.refl Eq.refl

step1 : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • m0 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • m0 • p (s3 • s4 • s5 • s6 • s2 • s3 • s4 • s5 • s1 • s2 • s3 • s4 • s0 • s1 • s2 • s3)
step1 = cong refl (cong refl PE00950.proved)

step2 : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • m0 • p (s3 • s4 • s5 • s6 • s2 • s3 • s4 • s5 • s1 • s2 • s3 • s4 • s0 • s1 • s2 • s3) ≈ M4
step2 = forget-frame (by-assoc-and MV00631.proved Eq.refl Eq.refl) (by-assoc-and PE00951.proved Eq.refl Eq.refl)

proved : m4 ≈ M4
proved = trans step0 (trans step1 step2)

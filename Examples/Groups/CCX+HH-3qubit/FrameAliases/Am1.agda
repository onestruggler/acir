{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.Am1 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; _•_ ; _≈_ ; by-assoc-and ; cong ; forget-frame ; m0 ; m1 ; p ; refl ; s0 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00000 as Move
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00000 as R
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00008 as Inv
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : m1 ≈ p (s0) • m0 • p (s0)
step0 = by-assoc-and (cong (GP.gatet01) (cong (refl {w = m0}) (GP.gatet01))) Eq.refl Eq.refl

step1 : p (s0) • m0 • p (s0) ≈ p (s0) • m0 • p (s0)
step1 = cong refl (cong refl R.proved)

step2 : p (s0) • m0 • p (s0) ≈ M1
step2 = forget-frame (by-assoc-and Move.proved Eq.refl Eq.refl) (by-assoc-and Inv.proved Eq.refl Eq.refl)

proved : m1 ≈ M1
proved = trans step0 (trans step1 step2)

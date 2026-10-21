{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At01 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; _≈_ ; by-assoc-and ; p ; s0 ; t01 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00000)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t01 ≈ p (s0)
step0 = by-assoc-and (GP.gatet01) Eq.refl Eq.refl

proved : t01 ≈ X01
proved = trans step0 (by-assoc-and PE00000.proved Eq.refl Eq.refl)

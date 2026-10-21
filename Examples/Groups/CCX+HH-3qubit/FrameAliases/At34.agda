{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At34 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; _≈_ ; by-assoc-and ; p ; s3 ; t34 ; trans ; module Eq)
open K
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00004)
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t34 ≈ p (s3)
step0 = by-assoc-and (GP.gatet34) Eq.refl Eq.refl

proved : t34 ≈ X34
proved = trans step0 (by-assoc-and PE00004.proved Eq.refl Eq.refl)

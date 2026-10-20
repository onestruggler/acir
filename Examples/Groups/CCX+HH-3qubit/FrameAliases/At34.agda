{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At34 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; _≈_ ; by-assoc-and ; p ; s3 ; t34 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00004 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t34 ≈ p (s3)
step0 = by-assoc-and (GP.gatet34) Eq.refl Eq.refl

proved : t34 ≈ X34
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

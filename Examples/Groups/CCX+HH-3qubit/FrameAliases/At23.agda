{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At23 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; _≈_ ; by-assoc-and ; p ; s2 ; t23 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00003 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t23 ≈ p (s2)
step0 = by-assoc-and (GP.gatet23) Eq.refl Eq.refl

proved : t23 ≈ X23
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.At45 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X45 ; _≈_ ; by-assoc-and ; p ; s4 ; t45 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00005 as E
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GP

step0 : t45 ≈ p (s4)
step0 = by-assoc-and (GP.gatet45) Eq.refl Eq.refl

proved : t45 ≈ X45
proved = trans step0 (by-assoc-and E.proved Eq.refl Eq.refl)

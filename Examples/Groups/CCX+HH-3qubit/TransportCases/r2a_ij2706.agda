{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2706 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01198 as E

proved : X27 • X06 ≈ X06 • X27
proved = by-assoc-and E.proved Eq.refl Eq.refl

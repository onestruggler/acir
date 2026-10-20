{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2506 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01167 as E

proved : X25 • X06 ≈ X06 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

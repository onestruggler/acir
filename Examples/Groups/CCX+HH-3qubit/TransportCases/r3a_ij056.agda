{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij056 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X06 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01313 as E

proved : X05 • X06 ≈ X56 • X05
proved = by-assoc-and E.proved Eq.refl Eq.refl

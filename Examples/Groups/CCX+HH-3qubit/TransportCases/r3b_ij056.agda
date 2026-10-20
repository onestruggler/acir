{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij056 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X06 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00045 as E

proved : X56 • X05 ≈ X06 • X56
proved = by-assoc-and E.proved Eq.refl Eq.refl

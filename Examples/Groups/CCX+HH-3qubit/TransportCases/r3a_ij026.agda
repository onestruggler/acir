{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij026 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X06 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01304 as E

proved : X02 • X06 ≈ X26 • X02
proved = by-assoc-and E.proved Eq.refl Eq.refl

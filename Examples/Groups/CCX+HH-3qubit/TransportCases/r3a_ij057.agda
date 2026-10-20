{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij057 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X07 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01314 as E

proved : X05 • X07 ≈ X57 • X05
proved = by-assoc-and E.proved Eq.refl Eq.refl

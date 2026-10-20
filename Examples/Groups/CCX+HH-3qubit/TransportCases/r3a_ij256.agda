{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij256 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; X26 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01329 as E

proved : X25 • X26 ≈ X56 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

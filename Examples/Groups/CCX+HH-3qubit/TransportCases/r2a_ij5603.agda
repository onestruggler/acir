{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij5603 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00029 as E

proved : X56 • X03 ≈ X03 • X56
proved = by-assoc-and E.proved Eq.refl Eq.refl

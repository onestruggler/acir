{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X56 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00202 as E

proved : X56 • X57 ≈ X67 • X56
proved = by-assoc-and E.proved Eq.refl Eq.refl

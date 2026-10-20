{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0645 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01056 as E

proved : X06 • X45 ≈ X45 • X06
proved = by-assoc-and E.proved Eq.refl Eq.refl

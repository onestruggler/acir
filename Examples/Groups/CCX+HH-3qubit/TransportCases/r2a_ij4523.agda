{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4523 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00113 as E

proved : X45 • X23 ≈ X23 • X45
proved = by-assoc-and E.proved Eq.refl Eq.refl

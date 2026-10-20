{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4527 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X27 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00141 as E

proved : X45 • X27 ≈ X27 • X45
proved = by-assoc-and E.proved Eq.refl Eq.refl

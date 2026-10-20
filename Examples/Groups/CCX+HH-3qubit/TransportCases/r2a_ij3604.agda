{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3604 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01226 as E

proved : X36 • X04 ≈ X04 • X36
proved = by-assoc-and E.proved Eq.refl Eq.refl

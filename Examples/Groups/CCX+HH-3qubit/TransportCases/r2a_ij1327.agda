{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1327 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01082 as E

proved : X13 • X27 ≈ X27 • X13
proved = by-assoc-and E.proved Eq.refl Eq.refl

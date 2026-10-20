{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1427 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01097 as E

proved : X14 • X27 ≈ X27 • X14
proved = by-assoc-and E.proved Eq.refl Eq.refl

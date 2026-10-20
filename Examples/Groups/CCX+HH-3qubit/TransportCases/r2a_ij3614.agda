{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3614 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01230 as E

proved : X36 • X14 ≈ X14 • X36
proved = by-assoc-and E.proved Eq.refl Eq.refl

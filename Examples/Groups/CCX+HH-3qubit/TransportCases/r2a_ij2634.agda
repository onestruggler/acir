{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2634 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X26 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01188 as E

proved : X26 • X34 ≈ X34 • X26
proved = by-assoc-and E.proved Eq.refl Eq.refl

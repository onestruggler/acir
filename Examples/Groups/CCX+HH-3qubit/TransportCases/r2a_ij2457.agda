{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01162 as E

proved : X24 • X57 ≈ X57 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

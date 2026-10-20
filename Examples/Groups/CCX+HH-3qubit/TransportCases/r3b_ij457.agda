{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X45 ; X47 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01370 as E

proved : X57 • X45 ≈ X47 • X57
proved = by-assoc-and E.proved Eq.refl Eq.refl

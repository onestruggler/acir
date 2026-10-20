{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01011 as E

proved : X03 • X56 ≈ X56 • X03
proved = by-assoc-and E.proved Eq.refl Eq.refl

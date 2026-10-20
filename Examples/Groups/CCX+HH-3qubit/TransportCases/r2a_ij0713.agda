{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0713 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; X13 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01060 as E

proved : X07 • X13 ≈ X13 • X07
proved = by-assoc-and E.proved Eq.refl Eq.refl

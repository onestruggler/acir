{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4602 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01255 as E

proved : X46 • X02 ≈ X02 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

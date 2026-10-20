{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij024 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X04 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01302 as E

proved : X02 • X04 ≈ X24 • X02
proved = by-assoc-and E.proved Eq.refl Eq.refl

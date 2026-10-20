{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0423 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01019 as E

proved : X04 • X23 ≈ X23 • X04
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01013 as E

proved : X03 • X67 ≈ X67 • X03
proved = by-assoc-and E.proved Eq.refl Eq.refl

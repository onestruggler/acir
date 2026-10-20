{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2416 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01156 as E

proved : X24 • X16 ≈ X16 • X24
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1623 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01124 as E

proved : X16 • X23 ≈ X23 • X16
proved = by-assoc-and E.proved Eq.refl Eq.refl

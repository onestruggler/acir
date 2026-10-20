{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1204 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00033 as E

proved : X12 • X04 ≈ X04 • X12
proved = by-assoc-and E.proved Eq.refl Eq.refl

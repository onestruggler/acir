{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6715 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00095 as E

proved : X67 • X15 ≈ X15 • X67
proved = by-assoc-and E.proved Eq.refl Eq.refl

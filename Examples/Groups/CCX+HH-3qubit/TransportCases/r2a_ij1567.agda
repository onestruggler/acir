{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1567 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01118 as E

proved : X15 • X67 ≈ X67 • X15
proved = by-assoc-and E.proved Eq.refl Eq.refl

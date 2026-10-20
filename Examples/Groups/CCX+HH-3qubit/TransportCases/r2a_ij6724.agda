{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6724 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00122 as E

proved : X67 • X24 ≈ X24 • X67
proved = by-assoc-and E.proved Eq.refl Eq.refl

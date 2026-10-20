{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4512 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00072 as E

proved : X45 • X12 ≈ X12 • X45
proved = by-assoc-and E.proved Eq.refl Eq.refl

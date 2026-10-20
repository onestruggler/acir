{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4503 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00028 as E

proved : X45 • X03 ≈ X03 • X45
proved = by-assoc-and E.proved Eq.refl Eq.refl

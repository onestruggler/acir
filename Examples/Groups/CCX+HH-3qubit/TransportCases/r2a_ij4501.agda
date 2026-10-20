{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4501 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00012 as E

proved : X45 • X01 ≈ X01 • X45
proved = by-assoc-and E.proved Eq.refl Eq.refl

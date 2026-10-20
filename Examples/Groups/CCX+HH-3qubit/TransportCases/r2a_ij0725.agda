{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0725 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01066 as E

proved : X07 • X25 ≈ X25 • X07
proved = by-assoc-and E.proved Eq.refl Eq.refl

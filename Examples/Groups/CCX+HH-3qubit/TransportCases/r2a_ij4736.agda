{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4736 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X36 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01282 as E

proved : X47 • X36 ≈ X36 • X47
proved = by-assoc-and E.proved Eq.refl Eq.refl

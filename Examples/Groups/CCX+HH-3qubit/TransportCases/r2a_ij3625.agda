{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3625 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01234 as E

proved : X36 • X25 ≈ X25 • X36
proved = by-assoc-and E.proved Eq.refl Eq.refl

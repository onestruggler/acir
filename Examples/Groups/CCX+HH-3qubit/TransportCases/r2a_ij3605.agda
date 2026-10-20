{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3605 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01227 as E

proved : X36 • X05 ≈ X05 • X36
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1702 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X17 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01134 as E

proved : X17 • X02 ≈ X02 • X17
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1723 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X17 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01139 as E

proved : X17 • X23 ≈ X23 • X17
proved = by-assoc-and E.proved Eq.refl Eq.refl

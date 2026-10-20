{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00193 as E

proved : X23 • X56 ≈ X56 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

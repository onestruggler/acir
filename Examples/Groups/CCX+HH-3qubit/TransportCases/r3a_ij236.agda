{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X26 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00132 as E

proved : X23 • X26 ≈ X36 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

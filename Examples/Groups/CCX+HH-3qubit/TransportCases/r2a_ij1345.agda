{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1345 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01083 as E

proved : X13 • X45 ≈ X45 • X13
proved = by-assoc-and E.proved Eq.refl Eq.refl

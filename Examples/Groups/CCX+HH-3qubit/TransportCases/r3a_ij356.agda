{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij356 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X35 ; X36 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01332 as E

proved : X35 • X36 ≈ X56 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

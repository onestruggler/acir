{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3524 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01218 as E

proved : X35 • X24 ≈ X24 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

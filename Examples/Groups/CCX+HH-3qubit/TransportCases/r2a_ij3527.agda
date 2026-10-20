{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3527 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X27 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01220 as E

proved : X35 • X27 ≈ X27 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

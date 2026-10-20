{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4635 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X35 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01266 as E

proved : X46 • X35 ≈ X35 • X46
proved = by-assoc-and E.proved Eq.refl Eq.refl

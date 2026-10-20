{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3504 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01211 as E

proved : X35 • X04 ≈ X04 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

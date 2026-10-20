{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2607 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01183 as E

proved : X26 • X07 ≈ X07 • X26
proved = by-assoc-and E.proved Eq.refl Eq.refl

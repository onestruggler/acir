{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2603 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01180 as E

proved : X26 • X03 ≈ X03 • X26
proved = by-assoc-and E.proved Eq.refl Eq.refl

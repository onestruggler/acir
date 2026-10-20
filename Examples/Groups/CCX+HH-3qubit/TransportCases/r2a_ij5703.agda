{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij5703 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01286 as E

proved : X57 • X03 ≈ X03 • X57
proved = by-assoc-and E.proved Eq.refl Eq.refl

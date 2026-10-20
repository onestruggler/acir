{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0457 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01027 as E

proved : X04 • X57 ≈ X57 • X04
proved = by-assoc-and E.proved Eq.refl Eq.refl

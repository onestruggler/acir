{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4756 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X47 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01283 as E

proved : X47 • X56 ≈ X56 • X47
proved = by-assoc-and E.proved Eq.refl Eq.refl

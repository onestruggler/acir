{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1547 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01117 as E

proved : X15 • X47 ≈ X47 • X15
proved = by-assoc-and E.proved Eq.refl Eq.refl

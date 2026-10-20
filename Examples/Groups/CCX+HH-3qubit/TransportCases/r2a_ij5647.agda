{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij5647 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X47 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00189 as E

proved : X56 • X47 ≈ X47 • X56
proved = by-assoc-and E.proved Eq.refl Eq.refl

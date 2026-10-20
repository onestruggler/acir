{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1437 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01100 as E

proved : X14 • X37 ≈ X37 • X14
proved = by-assoc-and E.proved Eq.refl Eq.refl

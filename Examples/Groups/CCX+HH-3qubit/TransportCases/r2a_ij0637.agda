{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0637 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01055 as E

proved : X06 • X37 ≈ X37 • X06
proved = by-assoc-and E.proved Eq.refl Eq.refl

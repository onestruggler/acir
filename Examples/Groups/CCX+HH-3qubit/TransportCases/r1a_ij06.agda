{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij06 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00961 as E

proved : X06 • X06 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

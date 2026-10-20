{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij13 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00964 as E

proved : X13 • X13 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

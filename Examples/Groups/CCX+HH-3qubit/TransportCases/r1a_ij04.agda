{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij04 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00959 as E

proved : X04 • X04 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

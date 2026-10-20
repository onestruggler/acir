{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij26 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X26 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00972 as E

proved : X26 • X26 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

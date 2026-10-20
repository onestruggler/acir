{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij25 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00971 as E

proved : X25 • X25 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

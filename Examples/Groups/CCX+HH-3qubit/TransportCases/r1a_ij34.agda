{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij34 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00213 as E

proved : X34 • X34 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

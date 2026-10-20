{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij37 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X37 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00976 as E

proved : X37 • X37 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

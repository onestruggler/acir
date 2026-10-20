{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2537 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01175 as E

proved : X25 • X37 ≈ X37 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

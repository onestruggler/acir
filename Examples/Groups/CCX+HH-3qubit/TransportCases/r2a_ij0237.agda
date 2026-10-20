{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0237 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00992 as E

proved : X02 • X37 ≈ X37 • X02
proved = by-assoc-and E.proved Eq.refl Eq.refl

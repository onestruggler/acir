{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1402 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X14 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01089 as E

proved : X14 • X02 ≈ X02 • X14
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3402 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00019 as E

proved : X34 • X02 ≈ X02 • X34
proved = by-assoc-and E.proved Eq.refl Eq.refl

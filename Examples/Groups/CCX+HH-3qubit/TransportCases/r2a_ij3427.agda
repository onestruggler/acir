{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3427 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X27 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00140 as E

proved : X34 • X27 ≈ X27 • X34
proved = by-assoc-and E.proved Eq.refl Eq.refl

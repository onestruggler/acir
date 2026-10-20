{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3425 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00126 as E

proved : X34 • X25 ≈ X25 • X34
proved = by-assoc-and E.proved Eq.refl Eq.refl

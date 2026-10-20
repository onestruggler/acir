{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2514 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X25 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01170 as E

proved : X25 • X14 ≈ X14 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

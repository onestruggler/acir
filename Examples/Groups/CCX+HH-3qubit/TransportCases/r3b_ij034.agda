{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij034 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X04 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00027 as E

proved : X34 • X03 ≈ X04 • X34
proved = by-assoc-and E.proved Eq.refl Eq.refl

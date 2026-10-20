{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3516 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01216 as E

proved : X35 • X16 ≈ X16 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

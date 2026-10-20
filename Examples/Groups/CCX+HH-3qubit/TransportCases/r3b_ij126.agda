{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij126 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; X16 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01353 as E

proved : X26 • X12 ≈ X16 • X26
proved = by-assoc-and E.proved Eq.refl Eq.refl

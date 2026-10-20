{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1657 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01133 as E

proved : X16 • X57 ≈ X57 • X16
proved = by-assoc-and E.proved Eq.refl Eq.refl

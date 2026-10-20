{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij1602 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X16 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01119 as E

proved : X16 • X02 ≈ X02 • X16
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij16 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00967 as E

proved : X16 • X16 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij5602 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00021 as E

proved : X56 • X02 ≈ X02 • X56
proved = by-assoc-and E.proved Eq.refl Eq.refl

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3b_ij023 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X03 ; X23 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00018 as E

proved : X23 • X02 ≈ X03 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

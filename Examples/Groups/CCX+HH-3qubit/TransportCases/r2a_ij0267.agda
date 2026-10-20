{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0267 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00998 as E

proved : X02 • X67 ≈ X67 • X02
proved = by-assoc-and E.proved Eq.refl Eq.refl

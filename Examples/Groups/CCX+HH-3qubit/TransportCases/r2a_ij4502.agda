{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4502 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X02 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00020 as E

proved : X45 • X02 ≈ X02 • X45
proved = by-assoc-and E.proved Eq.refl Eq.refl

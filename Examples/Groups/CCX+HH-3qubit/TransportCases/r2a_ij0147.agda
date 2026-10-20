{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0147 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00184 as E

proved : X01 • X47 ≈ X47 • X01
proved = by-assoc-and E.proved Eq.refl Eq.refl

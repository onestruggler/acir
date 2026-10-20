{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r1a_ij24 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; _•_ ; _≈_ ; by-assoc-and ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00970 as E

proved : X24 • X24 ≈ ε
proved = by-assoc-and E.proved Eq.refl Eq.refl

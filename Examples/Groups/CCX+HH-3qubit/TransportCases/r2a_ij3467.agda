{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij3467 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00207 as E

proved : X34 • X67 ≈ X67 • X34
proved = by-assoc-and E.proved Eq.refl Eq.refl

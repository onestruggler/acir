{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2367 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00206 as E

proved : X23 • X67 ≈ X67 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

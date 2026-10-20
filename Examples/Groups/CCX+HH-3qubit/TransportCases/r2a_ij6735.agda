{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij6735 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X35 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00156 as E

proved : X67 • X35 ≈ X35 • X67
proved = by-assoc-and E.proved Eq.refl Eq.refl

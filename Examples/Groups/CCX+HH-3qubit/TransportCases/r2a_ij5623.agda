{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij5623 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00114 as E

proved : X56 • X23 ≈ X23 • X56
proved = by-assoc-and E.proved Eq.refl Eq.refl

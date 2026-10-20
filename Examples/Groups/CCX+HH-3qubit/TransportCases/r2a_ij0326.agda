{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij0326 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01006 as E

proved : X03 • X26 ≈ X26 • X03
proved = by-assoc-and E.proved Eq.refl Eq.refl

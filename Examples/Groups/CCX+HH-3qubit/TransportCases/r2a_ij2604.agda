{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij2604 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01181 as E

proved : X26 • X04 ≈ X04 • X26
proved = by-assoc-and E.proved Eq.refl Eq.refl

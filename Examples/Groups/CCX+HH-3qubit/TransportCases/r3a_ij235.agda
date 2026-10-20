{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij235 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X25 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00125 as E

proved : X23 • X25 ≈ X35 • X23
proved = by-assoc-and E.proved Eq.refl Eq.refl

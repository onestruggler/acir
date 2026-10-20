{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij257 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X25 ; X27 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01330 as E

proved : X25 • X27 ≈ X57 • X25
proved = by-assoc-and E.proved Eq.refl Eq.refl

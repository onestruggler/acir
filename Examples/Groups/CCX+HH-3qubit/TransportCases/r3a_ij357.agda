{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r3a_ij357 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X35 ; X37 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE01333 as E

proved : X35 • X37 ≈ X57 • X35
proved = by-assoc-and E.proved Eq.refl Eq.refl

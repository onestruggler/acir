{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00006 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; axiom ; m0 ; p ; r090 ; s6)
open K

proved : p (s6) • m0 ≈ m0 • p (s6)
proved = axiom r090

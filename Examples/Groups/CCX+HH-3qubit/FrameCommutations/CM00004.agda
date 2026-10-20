{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00004 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; axiom ; m0 ; p ; r088 ; s4)
open K

proved : p (s4) • m0 ≈ m0 • p (s4)
proved = axiom r088

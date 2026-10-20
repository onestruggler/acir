{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00005 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; axiom ; m0 ; p ; r089 ; s5)
open K

proved : p (s5) • m0 ≈ m0 • p (s5)
proved = axiom r089

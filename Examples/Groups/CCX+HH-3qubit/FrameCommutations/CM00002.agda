{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00002 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; axiom ; m0 ; p ; r086 ; s2)
open K

proved : p (s2) • m0 ≈ m0 • p (s2)
proved = axiom r086

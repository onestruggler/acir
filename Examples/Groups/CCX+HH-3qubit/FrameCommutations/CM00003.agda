{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00003 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; axiom ; m0 ; p ; r087 ; s3)
open K

proved : p (s3) • m0 ≈ m0 • p (s3)
proved = axiom r087

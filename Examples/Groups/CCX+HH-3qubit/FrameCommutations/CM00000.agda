{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameCommutations.CM00000 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (_•_ ; _≈_ ; left-unit ; m0 ; p ; right-unit ; sym ; trans ; ε)
open K

proved : p (ε) • m0 ≈ m0 • p (ε)
proved = trans left-unit (sym right-unit)
